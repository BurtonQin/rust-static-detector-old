// Place: Direct, Indirect
// Target: Replace as many Indirect with Directs
// Graph:
// Node: Alloc_i, Concrete(PlaceRef), Virtual(PlaceRef)
// Edge: Node -> Nodes
// if Place is Indirect:
//  if a.b.Deref: cannot find a.b but a.b.Deref exist, add a.b.Deref
//      Concrete(a.b) -> Virtual(a.b.Deref)
//      return Virtual(a.b.Deref)
//  else if a.b.Deref.c.d: resolve a.b.Deref to x.y, x.y.c.d not exists
//      NewPlace(x.y.c.d)
//      return Concrete(x.y.c.d)
//  else if a.b.Deref.c.d.Deref: resolve a.b.Deref to x.y, x.y.c.d not exists
//      NewPlace(x.y.c.d) -> NewPlace(x.y.c.d.Deref)
//      return Virtual(x.y.c.d.Deref)
//  else if a.b.Deref.c.d.Deref: resolve a.b.Deref to x.y, x.y.c.d exists
//      x.y.c.d.Deref not exists
//      Concrete(xy.c.d) -> NewPlace(x.y.c.d.Deref)
//      return Virtual(x.y.c.d.Deref)
// else: // PlaceRef is Direct
//  return Concrete(PlaceRef)
// statement: p = &(_) o:
//  left = resolve(p)
//  right = resolve(o)
//  if left -> Virtual(?):
//      replace Virtual with right
//  else:
//      left -> right
// statement: p = move o:
//  left = resolve(p)
//  right = resolve(o)
//  replace left -> ? with right -> ?
//  mark o as Moved
// statement: p = o: (Copy)
//  left = resolve(p)
//  right = resolve(o)
//  replace left -> ? with right -> ?
// Alloc(i) => {Return, Arg, Constant(c), Static(s)}
use crate::util::Graph;
use once_cell::sync::Lazy;
use regex::Regex;
use rustc_hir::def_id::DefId;
use rustc_middle::bug;
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::{
    BasicBlock, Body, Constant, Local, Location, Operand, Place, PlaceElem, PlaceRef,
    ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, RETURN_PLACE,
};
use rustc_middle::ty::{self, Instance, InstanceDef, List, Ty, TyCtxt};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MemCell<'tcx> {
    Alloc(PlaceRef<'tcx>, Option<Location>),
    Concrete(PlaceRef<'tcx>),
    Virtual(PlaceRef<'tcx>),
}

impl<'tcx> MemCell<'tcx> {
    pub fn from_direct_place(place: Place<'tcx>) -> Option<Self> {
        if place.is_indirect() {
            None
        } else {
            Some(MemCell::Concrete(place.as_ref()))
        }
    }

    pub fn from_direct_place_ref(place_ref: PlaceRef<'tcx>) -> Self {
        // Must ensure place_ref is direct
        MemCell::Concrete(place_ref)
    }

    pub fn from_virtual(place_ref: PlaceRef<'tcx>) -> Self {
        MemCell::Virtual(place_ref)
    }

    pub fn from_place_ref(place_ref: PlaceRef<'tcx>) -> Self {
        if place_ref
            .projection
            .iter()
            .any(|elem| *elem == ProjectionElem::Deref)
        {
            MemCell::Virtual(place_ref)
        } else {
            MemCell::Concrete(place_ref)
        }
    }

    pub fn as_place_ref(self) -> Option<PlaceRef<'tcx>> {
        match self {
            MemCell::Alloc(_, _) => None,
            MemCell::Concrete(place_ref) | MemCell::Virtual(place_ref) => Some(place_ref),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PtsState<'tcx> {
    pub pts: Graph<MemCell<'tcx>>,
}

impl<'tcx> PtsState<'tcx> {
    pub fn new() -> Self {
        Self {
            pts: Graph::<MemCell<'tcx>>::new(),
        }
    }

    pub fn debug_print(&self) {
        self.pts.debug_print();
    }

    pub fn union(&mut self, other: Option<Rc<PtsState<'tcx>>>) -> bool {
        match other {
            Some(state) => self.pts.union(Graph::clone(&state.pts)),
            None => false,
        }
    }

    pub fn add_direct_node(&mut self, place_ref: PlaceRef<'tcx>) -> bool {
        // Must ensure place_ref is direct
        let direct_node = MemCell::from_direct_place_ref(place_ref);
        self.pts.add_node(direct_node)
    }

    pub fn add_virtual_node(&mut self, place_ref: PlaceRef<'tcx>) -> bool {
        let virtual_node = MemCell::from_virtual(place_ref);
        self.pts.add_node(virtual_node)
    }

    pub fn get_node(&self, place_ref: PlaceRef<'tcx>) -> Option<MemCell<'tcx>> {
        let direct_node = MemCell::from_direct_place_ref(place_ref);
        match self.pts.nodes.get(&direct_node) {
            Some(node) => Some(*node),
            None => {
                let virtual_node = MemCell::from_virtual(place_ref);
                match self.pts.nodes.get(&virtual_node) {
                    Some(node) => Some(*node),
                    None => None,
                }
            }
        }
    }

    pub fn points_to(&self, node: MemCell<'tcx>) -> Option<HashSet<MemCell<'tcx>>> {
        self.pts.neighbors(node).map(|nodes| nodes.clone())
    }

    pub fn set_points_to(&mut self, pointer: MemCell<'tcx>, pointee: MemCell<'tcx>) -> bool {
        if let MemCell::Virtual(new_pointee) = pointee {
            let mut changed = false;
            let deref_num = new_pointee
                .projection
                .iter()
                .filter_map(|elem| {
                    if *elem == ProjectionElem::Deref {
                        Some(*elem)
                    } else {
                        None
                    }
                })
                .count();
            if let Some(old_pointees) = self.points_to(pointer) {
                let mut has_removed = false;
                for old_pointee in old_pointees {
                    if let MemCell::Virtual(old_pointee_place) = old_pointee {
                        let old_deref_num = old_pointee_place
                            .projection
                            .iter()
                            .filter_map(|elem| {
                                if *elem == ProjectionElem::Deref {
                                    Some(*elem)
                                } else {
                                    None
                                }
                            })
                            .count();
                        if old_deref_num > deref_num {
                            changed |= self.pts.replace_node(old_pointee, pointee);
                            has_removed = true;
                        } else if old_deref_num == deref_num {
                            // remove _1 -> _1.Deref
                            if let Some(pointee_place_ref) = pointee.as_place_ref() {
                                if let Some(pointer_place_ref) = pointer.as_place_ref() {
                                    if pointee_place_ref.local == pointer_place_ref.local {
                                        changed |= self.pts.replace_node(pointer, old_pointee);
                                        has_removed = true;
                                    }
                                }
                            }
                        }
                    }
                }
                self.pts.add_edge(pointer, pointee) | changed
            } else {
                self.pts.add_edge(pointer, pointee)
            }
        } else {
            let mut changed = false;
            if let Some(old_pointees) = self.points_to(pointer) {
                for old_pointee in old_pointees {
                    if let MemCell::Virtual(_) = old_pointee {
                        changed |= self.pts.replace_node(old_pointee, pointee);
                    }
                }
            }
            self.pts.add_edge(pointer, pointee) | changed
        }
    }

    pub fn batch_points_to(&self, nodes: HashSet<MemCell<'tcx>>) -> Option<HashSet<MemCell<'tcx>>> {
        let mut pointees = HashSet::new();
        for node in nodes {
            if let Some(nodes) = self.points_to(node) {
                pointees.extend(nodes.into_iter());
            }
        }
        if pointees.is_empty() {
            None
        } else {
            Some(pointees)
        }
    }

    pub fn set_points_to_strong_update(
        &mut self,
        pointer: MemCell<'tcx>,
        pointee: MemCell<'tcx>,
    ) -> bool {
        self.pts.remove_all_edges(pointer);
        self.pts.add_edge(pointer, pointee)
    }

    pub fn set_batch_points_to_strong_update(
        &mut self,
        pointers: HashSet<MemCell<'tcx>>,
        pointees: HashSet<MemCell<'tcx>>,
    ) -> bool {
        let mut changed = false;
        for pointer in pointers {
            for pointee in pointees.iter() {
                changed |= self.set_points_to_strong_update(pointer, *pointee);
            }
        }
        changed
    }

    pub fn set_batch_points_to(
        &mut self,
        pointers: HashSet<MemCell<'tcx>>,
        pointees: HashSet<MemCell<'tcx>>,
    ) -> bool {
        let mut changed = false;
        for pointer in pointers {
            for pointee in pointees.iter() {
                changed |= self.set_points_to(pointer, *pointee);
            }
        }
        changed
    }

    pub fn process_place(
        &mut self,
        place: Place<'tcx>,
        concrete_places: &mut ConcretePlaces<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> (HashSet<MemCell<'tcx>>, bool, bool) {
        // println!("{:?}", place);
        if let Some(node) = MemCell::from_direct_place(place) {
            // direct place
            let mut result = HashSet::new();
            let added = self.pts.add_node(node);
            result.insert(node);
            (result, added, false)
        } else {
            // indirect place
            let mut has_derefed = false;
            let mut pointees = HashSet::new();
            let mut last_derefed_pos = 0usize;
            let mut place_added = false;
            let mut added = false;
            // a.b.c
            // => a, .b
            // => a.b, .c
            for i in 0..place.projection.len() {
                match place.projection[i] {
                    ProjectionElem::Deref => {
                        if !has_derefed {
                            has_derefed = true;
                            let pre = PlaceRef {
                                local: place.local,
                                projection: &place.projection[..i],
                            };
                            // pre must be direct
                            let node = MemCell::from_direct_place_ref(pre);
                            if let Some(nodes) = self.pts.neighbors(node) {
                                // found derefed
                                pointees.extend(nodes.iter().copied());
                            } else {
                                // create a virtual node with Deref
                                let pre_next = PlaceRef {
                                    local: place.local,
                                    projection: &place.projection[..i + 1],
                                };
                                let node = MemCell::from_virtual(pre_next);
                                added |= self.pts.add_node(node);
                                pointees.insert(node);
                            }
                        } else {
                            // combine pointees and elems after last Deref as new Place
                            let new_proj = &place.projection[last_derefed_pos + 1..i];
                            // pointees combine new_proj
                            let mut new_pointees = HashSet::new();
                            for pointee in pointees.iter() {
                                let place_ref = pointee.as_place_ref();
                                if let Some(place_ref) = place_ref {
                                    let (combined, added_place) =
                                        concrete_places.combine(place_ref, new_proj, tcx);
                                    place_added |= added_place;
                                    match self.get_node(combined) {
                                        Some(node) => {
                                            if let Some(nodes) = self.pts.neighbors(node) {
                                                // found derefed
                                                new_pointees.extend(nodes.iter().copied());
                                            } else {
                                                // create a virtual node with Deref
                                                let pre_next = PlaceRef {
                                                    local: place.local,
                                                    projection: &place.projection[..i + 1],
                                                };
                                                let node = MemCell::from_virtual(pre_next);
                                                added |= self.pts.add_node(node);
                                                new_pointees.insert(node);
                                            }
                                        }
                                        None => {
                                            // combined -> combined.Deref
                                            let (combined_deref, added_place) = concrete_places
                                                .combine(combined, &[ProjectionElem::Deref], tcx);
                                            place_added |= added_place;
                                            let combined_node = MemCell::from_place_ref(combined);
                                            let combined_deref_node =
                                                MemCell::from_place_ref(combined_deref);
                                            added |= self
                                                .pts
                                                .add_edge(combined_node, combined_deref_node);
                                            new_pointees.insert(combined_deref_node);
                                        }
                                    }
                                }
                            }
                            pointees = new_pointees;
                        }
                        last_derefed_pos = i;
                    }
                    _ => {}
                }
            }
            let new_proj = &place.projection[last_derefed_pos + 1..];
            if !new_proj.is_empty() {
                // combine remaining proj
                let mut new_pointees = HashSet::new();
                for pointee in pointees.iter() {
                    let place_ref = pointee.as_place_ref();
                    if let Some(place_ref) = place_ref {
                        let (combined, added_place) =
                            concrete_places.combine(place_ref, new_proj, tcx);
                        place_added |= added_place;
                        match self.get_node(combined) {
                            Some(node) => {
                                new_pointees.insert(node);
                            }
                            None => {
                                let node = MemCell::from_place_ref(combined);
                                added |= self.pts.add_node(node);
                                new_pointees.insert(node);
                            }
                        }
                    }
                }
                pointees = new_pointees;
            }
            // println!("{:#?}", pointees);
            (pointees, added, place_added)
        }
    }
}

pub fn union_state<'tcx>(
    this: &mut Option<Rc<PtsState<'tcx>>>,
    other: Option<Rc<PtsState<'tcx>>>,
) -> bool {
    if other.is_none() {
        return false;
    }
    match this.as_ref() {
        None => {
            *this = other;
            true
        }
        Some(this_state) => {
            let mut cloned = PtsState::clone(this_state);
            if cloned.union(other) {
                *this = Some(Rc::new(cloned));
                true
            } else {
                false
            }
        }
    }
}

pub struct IntraProceduralPointerAnalysis<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub pts_states: HashMap<Location, Option<Rc<PtsState<'tcx>>>>,
}

impl<'tcx> IntraProceduralPointerAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            pts_states: HashMap::new(),
        }
    }

    pub fn may_points_to_ref(
        &self,
        location: Location,
        pointer: PlaceRef<'tcx>,
        pointee: PlaceRef<'tcx>,
        globals: &Option<HashMap<MemCell<'tcx>, DefId>>,
    ) -> bool {
        let state = match self.pts_states.get(&location).unwrap() {
            None => return false,
            Some(state) => state,
        };
        let mut pointers = HashSet::new();
        for node in state.pts.nodes.iter() {
            if let Some(p) = node.as_place_ref() {
                if p.local == pointer.local {
                    if !p
                        .projection
                        .iter()
                        .any(|elem| *elem == ProjectionElem::Deref)
                    {
                        pointers.insert(node);
                    }
                }
            }
        }
        // let prc = MemCell::from_direct_place_ref(pointer);
        for prc in pointers {
            // println!("prc: {:?}", prc);
            let pec = MemCell::from_direct_place_ref(pointee);
            let prces = match state.points_to(*prc) {
                None => continue,
                Some(prces) => prces,
            };
            // eq || local eq for direct place
            // e.g. p -> local, drop(local.0) => p -> local.0
            if prces.iter().any(|prce| {
                if *prce == pec {
                    return true;
                }
                let point_to_place = match prce.as_place_ref() {
                    None => return false,
                    Some(p) => {
                        if p.projection
                            .iter()
                            .any(|elem| *elem == ProjectionElem::Deref)
                        {
                            return false;
                        }
                        p
                    }
                };
                let pointee_place = match pec.as_place_ref() {
                    None => return false,
                    Some(p) => {
                        if p.projection
                            .iter()
                            .any(|elem| *elem == ProjectionElem::Deref)
                        {
                            return false;
                        }
                        p
                    }
                };
                if point_to_place.local != pointee_place.local {
                    return false;
                }
                // point_to_place.projection contains pointee_place.projection or vice versa
                if point_to_place
                    .projection
                    .iter()
                    .zip(pointee_place.projection.iter())
                    .any(|(a, b)| *a != *b)
                {
                    return false;
                }
                true
            }) {
                return true;
            }
            let globals = match globals.as_ref() {
                None => continue,
                Some(globals) => globals,
            };
            let prcegs: HashSet<DefId> = prces
                .iter()
                .filter_map(|prce| match prce {
                    MemCell::Alloc(_, _) => globals.get(prce).map(|def_id| *def_id),
                    _ => None,
                })
                .collect();
            if prcegs.is_empty() {
                continue;
            }
            let peces = match state.points_to(pec) {
                None => continue,
                Some(peces) => peces,
            };
            let pecegs: HashSet<DefId> = peces
                .iter()
                .filter_map(|prce| match prce {
                    MemCell::Alloc(_, _) => globals.get(prce).map(|def_id| *def_id),
                    _ => None,
                })
                .collect();
            if !prcegs.is_disjoint(&pecegs) {
                return true;
            }
        }
        false
    }

    pub fn may_points_to(
        &self,
        location: Location,
        pointer: Place<'tcx>,
        pointee: Place<'tcx>,
        globals: &Option<HashMap<MemCell<'tcx>, DefId>>,
    ) -> bool {
        let state = match self.pts_states.get(&location).unwrap() {
            None => return false,
            Some(state) => state,
        };
        let prc = match MemCell::from_direct_place(pointer) {
            None => return false,
            Some(prc) => prc,
        };
        let pec = match MemCell::from_direct_place(pointee) {
            None => return false,
            Some(pec) => pec,
        };
        let prces = match state.points_to(prc) {
            None => return false,
            Some(prces) => prces,
        };
        // eq || local eq for direct place
        // e.g. p -> local, drop(local.0) => p -> local.0
        if prces.iter().any(|prce| {
            if *prce == pec {
                return true;
            }
            let point_to_place = match prce.as_place_ref() {
                None => return false,
                Some(p) => {
                    if p.projection
                        .iter()
                        .any(|elem| *elem == ProjectionElem::Deref)
                    {
                        return false;
                    }
                    p
                }
            };
            let pointee_place = match pec.as_place_ref() {
                None => return false,
                Some(p) => {
                    if p.projection
                        .iter()
                        .any(|elem| *elem == ProjectionElem::Deref)
                    {
                        return false;
                    }
                    p
                }
            };
            if point_to_place.local != pointee_place.local {
                return false;
            }
            // point_to_place.projection contains pointee_place.projection or vice versa
            if point_to_place
                .projection
                .iter()
                .zip(pointee_place.projection.iter())
                .any(|(a, b)| *a != *b)
            {
                return false;
            }
            true
        }) {
            return true;
        }
        let globals = match globals.as_ref() {
            None => return false,
            Some(globals) => globals,
        };
        let prcegs: HashSet<DefId> = prces
            .iter()
            .filter_map(|prce| match prce {
                MemCell::Alloc(_, _) => globals.get(prce).map(|def_id| *def_id),
                _ => None,
            })
            .collect();
        if prcegs.is_empty() {
            return false;
        }
        let peces = match state.points_to(pec) {
            None => return false,
            Some(peces) => peces,
        };
        let pecegs: HashSet<DefId> = peces
            .iter()
            .filter_map(|prce| match prce {
                MemCell::Alloc(_, _) => globals.get(prce).map(|def_id| *def_id),
                _ => None,
            })
            .collect();
        if !prcegs.is_disjoint(&pecegs) {
            return true;
        }

        false
    }

    // should we consider partial alias?
    pub fn may_alias(
        &self,
        location: Location,
        a: Place<'tcx>,
        b: Place<'tcx>,
        globals: &Option<HashMap<MemCell<'tcx>, DefId>>,
    ) -> bool {
        let state = self.pts_states.get(&location).unwrap();
        if let Some(state) = state {
            let ac = match MemCell::from_direct_place(a) {
                None => return false,
                Some(ac) => ac,
            };
            let bc = match MemCell::from_direct_place(b) {
                None => return false,
                Some(bc) => bc,
            };
            if let Some(aps) = state.points_to(ac) {
                if let Some(bps) = state.points_to(bc) {
                    if !aps.is_disjoint(&bps) {
                        return true;
                    }
                    if let Some(globals) = globals {
                        let ags: HashSet<DefId> = aps
                            .iter()
                            .filter_map(|ap| match ap {
                                MemCell::Alloc(_, _) => globals.get(ap).map(|def_id| *def_id),
                                _ => None,
                            })
                            .collect();
                        if !ags.is_empty() {
                            let bgs: HashSet<DefId> = bps
                                .iter()
                                .filter_map(|bp| match bp {
                                    MemCell::Alloc(_, _) => globals.get(bp).map(|def_id| *def_id),
                                    _ => None,
                                })
                                .collect();
                            if !ags.is_disjoint(&bgs) {
                                return true;
                            }
                        }
                    }
                }
            }
        }
        false
    }

    pub fn analyze(
        &mut self,
        instance: Instance<'tcx>,
    ) -> (
        Option<HashMap<MemCell<'tcx>, DefId>>,
        Option<HashMap<MemCell<'tcx>, DefId>>,
    ) {
        let body = self.tcx.instance_mir(instance.def);
        // collect all places
        let mut all_places = ConcretePlaces::new();
        all_places.visit_body(body);
        // collect points-to info
        // init worklist and states
        let mut worklist = Vec::new();
        for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
            for stmt_idx in 0..=bb_data.statements.len() {
                let location = Location {
                    block: bb,
                    statement_index: stmt_idx,
                };
                worklist.push(location);
                self.pts_states.insert(location, None);
            }
        }
        // arg -> Alloc(arg)
        let mut start_state = PtsState::new();
        // let return_place = Place::from(RETURN_PLACE).as_ref();
        // start_state.pts.add_edge(
        //     MemCell::Concrete(return_place),
        //     MemCell::Alloc(return_place, None),
        // );
        for arg in body.args_iter() {
            let arg_place = Place::from(arg).as_ref();
            start_state.pts.add_edge(
                MemCell::Concrete(arg_place),
                MemCell::Alloc(arg_place, None),
            );
        }
        self.pts_states
            .insert(Location::START, Some(Rc::new(start_state)));
        // dataflow analysis
        let mut globals = HashMap::<MemCell<'tcx>, DefId>::new();
        let mut escapes = HashMap::<MemCell<'tcx>, DefId>::new();
        static MAX_LOOP_TIMES: u32 = 100000;
        let mut loop_times = 0u32;
        while let Some(location) = worklist.pop() {
            loop_times += 1;
            if loop_times > MAX_LOOP_TIMES {
                break;
            }
            if body.terminator_loc(location.block) == location {
                let terminator = body.basic_blocks()[location.block].terminator();
                let before = self.pts_states.get(&location).unwrap();
                let bb_after = self.transfer_terminator(
                    terminator,
                    location,
                    before,
                    &mut all_places,
                    instance,
                    body,
                );
                for (succ_bb, after) in bb_after {
                    let succ_loc = Location {
                        block: succ_bb,
                        statement_index: 0,
                    };
                    let changed = {
                        let state = self.pts_states.get_mut(&succ_loc).unwrap();
                        union_state(state, after)
                    };
                    if changed {
                        worklist.push(succ_loc);
                    }
                }
            } else {
                let statement =
                    &body.basic_blocks()[location.block].statements[location.statement_index];
                let before = self.pts_states.get(&location).unwrap();
                let after = self.transfer_statement(
                    statement,
                    location,
                    before,
                    &mut all_places,
                    &mut globals,
                    &mut escapes,
                );
                let succ_loc = location.successor_within_block();
                let changed = {
                    let state = self.pts_states.get_mut(&succ_loc).unwrap();
                    union_state(state, after)
                };
                if changed {
                    worklist.push(succ_loc);
                }
            }
        }
        // // debug print
        // for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
        //     let term_loc = body.terminator_loc(bb);
        //     self.pts_states
        //         .get(&term_loc)
        //         .unwrap()
        //         .as_ref()
        //         .unwrap()
        //         .debug_print()
        //     // for stmt_idx in 0..=bb_data.statements.len() {
        //     //     let location = Location {
        //     //         block: bb,
        //     //         statement_index: stmt_idx,
        //     //     };
        //     //     print!("{:?}:", location);
        //     //     self.pts_states
        //     //         .get(&location)
        //     //         .unwrap()
        //     //         .as_ref()
        //     //         .unwrap()
        //     //         .debug_print();
        //     // }
        // }
        // println!("");
        if !globals.is_empty() {
            if !escapes.is_empty() {
                (Some(globals), Some(escapes))
            } else {
                (Some(globals), None)
            }
        } else {
            if !escapes.is_empty() {
                (None, Some(escapes))
            } else {
                (None, None)
            }
        }
    }

    fn transfer_statement(
        &self,
        statement: &Statement<'tcx>,
        location: Location,
        before: &Option<Rc<PtsState<'tcx>>>,
        all_places: &mut ConcretePlaces<'tcx>,
        globals: &mut HashMap<MemCell<'tcx>, DefId>,
        escapes: &mut HashMap<MemCell<'tcx>, DefId>,
    ) -> Option<Rc<PtsState<'tcx>>> {
        match &statement.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let mut state = before
                    .as_ref()
                    .map(|rc| PtsState::clone(rc))
                    .unwrap_or(PtsState::new());
                let mut changed = false;
                // println!("{:?}", statement);
                let (lmemcells, state_changed, added_place) =
                    state.process_place(*place, all_places, self.tcx);
                let def_ids: HashSet<_> = lmemcells
                    .iter()
                    .copied()
                    .filter_map(|c| {
                        if let MemCell::Alloc(_, _) = c {
                            return globals.get(&c).map(|r| *r);
                        }
                        None
                    })
                    .collect();
                // println!("{:?}", def_ids);
                changed |= state_changed;
                match rvalue {
                    Rvalue::Use(operand)
                    | Rvalue::Repeat(operand, _)
                    | Rvalue::Cast(_, operand, _) => {
                        match operand {
                            Operand::Move(rplace) | Operand::Copy(rplace) => {
                                // println!("{:?}", statement);
                                let (rmemcells, state_changed, added_place) =
                                    state.process_place(*rplace, all_places, self.tcx);
                                changed |= state_changed;
                                // lplaces = rplaces: rplaces->?=>lplaces->?
                                if let Some(points_to) = state.batch_points_to(rmemcells.clone()) {
                                    changed |=
                                        state.set_batch_points_to(lmemcells.clone(), points_to);
                                }
                                // println!("rmemcells for {:?}: {:?}", rplace, rmemcells);
                                for def_id in def_ids.clone() {
                                    for rmemcell in rmemcells.clone() {
                                        escapes.insert(rmemcell, def_id);
                                    }
                                }
                            }
                            Operand::Constant(constant) => {
                                // lplaces = constant, but alloc for now
                                let memcell = MemCell::Alloc(place.as_ref(), Some(location));
                                if let Some(def_id) = constant.check_static_ptr(self.tcx) {
                                    globals.insert(memcell, def_id);
                                }
                                for pointer in lmemcells.iter() {
                                    changed |= state.set_points_to(*pointer, memcell);
                                }
                            }
                        }
                    }
                    Rvalue::Ref(_, _, rplace) | Rvalue::AddressOf(_, rplace) => {
                        // lplaces = &rplaces: lplaces->rplaces
                        let (rmemcells, state_changed, added_place) =
                            state.process_place(*rplace, all_places, self.tcx);
                        changed |= state_changed;
                        for pointer in lmemcells.iter() {
                            for pointee in rmemcells.iter() {
                                changed |= state.set_points_to(*pointer, *pointee);
                            }
                        }
                    }
                    Rvalue::Discriminant(rplace) => {
                        let (rmemcells, state_changed, added_place) =
                            state.process_place(*rplace, all_places, self.tcx);
                        changed |= state_changed;
                        // lplaces = rplaces: rplaces->?=>lplaces->?
                        let mut points_to = HashSet::new();
                        for rmemcell in rmemcells {
                            if let Some(pointees) = state.points_to(rmemcell) {
                                points_to.extend(pointees.into_iter());
                            }
                        }
                        for pointer in lmemcells.iter() {
                            for pointee in points_to.iter() {
                                changed |= state.set_points_to(*pointer, *pointee);
                            }
                        }
                    }
                    Rvalue::Len(_)
                    | Rvalue::BinaryOp(_, _, _)
                    | Rvalue::CheckedBinaryOp(_, _, _)
                    | Rvalue::NullaryOp(_, _)
                    | Rvalue::UnaryOp(_, _)
                    | Rvalue::Aggregate(_, _) => {
                        let memcell = MemCell::Alloc(place.as_ref(), Some(location));
                        for pointer in lmemcells.iter() {
                            changed |= state.set_points_to(*pointer, memcell);
                        }
                    }
                    Rvalue::ThreadLocalRef(def_id) => {
                        let memcell = MemCell::Alloc(place.as_ref(), Some(location));
                        globals.insert(memcell, *def_id);
                    }
                }

                if !changed {
                    before.as_ref().map(|rc| Rc::clone(rc))
                } else {
                    Some(Rc::new(state))
                }
            }
            StatementKind::SetDiscriminant {
                box place,
                variant_index: _variant_index,
            } => {
                let mut state = before
                    .as_ref()
                    .map(|rc| PtsState::clone(rc))
                    .unwrap_or(PtsState::new());
                let mut changed = false;
                let (lmemcells, state_changed, added_place) =
                    state.process_place(*place, all_places, self.tcx);
                changed |= state_changed;
                let memcell = MemCell::Alloc(place.as_ref(), Some(location));
                for pointer in lmemcells.iter() {
                    changed |= state.set_points_to(*pointer, memcell);
                }
                if !changed {
                    before.as_ref().map(|rc| Rc::clone(rc))
                } else {
                    Some(Rc::new(state))
                }
            }
            _ => before.as_ref().map(|rc| Rc::clone(rc)),
        }
    }

    fn transfer_terminator(
        &self,
        terminator: &Terminator<'tcx>,
        location: Location,
        before: &Option<Rc<PtsState<'tcx>>>,
        all_places: &mut ConcretePlaces<'tcx>,
        instance: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
    ) -> HashMap<BasicBlock, Option<Rc<PtsState<'tcx>>>> {
        let mut result = HashMap::new();
        match &terminator.kind {
            // Arc::clone, Rc::clone
            TerminatorKind::Call {
                func,
                args,
                destination,
                cleanup,
                ..
            } => {
                let mut all_changed = false;
                let mut all_added = false;
                let mut state = before
                    .as_ref()
                    .map(|rc| PtsState::clone(rc))
                    .unwrap_or(PtsState::new());
                if let Some(callee) = self.resolve_call_func(func, instance, body) {
                    // println!("Call {:?}", callee_def_path_str);
                    match SmartPtrAPI::new(callee, self.tcx) {
                        Some(SmartPtrAPI::ArcClone) | Some(SmartPtrAPI::RcClone) => {
                            // destination.0: Arc1
                            // args[0]: &Arc2
                            // Arc2->?=>Arc1->?
                            let lmemcells = destination.map(|(lplace, _)| {
                                let (lmemcells, changed, added) =
                                    state.process_place(lplace, all_places, self.tcx);
                                all_changed |= changed;
                                all_added |= added;
                                lmemcells
                            });
                            if let Some(lmemcells) = lmemcells {
                                if let Some(rplace) = args[0].place() {
                                    let (rmemcells, changed, added) =
                                        state.process_place(rplace, all_places, self.tcx);
                                    all_changed |= changed;
                                    all_added |= added;
                                    // rmemcells: &Arc -> Arc -> Arc.Deref
                                    let pointees = if let Some(pointees) =
                                        state.batch_points_to(rmemcells.clone())
                                    {
                                        pointees
                                    } else {
                                        // rmemcell -> rmemcell.Deref
                                        let mut pointees = HashSet::new();
                                        for rmemcell in rmemcells.iter() {
                                            if let Some(place_ref) = rmemcell.as_place_ref() {
                                                let (combined, added) = all_places.combine(
                                                    place_ref,
                                                    &[ProjectionElem::Deref],
                                                    self.tcx,
                                                );
                                                all_added |= added;
                                                let virt = MemCell::from_virtual(combined);
                                                pointees.insert(virt);
                                            }
                                        }
                                        all_changed |=
                                            state.set_batch_points_to(rmemcells, pointees.clone());
                                        pointees
                                    };
                                    let pointees2 = if let Some(pointees2) =
                                        state.batch_points_to(pointees.clone())
                                    {
                                        pointees2
                                    } else {
                                        // pointee -> pointee.Deref
                                        let mut pointees2 = HashSet::new();
                                        for pointee in pointees.iter() {
                                            if let Some(place_ref) = pointee.as_place_ref() {
                                                let (combined, added) = all_places.combine(
                                                    place_ref,
                                                    &[ProjectionElem::Deref],
                                                    self.tcx,
                                                );
                                                all_added |= added;
                                                let virt = MemCell::from_virtual(combined);
                                                pointees2.insert(virt);
                                            }
                                        }
                                        all_changed |=
                                            state.set_batch_points_to(pointees, pointees2.clone());
                                        pointees2
                                    };
                                    all_changed |= state.set_batch_points_to(lmemcells, pointees2);
                                    if let Some((_, dst_bb)) = destination {
                                        if all_changed {
                                            result.insert(*dst_bb, Some(Rc::new(state)));
                                        } else {
                                            result.insert(
                                                *dst_bb,
                                                before.as_ref().map(|rc| Rc::clone(rc)),
                                            );
                                        }
                                    }
                                }
                            }
                            if let Some(unwind_bb) = cleanup {
                                result.insert(*unwind_bb, before.as_ref().map(|rc| Rc::clone(rc)));
                            }
                        }
                        Some(SmartPtrAPI::ArcDeref) | Some(SmartPtrAPI::RcDeref) => {
                            // destination.0: &T
                            // args[0]: &Arc2
                            // Arc2->?=>T->?
                            let lmemcells = destination.map(|(lplace, _)| {
                                let (lmemcells, changed, added) =
                                    state.process_place(lplace, all_places, self.tcx);
                                all_changed |= changed;
                                all_added |= added;
                                lmemcells
                            });
                            if let Some(lmemcells) = lmemcells {
                                if let Some(rplace) = args[0].place() {
                                    let (rmemcells, changed, added) =
                                        state.process_place(rplace, all_places, self.tcx);
                                    all_changed |= changed;
                                    all_added |= added;
                                    // rmemcells: &Arc -> Arc -> Arc.Deref
                                    let pointees = if let Some(pointees) =
                                        state.batch_points_to(rmemcells.clone())
                                    {
                                        pointees
                                    } else {
                                        // rmemcell -> rmemcell.Deref
                                        let mut pointees = HashSet::new();
                                        for rmemcell in rmemcells.iter() {
                                            if let Some(place_ref) = rmemcell.as_place_ref() {
                                                let (combined, added) = all_places.combine(
                                                    place_ref,
                                                    &[ProjectionElem::Deref],
                                                    self.tcx,
                                                );
                                                all_added |= added;
                                                let virt = MemCell::from_virtual(combined);
                                                pointees.insert(virt);
                                            }
                                        }
                                        all_changed |=
                                            state.set_batch_points_to(rmemcells, pointees.clone());
                                        pointees
                                    };
                                    let pointees2 = if let Some(pointees2) =
                                        state.batch_points_to(pointees.clone())
                                    {
                                        pointees2
                                    } else {
                                        // pointee -> pointee.Deref
                                        let mut pointees2 = HashSet::new();
                                        for pointee in pointees.iter() {
                                            if let Some(place_ref) = pointee.as_place_ref() {
                                                let (combined, added) = all_places.combine(
                                                    place_ref,
                                                    &[ProjectionElem::Deref],
                                                    self.tcx,
                                                );
                                                all_added |= added;
                                                let virt = MemCell::from_virtual(combined);
                                                pointees2.insert(virt);
                                            }
                                        }
                                        all_changed |=
                                            state.set_batch_points_to(pointees, pointees2.clone());
                                        pointees2
                                    };
                                    all_changed |= state.set_batch_points_to(lmemcells, pointees2);
                                    if let Some((_, dst_bb)) = destination {
                                        if all_changed {
                                            result.insert(*dst_bb, Some(Rc::new(state)));
                                        } else {
                                            result.insert(
                                                *dst_bb,
                                                before.as_ref().map(|rc| Rc::clone(rc)),
                                            );
                                        }
                                    }
                                }
                            }
                            if let Some(unwind_bb) = cleanup {
                                result.insert(*unwind_bb, before.as_ref().map(|rc| Rc::clone(rc)));
                            }
                        }
                        Some(SmartPtrAPI::BoxFromRaw)
                        | Some(SmartPtrAPI::BoxIntoRaw)
                        | Some(SmartPtrAPI::AsMutPtr)
                        | Some(SmartPtrAPI::AsPtr)
                        | Some(SmartPtrAPI::AsMutSlice)
                        | Some(SmartPtrAPI::AsSlice)
                        | Some(SmartPtrAPI::Index)
                        | Some(SmartPtrAPI::IndexMut) => {
                            let lmemcells = destination.map(|(lplace, _)| {
                                let (lmemcells, changed, added) =
                                    state.process_place(lplace, all_places, self.tcx);
                                all_changed |= changed;
                                all_added |= added;
                                lmemcells
                            });
                            if let Some(lmemcells) = lmemcells {
                                if let Some(rplace) = args[0].place() {
                                    let (rmemcells, changed, added) =
                                        state.process_place(rplace, all_places, self.tcx);
                                    all_changed |= changed;
                                    all_added |= added;
                                    // rmemcells: &Arc -> Arc -> Arc.Deref
                                    let pointees = if let Some(pointees) =
                                        state.batch_points_to(rmemcells.clone())
                                    {
                                        pointees
                                    } else {
                                        // rmemcell -> rmemcell.Deref
                                        let mut pointees = HashSet::new();
                                        for rmemcell in rmemcells.iter() {
                                            if let Some(place_ref) = rmemcell.as_place_ref() {
                                                let (combined, added) = all_places.combine(
                                                    place_ref,
                                                    &[ProjectionElem::Deref],
                                                    self.tcx,
                                                );
                                                all_added |= added;
                                                let virt = MemCell::from_virtual(combined);
                                                pointees.insert(virt);
                                            }
                                        }
                                        all_changed |=
                                            state.set_batch_points_to(rmemcells, pointees.clone());
                                        pointees
                                    };
                                    all_changed |= state.set_batch_points_to(lmemcells, pointees);
                                    if let Some((_, dst_bb)) = destination {
                                        if all_changed {
                                            result.insert(*dst_bb, Some(Rc::new(state)));
                                        } else {
                                            result.insert(
                                                *dst_bb,
                                                before.as_ref().map(|rc| Rc::clone(rc)),
                                            );
                                        }
                                    }
                                }
                            }
                            if let Some(unwind_bb) = cleanup {
                                result.insert(*unwind_bb, before.as_ref().map(|rc| Rc::clone(rc)));
                            }
                        }
                        None => {
                            // println!("Call {:?}", func);
                            if let Some((lplace, dst_bb)) = destination {
                                // lplace -> Alloc(lplace)
                                let (lmemcells, changed, added) =
                                    state.process_place(*lplace, all_places, self.tcx);
                                all_changed |= changed;
                                all_added |= added;
                                let alloc_mem = MemCell::Alloc(lplace.as_ref(), Some(location));
                                let mut new_pointees = HashSet::new();
                                new_pointees.insert(alloc_mem);
                                // redef: replace old pts with new alloc
                                all_changed |= state
                                    .set_batch_points_to_strong_update(lmemcells, new_pointees);
                                result.insert(*dst_bb, Some(Rc::new(state)));
                            }
                            if let Some(unwind_bb) = cleanup {
                                result.insert(*unwind_bb, before.as_ref().map(|rc| Rc::clone(rc)));
                            }
                        }
                    }
                } else {
                    // println!("Call {:?}", func);
                    if let Some((lplace, dst_bb)) = destination {
                        // lplace -> Alloc(lplace)
                        let (lmemcells, changed, added) =
                            state.process_place(*lplace, all_places, self.tcx);
                        all_changed |= changed;
                        all_added |= added;
                        let alloc_mem = MemCell::Alloc(lplace.as_ref(), Some(location));
                        let mut new_pointees = HashSet::new();
                        new_pointees.insert(alloc_mem);
                        // redef: replace old pts with new alloc
                        all_changed |=
                            state.set_batch_points_to_strong_update(lmemcells, new_pointees);
                        result.insert(*dst_bb, Some(Rc::new(state)));
                    }
                    if let Some(unwind_bb) = cleanup {
                        result.insert(*unwind_bb, before.as_ref().map(|rc| Rc::clone(rc)));
                    }
                }
            }
            _ => {
                for succ in terminator.successors() {
                    result.insert(*succ, before.as_ref().map(|rc| Rc::clone(rc)));
                }
            }
        };
        result
    }

    fn resolve_call_func(
        &self,
        func: &Operand<'tcx>,
        instance: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
    ) -> Option<Instance<'tcx>> {
        let func_ty = func.ty(body, self.tcx);
        let func_ty = instance.subst_mir_and_normalize_erasing_regions(
            self.tcx,
            ty::ParamEnv::reveal_all(),
            func_ty,
        );
        if let ty::TyKind::FnDef(def_id, substs_ref) = func_ty.kind() {
            if let Some(callee_instance) =
                Instance::resolve(self.tcx, ty::ParamEnv::reveal_all(), *def_id, substs_ref)
                    .ok()
                    .flatten()
            {
                return Some(callee_instance);
            }
        }
        None
    }
}

static SMARTPTR_API_REGEX: Lazy<HashMap<SmartPtrAPI, Regex>> = Lazy::new(|| {
    let mut m = HashMap::new();
    m.insert(
        SmartPtrAPI::ArcDeref,
        Regex::new(r"^<std::sync::Arc<.+> as std::ops::Deref>::deref$").unwrap(),
    );
    m.insert(
        SmartPtrAPI::ArcClone,
        Regex::new(r"<std::sync::Arc<.+> as std::clone::Clone>::clone$").unwrap(),
    );
    m.insert(
        SmartPtrAPI::RcDeref,
        Regex::new(r"^<std::rc::Rc<.+> as std::ops::Deref>::deref$").unwrap(),
    );
    m.insert(
        SmartPtrAPI::RcClone,
        Regex::new(r"^<std::rc::Rc<.+> as std::clone::Clone>::clone$").unwrap(),
    );
    m.insert(SmartPtrAPI::AsSlice, Regex::new(r"as_slice$").unwrap());
    m.insert(
        SmartPtrAPI::AsMutSlice,
        Regex::new(r"as_mut_slice$").unwrap(),
    );
    m.insert(SmartPtrAPI::AsPtr, Regex::new(r"as_ptr$").unwrap());
    m.insert(SmartPtrAPI::AsMutPtr, Regex::new(r"as_mut_ptr$").unwrap());
    m.insert(
        SmartPtrAPI::BoxIntoRaw,
        Regex::new(r"Box::<.+>::into_raw$").unwrap(),
    );
    m.insert(
        SmartPtrAPI::BoxFromRaw,
        Regex::new(r"Box::<.+>::from_raw$").unwrap(),
    );
    m.insert(SmartPtrAPI::Index, Regex::new(r"::index$").unwrap());
    m.insert(SmartPtrAPI::IndexMut, Regex::new(r"::index_mut$").unwrap());
    m
});

#[cfg(test)]
mod tests {
    use super::SmartPtrAPI;
    use super::SMARTPTR_API_REGEX;

    #[test]
    fn test_atomic_api_regex() {
        assert!(SMARTPTR_API_REGEX
            .get(&SmartPtrAPI::AsMutSlice)
            .unwrap()
            .is_match("Vec::<i32>::as_mut_slice"));
        assert!(SMARTPTR_API_REGEX
            .get(&SmartPtrAPI::AsSlice)
            .unwrap()
            .is_match("Vec::<i32>::as_slice"));
        assert!(SMARTPTR_API_REGEX
            .get(&SmartPtrAPI::AsMutPtr)
            .unwrap()
            .is_match("core::slice::<impl [i32]>::as_mut_ptr"));
        assert!(SMARTPTR_API_REGEX
            .get(&SmartPtrAPI::AsPtr)
            .unwrap()
            .is_match("core::slice::<impl [i32]>::as_ptr"));
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum SmartPtrAPI {
    ArcClone,
    ArcDeref,
    RcClone,
    RcDeref,
    AsSlice,
    AsMutSlice,
    AsPtr,
    AsMutPtr,
    BoxIntoRaw,
    BoxFromRaw,
    Index,
    IndexMut,
}

impl SmartPtrAPI {
    pub fn new<'tcx>(instance: Instance<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Self> {
        let def_path_str = tcx.def_path_str_with_substs(instance.def_id(), instance.substs);
        for (api, regex) in SMARTPTR_API_REGEX.iter() {
            if regex.is_match(&def_path_str) {
                return Some(*api);
            }
        }
        None
    }
}

pub struct ConcretePlaces<'tcx> {
    pub places: HashMap<Local, HashSet<&'tcx [PlaceElem<'tcx>]>>,
}

impl<'tcx> ConcretePlaces<'tcx> {
    pub fn new() -> Self {
        Self {
            places: HashMap::new(),
        }
    }

    pub fn combine(
        &mut self,
        place_ref: PlaceRef<'tcx>,
        appended: &'tcx [PlaceElem<'tcx>],
        tcx: TyCtxt<'tcx>,
    ) -> (PlaceRef<'tcx>, bool) {
        if place_ref.projection.is_empty() {
            return (
                PlaceRef {
                    local: place_ref.local,
                    projection: appended,
                },
                false,
            );
        }
        let new_proj = [place_ref.projection, appended].concat();
        let new_proj = new_proj.as_slice();
        for proj in self.places.get(&place_ref.local).unwrap() {
            if let Some(pos) = proj
                .windows(new_proj.len())
                .position(|window| window == new_proj)
            {
                return (
                    PlaceRef {
                        local: place_ref.local,
                        projection: &proj[pos..pos + new_proj.len()],
                    },
                    false,
                );
            }
        }
        // Cannot find new_proj, alloc new_proj in arena
        (
            PlaceRef {
                local: place_ref.local,
                projection: hack::from_arena(tcx.arena, new_proj),
            },
            true,
        )
    }
}

impl<'tcx> Visitor<'tcx> for ConcretePlaces<'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        self.places
            .entry(place.local)
            .or_default()
            .insert(place.projection.as_ref());
    }
}

mod hack {
    use rustc_middle::arena::Arena;

    use rustc_middle::ty::List;
    use std::alloc::Layout;
    use std::cmp::Ordering;
    use std::fmt;
    use std::hash::{Hash, Hasher};
    use std::iter;
    use std::mem;
    use std::ops::Deref;
    use std::ptr;
    use std::slice;
    pub(super) fn from_arena<'tcx, T: Copy>(
        arena: &'tcx Arena<'tcx>,
        slice: &[T],
    ) -> &'tcx List<T> {
        assert!(!mem::needs_drop::<T>());
        assert!(mem::size_of::<T>() != 0);
        assert!(!slice.is_empty());

        let (layout, _offset) = Layout::new::<usize>()
            .extend(Layout::for_value::<[T]>(slice))
            .unwrap();
        let mem = arena.dropless.alloc_raw(layout);
        unsafe {
            let result = &mut *(mem as *mut List<T>);
            // Write the length
            // Hack the private field len
            let len_ptr = result as *mut _ as *mut usize;
            *len_ptr = slice.len();

            // Write the elements
            // Hack the private field data
            let data_ptr = len_ptr.add(1) as *mut [T; 0];
            let arena_slice = slice::from_raw_parts_mut((*data_ptr).as_mut_ptr(), *len_ptr);
            arena_slice.copy_from_slice(slice);

            result
        }
    }
}
