// alloc-i, global, constant, args, return
// alloc-i: DirectPlace(Args/Return)
// p = &o
// p = q
// o = *q
// *p = o

use petgraph::{
    dot::{Config, Dot},
    graphmap::{GraphMap, NodeTrait},
    prelude::NodeIndex,
    Directed, Graph,
};
use rustc_middle::bug;
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::{
    Body, Local, Location, Operand, Place, PlaceElem, PlaceRef, ProjectionElem, Rvalue, Statement,
    StatementKind, Terminator, TerminatorKind, RETURN_PLACE,
};
use rustc_middle::ty::{self, Instance, InstanceDef, List, Ty, TyCtxt};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub struct ConcretePlaces<'tcx> {
    pub places: HashMap<Local, HashSet<&'tcx [PlaceElem<'tcx>]>>,
}

impl<'tcx> ConcretePlaces<'tcx> {
    pub fn new() -> Self {
        Self {
            places: HashMap::new(),
        }
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

// Intra states = Location x PtsState
// concrete_places

pub struct PtsState<'tcx> {
    pub pts: RefCell<petgraph::Graph<MemCell<'tcx>, MemCellRelation, Directed>>,
    pub mapping: RefCell<HashMap<MemCell<'tcx>, NodeIndex>>,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> PtsState<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            pts: RefCell::new(petgraph::Graph::new()),
            mapping: RefCell::new(HashMap::new()),
            tcx,
        }
    }

    // TODO: find a better way to handle this.
    pub fn union(&mut self, other: &PtsState<'tcx>) -> bool {
        if self.mapping == other.mapping {
            false
        } else {
            self.mapping = other.mapping.clone();
            *self.pts.borrow_mut() = other.pts.borrow().clone();
            true
        }
        // let nodes = other.raw_nodes();
        // // let mapping = other.mapping;
        // let mut other_self_mapping = HashMap::new();
        // for node in nodes {
        //     let weight = other.node_weight(*node).unwrap();
        //     let new_node = self.pts.borrow_mut().add_node(weight);
        //     other_self_mapping.insert(*node, new_node);
        // }
        // self.pts.borrow_mut().add_node()

        // let edges = other.raw_edges();
    }

    pub fn debug_print(&self) {
        // Dot::with_config(&*self.pts.borrow(), &[Config::EdgeIndexLabel, Config::NodeIndexLabel]);
        println!("raw edges: {:#?}", self.pts.borrow().raw_edges());
        for (m, n) in &*self.mapping.borrow() {
            println!("{:?}, {:?}", m, n);
        }
    }

    pub fn get_or_insert(&self, memcell: MemCell<'tcx>) -> NodeIndex {
        *self
            .mapping
            .borrow_mut()
            .entry(memcell)
            .or_insert_with(|| self.pts.borrow_mut().add_node(memcell))
    }

    pub fn get_or_insert_place(
        &self,
        place: PlaceRef<'tcx>,
        suffix: &[PlaceElem<'tcx>],
        concrete_places: &mut ConcretePlaces<'tcx>,
    ) -> PlaceRef<'tcx> {
        let projection: Vec<_> = place
            .projection
            .iter()
            .copied()
            .chain(suffix.iter().copied())
            .collect();
        let slice = projection.as_slice();
        if let Some(concrete_projections) = concrete_places.places.get(&place.local) {
            if let Some(concrete_projection) =
                concrete_projections.iter().find(|elem| *elem == &slice)
            {
                PlaceRef {
                    local: place.local,
                    projection: concrete_projection,
                }
            } else {
                let new_projection = hack::from_arena(self.tcx.arena, slice);
                let place_ref = PlaceRef {
                    local: place.local,
                    projection: new_projection.as_ref(),
                };
                drop(concrete_projections);
                concrete_places
                    .places
                    .get_mut(&place.local)
                    .unwrap()
                    .insert(place_ref.projection);
                place_ref
            }
        } else {
            bug!("Cannot find {:?}", place.local)
        }
    }

    // concrete place
    fn get_or_insert_pts<F>(&self, place: PlaceRef<'tcx>, derefed: F) -> HashSet<NodeIndex>
    where
        F: FnOnce() -> PlaceRef<'tcx>,
    {
        let memcell = MemCell::Concrete(place);
        let node = self.get_or_insert(memcell);
        let pointees: HashSet<_> = self.pts.borrow().neighbors(node).collect();
        if pointees.is_empty() {
            let virt_memcell = MemCell::Virtual(derefed());
            let virt_node = self.get_or_insert(virt_memcell);
            self.pts
                .borrow_mut()
                .add_edge(node, virt_node, MemCellRelation::PointsTo);
            let mut result = HashSet::new();
            result.insert(virt_node);
            result
        } else {
            pointees
        }
    }

    // place = ...
    pub fn process_left_place(
        &mut self,
        place: Place<'tcx>,
        concrete_places: &RefCell<ConcretePlaces<'tcx>>,
    ) -> HashSet<NodeIndex> {
        // Local(.Field|Index)*= ...
        if !place.is_indirect() {
            let mut result = HashSet::new();
            let memcell = MemCell::Concrete(place.as_ref());
            let option_node = self
                .mapping
                .borrow()
                .get(&memcell)
                .and_then(|node_ref| Some(*node_ref));
            if let Some(node) = option_node {
                result.insert(node);
            } else {
                result.insert(self.get_or_insert(memcell));
            }
            result
        } else {
            // Local(.Field|Index|Deref)*=...
            // e.g. Local.Field.Deref.Field.Deref.Field
            // let mut result: HashSet<NodeIndex> = HashSet::new();
            let mut prev_nodes = HashSet::new();
            let mut prev_elems = Vec::new();
            let mut has_derefed = false;
            for (place_ref, elem) in place.iter_projections() {
                match place_ref.last_projection() {
                    Some((prev, ProjectionElem::Deref)) => {
                        if !has_derefed {
                            // resolve prev.Deref
                            prev_nodes = self.get_or_insert_pts(prev, || place_ref);
                        } else {
                            // resolve prev_nodes.Deref
                            let mut derefed = HashSet::new();
                            for prev_node in prev_nodes.iter().copied() {
                                let option_place = self
                                    .pts
                                    .borrow()
                                    .node_weight(prev_node)
                                    .unwrap()
                                    .as_place_ref();
                                if let Some(place) = option_place {
                                    let new_place = self.get_or_insert_place(
                                        place,
                                        &prev_elems,
                                        &mut concrete_places.borrow_mut(),
                                    );
                                    let virt_derefed = || {
                                        self.get_or_insert_place(
                                            new_place,
                                            &[ProjectionElem::Deref],
                                            &mut concrete_places.borrow_mut(),
                                        )
                                    };
                                    derefed.extend(
                                        self.get_or_insert_pts(new_place, virt_derefed).into_iter(),
                                    );

                                    prev_elems.clear();
                                }
                            }
                            prev_nodes = derefed;
                        }
                        has_derefed = true;
                    }
                    Some((prev, elem)) => {
                        if has_derefed {
                            prev_elems.push(elem);
                        }
                    }
                    None => {}
                }
            }
            if !prev_elems.is_empty() {
                let mut new_nodes = HashSet::new();
                for prev_node in prev_nodes.iter().copied() {
                    let option_place = self
                        .pts
                        .borrow()
                        .node_weight(prev_node)
                        .unwrap()
                        .as_place_ref();
                    if let Some(place) = option_place {
                        let new_place = self.get_or_insert_place(
                            place,
                            &prev_elems,
                            &mut concrete_places.borrow_mut(),
                        );
                        let memcell = if new_place
                            .projection
                            .iter()
                            .any(|elem| *elem == ProjectionElem::Deref)
                        {
                            MemCell::Virtual(new_place)
                        } else {
                            MemCell::Concrete(new_place)
                        };
                        let node = self.get_or_insert(memcell);
                        new_nodes.insert(node);
                    }
                }
                new_nodes
            } else {
                prev_nodes
            }
        }
    }

    pub fn get_points_to(&self, ptr: MemCell<'tcx>) -> HashSet<NodeIndex> {
        let ptr = self.get_or_insert(ptr);
        self.pts.borrow().neighbors(ptr).collect()
    }

    pub fn get_virtual_points_to(&self, ptr: NodeIndex) -> HashSet<NodeIndex> {
        self.pts
            .borrow()
            .neighbors(ptr)
            .filter_map(|n| {
                if self.pts.borrow().node_weight(n).unwrap().is_virtual() {
                    Some(n)
                } else {
                    None
                }
            })
            .collect()
    }
    pub fn add_points_to(&self, ptr: MemCell<'tcx>, obj: MemCell<'tcx>) {
        let ptr = self.get_or_insert(ptr);
        let obj = self.get_or_insert(obj);
        let virtuals = self.get_virtual_points_to(ptr);
        for v in virtuals {
            self.pts.borrow_mut().remove_node(v);
        }
        self.pts
            .borrow_mut()
            .add_edge(ptr, obj, MemCellRelation::PointsTo);
    }
    // replace_virutal()

    // pub fn direct_points_to(&self, place: PlaceRef<'tcx>) -> Option<HashSet<MemCell<'tcx>>> {
    //     let memcell = MemCell::Mem(place);
    //     let node = match self.mapping.get(&memcell) {
    //         Some(node) => *node;
    //         None => return None;
    //     }
    //     Some(self.pts.neighbors(node).map(|node| *self.pts.node_weight(node).unwrap()).collect())
    // }

    // pub fn points_to(&mut self, place: PlaceRef<'tcx>) -> Option<HashSet<MemCell<'tcx>>> {
    //     let memcells = match self.direct_points_to(place) {
    //         Some(memcells) => memcells,
    //         None => return None;
    //     };
    //     if memcells.is_empty() {

    //     }
    // }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MemCellRelation {
    PointsTo,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MemCell<'tcx> {
    Alloc(PlaceRef<'tcx>, Option<Location>),
    Concrete(PlaceRef<'tcx>),
    //ConcreteWith(PlaceRef<'tcx>, Vec<PlaceElem<'tcx>>),
    Virtual(PlaceRef<'tcx>),
    //VirtualWith(PlaceRef<'tcx>, Vec<PlaceElem<'tcx>>),
}

impl<'tcx> MemCell<'tcx> {
    pub fn from_return_or_arg(local: Local) -> Self {
        MemCell::Alloc(Place::from(local).as_ref(), None)
    }
    pub fn is_virtual(&self) -> bool {
        match *self {
            MemCell::Virtual(_) => true,
            _ => false,
        }
    }
    pub fn as_place_ref(&self) -> Option<PlaceRef<'tcx>> {
        match *self {
            MemCell::Alloc(_, _) => None,
            MemCell::Concrete(place) | MemCell::Virtual(place) => Some(place),
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MCellState {
    FromArg,
    FromReturn,
    Init,
    PartialInit,
    Uninit,
    Dropped,
    PartialDropped,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MCell<'tcx> {
    Direct(PlaceRef<'tcx>, Location, MCellState),
    Indirect(PlaceRef<'tcx>, Location, MCellState),
    Static(PlaceRef<'tcx>, Location, MCellState),
    Constant(PlaceRef<'tcx>, Location, MCellState),
}

impl<'tcx> MCell<'tcx> {
    pub fn from_direct(place: Place<'tcx>, location: Location, state: MCellState) -> Option<Self> {
        if place.is_indirect() {
            None
        } else {
            Some(Self::Direct(place.as_ref(), location, state))
        }
    }

    pub fn from_direct_ref(place: PlaceRef<'tcx>, location: Location, state: MCellState) -> Self {
        Self::Direct(place, location, state)
    }

    pub fn from_indirect(
        place: Place<'tcx>,
        location: Location,
        state: MCellState,
    ) -> Option<Self> {
        if !place.is_indirect() {
            None
        } else {
            Some(Self::Indirect(place.as_ref(), location, state))
        }
    }

    pub fn as_place(&self) -> PlaceRef<'tcx> {
        match self {
            Self::Direct(place, _, _)
            | Self::Indirect(place, _, _)
            | Self::Static(place, _, _)
            | Self::Constant(place, _, _) => *place,
        }
    }
}

pub struct IntraProceduralPointerAnalysis<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub states: HashMap<Location, HashSet<(MCell<'tcx>, MCell<'tcx>)>>,
    pub pts_states: HashMap<Location, Option<Rc<PtsState<'tcx>>>>,
}

impl<'tcx> IntraProceduralPointerAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            states: Default::default(),
            pts_states: HashMap::new(),
        }
    }

    pub fn debug_print(&self, body: &'tcx Body<'tcx>) {
        for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
            for stmt_idx in 0..=bb_data.statements.len() {
                let location = Location {
                    block: bb,
                    statement_index: stmt_idx,
                };
                println!("{:?}: {:#?}", location, self.states.get(&location).unwrap());
            }
        }
    }

    // fn union_pts_states(&self, old: Rc<PtsState<'tcx>>, add: Rc<PtsState<'tcx>>) -> Option<Rc<PtsState>> {
    //     let mut changed = false;
    //     let mut after = PtsState::clone(*old);
    //     changed = after.union(&*add.borrow());
    //     if !changed {
    //         Arc::clone(old),
    //     } else {
    //         Rc::new(after)
    //     }
    // }

    pub fn analyze(&mut self, instance: Instance<'tcx>) {
        let body = self.tcx.instance_mir(instance.def);
        let mut concrete_places = ConcretePlaces::new();
        concrete_places.visit_body(body);
        // println!("{:#?}", concrete_places.places);
        let start_state = PtsState::new(self.tcx);
        let mcell = MemCell::from_return_or_arg(RETURN_PLACE);
        start_state.add_points_to(MemCell::Concrete(Place::from(RETURN_PLACE).as_ref()), mcell);
        for arg in body.args_iter() {
            let mcell = MemCell::from_return_or_arg(arg);
            start_state.add_points_to(MemCell::Concrete(Place::from(arg).as_ref()), mcell);
        }
        // start_state.debug_print();
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
        // self.states
        //     .insert(Location::START, Some(Rc::new(start_state)));
        // while let Some(location) = worklist.pop() {
        //     if body.terminator_loc(location.block) == location {
        //         let terminator = body.basic_blocks()[location.block].terminator();
        //         let before = self.pts_states.get(&location).unwrap();
        //         let after = self.transfer_terminator_pts(terminator, location, before);
        //         *self.states.get_mut(&location).unwrap() = after;
        //         for succ_bb in terminator.successors() {
        //             let succ_loc = Location {
        //                 block: *succ_bb,
        //                 statement_index: 0,
        //             };
        //             let succ = self.states.get_mut(&succ_loc).unwrap();
        //             let succ_before_len = succ.len();
        //             succ.extend(after.clone().into_iter());
        //             if succ_before_len != succ.len() {
        //                 // changed
        //                 worklist.push(succ_loc);
        //             }
        //         }
        //     } else {
        //         let statement =
        //             &body.basic_blocks()[location.block].statements[location.statement_index];
        //         let before = self.pts_states.get(&location).unwrap();
        //         let after = self.transfer_statement_pts(statement, location, before);
        //         *self.pts_states.get_mut(&location).unwrap() = Rc::clone(after);
        //         let succ_loc = location.successor_within_block();
        //         let succ = self.pts_states.get_mut(&succ_loc).unwrap();
        //         let changed = false;
        //         if succ.is_none() && before.is_none() {
        //             changed = false;
        //         } else if succ.is_none() {
        //             *succ = 
        //         }
        //         if changed {
        //             // changed
        //             worklist.push(succ_loc);
        //         }
        //     };
        // }

        // points_to()
        // states: Graph<Place, Raw/Ref>
        //
        if false {
            let return_mcell = MCell::from_direct(
                Place::from(RETURN_PLACE),
                Location::START,
                MCellState::FromReturn,
            )
            .unwrap();
            let mut start_state = HashSet::new();
            start_state.insert((return_mcell, return_mcell));
            for arg in body.args_iter() {
                let mcell =
                    MCell::from_direct(Place::from(arg), Location::START, MCellState::FromArg)
                        .unwrap();
                start_state.insert((mcell, mcell));
            }
            let mut worklist = Vec::new();
            for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
                for stmt_idx in 0..=bb_data.statements.len() {
                    let location = Location {
                        block: bb,
                        statement_index: stmt_idx,
                    };
                    worklist.push(location);
                    self.states.insert(location, HashSet::new());
                }
            }
            // self.states.insert(Location::START, start_state);
            // while let Some(location) = worklist.pop() {
            //     if body.terminator_loc(location.block) == location {
            //         let terminator = body.basic_blocks()[location.block].terminator();
            //         let before = self.states.get(&location).unwrap();
            //         let after = self.transfer_terminator(terminator, location, before);
            //         *self.states.get_mut(&location).unwrap() = after.clone();
            //         for succ_bb in terminator.successors() {
            //             let succ_loc = Location {
            //                 block: *succ_bb,
            //                 statement_index: 0,
            //             };
            //             let succ = self.states.get_mut(&succ_loc).unwrap();
            //             let succ_before_len = succ.len();
            //             succ.extend(after.clone().into_iter());
            //             if succ_before_len != succ.len() {
            //                 // changed
            //                 worklist.push(succ_loc);
            //             }
            //         }
            //     } else {
            //         let statement =
            //             &body.basic_blocks()[location.block].statements[location.statement_index];
            //         let before = self.states.get(&location).unwrap();
            //         let after = self.transfer_statement(statement, location, before);
            //         *self.states.get_mut(&location).unwrap() = after.clone();
            //         let succ_loc = location.successor_within_block();
            //         let succ = self.states.get_mut(&succ_loc).unwrap();
            //         let succ_before_len = succ.len();
            //         succ.extend(after.into_iter());
            //         if succ_before_len != succ.len() {
            //             // changed
            //             worklist.push(succ_loc);
            //         }
            //     };
            // }
        }
    }

    fn points_to(
        &self,
        place: PlaceRef<'tcx>,
        state: &HashSet<(MCell<'tcx>, MCell<'tcx>)>,
    ) -> HashSet<MCell<'tcx>> {
        state
            .iter()
            .filter_map(|(ptr, obj)| {
                if let MCell::Direct(p, _, _) = ptr {
                    if *p == place {
                        return Some(*obj);
                    }
                }
                None
            })
            .collect()
    }

    fn process_indirect_place(
        &self,
        place: Place<'tcx>,
        before: &HashSet<(MCell<'tcx>, MCell<'tcx>)>,
    ) -> Option<HashSet<PlaceRef<'tcx>>> {
        if !place.is_indirect() {
            return None;
        }
        // PlaceRef: a.b.c
        // (a, .b)
        // (a.b, .c)
        let mut curr_places = HashSet::new();
        curr_places.insert(Place::from(place.local).as_ref());
        let mut derefed = false;
        for (place_ref, elem) in place.iter_projections() {
            match elem {
                ProjectionElem::Deref => {
                    // curr = pts(curr)
                    curr_places = curr_places.into_iter().fold(
                        HashSet::new(),
                        |mut acc: HashSet<PlaceRef>, p| {
                            acc.extend(self.points_to(p, before).into_iter().filter_map(|mcell| {
                                match mcell {
                                    MCell::Direct(place_ref, _, _)
                                    | MCell::Indirect(place_ref, _, _)
                                    | MCell::Static(place_ref, _, _)
                                    | MCell::Constant(place_ref, _, _) => Some(place_ref),
                                    _ => None,
                                }
                            }));
                            acc
                        },
                    );
                    derefed = true;
                }
                _ => {
                    if !derefed {
                        // curr = place_ref
                        curr_places.clear();
                        curr_places.insert(place_ref);
                    } else {
                        // curr.proj append elem
                        // TODO(boqin): deferred appending until Deref is met
                        curr_places = curr_places
                            .into_iter()
                            .map(|p| {
                                let mut proj: Vec<_> = p.projection.iter().copied().collect();
                                proj.push(elem);
                                let projection = hack::from_arena(self.tcx.arena, proj.as_slice());
                                Place {
                                    local: p.local,
                                    projection,
                                }
                                .as_ref()
                            })
                            .collect();
                    }
                }
            }
        }
        Some(curr_places)
    }

    fn find_place(
        &self,
        place: PlaceRef<'tcx>,
        before: &HashSet<(MCell<'tcx>, MCell<'tcx>)>,
    ) -> HashSet<(MCell<'tcx>, MCell<'tcx>)> {
        before
            .iter()
            .copied()
            .filter_map(|(ptr, obj)| {
                if ptr.as_place() == place {
                    Some((ptr, obj))
                } else {
                    None
                }
            })
            .collect()
    }

    fn direct_places(
        &self,
        place: Place<'tcx>,
        before: &HashSet<(MCell<'tcx>, MCell<'tcx>)>,
    ) -> HashSet<PlaceRef<'tcx>> {
        if !place.is_indirect() {
            let mut s = HashSet::new();
            s.insert(place.as_ref());
            s
        } else {
            if let Some(direct_places) = self.process_indirect_place(place, before) {
                direct_places
            } else {
                unreachable!();
            }
        }
    }

    // fn process_rvalues(&self, rvalue: &Rvalue<'tcx>, before: &HashSet<(MCell<'tcx>, MCell<'tcx>)>) -> {
    //     match rvalue {
    //         Rvalue::Use(operand) => {

    //         }
    //     }
    // }

    fn transfer_terminator(
        &self,
        terminator: &Terminator<'tcx>,
        location: Location,
        before: &HashSet<(MCell<'tcx>, MCell<'tcx>)>,
    ) -> HashSet<(MCell<'tcx>, MCell<'tcx>)> {
        let mut after = before.clone();
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                if let Some((place, bb)) = destination {
                    let directs = self.direct_places(*place, before);
                    // TODO: remove directs from before
                    let rmcells = directs
                        .into_iter()
                        .map(|direct| MCell::from_direct_ref(direct, location, MCellState::Init));
                    for rmcell in rmcells {
                        after.insert((rmcell, rmcell));
                    }
                }
            }
            _ => {}
        }
        after
    }

    //    fn transfer_terminator_pts(&self, terminator: &Terminator<'tcx>, location: Location, before: &Option<Rc<PtsState<'tcx>>>) -> Option<Rc<PtsState<'tcx>> {
    //     let before = match *before {
    //         None => return None,
    //         Some(before) => before,
    //     };
    //     match &terminator.kind {
    //         TerminatorKind::Call {..} => {
    //             Some(Rc::clone(before))
    //         }
    //         TerminatorKind::Drop {..} => {
    //             Some(Rc::clone(before))
    //         }
    //         _ => {
    //             Some(Rc::clone(before))
    //         }
    //     }
    // } 

    // fn transfer_statement_pts(&self, statement: &Statement<'tcx>, location: Location, before: &Option<Rc<PtsState<'tcx>>>) -> Option<Rc<PtsState<'tcx>> {
    //     let before = match *before {
    //         None => return None,
    //         Some(before) => before,
    //     }
    //     match &statement.kind {
    //         StatementKind::Assign(box (place, rvalue)) => {
    //             Some(Rc::clone(before))
    //         }
    //         StatementKind::SetDiscriminant(place, variant_index) => {
    //             Some(Rc::clone(before))
    //         }
    //         _ => {
    //             Some(Rc::clone(before))
    //         }
    //     }
    // } 

    fn transfer_statement(
        &self,
        statement: &Statement<'tcx>,
        location: Location,
        before: &HashSet<(MCell<'tcx>, MCell<'tcx>)>,
    ) -> HashSet<(MCell<'tcx>, MCell<'tcx>)> {
        let mut after = before.clone();
        match &statement.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                println!("{:?}", statement);
                let lplaces = self.direct_places(*place, before);
                match rvalue {
                    Rvalue::Use(operand) => {
                        match operand {
                            Operand::Move(rplace) => {
                                // after.update(rplace, moved)
                                let lmcells: HashSet<_> = lplaces
                                    .into_iter()
                                    .map(|place| {
                                        MCell::from_direct_ref(place, location, MCellState::Init)
                                    })
                                    .collect();
                                for direct in self.direct_places(*rplace, before) {
                                    let pts = self.points_to(direct, before);
                                    for lmcell in lmcells.iter() {
                                        for rmcell in pts.iter() {
                                            after.insert((*lmcell, *rmcell));
                                        }
                                    }
                                }
                            }
                            Operand::Copy(rplace) => {
                                let lmcells: HashSet<_> = lplaces
                                    .into_iter()
                                    .map(|place| {
                                        MCell::from_direct_ref(place, location, MCellState::Init)
                                    })
                                    .collect();
                                for direct in self.direct_places(*rplace, before) {
                                    let pts = self.points_to(direct, before);
                                    for lmcell in lmcells.iter() {
                                        for rmcell in pts.iter() {
                                            after.insert((*lmcell, *rmcell));
                                        }
                                    }
                                }
                            }
                            Operand::Constant(box constant) => {
                                let lmcells: HashSet<_> = lplaces
                                    .iter()
                                    .map(|place| {
                                        MCell::from_direct_ref(*place, location, MCellState::Init)
                                    })
                                    .collect();
                                let rmcell =
                                    MCell::Constant(place.as_ref(), location, MCellState::Init);
                                for lmcell in lmcells.iter() {
                                    after.insert((*lmcell, rmcell));
                                }
                            }
                        }
                    }
                    Rvalue::Ref(rg, bk, rplace) => {
                        // lplace = &rplace: (lmcell, rmcell, state)
                        let rplaces = if rplace.is_indirect() {
                            if let Some(places) = self.process_indirect_place(*rplace, before) {
                                println!("{:?} resolves to {:#?}", place, places);
                                if places.is_empty() {
                                    let mut places = HashSet::new();
                                    places.insert(rplace.as_ref());
                                    places
                                } else {
                                    places
                                }
                            } else {
                                println!(
                                    "Cannot resolve indirect place {:?} in {:?} at {:?}",
                                    place, statement, location
                                );
                                // HashSet::new()
                                let mut s = HashSet::new();
                                s.insert(place.as_ref());
                                s
                            }
                        } else {
                            let mut s = HashSet::new();
                            s.insert(place.as_ref());
                            s
                        };
                        for lplace in lplaces.iter() {
                            let pts = self.find_place(*lplace, before);
                            if !pts.is_empty() {
                                // remove pts (redef: first remove)
                                after.retain(|pt| !pts.contains(&pt));
                            }

                            // add lmcells (def)
                            let mut lmcells = HashSet::new();
                            lmcells.insert(MCell::from_direct_ref(
                                *lplace,
                                location,
                                MCellState::Init,
                            ));

                            for lmcell in lmcells {
                                for rplace in rplaces.iter() {
                                    let pts = self.find_place(*rplace, before);
                                    if !pts.is_empty() {
                                        for (ptr, _) in pts {
                                            after.insert((lmcell, ptr));
                                        }
                                    } else {
                                        println!(
                                            "Cannot find Def of rplace {:?} in {:?} at {:?}",
                                            rplace, statement, location
                                        );
                                        let pts = self
                                            .find_place(Place::from(rplace.local).as_ref(), before);
                                        for (ptr, _) in pts {
                                            after.insert((lmcell, ptr));
                                        }
                                    }
                                }
                            }
                        }
                    }
                    Rvalue::AddressOf(mutbl, place) => {
                        if place.is_indirect() {
                            let rplaces = self.process_indirect_place(*place, before);
                        }
                    }
                    _ => {}
                }
            }
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                println!("{:?}", statement);
                let directs = self.direct_places(**place, before);
                // TODO: remove directs from before
                let rmcells = directs
                    .into_iter()
                    .map(|direct| MCell::from_direct_ref(direct, location, MCellState::Init));
                for rmcell in rmcells {
                    after.insert((rmcell, rmcell));
                }
            }
            _ => {}
        }
        after
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
