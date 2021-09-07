//! Use-After-Free Detector
//! Rules:
//! 1. The function contains raw pointers
//! 2.1 raw pointers are dereferenced after the pointee obj is dropped
//! 2.2 or raw pointers to local obj escape the current function by return/parameter
//! 2.3 or raw pointers to local obj escape the current function by assigning to globals

use rustc_middle::mir::{
    visit::{PlaceContext, Visitor},
    RETURN_PLACE,
};
use rustc_middle::mir::{Body, Local, Location, Place, Statement, Terminator, TerminatorKind};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_middle::ty::{Instance, InstanceDef};
use std::collections::{HashMap, HashSet};

use crate::pointer_analysis::IntraProceduralPointerAnalysis;
pub struct UseAfterFreeDetector<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> UseAfterFreeDetector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    pub fn analyze(&mut self, instance: Instance<'tcx>) {
        if !self.should_analyze(&instance) {
            return;
        }

        let body = self.tcx.instance_mir(instance.def);
        let raw_ptrs = self.raw_ptrs(body);
        if raw_ptrs.is_empty() {
            return;
        }
        let mut intra_pointer_analysis = IntraProceduralPointerAnalysis::new(self.tcx);
        let (globals, escapes) = intra_pointer_analysis.analyze(instance);
        // drop, return, resume
        let mut collector = DropReturnResumeCollector::new(self.tcx);
        collector.visit_body(body);
        let mut dropped_raw_ptrs = HashSet::new();
        let mut dropped_places = HashSet::new();
        for drop in collector.drops {
            let terminator = body.basic_blocks()[drop.block].terminator();
            if let TerminatorKind::Drop { place, target, .. } = terminator.kind {
                dropped_places.insert(place);
                for raw_ptr in raw_ptrs.iter() {
                    if intra_pointer_analysis.may_points_to(
                        drop,
                        Place::from(*raw_ptr),
                        place,
                        &globals,
                    ) {
                        // raw ptr -> dropped place, raw ptr is used in blocks reachable from target
                        dropped_raw_ptrs.insert((drop, target, *raw_ptr, place));
                    }
                }
            }
        }
        // find usage of raw_ptr from target to return/resume
        // use(raw_ptr)
        let mut raw_ptr_deref_collector = RawPtrDerefCollector::new(self.tcx, raw_ptrs.clone());
        raw_ptr_deref_collector.visit_body(body);
        for (dropped_loc, target_bb, raw_ptr, dropped_place) in dropped_raw_ptrs.iter().copied() {
            let target_loc = Location {
                block: target_bb,
                statement_index: 0,
            };
            if let Some(derefed_locs) = raw_ptr_deref_collector.locations.get(&raw_ptr) {
                for derefed_loc in derefed_locs {
                    // (target_bb, 0) -> derefed_loc.block
                    if is_reachable_from(target_loc, *derefed_loc, body) {
                        println!("Bug: Use-After-Drop: Dropped Loc: {:?}, {:?}, RawPtr: {:?}, Dropped Place: {:?}, DerefedLoc: {:?}, {:?}", body.source_info(dropped_loc), dropped_loc, raw_ptr, dropped_place, body.source_info(*derefed_loc), derefed_loc);
                    }
                }
            }
        }
        // check at return
        let mut return_or_args = HashSet::new();
        return_or_args.insert(RETURN_PLACE);
        for arg in body.args_iter() {
            return_or_args.insert(arg);
        }
        for return_loc in collector.returns {
            for pointer in return_or_args.iter().map(|local| Place::from(*local)) {
                for (dropped_loc, target_bb, _raw_ptr, dropped_place) in
                    dropped_raw_ptrs.iter().copied()
                {
                    let drop_target_loc = Location { block: target_bb, statement_index: 0 };
                    if !is_reachable_from(drop_target_loc, return_loc, body) {
                        continue;
                    }
                    if intra_pointer_analysis.may_points_to(
                        return_loc,
                        pointer,
                        dropped_place,
                        &globals,
                    ) {
                        println!("Bug: Return/Arg Escape: Dropped Loc: {:?}, {:?}, Ptr: {:?}, Dropped Place: {:?}, DerefedLoc: {:?}, {:?}", body.source_info(dropped_loc), dropped_loc, pointer, dropped_place, body.source_info(return_loc), return_loc);
                    }
                }
            }

            // println!("escapes: {:#?}", escapes);
            if let Some(ref escapes) = escapes {
                for (pointer, def_id) in escapes.iter() {
                    // println!("escape place1: {:?}", pointer.as_place_ref());
                    // println!("escape place1: {:?}", dropped_raw_ptrs);
                    for dropped_place in dropped_places.iter().copied() {
                        if let Some(place_ref) = pointer.as_place_ref() {
                            // println!("escape place: {:?}", place_ref);
                            // println!("dropped place: {:?}", dropped_place.as_ref());
                            if intra_pointer_analysis.may_points_to_ref(
                                return_loc,
                                place_ref,
                                dropped_place.as_ref(),
                                &globals,
                            ) {
                                println!(
                                    "Bug: Global Escape: Dropped Place: {:?}, Escaped Place: {:?}, Return Location: {:?}, Save to Global DefId: {:?}",
                                    dropped_place, place_ref, body.source_info(return_loc), def_id
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    fn should_analyze(&self, instance: &Instance<'tcx>) -> bool {
        if let InstanceDef::Item(_) = instance.def {
            self.tcx.is_mir_available(instance.def_id())
        } else {
            false
        }
    }

    fn raw_ptrs(&self, body: &'tcx Body<'tcx>) -> HashSet<Local> {
        body.local_decls
            .iter_enumerated()
            .filter_map(|(local, local_decl)| {
                if local_decl.ty.is_unsafe_ptr() {
                    Some(local)
                } else {
                    None
                }
            })
            .collect()
    }
}

fn is_reachable_from<'tcx>(from: Location, to: Location, body: &Body<'tcx>) -> bool {
    let mut worklist = Vec::new();
    worklist.push(from);
    while let Some(curr) = worklist.pop() {
        if curr == to {
            return true;
        }
        if body.terminator_loc(curr.block) == curr {
            for succ in body.basic_blocks()[curr.block].terminator().successors() {
                worklist.push(Location {
                    block: *succ,
                    statement_index: 0,
                });
            }
        } else {
            worklist.push(curr.successor_within_block());
        }
    }
    false
}
pub struct RawPtrDerefCollector<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub raw_ptrs: HashSet<Local>,
    pub locations: HashMap<Local, HashSet<Location>>,
}

impl<'tcx> RawPtrDerefCollector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, raw_ptrs: HashSet<Local>) -> Self {
        Self {
            tcx,
            raw_ptrs,
            locations: HashMap::new(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for RawPtrDerefCollector<'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, _context: PlaceContext, location: Location) {
        if !self.raw_ptrs.contains(&place.local) {
            return;
        }
        if !place.is_indirect() {
            return;
        }
        self.locations
            .entry(place.local)
            .or_default()
            .insert(location);
    }
}

// DropReturnResumeCollector
pub struct DropReturnResumeCollector<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub drops: HashSet<Location>,
    pub returns: HashSet<Location>,
    pub resumes: HashSet<Location>,
}

impl<'tcx> DropReturnResumeCollector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            drops: HashSet::new(),
            returns: HashSet::new(),
            resumes: HashSet::new(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for DropReturnResumeCollector<'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            TerminatorKind::Drop { .. } => {
                self.drops.insert(location);
            }
            TerminatorKind::Return => {
                self.returns.insert(location);
            }
            TerminatorKind::Resume => {
                self.resumes.insert(location);
            }
            _ => {}
        }
    }
}
