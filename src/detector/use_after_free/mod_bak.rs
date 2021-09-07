//! # Use After Free Detectors
//!
//! a ptr is still alive when the pointed-to obj is dropped.
//! So we check each obj dropping place to find the live ptr and check if any ptr points to the obj.

// use crate::callgraph::Callgraph;
// use crate::pointer_analysis::{InstLocation, MemCell, PointerAnalysis, Var};
// use crate::util::{Instruction, Monomorphizer};
// use rustc_middle::{
//     mir::{
//         Body, Constant, Field, Local, Location, Operand, Place, ProjectionElem, Rvalue,
//         StatementKind, Terminator, TerminatorKind, RETURN_PLACE,
//     },
//     ty::{self, Instance, InstanceDef, ParamEnv, TyCtxt, TyKind},
// };
// use rustc_span::Span;
// use std::collections::{HashMap, HashSet, VecDeque};

// type State = HashSet<Local>;
// pub struct UseAfterFree<'tcx> {
//     tcx: TyCtxt<'tcx>,
//     pointer_analysis: PointerAnalysis<'tcx>,
//     states: HashMap<InstLocation<'tcx>, State>,
//     worklist: VecDeque<InstLocation<'tcx>>,
// }

// impl<'tcx> UseAfterFree<'tcx> {
//     pub fn new(tcx: TyCtxt<'tcx>, pointer_analysis: PointerAnalysis<'tcx>) -> Self {
//         Self {
//             tcx,
//             pointer_analysis,
//             states: HashMap::new(),
//             worklist: VecDeque::new(),
//         }
//     }

//     pub fn analyze(&mut self, instance: Instance<'tcx>) {
//         self.analyze_instance_recur(instance);
//     }

//     pub fn analyze_instance_recur(&mut self, instance: Instance<'tcx>) {
//         if !self.should_analyze(&instance) {
//             return;
//         }
//         let body = self.tcx.instance_mir(instance.def);
//         self.init_empty(instance, body);
//         // make return and args live
//         self.init_with_args_states(instance, body);
//         // BFS InstLocations
//         while let Some(instloc) = self.worklist.pop_front() {
//             if let Some(instruction) = Instruction::new(body, instloc.location) {
//                 let after = if instruction.is_terminator() {
//                     let state = self.states.get(&instloc).unwrap().clone();
//                     self.transfer_terminator(state, body, instance, instruction)
//                 } else {
//                     let state = self.states.get(&instloc).unwrap();
//                     Self::transfer_statement(state, instance, instruction)
//                 };
//                 if instruction.successors().is_empty() {
//                     // return_like_instlocs.push(instloc);
//                     continue;
//                 }
//                 for next in instruction.successors() {
//                     let next_instloc = InstLocation {
//                         instance,
//                         location: next.location,
//                     };
//                     let next_state = self.states.get_mut(&next_instloc).unwrap();
//                     let changed = Self::union_states(next_state, after.clone());
//                     if changed {
//                         self.worklist.push_back(next_instloc);
//                     }
//                 }
//             }
//         }
//     }

//     fn transfer_terminator(
//         &mut self,
//         mut state: State,
//         body: &Body<'tcx>,
//         instance: Instance<'tcx>,
//         instruction: Instruction<'tcx>,
//     ) -> State {
//         println!(
//             "Location: {:?}, {:?}",
//             instance.def.def_id(),
//             instruction.location
//         );
//         match instruction.get_terminator().kind {
//             TerminatorKind::Drop { place, .. } => {
//                 let to_be_dropped = MemCell::from_var(instance, Var::from_local(place.local));
//                 let instloc = InstLocation {
//                     instance,
//                     location: instruction.location,
//                 };
//                 let live_locals = self.states.get(&instloc).unwrap();
//                 println!("Live: {:?}", live_locals);
//                 for succ in instruction.successors() {
//                     let mut worklist = Vec::new();
//                     worklist.push(succ);
//                     while let Some(next) = worklist.pop() {
//                         if next.is_terminator() {
//                             if let Some(pts) = self.pointer_analysis.states.get(&instloc) {
//                                 for live_local in &state {
//                                     if let TyKind::RawPtr(_) =
//                                         body.local_decls[*live_local].ty.kind()
//                                     {
//                                         let var = Var::from_local(*live_local);
//                                         if let Some(memcells) = pts.get(&var) {
//                                             if memcells.contains(&to_be_dropped) {
//                                                 println!("body: {:#?}", body);
//                                                 println!("Terminator: {:?}", next.location);
//                                                 println!(
//                                                     "LivLocal: {:?}, UAF: {:#?}",
//                                                     live_local, memcells
//                                                 );
//                                             }
//                                         }
//                                     }
//                                 }
//                             }
//                             break;
//                         }

//                         match next.get_statement().kind {
//                             StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {
//                                 state = Self::transfer_statement(&state, instance, next);
//                                 for next_succ in next.successors() {
//                                     worklist.push(next_succ);
//                                 }
//                             }
//                             _ => {
//                                 if let Some(pts) = self.pointer_analysis.states.get(&instloc) {
//                                     for live_local in &state {
//                                         if let TyKind::RawPtr(_) =
//                                             body.local_decls[*live_local].ty.kind()
//                                         {
//                                             let var = Var::from_local(*live_local);
//                                             if let Some(memcells) = pts.get(&var) {
//                                                 if memcells.contains(&to_be_dropped) {
//                                                     println!("body: {:#?}", body);
//                                                     println!("Statement: {:?}", next.location);
//                                                     println!(
//                                                         "LivLocal: {:?}, UAF: {:#?}",
//                                                         live_local, memcells
//                                                     );
//                                                 }
//                                             }
//                                         }
//                                     }
//                                 }
//                                 break;
//                             }
//                         }
//                     }
//                 }
//             }
//             // TODO(Boqin)
//             _ => {}
//         }
//         state
//     }

//     fn transfer_statement(
//         state: &State,
//         instance: Instance<'tcx>,
//         instruction: Instruction<'tcx>,
//     ) -> State {
//         let mut after = state.clone();
//         let stmt = instruction.get_statement();
//         match stmt.kind {
//             StatementKind::StorageLive(local) => {
//                 after.insert(local);
//             }
//             StatementKind::StorageDead(local) => {
//                 after.remove(&local);
//             }
//             _ => {}
//         };
//         after
//     }

//     /// Merge rhs map into lhs map, return true if lhs is changed
//     fn union_states(lhs: &mut State, rhs: State) -> bool {
//         let old_len = lhs.len();
//         lhs.extend(rhs.into_iter());
//         old_len != lhs.len()
//     }

//     fn should_analyze(&self, instance: &Instance<'tcx>) -> bool {
//         if let InstanceDef::Item(_) = instance.def {
//             self.tcx.is_mir_available(instance.def_id())
//         } else {
//             false
//         }
//     }

//     /// init empty states and worklist
//     /// body must correspond to instance
//     fn init_empty(&mut self, instance: Instance<'tcx>, body: &Body<'tcx>) {
//         for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
//             for (stmt_idx, _) in bb_data.statements.iter().enumerate() {
//                 let location = Location {
//                     block: bb,
//                     statement_index: stmt_idx,
//                 };
//                 let inst_location = InstLocation { instance, location };
//                 self.states.insert(inst_location, HashSet::new());
//                 self.worklist.push_back(inst_location)
//             }
//             if bb_data.terminator.is_some() {
//                 let location = Location {
//                     block: bb,
//                     statement_index: bb_data.statements.len(),
//                 };
//                 let inst_location = InstLocation { instance, location };
//                 self.states.insert(inst_location, HashSet::new());
//                 self.worklist.push_back(inst_location);
//             }
//         }
//     }

//     /// args and return lives
//     /// body must correspond to instance
//     fn init_with_args_states(&mut self, instance: Instance<'tcx>, body: &Body<'tcx>) {
//         let mut live_state = HashSet::new();
//         for arg in body.args_iter() {
//             live_state.insert(arg);
//         }
//         live_state.insert(RETURN_PLACE);
//         self.states.insert(
//             InstLocation {
//                 instance,
//                 location: Location::START,
//             },
//             live_state,
//         );
//     }
// }
