extern crate rustc_target;

use crate::callgraph::Callgraph;
// use crate::pointer_analysis::{InstLocation, MemCell, PointerAnalysis, Var};
use crate::util::{Instruction, Monomorphizer};
use once_cell::sync::Lazy;
use regex::Regex;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, Body, BorrowKind, Constant, Field, Local, Location, Operand, Place, PlaceElem,
        ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, RETURN_PLACE,
    },
    ty::{self, Instance, InstanceDef, ParamEnv, Ty, TyCtxt, TyKind, TyS},
};
use rustc_span::Span;
use rustc_target::abi::VariantIdx;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
// pub struct TotalAnalysis<'tcx> {
//     pub tcx: TyCtxt<'tcx>,
//     pub states: HashMap<Location, HashSet<TotalMemObj<'tcx>>>,
// }

pub struct ValueFlowAnalysis<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub states: HashMap<Location, OneState<'tcx>>,
}

impl<'tcx> ValueFlowAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            states: HashMap::new(),
        }
    }

    fn has_ptr(&self, body: &Body<'tcx>) -> bool {
        body.local_decls.iter().any(|decl| decl.ty.is_unsafe_ptr())
    }

    fn has_uninit(&self, body: &Body<'tcx>, instance: &Instance<'tcx>) -> bool {
        body.basic_blocks().iter_enumerated().any(|(_bb, bb_data)| {
            let term = bb_data.terminator();
            if let TerminatorKind::Call {
                ref func,
                ref args,
                destination,
                ..
            } = term.kind
            {
                let func_ty = func.ty(body, self.tcx);
                let func_ty = instance.subst_mir_and_normalize_erasing_regions(
                    self.tcx,
                    ty::ParamEnv::reveal_all(),
                    func_ty,
                );
                if let TyKind::FnDef(def_id, substs_ref) = func_ty.kind() {
                    let def_path_str = self.tcx.def_path_str_with_substs(*def_id, substs_ref);
                    match check_uninit(&def_path_str) {
                        Uninit::Not => {}
                        _ => {
                            return true;
                        }
                    }
                }
            }
            false
        })
    }
    pub fn analyze(&mut self, instance: Instance<'tcx>) {
        if !self.should_analyze(&instance) {
            return;
        }
        if !instance.def_id().is_local() {
            return;
        }
        // println!("{:?}", instance.def_id());
        let body = self.tcx.instance_mir(instance.def);
        if self.has_ptr(body) && self.has_uninit(body, &instance) {
            println!("{:?}", body.span);
        }
        return;
        let mut worklist = Self::init_worklist(body);
        self.init_mapping(body);
        let mut cnt = 10000;
        while let Some(loc) = worklist.pop() {
            // state transfer
            if cnt == 0 {
                break;
            }
            cnt -= 1;
            if body.terminator_loc(loc.block) != loc {
                let before = self.states.get(&loc).unwrap();
                let stmt = &body[loc.block].statements[loc.statement_index];
                let after = self.transfer_statement(before, stmt, loc);
                // strong update
                *self.states.get_mut(&loc).unwrap() = after.clone();
                let succ = loc.successor_within_block();
                let succ_state = self.states.get_mut(&succ).unwrap();
                let changed = union_states(succ_state, after);
                if changed {
                    worklist.push(succ);
                }
            } else {
                // transfer_terminator
                let term = body[loc.block].terminator();
                let before = self.states.get(&loc).unwrap().clone();
                let afters = self.transfer_terminator(&before, term, loc, instance, body);
                for succ_bb in term.successors() {
                    // TODO(boqin): transfer terminator state
                    let after = afters.get(&succ_bb).unwrap().clone();
                    let succ = Location {
                        block: *succ_bb,
                        statement_index: 0,
                    };
                    let succ_state = self.states.get_mut(&succ).unwrap();
                    let changed = union_states(succ_state, after);
                    if changed {
                        worklist.push(succ);
                    }
                }
            }
        }
        if self
            .tcx
            .def_path_str(instance.def_id())
            .contains("custom_deref")
        {
            println!("{:?}", instance.def);
            for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
                for stmt_idx in 0..=bb_data.statements.len() {
                    let loc = Location {
                        block: bb,
                        statement_index: stmt_idx,
                    };
                    println!("{:?}: {:#?}", loc, self.states.get(&loc).unwrap());
                }
            }
        }
    }

    fn init_mapping(&mut self, body: &'tcx Body<'tcx>) {
        for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
            for stmt_idx in 0..=bb_data.statements.len() {
                self.states.insert(
                    Location {
                        block: bb,
                        statement_index: stmt_idx,
                    },
                    HashMap::new(),
                );
            }
        }
        self.init_args(body);
    }

    fn init_args(&mut self, body: &'tcx Body<'tcx>) {
        let svalues: HashMap<_, _> = body
            .args_iter()
            .map(|arg| {
                let mcell = MCell::from_place(Place::from(arg));
                let tcell = TCell::from_arg(arg);
                let svalue = SValue::new(tcell, Location::START, ValueState::FromArg);
                let mut svalues = HashSet::new();
                svalues.insert(svalue);
                (mcell, svalues)
            })
            .collect();
        self.states.insert(Location::START, svalues);
    }

    fn init_worklist(body: &'tcx Body<'tcx>) -> Vec<Location> {
        let mut worklist = Vec::new();
        for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
            for stmt_idx in 0..=bb_data.statements.len() {
                worklist.push(Location {
                    block: bb,
                    statement_index: stmt_idx,
                });
            }
        }
        worklist
    }

    fn should_analyze(&self, instance: &Instance<'tcx>) -> bool {
        if let InstanceDef::Item(_) = instance.def {
            self.tcx.is_mir_available(instance.def_id())
        } else {
            false
        }
    }
    pub fn transfer_statement(
        &self,
        before: &OneState<'tcx>,
        stmt: &Statement<'tcx>,
        loc: Location,
    ) -> OneState<'tcx> {
        let mut after = before.clone();
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                // A
                // A [F]
                // A [Deref]
                // A [F] [Deref]
                let left = MCell::from_place(*place);
                let svalues = process_rvalue(&mut after, &rvalue, loc, self.tcx);
                after.insert(left, svalues); // strong update
            }
            StatementKind::SetDiscriminant {
                box place,
                variant_index,
            } => {
                let left = MCell::from_place(*place);
                let mut svalues = HashSet::new();
                let tcell = TCell::from_variant_idx(*variant_index);
                svalues.insert(SValue::new(tcell, loc, ValueState::Init));
                after.insert(left, svalues); // strong update
            }
            _ => {}
        };
        after
    }

    pub fn transfer_terminator(
        &mut self,
        before: &OneState<'tcx>,
        term: &Terminator<'tcx>,
        loc: Location,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) -> HashMap<BasicBlock, OneState<'tcx>> {
        let mut afters = HashMap::new();
        for succ_bb in term.successors() {
            afters.insert(*succ_bb, before.clone());
        }
        match term.kind {
            TerminatorKind::Call {
                ref func,
                ref args,
                destination,
                ..
            } => {
                let func_ty = func.ty(body, self.tcx);
                let func_ty = instance.subst_mir_and_normalize_erasing_regions(
                    self.tcx,
                    ty::ParamEnv::reveal_all(),
                    func_ty,
                );
                if let TyKind::FnDef(def_id, substs_ref) = func_ty.kind() {
                    let def_path_str = self.tcx.def_path_str_with_substs(*def_id, substs_ref);
                    // println!("{}", def_path_str);
                    match check_uninit(&def_path_str) {
                        Uninit::UninitObj => {
                            println!("{}", def_path_str);
                            if let Some((dst, bb)) = destination {
                                let mcell = MCell::from_place(dst);
                                let svalue =
                                    SValue::new(TCell::CallUninit, loc, ValueState::Uninit);
                                let mut svalues = HashSet::new();
                                svalues.insert(svalue);
                                let mut one_state = HashMap::new();
                                one_state.insert(mcell, svalues);
                                union_replace_states(afters.get_mut(&bb).unwrap(), one_state);
                            }
                        }
                        Uninit::UninitPtr => {
                            println!("{}", def_path_str);
                            if let Some((dst, bb)) = destination {
                                let mcell = MCell::from_place(dst);
                                let svalue =
                                    SValue::new(TCell::CallUninit, loc, ValueState::PtUninit);
                                let mut svalues = HashSet::new();
                                svalues.insert(svalue);
                                let mut one_state = HashMap::new();
                                one_state.insert(mcell, svalues);
                                union_replace_states(afters.get_mut(&bb).unwrap(), one_state);
                            }
                        }
                        Uninit::UnintFirstArg => {
                            println!("{}", def_path_str);
                            if let Some((_, bb)) = destination {
                                let first_arg = &args[0];
                                let mcell = MCell::from_place(first_arg.place().unwrap());
                                let svalue =
                                    SValue::new(TCell::CallUninit, loc, ValueState::PtUninit);
                                let mut svalues = HashSet::new();
                                svalues.insert(svalue);
                                let mut one_state = HashMap::new();
                                one_state.insert(mcell, svalues);
                                union_replace_states(afters.get_mut(&bb).unwrap(), one_state);
                            }
                        }
                        Uninit::Not => {}
                    }
                    if is_ptr_write(&def_path_str) {
                        println!("{}", def_path_str);
                        let dst_ptr = &args[0];
                        let dst_cell = MCell::from_place(dst_ptr.place().unwrap());
                        let deref_cell = dst_cell.push_deref();
                        let src = &args[1];
                        let mut after = before.clone();
                        let svalues = process_operand(&mut after, src, loc, self.tcx);
                        after.insert(deref_cell, svalues);
                        if let Some((_, bb)) = destination {
                            // strong update
                            *afters.get_mut(&bb).unwrap() = after;
                        }
                    } else if is_ptr_read(&def_path_str) {
                        // if let Some(dst, bb) = destination {
                        //     let dst_cell = MCell::from_place(dst.place().unwrap());
                        //     let src_ptr = &args[0];
                        // }
                    }
                }
            }
            TerminatorKind::Drop {
                place,
                target,
                unwind,
            } => {
                let mcell = MCell::from_place(place);
                if let Some(values) = before.get(&mcell) {
                    // check drop invalid or double drop
                    if values.iter().any(|value| value.state == ValueState::Uninit) {
                        println!("Drop Uninit {:?}, {:?}, {:?}", mcell, loc, term);
                    }
                    // remove place
                    // drop values
                } else {
                    let mut curr_place = Place::from(place.local);
                    for prj in place.projection {
                        if prj == ProjectionElem::Deref {
                            let mcell = MCell::from_place(curr_place);
                            if let Some(svalues) = before.get(&mcell) {
                                if svalues
                                    .iter()
                                    .any(|value| value.state == ValueState::PtUninit)
                                {
                                    println!("Drop Uninit {:?}, {:?}, {:?}", mcell, loc, term);
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        afters
    }
}

// pub fn find_place<'tcx>(state: &OneState, place: Place<'tcx>) -> HashSet<SValue<'tcx>> {
//     let mcell = MCell::from_place(place);
//     if let Some(svalues) = state.get(&mcell) {
//         svalues.clone()
//     } else {

//     }
// }

// strong update
pub fn union_replace_states<'tcx>(target: &mut OneState<'tcx>, src: OneState<'tcx>) -> bool {
    let mut changed = false;
    for (k, v) in src.into_iter() {
        if !target.contains_key(&k) {
            target.insert(k, v);
            changed = true;
        } else {
            let values = target.get_mut(&k).unwrap();
            if *values != v {
                *values = v;
                changed = true;
            }
        }
    }
    changed
}

pub fn union_states<'tcx>(target: &mut OneState<'tcx>, src: OneState<'tcx>) -> bool {
    let mut changed = false;
    for (k, v) in src.into_iter() {
        if !target.contains_key(&k) {
            target.insert(k, v);
            changed = true;
        } else {
            let values = target.get_mut(&k).unwrap();
            for s in v {
                changed |= values.insert(s)
            }
        }
    }
    changed
}

static UNINIT_REGEX: Lazy<HashMap<&'static str, Regex>> = Lazy::new(|| {
    let mut m = HashMap::new();
    m.insert(
        "mem::uninitialized",
        Regex::new("^(std|core)::mem::uninitialized::<.+>$").unwrap(),
    );
    m.insert(
        "mem::MaybeUninit",
        Regex::new("^(std|core)::mem::MaybeUninit::<.+>::uninit$").unwrap(),
    );
    m.insert(
        "alloc::alloc::__rust_alloc",
        Regex::new("^alloc::alloc::__rust_alloc$").unwrap(),
    );
    m.insert(
        "std::alloc::alloc",
        Regex::new("^std::alloc::alloc$").unwrap(),
    );
    m.insert("::alloc", Regex::new("::alloc$").unwrap());
    m.insert("Vec::set_len", Regex::new("^Vec::<.+>::set_len$").unwrap());
    m
});

pub enum Uninit {
    UninitObj,
    UninitPtr,
    UnintFirstArg,
    Not,
}
pub fn check_uninit(fn_name: &str) -> Uninit {
    if UNINIT_REGEX
        .get(&"mem::uninitialized")
        .unwrap()
        .is_match(fn_name)
        || UNINIT_REGEX
            .get(&"mem::MaybeUninit")
            .unwrap()
            .is_match(fn_name)
    {
        Uninit::UninitObj
    } else if UNINIT_REGEX
        .get(&"alloc::alloc::__rust_alloc")
        .unwrap()
        .is_match(fn_name)
        || UNINIT_REGEX
            .get(&"std::alloc::alloc")
            .unwrap()
            .is_match(fn_name)
        || UNINIT_REGEX.get(&"::alloc").unwrap().is_match(fn_name)
        || UNINIT_REGEX
            .get(&"Vec::set_len") // arg > 0
            .unwrap()
            .is_match(fn_name)
    {
        Uninit::UninitPtr
    } else {
        Uninit::Not
    }
}

pub fn is_ptr_write(fn_name: &str) -> bool {
    fn_name.starts_with("std::ptr::write::<")
}

pub fn is_ptr_read(fn_name: &str) -> bool {
    fn_name.starts_with("std::ptr::read::<")
}

// MemCell: Path x State x Location
// MemCell points-to MemCell (A = &B) // borrow
// MemCell copy-from MemCell (A = B)  // copy B to A (Copyable)
// MemCell move-from MemCell (A = move B)  // drop old A and move B to A (ownership transfer)
// MemCell read-from MemCell (A = ptr::read(B))  // copy B to A (Non-copyable) (two ownerships)
// MemCell write-from MemCell (ptr::write(A, B))  // move B to A without dropping A (ownership transfer, no dropping)

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MConst<'tcx> {
    pub span: Span,
    pub literal: &'tcx ty::Const<'tcx>,
}

impl<'tcx> MConst<'tcx> {
    pub fn from_constant(c: &Constant<'tcx>) -> Self {
        Self {
            span: c.span,
            literal: c.literal,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TCell<'tcx> {
    Const(MConst<'tcx>),
    Static(DefId),
    Cell(MCell<'tcx>),
    Ref(MCell<'tcx>),
    Addr(MCell<'tcx>),
    Arg(MCell<'tcx>),
    VarIdx(VariantIdx),
    CallUninit,
}

impl<'tcx> TCell<'tcx> {
    pub fn from_constant(c: &Constant<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        if let Some(def_id) = c.check_static_ptr(tcx) {
            TCell::Static(def_id)
        } else {
            TCell::Const(MConst::from_constant(c))
        }
    }
    pub fn from_place(place: Place<'tcx>) -> Self {
        TCell::Cell(MCell::from_place(place))
    }
    pub fn from_ref(place: Place<'tcx>) -> Self {
        TCell::Ref(MCell::from_place(place))
    }
    pub fn from_addr(place: Place<'tcx>) -> Self {
        TCell::Addr(MCell::from_place(place))
    }
    pub fn from_arg(arg: Local) -> Self {
        TCell::Arg(MCell::from_place(Place::from(arg)))
    }
    pub fn from_variant_idx(variant_idx: VariantIdx) -> Self {
        TCell::VarIdx(variant_idx)
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MCell<'tcx> {
    pub local: Local,
    pub projection: Vec<PlaceElem<'tcx>>,
}

impl<'tcx> MCell<'tcx> {
    pub fn pop_deref(&self) -> Option<MCell<'tcx>> {
        if let Some(ProjectionElem::Deref) = self.projection.last() {
            let mut projection = Vec::new();
            projection.extend_from_slice(&self.projection[..self.projection.len() - 1]);
            Some(MCell {
                local: self.local,
                projection,
            })
        } else {
            None
        }
    }
    pub fn push_deref(&self) -> MCell<'tcx> {
        let mut projection = self.projection.clone();
        projection.push(ProjectionElem::Deref);
        MCell {
            local: self.local,
            projection,
        }
    }
}

// MCell stores SValues
type OneState<'tcx> = HashMap<MCell<'tcx>, HashSet<SValue<'tcx>>>;
pub struct PropState<'tcx> {
    pub mapping: HashMap<Location, OneState<'tcx>>,
}

pub fn place_to_val<'tcx>(state: &OneState<'tcx>, place: Place<'tcx>) -> HashSet<SValue<'tcx>> {
    let mcell = MCell::from_place(place);
    if let Some(values) = state.get(&mcell) {
        (*values).clone()
    } else {
        HashSet::new()
    }
}

fn take_val<'tcx>(mcell: &MCell<'tcx>, state: &mut OneState<'tcx>) -> HashSet<SValue<'tcx>> {
    if let Some(values) = state.get_mut(mcell) {
        std::mem::replace(values, HashSet::new())
    } else {
        HashSet::new()
    }
}

fn copy_val<'tcx>(mcell: &MCell<'tcx>, state: &OneState<'tcx>) -> HashSet<SValue<'tcx>> {
    if let Some(values) = state.get(mcell) {
        values.clone()
    } else {
        HashSet::new()
    }
}
// [deref ptr] => {v}
// [ptr] = {v}
pub fn process_operand<'tcx>(
    state: &mut OneState<'tcx>,
    operand: &Operand<'tcx>,
    loc: Location,
    tcx: TyCtxt<'tcx>,
) -> HashSet<SValue<'tcx>> {
    match operand {
        Operand::Copy(place) => {
            let mcell = MCell::from_place(*place);
            copy_val(&mcell, state)
        }
        Operand::Move(place) => {
            let mcell = MCell::from_place(*place);
            take_val(&mcell, state)
        }
        Operand::Constant(ref constant) => {
            let mut m = HashSet::new();
            let tcell = TCell::from_constant(constant, tcx);
            let svalue = SValue::new(tcell, loc, ValueState::Init);
            m.insert(svalue);
            m
        }
    }
}

pub fn process_rvalue<'tcx>(
    state: &mut OneState<'tcx>,
    rvalue: &Rvalue<'tcx>,
    loc: Location,
    tcx: TyCtxt<'tcx>,
) -> HashSet<SValue<'tcx>> {
    let mut m = HashSet::new();
    match rvalue {
        Rvalue::Use(operand) | Rvalue::Repeat(operand, _) | Rvalue::Cast(_, operand, _) => {
            m.extend(process_operand(state, operand, loc, tcx).into_iter());
        }
        Rvalue::Ref(_, bk, place) => {
            let mcell = MCell::from_place(*place);
            let value_state = if let Some(values) = state.get(&mcell) {
                if values.iter().any(|value| value.state == ValueState::Uninit) {
                    ValueState::PtUninit
                } else {
                    ValueState::PtInit
                }
            } else {
                ValueState::PtUnknown
            };
            let tcell = TCell::from_ref(*place);
            let svalue = SValue::new(tcell, loc, value_state);
            m.insert(svalue);
        }
        Rvalue::AddressOf(mutbl, place) => {
            let mcell = MCell::from_place(*place);
            let tcell = TCell::from_addr(*place);
            let value_state = if let Some(values) = state.get(&mcell) {
                if values.iter().any(|value| value.state == ValueState::Uninit) {
                    ValueState::PtUninit
                } else {
                    ValueState::PtInit
                }
            } else {
                ValueState::PtUnknown
            };
            let svalue = SValue::new(tcell, loc, value_state);
            m.insert(svalue);
        }
        Rvalue::Discriminant(place) => {
            let tcell = TCell::from_place(*place);
            let svalue = SValue::new(tcell, loc, ValueState::Init);
            m.insert(svalue);
        }
        _ => {}
    }
    m
}

impl<'tcx> MCell<'tcx> {
    pub fn from_place(place: Place<'tcx>) -> Self {
        // a.b.c.Deref.d.e.f.Deref
        Self {
            local: place.local,
            projection: place.projection.clone().into_iter().collect(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SPtrTy {
    SBox,
    SRef,
    SRefMut,
    SRaw,
    SRawMut,
    SUsize,
    SRc,
    SArc,
    SFnPtr,
    SOther,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValueState {
    Uninit,
    Init,
    Dropped,
    PtUninit,
    PtInit,
    PtDropped,
    PtUnknown,
    FromArg,
}

// #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
// pub enum SValueTy {
//     Bool,
//     Char,
//     Float,
//     Int,
//     Uint,
//     Ptr(SPtrTy),
//     Adt,
//     Foregin,
//     Str,
//     Array,
//     Slice,
//     Tuple,
// }
// #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
// pub enum SValueTy {
//     Bool,
//     Char,
//     Float,
//     Int,
//     Uint,
//     Ptr(SPtrTy),
//     Adt,
//     Foregin,
//     Str,
//     Array,
//     Slice,
//     Tupl,
// }

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SValue<'tcx> {
    pub cell: TCell<'tcx>,
    pub loc: Location,
    pub state: ValueState,
    //    pub owners: Vec<MCell<'tcx>>,
}

impl<'tcx> SValue<'tcx> {
    pub fn new(cell: TCell<'tcx>, loc: Location, state: ValueState) -> Self {
        Self { cell, loc, state }
    }
}

// SPtr points-to MCell*
// Deref SPtr => if points-to not empty, return points-to, else return Deref SPtr

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_uninit_regex() {
        assert!(UNINIT_REGEX.get(&"mem::uninitialized").unwrap().is_match("core::mem::uninitialized::<std::result::Result<std::vec::Vec<i32>, std::vec::Vec<i32>>>"));
        assert!(UNINIT_REGEX
            .get(&"mem::MaybeUninit")
            .unwrap()
            .is_match("core::mem::MaybeUninit::<Obj>::uninit"));
        assert!(UNINIT_REGEX
            .get(&"alloc::alloc::__rust_alloc")
            .unwrap()
            .is_match("alloc::alloc::__rust_alloc"));
        assert!(UNINIT_REGEX
            .get(&"std::alloc::alloc")
            .unwrap()
            .is_match("std::alloc::alloc"));
        assert!(UNINIT_REGEX
            .get(&"::alloc")
            .unwrap()
            .is_match("Process::alloc"));
        assert!(UNINIT_REGEX
            .get(&"Vec::set_len")
            .unwrap()
            .is_match("Vec::<Obj>::set_len")); // arg > 0
    }
}

// impl<'tcx> TotalAnalysis<'tcx> {
//     pub fn new(tcx: TyCtxt<'tcx>) -> Self {
//         Self {
//             tcx,
//             states: HashMap::new(),
//         }
//     }
//     // fn mark_uninitialized(def_path_str: &str, args: Vec<Operand>, destination: Option<(Place<'tcx>, BasicBlock)>) -> Place<'tcx> {

//     // }

//     pub fn analyze(&mut self, instance: Instance<'tcx>) {
//         println!("Analyzing instance: {:?}", instance.def_id());
//         if !self.should_analyze(&instance) {
//             return;
//         }
//         let body = self.tcx.instance_mir(instance.def);
//         let mut worklist = Self::init_worklist(body);
//         self.init_mapping(body);
//         let mut visited = HashSet::new();
//         while let Some(node) = worklist.pop() {
//             // transfer node state -> state
//             {
//                 // let curr_state = self.states.get_mut(&node).unwrap();
//                 //
//             }
//             if node == body.terminator_loc(node.block) {
//                 let term = body[node.block].terminator();
//                 match term.kind {
//                     TerminatorKind::Call{ref func, ref args, destination, ..} => {
//                         let func_ty = func.ty(body, self.tcx);
//                         let func_ty = instance.subst_mir_and_normalize_erasing_regions(
//                             self.tcx,
//                             ty::ParamEnv::reveal_all(),
//                             func_ty,
//                         );
//                         if let TyKind::FnDef(def_id, substs_ref) = func_ty.kind() {
//                             let def_path_str = self.tcx.def_path_str_with_substs(*def_id, substs_ref);

//                         }
//                     }
//                     _ => {

//                     }
//                 }
//                 let succs = term
//                     .successors()
//                     .map(|bb| Location {
//                         block: *bb,
//                         statement_index: 0,
//                     });
//                 for succ in succs {
//                     // if state(succ) union curr_state: push
//                     if visited.insert(succ) {
//                         worklist.push(succ);
//                     }
//                 }
//             } else {
//                 let succ = node.successor_within_block();
//                 // if state(succ) \union curr_state: push
//                 worklist.push(succ);
//             }
//         }
//     }

//     fn transfer_statement(
//         &mut self,
//         curr_state: &mut HashSet<TotalMemObj<'tcx>>,
//         loc: Location,
//         stmt: &Statement<'tcx>,
//     ) {
//         match stmt.kind {
//             StatementKind::Assign(box (place, ref rvalue)) => {
//                 // remove TMO eq to place
//                 // curr_state.retain(|tmo| !tmo.eq_place(place));
//                 // add TMO from place
//                 let new = TotalMemObj::from_place(place, loc);
//                 // rvalue: Use, Ref, AddressOf
//                 curr_state.insert(new);
//             }
//             _ => {}
//         }
//     }

//     fn process_place(curr_state: &mut HashSet<TotalMemObj>, place: Place<'tcx>) {
//         // let mut old = curr_state.iter_mut(|tmo| tmo.eq_place(place));
//         // if old is None: place => new
//         //
//     }

//     fn process_rvalue(curr_state: &mut HashSet<TotalMemObj>, rvalue: Rvalue) {
//         // match rvalue {
//         //     Rvalue::Use(op) | Rvalue::Repeat(op, _) | Rvalue::Cast(_, op, _) => {}
//         //     Rvalue::Ref(_, bk, place) => {
//         //         for tmo in curr_state {
//         //             if tmo.eq_place(place) {
//         //                 // tmo; tmo.ref_by.insert()
//         //             }
//         //         }
//         //         match bk {
//         //             BorrowKind::Shared =>  {}
//         //             _ => {}
//         //         };
//         //     }
//         //     Rvalue::AddressOf(_, place) => {

//         //     }
//         //     Rvalue::Discriminant(place) => {}
//         //     _ => {}
//         // }
//     }

//     fn init_mapping(&mut self, body: &'tcx Body<'tcx>) {
//         self.init_args(body);
//         for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
//             for stmt_idx in 1..=bb_data.statements.len() {
//                 self.states.insert(
//                     Location {
//                         block: bb,
//                         statement_index: stmt_idx,
//                     },
//                     HashSet::new(),
//                 );
//             }
//         }
//     }

//     fn init_args(&mut self, body: &'tcx Body<'tcx>) {
//         let tmobjs: HashSet<_> = body
//             .args_iter()
//             .map(|arg| TotalMemObj::from_place(Place::from(arg), Location::START))
//             .collect();
//         self.states.insert(Location::START, tmobjs);
//     }

//     fn init_worklist(body: &'tcx Body<'tcx>) -> Vec<Location> {
//         let mut worklist = Vec::new();
//         for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
//             for stmt_idx in 0..=bb_data.statements.len() {
//                 worklist.push(Location {
//                     block: bb,
//                     statement_index: stmt_idx,
//                 });
//             }
//         }
//         worklist
//     }

//     fn should_analyze(&self, instance: &Instance<'tcx>) -> bool {
//         if let InstanceDef::Item(_) = instance.def {
//             self.tcx.is_mir_available(instance.def_id())
//         } else {
//             false
//         }
//     }
// }

// #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
// pub struct NonGlobalConstant<'tcx> {
//     pub span: Span,
//     pub literal: &'tcx ty::Const<'tcx>,
// }

// impl<'tcx> NonGlobalConstant<'tcx> {
//     pub fn from_constant(constant: &Constant<'tcx>) -> Self {
//         Self {
//             span: constant.span,
//             literal: constant.literal,
//         }
//     }
// }

// #[derive(Debug, PartialEq, Eq, Hash)]
// pub enum TotalMemObj<'tcx> {
//     Global(DefId),
//     NonGlobalConstant(NonGlobalConstant<'tcx>),
//     Concret(MemObj<'tcx>),
//     Virtual(MemObj<'tcx>),
// }

// impl<'tcx> TotalMemObj<'tcx> {
//     pub fn from_place(place: Place<'tcx>, location: Location) -> Self {
//         let memobj = MemObj::from_place(place, location);
//         if !place.is_indirect() {
//             TotalMemObj::Concret(memobj)
//         } else {
//             TotalMemObj::Virtual(memobj)
//         }
//     }

//     pub fn from_constant(constant: &Constant<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
//         if let Some(def_id) = constant.check_static_ptr(tcx) {
//             Self::Global(def_id)
//         } else {
//             Self::NonGlobalConstant(NonGlobalConstant::from_constant(constant))
//         }
//     }

//     // pub fn eq_place(&self, place: Place<'tcx>) -> bool {
//     //     match *self {
//     //         Self::Concret(memobj) | Self::Virtual(memobj) => memobj.eq_place(place),
//     //         Self::Global(_) | Self::NonGlobalConstant(_) => false,
//     //     }
//     // }
// }

// #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
// pub enum PointsToTy {
//     ImmuRef,
//     MuRef,
//     ImmuRaw,
//     MuRaw,
// }

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub struct MemObj<'tcx> {
//     pub local: Local,
//     pub projection: Vec<PlaceElem<'tcx>>,
//     pub location: Location,
//     pub points_to: Vec<(PointsToTy, Rc<MemObj<'tcx>>)>,
//     pub ref_by: Vec<(PointsToTy, Rc<MemObj<'tcx>>)>,
// }

// impl<'tcx> MemObj<'tcx> {
//     pub fn from_place(place: Place<'tcx>, location: Location) -> Self {
//         Self {
//             local: place.local,
//             projection: place.projection.iter().clone().collect(),
//             location,
//             points_to: Vec::new(),
//             ref_by: Vec::new(),
//         }
//     }

//     pub fn is_indirect(&self) -> bool {
//         self.projection
//             .iter()
//             .any(|elem| matches!(*elem, ProjectionElem::Deref))
//     }

//     pub fn eq_place(&self, place: Place<'tcx>) -> bool {
//         self.local == place.local
//             && self
//                 .projection
//                 .iter()
//                 .zip(place.projection)
//                 .all(|(l, r)| *l == r)
//     }
// }

// #[derive(PartialEq, Eq, Hash, Clone, Copy)]
// pub struct MemPlace {
//     pub local_loc: (Local, Location),
//     // pub projection: Field,
// }

// impl MemPlace {
//     pub fn from_arg(local: Local) -> Self {
//         Self {
//             local_loc: (local, Location::START),
//         }
//     }
//     pub fn from_local_loc(local: Local, location: Location) -> Self {
//         Self {
//             local_loc: (local, location),
//         }
//     }
// }

// impl fmt::Debug for MemPlace {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         write!(f, "{:?}@{:?}", self.local_loc.0, self.local_loc.1)
//     }
// }

// impl MemPlace {
//     pub fn resolve(&self, /*State */) -> Self {
//         // *arg
//     }
// }
// pub struct DropIdentifier<'tcx> {
//     pub tcx: TyCtxt<'tcx>,
// }

// impl<'tcx> DropIdentifier<'tcx> {
//     // MemorySSA
//     pub fn analyze(&mut self, instance: Instance<'tcx>) {
//         if !self.should_analyze(&instance) {
//             return;
//         }
//         let body = self.tcx.instance_mir(instance.def);
//         // dataflow
//         let mut worklist = Vec::new();
//         let mut states = HashMap::new();
//         // every Local has a src
//         for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
//             for ii in 0..=bb_data.statements.len() {
//                 let loc = Location {
//                     block: bb,
//                     statement_index: ii,
//                 };
//                 worklist.push(loc);
//                 states.insert(loc, HashSet::new());
//             }
//         }
//         for arg in body.args_iter() {
//             let args_state = {
//                 let mut args_state = HashSet::new();
//                 args_state.insert(MemPlace::from_arg(arg));
//                 args_state
//             };
//             states.insert(Location::START, args_state);
//         }
//         while let Some(location) = worklist.pop() {
//             if !self.is_terminator(location, body) {
//                 let curr_state = states.get_mut(&location).unwrap();
//                 let next_loc = Location {
//                     block: location.block,
//                     statement_index: location.statement_index + 1,
//                 };
//                 let stmt = &body[location.block].statements[location.statement_index];
//                 // println!("{:?}", stmt);
//                 match stmt.kind {
//                     StatementKind::Assign(box (place, ref rvalue)) => {
//                         let mut rmemplaces = Vec::new();
//                         match rvalue {
//                             Rvalue::Use(op) | Rvalue::Repeat(op, _) | Rvalue::Cast(_, op, _) => {
//                                 if let Some(rplace) = op.place() {
//                                     // replace rplace with states
//                                     if let Some(local) = rplace.as_local() {
//                                         // search states for local
//                                         for memplace in curr_state.iter() {
//                                             if memplace.local_loc.0 == local {
//                                                 rmemplaces.push(*memplace);
//                                             }
//                                         }
//                                     }
//                                 }
//                             }
//                             Rvalue::Ref(_, _, place)
//                             | Rvalue::AddressOf(_, place)
//                             | Rvalue::Discriminant(place) => {
//                                 if let Some(local) = place.as_local() {
//                                     // search states for local
//                                     for memplace in curr_state.iter() {
//                                         if memplace.local_loc.0 == local {
//                                             rmemplaces.push(*memplace);
//                                         }
//                                     }
//                                 }
//                             }
//                             _ => {}
//                         }
//                         if let Some(local) = place.as_local() {
//                             curr_state.retain(|memplace| memplace.local_loc.0 != local);
//                             curr_state.insert(MemPlace::from_local_loc(local, location));
//                             // println!("{:?} = {:?} {:?}", MemPlace::from_local_loc(local, location), "<-", rmemplaces);
//                             let new_curr_state = curr_state.clone();
//                             drop(curr_state);
//                             // curr_state \union to next_state if changed then propagate
//                             let next_state = states.get_mut(&next_loc).unwrap();
//                             let old_len = next_state.len();
//                             next_state.extend(new_curr_state.into_iter());
//                             if next_state.len() != old_len {
//                                 worklist.push(next_loc);
//                             }
//                         }
//                     }
//                     StatementKind::SetDiscriminant { ref place, .. } => {
//                         // place.local@location
//                         if let Some(local) = place.as_local() {
//                             curr_state.insert(MemPlace::from_local_loc(local, location));
//                             let new_curr_state = curr_state.clone();
//                             drop(curr_state);
//                             // curr_state \union to next_state if changed then propagate
//                             let next_state = states.get_mut(&next_loc).unwrap();
//                             let old_len = next_state.len();
//                             next_state.extend(new_curr_state.into_iter());
//                             if next_state.len() != old_len {
//                                 worklist.push(next_loc);
//                             }
//                         }
//                     }
//                     _ => {
//                         let new_curr_state = curr_state.clone();
//                         drop(curr_state);
//                         // curr_state \union to next_state if changed then propagate
//                         let next_state = states.get_mut(&next_loc).unwrap();
//                         let old_len = next_state.len();
//                         next_state.extend(new_curr_state.into_iter());
//                         if next_state.len() != old_len {
//                             worklist.push(next_loc);
//                         }
//                     }
//                 };
//             } else {
//                 let term = &body[location.block].terminator();
//                 // println!("{:?}", term.kind);
//                 let new_state = match term.kind {
//                     TerminatorKind::Call {
//                         ref func,
//                         ref args,
//                         destination: Some((place, _)),
//                         ..
//                     } => {
//                         // place.local@location
//                         let curr_state = states.get_mut(&location).unwrap();
//                         if let Some(local) = place.as_local() {
//                             // get curr state, insert, propagate
//                             curr_state.insert(MemPlace::from_local_loc(local, location));
//                         }
//                         curr_state.clone()
//                     }
//                     TerminatorKind::Drop { place, .. } => {
//                         // place.local@location
//                         let curr_state = states.get_mut(&location).unwrap();
//                         if let Some(local) = place.as_local() {
//                             curr_state.retain(|memplace| memplace.local_loc.0 != local);
//                         }
//                         curr_state.clone()
//                     }
//                     _ => states.get_mut(&location).unwrap().clone(),
//                 };
//                 for succ in term.successors() {
//                     let next_loc = Location {
//                         block: *succ,
//                         statement_index: 0,
//                     };
//                     let next_state = states.get_mut(&next_loc).unwrap();
//                     let old_len = next_state.len();
//                     next_state.extend(new_state.clone().into_iter());
//                     if old_len != next_state.len() {
//                         worklist.push(next_loc);
//                     }
//                 }
//             }
//         }
//         println!("{:?}", instance);
//         for (loc, state) in states.iter() {
//             println!("{:?}@{:?}", loc, state);
//         }
//     }

//     fn process_place(&self, place: Place<'tcx>) {
//         // place is direct, then place => memplace
//         // place is indirect, then find points-to => memplace
//     }

//     fn is_terminator(&self, location: Location, body: &'tcx Body<'tcx>) -> bool {
//         location.statement_index == body[location.block].statements.len()
//     }

//     pub fn analyze2(&mut self, instance: Instance<'tcx>) {
//         if self.should_analyze(&instance) {
//             println!("{:?}", instance.def);
//             let body = self.tcx.instance_mir(instance.def);
//             // for (local, local_decl) in body.local_decls.iter_enumerated() {
//             //     println!("{:?}: {:?}", local, local_decl);
//             // }
//             for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
//                 for stmt in &bb_data.statements {
//                     let kind = &stmt.kind;
//                     if false {
//                         match *kind {
//                             StatementKind::SetDiscriminant {
//                                 ref place,
//                                 variant_index,
//                             } => {
//                                 println!("{:?}", stmt);
//                                 println!("{:?}", place);
//                                 println!("{:?}", variant_index);
//                             }
//                             StatementKind::Assign(box (place, ref rvalue)) => {
//                                 // if let Rvalue::Discriminant(place) = rvalue {
//                                 //     println!("{:?} = DSCM({:?})", place, place);
//                                 // }
//                                 println!("{:?}", place);
//                                 println!("{:?}, {:?}", place.local, place.projection);

//                                 // // place_ty is raw ptr
//                                 // // rvalue is ref
//                                 // let place_ty = place.ty(body, self.tcx).ty;
//                                 // if place_ty.is_unsafe_ptr() {
//                                 //     match *rvalue {
//                                 //         Rvalue::AddressOf(mu, pl) => {
//                                 //             println!("{:?}", kind);
//                                 //             println!("{:?}", pl.ty(body, self.tcx).ty);
//                                 //         }
//                                 //         Rvalue::Cast(ck, ref op, ty) => {
//                                 //             println!("{:?}", kind);
//                                 //             match op {
//                                 //                 Operand::Move(pl) | Operand::Copy(pl) => {
//                                 //                     println!("{:?}", pl.ty(body, self.tcx).ty);
//                                 //                 }
//                                 //                 Operand::Constant(_) => {

//                                 //                 }
//                                 //             }
//                                 //         }
//                                 //         _ => {}
//                                 //     }
//                                 // }
//                             }
//                             _ => {}
//                         }
//                     }
//                 }
//                 println!("{:?}", bb_data.terminator().kind);
//                 match bb_data.terminator().kind {
//                     TerminatorKind::Call {
//                         ref func,
//                         ref args,
//                         ref destination,
//                         ..
//                     } => match func {
//                         Operand::Move(place) => {
//                             println!("move {:?}", place);
//                             let func_ty = func.ty(body, self.tcx);
//                             let func_ty = instance.subst_mir_and_normalize_erasing_regions(
//                                 self.tcx,
//                                 ty::ParamEnv::reveal_all(),
//                                 func_ty,
//                             );
//                             match func_ty.kind() {
//                                 ty::FnDef(def_id, substs) => {
//                                     if let Some(callee) = Instance::resolve(
//                                         self.tcx,
//                                         ty::ParamEnv::reveal_all(),
//                                         *def_id,
//                                         substs,
//                                     )
//                                     .ok()
//                                     .flatten()
//                                     {
//                                         println!("constant {:?}", callee);
//                                     } else {
//                                         println!("cannot resolve: {:?}", func_ty);
//                                     }
//                                 }
//                                 ty::FnPtr(fn_sig) => {
//                                     println!("fn_sig: {:?}", fn_sig);
//                                 }
//                                 _ => {
//                                     println!("do not support: {:?}", func_ty);
//                                 }
//                             }
//                         }
//                         Operand::Copy(place) => {
//                             println!("copy {:?}", place);
//                         }
//                         Operand::Constant(ref constant) => {
//                             let func_ty = func.ty(body, self.tcx);
//                             let func_ty = instance.subst_mir_and_normalize_erasing_regions(
//                                 self.tcx,
//                                 ty::ParamEnv::reveal_all(),
//                                 func_ty,
//                             );
//                             match func_ty.kind() {
//                                 ty::FnDef(def_id, substs) => {
//                                     if let Some(callee) = Instance::resolve(
//                                         self.tcx,
//                                         ty::ParamEnv::reveal_all(),
//                                         *def_id,
//                                         substs,
//                                     )
//                                     .ok()
//                                     .flatten()
//                                     {
//                                         println!(
//                                             "constant {:?} {:?}",
//                                             callee, constant.literal.val
//                                         );
//                                     } else {
//                                         println!("cannot resolve: {:?}", func_ty);
//                                     }
//                                 }
//                                 ty::FnPtr(fn_sig) => {
//                                     println!("fn_sig: {:?}", fn_sig);
//                                 }
//                                 _ => {
//                                     println!("do not support: {:?}", func_ty);
//                                 }
//                             }
//                         }
//                     },
//                     TerminatorKind::Drop { place, .. } => {
//                         let place_ty = place.ty(body, self.tcx).ty;
//                         let place_ty = instance.subst_mir_and_normalize_erasing_regions(
//                             self.tcx,
//                             ty::ParamEnv::reveal_all(),
//                             place_ty,
//                         );
//                         let drop_in_place = Instance::resolve_drop_in_place(self.tcx, place_ty);

//                         println!("DropGlue: {:?}", drop_in_place);
//                         place_ty.ty_adt_def().and_then(|adt_def| {
//                             adt_def.destructor(self.tcx).and_then(|dtor| {
//                                 println!("Actual: {:?}", dtor);
//                                 println!("Trait Of Item: {:?}", self.tcx.trait_of_item(dtor.did));
//                                 Some(())
//                             })
//                         });
//                     }
//                     _ => {}
//                 }
//                 // let kind = &bb_data.terminator().kind;
//                 // match kind {
//                 //     // &TerminatorKind::Drop { place, .. } => {
//                 //     //     if place.is_indirect() {
//                 //     //         println!("{:?}", bb_data);
//                 //     //         println!("{:?}", kind);
//                 //     //     }
//                 //     // }
//                 //     &TerminatorKind::DropAndReplace { .. } => {
//                 //         println!("{:?}", kind);
//                 //     }
//                 //     _ => {}
//                 // }
//             }
//         }
//     }

//     fn should_analyze(&self, instance: &Instance<'tcx>) -> bool {
//         if let InstanceDef::Item(_) = instance.def {
//             self.tcx.is_mir_available(instance.def_id())
//         } else {
//             false
//         }
//     }
// }
