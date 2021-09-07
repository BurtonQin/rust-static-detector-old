use rustc_middle::{
    mir::{
        BasicBlock, Body, Constant, Field, Local, Location, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, Terminator, TerminatorKind, RETURN_PLACE,
    },
    ty::{self, Instance, InstanceDef, ParamEnv, TyCtxt, TyKind},
};
use rustc_span::Span;
use std::collections::{HashMap, HashSet, VecDeque};

use crate::callgraph::Callgraph;
use crate::util::{Instruction, Monomorphizer};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Var<'tcx> {
    Local(LocalField),
    Global(MemCellConstant<'tcx>),
}

impl<'tcx> Var<'tcx> {
    pub fn from_local(local: Local) -> Self {
        Var::Local(LocalField { local, field: None })
    }

    pub fn from_local_field(local: Local, field: Field) -> Self {
        Var::Local(LocalField {
            local,
            field: Some(field),
        })
    }

    pub fn from_constant(memcell_constant: MemCellConstant<'tcx>) -> Self {
        Var::Global(memcell_constant)
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct LocalField {
    pub local: Local,
    pub field: Option<Field>,
}

impl LocalField {
    pub fn from_local(local: Local) -> Self {
        LocalField { local, field: None }
    }

    pub fn from_local_field(local: Local, field: Field) -> Self {
        LocalField {
            local,
            field: Some(field),
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct InstLocation<'tcx> {
    pub instance: Instance<'tcx>,
    pub location: Location,
}

/// Constant without user_ty for Eq trait
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct MemCellConstant<'tcx> {
    pub span: Span,
    pub literal: &'tcx ty::Const<'tcx>,
}

impl<'tcx> MemCellConstant<'tcx> {
    pub fn from_constant(constant: &Constant<'tcx>) -> Self {
        Self {
            span: constant.span,
            literal: constant.literal,
        }
    }
}
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum MemCell<'tcx> {
    Alloc((Instance<'tcx>, LocalField, Location)),
    Constant(MemCellConstant<'tcx>),
    Var((Instance<'tcx>, Var<'tcx>)),
}

impl<'tcx> MemCell<'tcx> {
    pub fn from_alloc(
        instance: Instance<'tcx>,
        local_field: LocalField,
        location: Location,
    ) -> Self {
        Self::Alloc((instance, local_field, location))
    }

    pub fn from_const(constant: &Constant<'tcx>) -> Self {
        Self::Constant(MemCellConstant::from_constant(constant))
    }

    pub fn from_var(instance: Instance<'tcx>, var: Var<'tcx>) -> Self {
        Self::Var((instance, var))
    }
}

type State<'tcx> = HashMap<Var<'tcx>, HashSet<MemCell<'tcx>>>;
pub struct PointerAnalysis<'tcx> {
    tcx: TyCtxt<'tcx>,
    pub states: HashMap<InstLocation<'tcx>, State<'tcx>>,
    worklist: VecDeque<InstLocation<'tcx>>,
    // calling context
    visited:
        HashMap<(Instance<'tcx>, InstLocation<'tcx>), (Vec<HashSet<MemCell<'tcx>>>, State<'tcx>)>,
    callgraph: Callgraph<'tcx>,
}

impl<'tcx> PointerAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, callgraph: Callgraph<'tcx>) -> Self {
        Self {
            tcx,
            states: HashMap::new(),
            worklist: VecDeque::new(),
            visited: HashMap::new(),
            callgraph,
        }
    }

    pub fn analyze(&mut self, entry: Instance<'tcx>) {
        println!("{:?}", entry);
        self.analyze_instance_recur(entry, &[]);
    }

    fn analyze_instance_recur(
        &mut self,
        instance: Instance<'tcx>,
        args_states: &[HashSet<MemCell<'tcx>>],
    ) -> HashSet<MemCell<'tcx>> {
        if !self.should_analyze(&instance) {
            return HashSet::new();
        }
        let body = self.tcx.instance_mir(instance.def);
        // init empty
        self.init_empty(instance, body);

        // init args with args states
        self.init_with_args_states(instance, body, args_states);

        // return-like instructions have no successors
        // details: return, resume, abort, unreachable
        // return: propagate normal state
        // resume/abort/unreachable: stop
        let mut return_like_instlocs = Vec::new();
        // BFS InstLocations
        while let Some(instloc) = self.worklist.pop_front() {
            if let Some(instruction) = Instruction::new(body, instloc.location) {
                if instruction.is_terminator() {
                    let state = self.states.get(&instloc).unwrap().clone();
                    let after = self.transfer_terminator(state, body, instance, instruction);
                    if instruction.successors().is_empty() {
                        return_like_instlocs.push(instloc);
                        continue;
                    }
                    for next in instruction.successors() {
                        if body[next.location.block].is_cleanup {
                            continue;
                        }
                        let next_instloc = InstLocation {
                            instance,
                            location: next.location,
                        };

                        let next_state = self.states.get_mut(&next_instloc).unwrap();
                        let changed = Self::union_states(next_state, after.clone());
                        if changed {
                            self.worklist.push_back(next_instloc);
                        }
                    }
                } else {
                    let state = self.states.get(&instloc).unwrap();
                    let after = Self::transfer_statement(state, instance, instruction);
                    if instruction.successors().is_empty() {
                        return_like_instlocs.push(instloc);
                        continue;
                    }
                    for next in instruction.successors() {
                        let next_instloc = InstLocation {
                            instance,
                            location: next.location,
                        };
                        let next_state = self.states.get_mut(&next_instloc).unwrap();
                        let changed = Self::union_states(next_state, after.clone());
                        if changed {
                            self.worklist.push_back(next_instloc);
                        }
                    }
                }
            }
        }

        let return_local_field = Var::from_local(RETURN_PLACE);
        println!("{:?}", instance);
        let mut return_states = HashSet::new();
        for return_like_instloc in return_like_instlocs {
            let instruction = Instruction::new_unchecked(body, return_like_instloc.location);
            let term = instruction.get_terminator();
            match term.kind {
                TerminatorKind::Return => {
                    let state = self.states.get(&return_like_instloc).unwrap();
                    println!("{:?}", return_like_instloc.location);
                    for local_field in state {
                        println!("{:?}", local_field);
                    }
                    if let Some(return_state) = state.get(&return_local_field) {
                        return_states.extend(return_state.clone().into_iter());
                    }
                }
                _ => {}
            }
        }
        return_states
    }

    fn resolve_call(
        func: &Operand<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Vec<Instance<'tcx>> {
        let func_ty = func.ty(body, tcx);
        let mono = Monomorphizer::new(instance, tcx);
        let func_ty = mono.monomorphize(func_ty);
        let param_env = ParamEnv::reveal_all();
        let mut instances = Vec::new();
        match *func_ty.kind() {
            ty::FnDef(def_id, substs) => {
                if let Some(instance) = Instance::resolve(tcx, param_env, def_id, substs)
                    .ok()
                    .flatten()
                {
                    instances.push(instance);
                } else {
                    dbg!("Unexpected unresolvable FnDef {:?}", func_ty);
                }
            }
            ty::Closure(def_id, substs) => {
                dbg!("Call FnPtr Unsupported: {:?}", func_ty);
                if let Some(instance) = Instance::resolve(tcx, param_env, def_id, substs)
                    .ok()
                    .flatten()
                {
                    instances.push(instance);
                } else {
                    dbg!("Unexpected unresolvable Closure {:?}", func_ty);
                }
            }
            ty::FnPtr(fn_sig) => {
                dbg!("Call FnPtr Unsupported: {:?}", func_ty);
            }
            _ => {
                dbg!("Call Others Unsupported: {:?}", func_ty);
            }
        }
        instances
    }

    /// Parse place without field
    fn parse_place(
        place: Place<'tcx>,
        state: &State<'tcx>,
        instance: Instance<'tcx>,
    ) -> HashSet<MemCell<'tcx>> {
        let mut memcells = HashSet::new();
        memcells.insert(MemCell::Var((instance, Var::from_local(place.local))));
        let mut field_accessed = false;
        for proj_elem in place.projection {
            match proj_elem {
                ProjectionElem::Deref => {
                    let mut new: HashSet<MemCell<'tcx>> = HashSet::new();
                    for memcell in memcells {
                        match memcell {
                            MemCell::Constant(constant) => {
                                let var = Var::from_constant(constant);
                                if let Some(deref_memcells) = state.get(&var) {
                                    new.extend(deref_memcells.clone().into_iter());
                                }
                            }
                            MemCell::Var((_, var)) => {
                                if let Some(deref_memcells) = state.get(&var) {
                                    new.extend(deref_memcells.clone().into_iter());
                                }
                            }
                            MemCell::Alloc(_) => {}
                        }
                    }
                    memcells = new;
                }
                ProjectionElem::Field(field, _) => {
                    if !field_accessed {
                        // let mut new: HashSet<MemCell<'tcx>> = HashSet::new();
                        // for memcell in memcells {
                        //     // if let MemCell::LocalField((_, local_field)) = memcell {
                        //     //     if let Some(
                        //     // }
                        // }
                        field_accessed = true;
                    }
                    // if (Local, Field) exists
                    // if local exists but field not exists
                    // else add local to it
                }
                _ => {}
            }
        }
        memcells
    }

    fn memcells_contents(
        memcells: HashSet<MemCell<'tcx>>,
        state: &HashMap<Var, HashSet<MemCell<'tcx>>>,
    ) -> HashSet<MemCell<'tcx>> {
        let mut result = HashSet::new();
        for memcell in memcells {
            match memcell {
                MemCell::Alloc(_) => {}
                MemCell::Constant(constant) => {
                    let var = Var::from_constant(constant);
                    if let Some(content) = state.get(&var) {
                        result.extend(content.clone().into_iter());
                    }
                }
                MemCell::Var((_, var)) => {
                    if let Some(content) = state.get(&var) {
                        result.extend(content.clone().into_iter());
                    }
                }
            };
        }
        result
    }

    /// contents of memcells
    fn parse_operand(
        operand: &Operand<'tcx>,
        state: &State<'tcx>,
        instance: Instance<'tcx>,
    ) -> HashSet<MemCell<'tcx>> {
        match operand {
            Operand::Move(place) => {
                let memcells = Self::parse_place(*place, state, instance);
                Self::memcells_contents(memcells, state)
            }
            Operand::Copy(place) => {
                let memcells = Self::parse_place(*place, state, instance);
                Self::memcells_contents(memcells, state)
            }
            Operand::Constant(ref constant) => {
                let mut memcells = HashSet::new();
                memcells.insert(MemCell::from_const(constant));
                memcells
            }
        }
    }

    fn field_num_of_local(body: &Body<'tcx>, local: Local) -> usize {
        match body.local_decls[local].ty.kind() {
            TyKind::Adt(adt_def, _) => adt_def.all_fields().count(),
            _ => 0,
        }
    }

    fn should_analyze(&self, instance: &Instance<'tcx>) -> bool {
        if let InstanceDef::Item(_) = instance.def {
            self.callgraph.instance_index(*instance).is_some()
                && self.tcx.is_mir_available(instance.def_id())
        } else {
            false
        }
    }

    /// init empty states and worklist
    /// body must correspond to instance
    fn init_empty(&mut self, instance: Instance<'tcx>, body: &Body<'tcx>) {
        for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
            for (stmt_idx, _) in bb_data.statements.iter().enumerate() {
                let location = Location {
                    block: bb,
                    statement_index: stmt_idx,
                };
                let inst_location = InstLocation { instance, location };
                self.states.insert(inst_location, HashMap::new());
                self.worklist.push_back(inst_location)
            }
            if bb_data.terminator.is_some() {
                let location = Location {
                    block: bb,
                    statement_index: bb_data.statements.len(),
                };
                let inst_location = InstLocation { instance, location };
                self.states.insert(inst_location, HashMap::new());
                self.worklist.push_back(inst_location);
            }
        }
    }

    /// init args with args states or else with alloc
    /// body must correspond to instance
    fn init_with_args_states(
        &mut self,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
        args_states: &[HashSet<MemCell<'tcx>>],
    ) {
        let mut init_args_states = HashMap::new();
        if args_states.is_empty() {
            // alloc args without args_states
            for arg in body.args_iter() {
                // dbg!("{:?}: {:?}", arg, body.local_decls[arg].ty);
                let memcells = {
                    let mut memcells = HashSet::new();
                    let alloc =
                        MemCell::from_alloc(instance, LocalField::from_local(arg), Location::START);
                    memcells.insert(alloc);
                    for field in 0..Self::field_num_of_local(body, arg) {
                        let alloc = MemCell::from_alloc(
                            instance,
                            LocalField::from_local_field(arg, Field::from_usize(field)),
                            Location::START,
                        );
                        memcells.insert(alloc);
                    }
                    memcells
                };
                let var = Var::from_local(arg);
                init_args_states.insert(var, memcells);
            }
        } else {
            // args_states must correspond to args
            // assert!(args_states.len() == body.arg_count);
            for (arg, arg_state) in body.args_iter().zip(args_states) {
                // dbg!(arg, body.local_decls[arg].ty);
                let var = Var::from_local(arg);
                init_args_states.insert(var, arg_state.clone());
            }
        }
        self.states.insert(
            InstLocation {
                instance,
                location: Location::START,
            },
            init_args_states,
        );
    }

    /// Merge rhs map into lhs map, return true if lhs is changed
    fn union_states(lhs: &mut State<'tcx>, rhs: State<'tcx>) -> bool {
        let mut changed = false;
        for (local_field, memcells) in rhs.into_iter() {
            if let Some(lhs_memcells) = lhs.get_mut(&local_field) {
                let old_len = lhs_memcells.len();
                lhs_memcells.extend(memcells.into_iter());
                if old_len != lhs_memcells.len() {
                    changed = true;
                }
            } else {
                lhs.insert(local_field, memcells);
                changed = true;
            }
        }
        changed
    }

    fn parse_rvalue(
        rvalue: &Rvalue<'tcx>,
        state: &State<'tcx>,
        instance: Instance<'tcx>,
    ) -> HashSet<MemCell<'tcx>> {
        match rvalue {
            Rvalue::Use(operand) | Rvalue::Repeat(operand, _) | Rvalue::Cast(_, operand, _) => {
                Self::parse_operand(operand, state, instance)
            }
            Rvalue::AddressOf(_, place) | Rvalue::Ref(_, _, place) => {
                Self::parse_place(*place, state, instance)
            }
            _ => HashSet::new(),
        }
    }

    fn transfer_terminator(
        &mut self,
        mut state: State<'tcx>,
        body: &Body<'tcx>,
        instance: Instance<'tcx>,
        instruction: Instruction<'tcx>,
    ) -> State<'tcx> {
        match instruction.get_terminator().kind {
            TerminatorKind::Call {
                ref func,
                ref args,
                destination,
                ..
            } => {
                // resolve instance from func
                let callee_instances = Self::resolve_call(func, instance, body, self.tcx);
                let before_state = state.clone();
                // extract args states
                let args_state: Vec<HashSet<_>> = args
                    .iter()
                    .map(|arg| Self::parse_operand(arg, &before_state, instance))
                    .collect();
                println!("{:?}", callee_instances);
                println!("{:#?}", args_state);
                for callee_instance in callee_instances.clone() {
                    let instloc = InstLocation {
                        instance,
                        location: instruction.location,
                    };
                    if let Some((before, after)) = self.visited.get(&(callee_instance, instloc)) {
                        if *before == args_state {
                            Self::union_states(&mut state, after.clone());
                            continue;
                        }
                    }
                    self.visited.insert(
                        (callee_instance, instloc),
                        (args_state.clone(), before_state.clone()),
                    );
                    // get args_states
                    let args_states: Vec<HashSet<_>> = args
                        .iter()
                        .map(|arg| Self::parse_operand(arg, &state, instance))
                        .collect();
                    // apply args_states to callee
                    let return_states = self.analyze_instance_recur(callee_instance, &args_states);
                    // apply return_states to destination
                    if let Some((dst, _)) = destination {
                        let dst_pts = Self::parse_place(dst, &state, instance);
                        // pts[dst_pts] <- return_states
                        for dst_pt in dst_pts {
                            match dst_pt {
                                MemCell::Var((_, var)) => {
                                    state
                                        .entry(var)
                                        .or_default()
                                        .extend(return_states.clone().into_iter());
                                }
                                _ => {}
                            };
                        }
                    }
                    self.visited.insert(
                        (callee_instance, instloc),
                        (args_state.clone(), state.clone()),
                    );
                }
            }
            _ => {}
        }
        state
    }

    fn transfer_statement(
        state: &State<'tcx>,
        instance: Instance<'tcx>,
        instruction: Instruction<'tcx>,
    ) -> State<'tcx> {
        let mut after = state.clone();
        let stmt = instruction.get_statement();
        match stmt.kind {
            StatementKind::Assign(box (place, ref rvalue)) => {
                let left_memcells = Self::parse_place(place, state, instance);
                let right_contents = Self::parse_rvalue(rvalue, state, instance);
                // println!("LEFT: {:?}", left_memcells);
                // println!("RIGHT: {:?}", right_contents);
                // println!("RVALUE: {:?}", rvalue);
                // println!("STATE: {:?}", state);
                for left_memcell in left_memcells {
                    match left_memcell {
                        MemCell::Var((_, var)) => {
                            if right_contents.is_empty() {
                                // if let Var::Local(local_field) = var {
                                //     after.entry(var).or_default().insert(MemCell::from_alloc(
                                //         instance,
                                //         local_field,
                                //         instruction.location,
                                //     ));
                                // }
                            } else {
                                after
                                    .entry(var)
                                    .or_default()
                                    .extend(right_contents.clone().into_iter());
                            }
                        }
                        MemCell::Constant(constant) => {
                            let var = Var::from_constant(constant);
                            after
                                .entry(var)
                                .or_default()
                                .extend(right_contents.clone().into_iter());
                        }
                        MemCell::Alloc(_) => {}
                    }
                }
            }
            _ => {}
        }
        after
    }

    fn apply_before_call(&mut self) {}

    fn apply_after_call(&mut self) {}

    fn apply_assignment(&mut self) {}
}

/// Field Insensitive
pub struct FIAndersen<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) pts: HashMap<Local, HashSet<Local>>,
}

impl<'tcx> FIAndersen<'tcx> {
    fn parse_place(
        &self,
        state: &HashMap<Local, HashSet<Local>>,
        place: &Place<'tcx>,
    ) -> HashSet<Local> {
        let mut locals = HashSet::new();
        locals.insert(place.local);
        for proj_elem in place.projection {
            match proj_elem {
                ProjectionElem::Deref => {
                    let mut new_locals: HashSet<Local> = HashSet::new();
                    for local in locals {
                        if let Some(ls) = state.get(&local) {
                            new_locals.extend(ls.iter());
                        }
                    }
                    locals = new_locals
                }
                _ => {}
            }
        }
        locals
    }

    fn parse_assignment(
        &self,
        state: &mut HashMap<Local, HashSet<Local>>,
        place: Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> bool {
        let llocals = self.parse_place(state, &place);
        match rvalue {
            Rvalue::Use(operand) | Rvalue::Repeat(operand, _) | Rvalue::Cast(_, operand, _) => {
                // p = (move )?O | p = [O; C] | p = O as T
                match operand {
                    Operand::Move(rplace) | Operand::Copy(rplace) => {
                        let rlocals = self.parse_place(state, rplace);
                        // let mut pts_rlocals = HashSet::new();
                        // for rlocal in rlocals {
                        //     if let Some(pts_rlocal) = self.pts.get(rlocal) {
                        //         pts_rlocals.extend(pts_rocal.iter());
                        //     }
                        // }
                        let pts_rlocals: HashSet<Local> =
                            rlocals.into_iter().fold(HashSet::new(), |mut acc, rlocal| {
                                if let Some(pts_rlocal) = state.get(&rlocal) {
                                    acc.extend(pts_rlocal.iter());
                                }
                                acc
                            });
                        // pts[llocal] <- pts[rlocal]
                        let old_state = state.clone();
                        for llocal in llocals {
                            state.entry(llocal).or_default().extend(pts_rlocals.iter());
                        }
                        return old_state != *state;
                    }
                    Operand::Constant(box constant) => {
                        // println!("{:?}", constant);
                        return false;
                    }
                }
            }
            Rvalue::Ref(_, _, rplace) | Rvalue::AddressOf(_, rplace) => {
                // p = &P | p = &raw const P
                // pts[llocal] <- {rlocal}
                let rlocals = self.parse_place(state, rplace);
                let old_state = state.clone();
                for llocal in llocals {
                    state.entry(llocal).or_default().extend(rlocals.iter());
                }
                return old_state != *state;
            }
            _ => {
                return false;
            }
        }
    }

    fn parse_terminator(
        &self,
        state: &mut HashMap<Local, HashSet<Local>>,
        terminator: &Terminator<'tcx>,
    ) {
        match terminator.kind {
            TerminatorKind::Call {
                ref func,
                ref args,
                destination,
                ..
            } => {
                let mut rlocals = HashSet::new();
                for arg in args {
                    match arg {
                        Operand::Move(rplace) | Operand::Copy(rplace) => {
                            rlocals.extend(self.parse_place(state, rplace));
                        }
                        Operand::Constant(box constant) => {
                            // println!("{:?}", constant);
                        }
                    }
                }
                if let Some((place, _)) = destination {
                    let llocals = self.parse_place(state, &place);
                    if rlocals.is_empty() {
                        for llocal in llocals {
                            state.entry(llocal).or_default().insert(llocal);
                        }
                    } else {
                        let pts_rlocals: HashSet<Local> =
                            rlocals.into_iter().fold(HashSet::new(), |mut acc, rlocal| {
                                if let Some(pts_rlocal) = state.get(&rlocal) {
                                    acc.extend(pts_rlocal.iter());
                                }
                                acc
                            });
                        for llocal in llocals {
                            state.entry(llocal).or_default().extend(pts_rlocals.iter());
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn transfer<'a>(
        &self,
        state: &mut HashMap<Local, HashSet<Local>>,
        instruction: Instruction<'tcx>,
    ) -> bool {
        if instruction.is_terminator() {
            let term = instruction.get_terminator();
            self.parse_terminator(state, term);
            return false;
        } else {
            let stmt = instruction.get_statement();
            if let StatementKind::Assign(box (place, ref rvalue)) = stmt.kind {
                return self.parse_assignment(state, place, rvalue);
            }
            return false;
        }
    }

    pub fn visit_instance(&mut self, instance: Instance<'tcx>) {
        if !self.tcx.is_mir_available(instance.def_id()) {
            return;
        }
        let body = self.tcx.instance_mir(instance.def);
        // alloc parameter and return
        // println!("{:?}", body.source.instance);
        let mut states = HashMap::<Location, HashMap<Local, HashSet<Local>>>::new();
        let mut worklist = VecDeque::new();
        for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
            for (stmt_idx, _) in bb_data.statements.iter().enumerate() {
                let location = Location {
                    block: bb,
                    statement_index: stmt_idx,
                };
                states.insert(location, HashMap::new());
                worklist.push_back(location)
            }
            if bb_data.terminator.is_some() {
                let location = Location {
                    block: bb,
                    statement_index: bb_data.statements.len(),
                };
                states.insert(location, HashMap::new());
                worklist.push_back(location);
            }
        }
        // println!(
        //     "{:?}: {:?}",
        //     RETURN_PLACE, body.local_decls[RETURN_PLACE].ty
        // );
        let mut init_state = HashMap::new();
        let return_set = {
            let mut return_set = HashSet::new();
            return_set.insert(RETURN_PLACE);
            return_set
        };
        init_state.insert(RETURN_PLACE, return_set);

        for arg in body.args_iter() {
            // println!("{:?}: {:?}", arg, body.local_decls[arg].ty);
            let arg_set = {
                let mut arg_set = HashSet::new();
                arg_set.insert(arg);
                arg_set
            };
            init_state.insert(arg, arg_set);
        }
        states.insert(Location::START, init_state);
        while let Some(location) = worklist.pop_front() {
            // println!("{:?}", location);
            if let Some(instruction) = Instruction::new(body, location) {
                let state = states.get_mut(&location).unwrap();
                let changed = self.transfer(state, instruction);
                // if !changed {
                //     continue;
                // }
                // if changed
                for next in instruction.successors() {
                    let mut changed = false;
                    let state = states.get(&location).unwrap().clone();
                    let next_state = states.get_mut(&next.location).unwrap();
                    // new = union(old, state)
                    // if not in, insert, if in, extend
                    for (local, local_set) in state.into_iter() {
                        if let Some(next_local_set) = next_state.get_mut(&local) {
                            let old = next_local_set.clone();
                            next_local_set.extend(local_set.iter());
                            if old != *next_local_set {
                                changed = true;
                            }
                        } else {
                            next_state.insert(local, local_set);
                            changed = true;
                        }
                    }
                    if changed {
                        worklist.push_back(next.location);
                    }

                    // let new = states[next.location].union(after);
                    // if new != states[next.location] {
                    //     states[next.location] = new;
                    //     worklist.push_back(next);
                    // }
                }
            }
        }
        // let mut v: Vec<_> = states.into_iter().collect();
        // v.sort_by(|x, y| x.0.cmp(&y.0));
        // println!("{:#?}", v);
    }
    //    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
    //        if let StatementKind::Assign(box (place, rvalue)) = &statement.kind {
    //           self.parse_assignment(*place, rvalue);
    //           println!("{:?}", statement);
    //           println!("{:#?}", self.pts);
    //        }
    //    }
    // visit call

    // /// Resolve direct call.
    // /// Inspired by rustc_mir/src/transform/inline.rs#get_valid_function_call.
    // fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
    //     if let TerminatorKind::Call { ref func, .. } = terminator.kind {
    //         println!("{:?}, {:?}", self.body.source.def_id(), terminator);
    //         let func_ty = func.ty(self.body, self.tcx);
    //         // Only after monomorphizing can Instance::resolve work
    //         let func_ty = self.monimorphizer.monomorphize(func_ty);
    //         if let ty::FnDef(def_id, substs) = *func_ty.kind() {
    //             if let Some(callee_instance) =
    //                 Instance::resolve(self.tcx, self.param_env, def_id, substs)
    //                     .ok()
    //                     .flatten()
    //             {
    //                 self.callee_sites.push((callee_instance, location));
    //             } else {
    //                 dbg!("Cannot resolve: {:?}, {:?}", def_id, substs);
    //             }
    //         } else {
    //             println!("Unknown call: {:?}, {:?}", *func_ty.kind(), self.body.source_info(location));
    //         }
    //     } else if let TerminatorKind::Drop { place, target, unwind} = terminator.kind {
    //         println!("{:?}, {:?}", self.body.source.def_id(), terminator);
    //         let place_ty = place.ty(self.body, self.tcx);
    //         println!("{:?}", place_ty);
    //     }
    // }
}
