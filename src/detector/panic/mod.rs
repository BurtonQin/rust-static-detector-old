// UnwrapAPI: Result::unwrap()/Result::expect(_)/Option::unwrap()/Option::expect(_)
// 0. Filter UnwrapAPI
// 1. Find the callsites of UnwrapAPI
// 2. Get args[0] (&Result/&Option) of UnwrapAPI
// 3. Track to Result/Option returned by functions
// 4. Check the inner of the functions
use once_cell::sync::Lazy;
use regex::Regex;

use rustc_middle::mir::{RETURN_PLACE, StatementKind, visit::Visitor};
use rustc_middle::mir::{Body, Location, Place, Statement, Terminator, TerminatorKind};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_middle::ty::{Instance, InstanceDef};
use std::collections::{HashMap, HashSet};

use crate::control_dependence_analysis::ControlDependenceGraph;
use crate::pointer_analysis::IntraProceduralPointerAnalysis;
use crate::util::DefUseAnalysis;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnwrapAPI {
    ResultUnwrap,
    ResultExpect,
    OptionUnwrap,
    OptionExpect,
}

static UNWRAP_API_REGEX: Lazy<HashMap<UnwrapAPI, Regex>> = Lazy::new(|| {
    let mut m = HashMap::new();
    m.insert(
        UnwrapAPI::ResultUnwrap,
        Regex::new(r"Result::<.+>::unwrap").unwrap(),
    );
    m.insert(
        UnwrapAPI::ResultExpect,
        Regex::new(r"Result::<.+>::expect").unwrap(),
    );
    m.insert(
        UnwrapAPI::OptionUnwrap,
        Regex::new(r"Option::<.+>::unwrap").unwrap(),
    );
    m.insert(
        UnwrapAPI::OptionExpect,
        Regex::new(r"Option::<.+>::expect").unwrap(),
    );
    m
});

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_unwrap_api_regex() {
        assert!(UNWRAP_API_REGEX[&UnwrapAPI::ResultUnwrap].is_match("Result::<i32, String>::unwrap"));
        assert!(UNWRAP_API_REGEX[&UnwrapAPI::ResultExpect].is_match("Result::<i32, String>::expect"));
        assert!(UNWRAP_API_REGEX[&UnwrapAPI::OptionUnwrap].is_match("Option::<i32>::unwrap"));
        assert!(UNWRAP_API_REGEX[&UnwrapAPI::OptionExpect].is_match("Option::<i32>::expect"));
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnwrapInstance<'tcx> {
    ResultUnwrap(Instance<'tcx>),
    ResultExpect(Instance<'tcx>),
    OptionUnwrap(Instance<'tcx>),
    OptionExpect(Instance<'tcx>),
}

impl<'tcx> UnwrapInstance<'tcx> {
    pub fn new(instance: Instance<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Self> {
        let def_path_str = tcx.def_path_str_with_substs(instance.def_id(), instance.substs);
        if UNWRAP_API_REGEX[&UnwrapAPI::ResultUnwrap].is_match(&def_path_str) {
            Some(UnwrapInstance::ResultUnwrap(instance))
        } else if UNWRAP_API_REGEX[&UnwrapAPI::ResultExpect].is_match(&def_path_str) {
            Some(UnwrapInstance::ResultExpect(instance))
        } else if UNWRAP_API_REGEX[&UnwrapAPI::OptionUnwrap].is_match(&def_path_str) {
            Some(UnwrapInstance::OptionUnwrap(instance))
        } else if UNWRAP_API_REGEX[&UnwrapAPI::OptionExpect].is_match(&def_path_str) {
            Some(UnwrapInstance::OptionExpect(instance))
        } else {
            None
        }
    }
}

pub struct UnwrapDetector<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub unwrap_apis: HashSet<UnwrapInstance<'tcx>>,
}

impl<'tcx> UnwrapDetector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            unwrap_apis: HashSet::new(),
        }
    }

    pub fn filter_unwrap(&mut self, instances: impl Iterator<Item = Instance<'tcx>>) -> usize {
        for instance in instances {
            if let Some(unwrap_instance) = UnwrapInstance::new(instance, self.tcx) {
                self.unwrap_apis.insert(unwrap_instance);
            }
        }
        self.unwrap_apis.len()
    }

    pub fn unwrap_api_arg0(
        &self,
        location: Location,
        body: &'tcx Body<'tcx>,
    ) -> Option<Place<'tcx>> {
        if let TerminatorKind::Call {
            func: _func, args, ..
        } = &body[location.block].terminator().kind
        {
            return args[0].place();
        }
        None
    }

    pub fn analyze(&mut self, instance: Instance<'tcx>) {
        if !self.should_analyze(&instance) {
            return;
        }
        let body = self.tcx.instance_mir(instance.def);
        let mut finder =
            UnwrapAPICallSitesFinder::new(instance, body, self.tcx, self.unwrap_apis.clone());
        finder.visit_body(body);
        for (location, unwrap_api) in finder.callsites.iter() {
            println!("{:?}: {:?}", body.source_info(*location), unwrap_api);
            if let Some(option_or_result) = self.unwrap_api_arg0(*location, body) {
                println!("{:?}: {:?}", option_or_result, option_or_result.ty(body, self.tcx).ty);
                let mut def_use_analysis = DefUseAnalysis::new(body);
                def_use_analysis.analyze(body);
                let info = def_use_analysis.local_info(option_or_result.local);
                let defs = info.defs_not_including_drop();
                // check current defs 
                // if not exists, then track move
                let mut state = 0u32;
                for def in defs {
                    println!("Def: {:?}: {:?}", def.context, def.location);
                    if let Some(instance) = finder.all_callsites.get(&def.location) {
                        println!("def_callee: {:?}", instance.def);
                        self.analyze_def(*instance);
                    }
                }
                // find def of option_or_result
                // if def is callsite
                // track the body
                // unwrap_instance_location: def_instance_location
                // def_instance_location return _0: defs
            }
        }
    }

    pub fn analyze_def(&mut self, instance: Instance<'tcx>) {
        let body = self.tcx.instance_mir(instance.def);
        let return_place = &body.local_decls[RETURN_PLACE];
        let mut def_use_analysis = DefUseAnalysis::new(body);
        def_use_analysis.analyze(body);
        let return_info = def_use_analysis.local_info(RETURN_PLACE);
        for def in return_info.defs_not_including_drop() {
            let location = def.location;
            if body.terminator_loc(location.block) == location {
                let term = body[location.block].terminator();
                println!("Return From Term: {:?}", term);
            } else {
                let stmt = &body[location.block].statements[location.statement_index];
                match stmt.kind {
                    StatementKind::SetDiscriminant {ref place, ref variant_index} => {
                        println!("VariantIndex: {:?}", variant_index);
                    }
                    _ => {

                    }
                }
            }
        }
        // for def in defs(return_place)
        //   if Ok/Some => 01; if Err/None => 10
        //   11 => Ok
    }

    fn should_analyze(&self, instance: &Instance<'tcx>) -> bool {
        if let InstanceDef::Item(_) = instance.def {
            self.tcx.is_mir_available(instance.def_id())
        } else {
            false
        }
    }
}

pub struct UnwrapAPICallSitesFinder<'tcx> {
    pub instance: Instance<'tcx>,
    pub body: &'tcx Body<'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub all_callsites: HashMap<Location, Instance<'tcx>>,
    pub callsites: HashSet<(Location, UnwrapInstance<'tcx>)>,
    pub unwrap_apis: HashSet<UnwrapInstance<'tcx>>,
}

impl<'tcx> UnwrapAPICallSitesFinder<'tcx> {
    pub fn new(
        instance: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        unwrap_apis: HashSet<UnwrapInstance<'tcx>>,
    ) -> Self {
        Self {
            instance,
            body,
            tcx,
            all_callsites: HashMap::new(),
            callsites: HashSet::new(),
            unwrap_apis,
        }
    }
}

impl<'tcx> Visitor<'tcx> for UnwrapAPICallSitesFinder<'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call {
            ref func,
            ref args,
            destination,
            ..
        } = terminator.kind
        {
            let func_ty = func.ty(self.body, self.tcx);
            let func_ty = self.instance.subst_mir_and_normalize_erasing_regions(
                self.tcx,
                ty::ParamEnv::reveal_all(),
                func_ty,
            );
            if let TyKind::FnDef(def_id, substs_ref) = func_ty.kind() {
                if let Some(callee_instance) =
                    Instance::resolve(self.tcx, ty::ParamEnv::reveal_all(), *def_id, substs_ref)
                        .ok()
                        .flatten()
                {
                    if let Some(unwrap_instance) = UnwrapInstance::new(callee_instance, self.tcx) {
                        if !self.unwrap_apis.contains(&unwrap_instance) {
                            println!(
                                "{:?} contains unknown {:?}",
                                self.body.source_info(location),
                                unwrap_instance
                            );
                        }
                        self.callsites.insert((location, unwrap_instance));
                    }
                    self.all_callsites.insert(location, callee_instance);
                }
            }
        }
    }
}
