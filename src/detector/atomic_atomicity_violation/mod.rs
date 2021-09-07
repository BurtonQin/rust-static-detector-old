use once_cell::sync::Lazy;
use regex::Regex;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{Body, Location, Place, Statement, Terminator, TerminatorKind};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_middle::ty::{Instance, InstanceDef};
use std::collections::{HashMap, HashSet};

use crate::control_dependence_analysis::ControlDependenceGraph;
use crate::pointer_analysis::IntraProceduralPointerAnalysis;

static ATOMIC_API_REGEX: Lazy<HashMap<&'static str, Regex>> = Lazy::new(|| {
    macro_rules! atomic_api_prefix {
        () => {
            r"^(std|core)::sync::atomic[:a-zA-Z0-9]*::"
        };
    }
    let mut m = HashMap::new();
    m.insert(
        "AtomicRead",
        Regex::new(std::concat!(atomic_api_prefix!(), r"load")).unwrap(),
    );
    m.insert(
        "AtomicWrite",
        Regex::new(std::concat!(atomic_api_prefix!(), r"store")).unwrap(),
    );
    m.insert(
        "AtomicReadWrite",
        Regex::new(std::concat!(
            atomic_api_prefix!(),
            r"(compare|fetch)_[a-zA-Z0-9]*"
        ))
        .unwrap(),
    );
    m
});

#[cfg(test)]
mod tests {
    use super::ATOMIC_API_REGEX;
    #[test]
    fn test_atomic_api_regex() {
        assert!(ATOMIC_API_REGEX["AtomicRead"].is_match("std::sync::atomic::AtomicUsize::load"));
        assert!(ATOMIC_API_REGEX["AtomicWrite"].is_match("std::sync::atomic::AtomicUsize::store"));
        assert!(ATOMIC_API_REGEX["AtomicReadWrite"]
            .is_match("std::sync::atomic::AtomicUsize::compare_and_swap"));
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum AtomicAPI<'tcx> {
    AtomicRead(Instance<'tcx>),
    AtomicWrite(Instance<'tcx>),
    AtomicReadWrite(Instance<'tcx>),
}

impl<'tcx> AtomicAPI<'tcx> {
    pub fn new(instance: Instance<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Self> {
        let def_path_str = tcx.def_path_str_with_substs(instance.def_id(), instance.substs);
        if ATOMIC_API_REGEX["AtomicRead"].is_match(&def_path_str) {
            Some(AtomicAPI::AtomicRead(instance))
        } else if ATOMIC_API_REGEX["AtomicWrite"].is_match(&def_path_str) {
            Some(AtomicAPI::AtomicWrite(instance))
        } else if ATOMIC_API_REGEX["AtomicReadWrite"].is_match(&def_path_str) {
            Some(AtomicAPI::AtomicReadWrite(instance))
        } else {
            None
        }
    }
}

pub struct AtomicAtomicityViolation<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub atomic_apis: HashSet<AtomicAPI<'tcx>>,
}

impl<'tcx> AtomicAtomicityViolation<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            atomic_apis: HashSet::new(),
        }
    }

    pub fn filter_atomic(&mut self, instances: impl Iterator<Item = Instance<'tcx>>) -> usize {
        for instance in instances {
            if let Some(atomic_api) = AtomicAPI::new(instance, self.tcx) {
                self.atomic_apis.insert(atomic_api);
            }
        }
        self.atomic_apis.len()
    }

    pub fn atomic_api_arg0(
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
            AtomicAPICallSitesFinder::new(instance, body, self.tcx, self.atomic_apis.clone());
        finder.visit_body(body);
        // finder.callsites.contains(AtomicRead) && AtomicWrite
        let mut contains_atomic_read = false;
        let mut contains_atomic_write = false;
        for (_, atomic_api) in finder.callsites.iter() {
            match atomic_api {
                AtomicAPI::AtomicRead(_) => contains_atomic_read = true,
                AtomicAPI::AtomicWrite(_) => contains_atomic_write = true,
                _ => {}
            };
        }
        if !(contains_atomic_read && contains_atomic_write) {
            return;
        }
        let mut intra_pointer_analysis = IntraProceduralPointerAnalysis::new(self.tcx);
        let (globals, escapes) = intra_pointer_analysis.analyze(instance);
        // atomic_read(arg0)
        // atomic_write(arg0')
        // arg0 alias arg0'
        let mut atomic_read_apis = HashSet::new();
        let mut atomic_write_apis = HashSet::new();
        let mut atomic_read_write_apis = HashSet::new();
        for (location, atomic_api) in finder.callsites.iter() {
            match atomic_api {
                AtomicAPI::AtomicRead(_) => atomic_read_apis.insert(*location),
                AtomicAPI::AtomicWrite(_) => atomic_write_apis.insert(*location),
                AtomicAPI::AtomicReadWrite(_) => atomic_read_write_apis.insert(*location),
            };
        }
        if !atomic_read_write_apis.is_empty() {
            return;
        }
        if finder.callsites.len() > 0 {
            println!("{:?}", instance.def_id());
            println!(
                "{:#?}",
                finder
                    .callsites
                    .iter()
                    .map(|(loc, instance)| { (body.source_info(*loc), instance) })
                    .collect::<HashSet<_>>()
            );
        }
        // location => terminator => arg0
        let mut aliased_read_write = HashSet::new();
        for read_loc in atomic_read_apis.iter() {
            if let Some(read_arg0) = self.atomic_api_arg0(*read_loc, body) {
                for write_loc in atomic_write_apis.iter() {
                    if let Some(write_arg0) = self.atomic_api_arg0(*write_loc, body) {
                        // read_arg0 alias write_arg0
                        if intra_pointer_analysis
                            .may_alias(*write_loc, read_arg0, write_arg0, &globals)
                        {
                            println!("Result: {:?}, {:?}, {:?}", write_loc, read_arg0, write_arg0);
                            aliased_read_write.insert((read_loc, write_loc));
                        }
                    }
                }
            }
        }
        if aliased_read_write.is_empty() {
            return;
        }
        // control dependence analysis
        let mut cda = ControlDependenceGraph::new(body, instance, self.tcx);
        cda.compute_dependence();
        for (read, write) in aliased_read_write {
            if let TerminatorKind::Call {
                func: _func,
                args: _args,
                destination,
                ..
            } = &body[read.block].terminator().kind
            {
                if let Some((_, bb)) = destination {
                    if cda.influences(*bb, write.block) {
                        println!(
                            "Bug: {:?}, {:?}",
                            body.source_info(body.terminator_loc(*bb)),
                            body.source_info(*write)
                        );
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
}

pub struct AtomicAPICallSitesFinder<'tcx> {
    pub instance: Instance<'tcx>,
    pub body: &'tcx Body<'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub callsites: HashSet<(Location, AtomicAPI<'tcx>)>,
    pub atomic_apis: HashSet<AtomicAPI<'tcx>>,
}

impl<'tcx> AtomicAPICallSitesFinder<'tcx> {
    pub fn new(
        instance: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        atomic_apis: HashSet<AtomicAPI<'tcx>>,
    ) -> Self {
        Self {
            instance,
            body,
            tcx,
            callsites: HashSet::new(),
            atomic_apis,
        }
    }
}

impl<'tcx> Visitor<'tcx> for AtomicAPICallSitesFinder<'tcx> {
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
                    if let Some(atomic_api) = AtomicAPI::new(callee_instance, self.tcx) {
                        if !self.atomic_apis.contains(&atomic_api) {
                            println!(
                                "{:?} contains unknown {:?}",
                                self.body.source_info(location),
                                atomic_api
                            );
                        }
                        self.callsites.insert((location, atomic_api));
                    }
                }
            }
        }
    }
}
