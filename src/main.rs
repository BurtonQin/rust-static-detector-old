#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(or_patterns)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use callgraph::Callgraph;
use rustc_driver::{Compilation, RunCompiler};
use rustc_errors::emitter::{ColorConfig, HumanReadableErrorType};
use rustc_hir::def_id::{CrateNum, DefIdSet};
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::*;
use rustc_middle::{mir::visit::TyContext, ty::*};
use rustc_session::early_error;
use rustc_session::{config::ErrorOutputType, CtfeBacktrace};

use std::{
    collections::{HashMap, HashSet, VecDeque},
    sync::atomic::AtomicI16,
};
use std::{env, marker::PhantomData};

mod callgraph;
mod control_dependence_analysis;
mod detector;
mod interior_mutability;
mod lockgraph;
mod pointer_analysis;
mod post_dominators;
mod util;

// use detector::use_after_free::UseAfterFree;
// use pointer_analysis::PointerAnalysis;
// use detector::drop_identifier::DropIdentifier;
// use detector::drop_identifier::TotalAnalysis;
// use detector::drop_identifier::ValueFlowAnalysis;
use control_dependence_analysis::{should_analyze, ControlDependenceGraph, ControlDependenceNode};
use detector::{
    atomic_atomicity_violation::AtomicAtomicityViolation, use_after_free::UseAfterFreeDetector, panic::UnwrapDetector
};

struct FindAssignments<'tcx> {
    d: PhantomData<&'tcx ()>,
}

impl<'tcx> Visitor<'tcx> for FindAssignments<'tcx> {
    // fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
    //     if let StatementKind::Assign(box (
    //         dest,
    //         Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
    //     )) = &statement.kind
    //     {
    //         println!("{:?}", dest);
    //     }
    // }
    fn visit_ty(&mut self, ty: Ty<'tcx>, _: TyContext) {
        println!("{:?}, {:?}", ty, ty.kind());
    }
}

struct RustStaticDetector {}

impl rustc_driver::Callbacks for RustStaticDetector {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
            if crate_name == "rocksdb" {
                return;
            }
            dbg!(crate_name);
            
            if tcx.sess.opts.debugging_opts.no_codegen
                || !tcx.sess.opts.output_types.should_codegen()
            {
                return;
            }

            let cgus = tcx.collect_and_partition_mono_items(LOCAL_CRATE).1;
            let instances: Vec<Instance<'tcx>> = cgus
                .into_iter()
                .flat_map(|cgu| {
                    cgu.items().into_iter().filter_map(|(mono_item, _)| {
                        if let MonoItem::Fn(instance) = mono_item {
                            Some(*instance)
                        } else {
                            None
                        }
                    })
                })
                .collect();
            // let mut atomic_av = AtomicAtomicityViolation::new(tcx);
            // atomic_av.filter_atomic(instances.clone().into_iter());
            // if atomic_av.atomic_apis.len() > 1 {
            //     println!("{:#?}", atomic_av.atomic_apis);
            // }
            for instance in instances.clone().into_iter() {
                // atomic_av.analyze(instance);
                if !should_analyze(&instance, tcx) {
                    continue;
                }
                // println!("{:?}", instance.def_id());
                let name = format!("{:?}", instance.def_id());
                // if !name.contains("gethostent") {
                //      continue;
                // }
                // let body = tcx.instance_mir(instance.def);
                match std::env::var("DETECTOR_TYPE") {
                    Ok(value) if &value == "UAF" => {
                        let mut uaf = UseAfterFreeDetector::new(tcx);
                        uaf.analyze(instance);
                    }
                    Ok(value) if &value == "AV" => {
                        let mut aav = AtomicAtomicityViolation::new(tcx);
                        aav.analyze(instance);
                    }
                    Ok(value) if &value == "PANIC" => {
                        let mut unwrap_detector = UnwrapDetector::new(tcx);
                        unwrap_detector.analyze(instance);
                    }
                    Ok(_) | Err(_) => {
                        panic!("DETECTOR_TYPE NOT SET OR SET TO WRONG VALUES (NOT UAF OR AV)");
                    }
                }
                
                // let mut cda = ControlDependenceGraph::new(body, instance, tcx);
                // cda.compute_dependence();
                // cda.dot();
                // let mut pta = pointer_analysis::IntraProceduralPointerAnalysis::new(tcx);
                // pta.analyze(instance);
            }
            //let mut drop_identifier = DropIdentifier { tcx };
            // let mut total_analyzer = TotalAnalysis { tcx, states: HashMap::new() };
            // let mut value_flow_analyzer = ValueFlowAnalysis::new(tcx);
            // for instance in instances.clone() {
            //     value_flow_analyzer.analyze(instance);
            //     // drop_identifier.analyze(instance);
            //     // total_analyzer.analyze(instance);
            // }
            if false {
                let mut callgraph = callgraph::Callgraph::new();
                callgraph.analyze(instances.clone(), tcx);
                callgraph.dot();
                // Collect root instances (non-generic entry function(s))
                let mut roots: Vec<Instance<'tcx>> = Vec::new();
                if let Some((entry_fn, _)) = tcx.entry_fn(LOCAL_CRATE) {
                    roots.push(Instance::new(entry_fn.to_def_id(), List::empty()));
                } else {
                    roots.extend(
                        callgraph
                            .weak_connected_component_roots()
                            .into_iter()
                            .filter_map(|idx| match callgraph.index_to_instance(idx) {
                                Some(instance)
                                    if instance.def_id().is_local()
                                        && instance.substs.is_empty() =>
                                {
                                    Some(*instance)
                                }
                                _ => None,
                            }),
                    );
                }
                // println!("root: {:?}", roots);
                println!("roots: {:?}", roots.len());
                // let mut pointer_analysis = PointerAnalysis::new(tcx, callgraph);
                // for root in roots {
                //     pointer_analysis.analyze(root);
                // }
                // let mut use_after_free_detector = UseAfterFree::new(tcx, pointer_analysis);
                // for root in instances {
                //     use_after_free_detector.analyze(root);
                // }
            }
            // }
            // for cgu in cgus {
            //     for mono_item in cgu.items() {
            //         // println!("{:?}", mono_item);
            //         match mono_item {
            //             (MonoItem::Fn(ref instance), _) => {
            //                 instances.push(*instance);
            //                 // println!("{:?}", instance.def);
            //                 // let body = tcx.instance_mir(instance.def);
            //                 // let mut finder = interior_mutability::InteriorMutabilityFinder { body, tcx };
            //                 // finder.visit_body(body);
            //                 // let body = tcx.instance_mir(instance.def);
            //                 // find_assignment.visit_body(body);
            //                 // println!("{:?}", body);
            //                 // for (local, decl) in body.local_decls().iter_enumerated() {
            //                 //     match decl.ty.kind() {
            //                 //         Adt(adt_def, subst_ref) => {
            //                 //             let adt_name = format!("{:?}", adt_def);
            //                 //             if adt_name == "Wrapper" {
            // for cgu in cgus {
            //     for mono_item in cgu.items() {
            //         // println!("{:?}", mono_item);
            //         match mono_item {
            //             (MonoItem::Fn(ref instance), _) => {
            //                 instances.push(*instance);
            //                 // println!("{:?}", instance.def);
            //                 // let body = tcx.instance_mir(instance.def);
            //                 // let mut finder = interior_mutability::InteriorMutabilityFinder { body, tcx };
            //                 // finder.visit_body(body);
            //                 // let body = tcx.instance_mir(instance.def);
            //                 // find_assignment.visit_body(body);
            //                 // println!("{:?}", body);
            //                 // for (local, decl) in body.local_decls().iter_enumerated() {
            //                 //     match decl.ty.kind() {
            //                 //         Adt(adt_def, subst_ref) => {
            //                 //             let adt_name = format!("{:?}", adt_def);
            //                 //             if adt_name == "Wrapper" {
            //                 //                 println!("{:?}, {:?}", adt_def, subst_ref);
            //                 //                 for field in adt_def.all_fields() {
            //                 //                     println!("{:?}", tcx.type_of(field.did));
            //                 //                 }
            //                 //             }

            //                 //         },
            //                 //         _ => {}
            //                 //     }
            //                 // }
            //             }
            //             (MonoItem::Static(_def_id), _) => {

            //             }
            //             (MonoItem::GlobalAsm(_hir_id), _) => {

            //             }
            //         };
            //     }
            // }
            // callgraph.analyze(instances, tcx);

            // let roots = callgraph.weak_connected_component_roots();
            // println!("{:#?}", roots);
            // let fi_andersen_analyzer = move |instance: &Instance<'tcx>| {
            //     let mut fi_andersen = pointer_analysis::FIAndersen { tcx, pts: HashMap::new() };
            //     fi_andersen.visit_instance(*instance);
            // };

            // callgraph.bfs_visit(&roots, fi_andersen_analyzer);
            // callgraph.dot();
        });

        Compilation::Continue
    }

    fn config(&mut self, _config: &mut rustc_interface::Config) {}

    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        _queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> Compilation {
        Compilation::Continue
    }

    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        _queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> Compilation {
        Compilation::Continue
    }
}

fn compile_time_sysroot() -> Option<String> {
    if option_env!("RUSTC_STAGE").is_some() {
        // This is being built as part of rustc, and gets shipped with rustup.
        // We can rely on the sysroot computation in librustc_session.
        return None;
    }
    // For builds outside rustc, we need to ensure that we got a sysroot
    // that gets used as a default.  The sysroot computation in librustc_session would
    // end up somewhere in the build dir (see `get_or_default_sysroot`).
    // Taken from PR <https://github.com/Manishearth/rust-clippy/pull/911>.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    Some(match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("To build RustStaticDetector without rustup, set the `RUST_SYSROOT` env var at build time")
            .to_owned(),
    })
}

/// Execute a compiler with the given CLI arguments and callbacks.
fn run_compiler(mut args: Vec<String>, callbacks: &mut (dyn rustc_driver::Callbacks + Send)) -> ! {
    // Make sure we use the right default sysroot. The default sysroot is wrong,
    // because `get_or_default_sysroot` in `librustc_session` bases that on `current_exe`.
    //
    // Make sure we always call `compile_time_sysroot` as that also does some sanity-checks
    // of the environment we were built in.
    // FIXME: Ideally we'd turn a bad build env into a compile-time error via CTFE or so.
    if let Some(sysroot) = compile_time_sysroot() {
        let sysroot_flag = "--sysroot";
        if !args.iter().any(|e| e == sysroot_flag) {
            // We need to overwrite the default that librustc_session would compute.
            args.push(sysroot_flag.to_owned());
            args.push(sysroot);
        }
    }

    // Invoke compiler, and handle return code.
    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&args, callbacks).run()
    });
    std::process::exit(exit_code)
}

fn main() {
    rustc_driver::init_rustc_env_logger();
    // We cannot use `rustc_driver::main` as we need to adjust the CLI arguments.
    let args = env::args_os()
        .enumerate()
        .map(|(i, arg)| {
            arg.into_string().unwrap_or_else(|arg| {
                early_error(
                    ErrorOutputType::default(),
                    &format!("argument {} is not valid Unicode: {:?}", i, arg),
                )
            })
        })
        .collect::<Vec<_>>();
    run_compiler(args, &mut RustStaticDetector {})
}
