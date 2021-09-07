//! # callgraph
//!
//! This module generates an incomplete callgraph for LOCAL crate (without indirect call for now).
//! Node is of type InstanceDef.
//! Edge (A, B, (C, D)) means InstanceDef A calls InstanceDef B with Substs C at Location D.
//! (C, D) is Weight of Edge.
//! Intuitively, Instance is better as a Node than InstanceDef.
//! But GraphMap's Node requires Ord trait which is implemented on InstanceDef not Instance.

use petgraph::visit::Bfs;
use petgraph::visit::EdgeRef;
use petgraph::visit::NodeIndexable;
use petgraph::{
    dot::{Config, Dot},
    graph::NodeIndex,
    unionfind::UnionFind,
    visit::IntoNodeReferences,
};
use petgraph::{Directed, Graph};

use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{Body, Location, Terminator, TerminatorKind};

use rustc_middle::ty::{self, Instance, ParamEnv, TyCtxt};

use crate::util::Monomorphizer;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallType {
    DirectCall,
    IndirectCall,
}

pub struct Callgraph<'tcx> {
    pub graph: Graph<Instance<'tcx>, Vec<(CallType, Location)>, Directed>,
}

impl<'tcx> Callgraph<'tcx> {
    pub fn new() -> Self {
        Self {
            graph: Graph::new(),
        }
    }

    pub fn instance_index(&self, instance: Instance<'tcx>) -> Option<NodeIndex> {
        for (idx, &weight) in self.graph.node_references() {
            if weight == instance {
                return Some(idx);
            }
        }
        None
    }

    pub fn analyze(&mut self, instances: Vec<Instance<'tcx>>, tcx: TyCtxt<'tcx>) {
        let mut worklist = instances;
        while let Some(caller) = worklist.pop() {
            // skip if caller has been analyzed
            if self.instance_index(caller).is_some() {
                continue;
            }
            let caller_idx = self.graph.add_node(caller);
            let body = tcx.instance_mir(caller.def);
            if body.source.promoted.is_some() {
                continue;
            }
            let monimorphizer = Monomorphizer::new(caller, tcx);
            let param_env = ParamEnv::reveal_all();
            let mut resolve_function_call = ResolveFunctionCall {
                body,
                monimorphizer,
                tcx,
                param_env,
                callee_sites: Vec::new(),
            };
            resolve_function_call.visit_body(body);
            for (callee_instance, location) in resolve_function_call.callee_sites {
                let callee_idx: NodeIndex = self
                    .instance_index(callee_instance)
                    .unwrap_or_else(|| self.graph.add_node(callee_instance));
                if let Some(edge_idx) = self.graph.find_edge(caller_idx, callee_idx) {
                    // update edge weight
                    self.graph
                        .edge_weight_mut(edge_idx)
                        .unwrap()
                        .push((CallType::DirectCall, location));
                } else {
                    // add edge if not exists
                    let mut weight = Vec::new();
                    weight.push((CallType::DirectCall, location));
                    self.graph.add_edge(caller_idx, callee_idx, weight);
                }
            }
        }
    }

    /// Roots of weak connected components.
    /// Since the callgraph is incomplete, there maybe multiple weak connected components.
    /// The return Vec contains the root InstanceDef for each component.
    /// Inspired by petgraph::algo::connected_components
    pub fn weak_connected_component_roots(&self) -> Vec<NodeIndex> {
        let mut vertex_sets = UnionFind::new(self.graph.node_bound());
        for edge in self.graph.edge_references() {
            let (a, b) = (edge.source(), edge.target());
            // union the two vertices of the edge
            vertex_sets.union(self.graph.to_index(a), self.graph.to_index(b));
        }

        let mut labels = vertex_sets.into_labeling();
        labels.sort();
        labels.dedup();
        labels.into_iter().map(|u| NodeIndex::new(u)).collect()
    }

    pub fn index_to_instance(&self, idx: NodeIndex) -> Option<&Instance<'tcx>> {
        self.graph.node_weight(idx)
    }

    /// Visit the callgraph in BFS order and apply analyzer on each instance
    pub fn bfs_visit<F>(&self, roots: &[NodeIndex], analyzer: F)
    where
        F: Fn(&Instance<'tcx>),
    {
        for root in roots {
            let mut bfs = Bfs::new(&self.graph, *root);
            while let Some(node_id) = bfs.next(&self.graph) {
                analyzer(self.graph.node_weight(node_id).unwrap());
            }
        }
    }

    /// Print the callgraph in dot format.
    pub fn dot(&self) {
        println!(
            "{:?}",
            Dot::with_config(&self.graph, &[Config::GraphContentOnly])
        );
    }
}

/// Visit Terminator and record callees (direct call only) in callee_sites.
pub struct ResolveFunctionCall<'tcx> {
    body: &'tcx Body<'tcx>,
    monimorphizer: Monomorphizer<'tcx>,
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    pub(crate) callee_sites: Vec<(Instance<'tcx>, Location)>,
}

impl<'tcx> Visitor<'tcx> for ResolveFunctionCall<'tcx> {
    /// Resolve direct call.
    /// Inspired by rustc_mir/src/transform/inline.rs#get_valid_function_call.
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call { ref func, .. } = terminator.kind {
            // println!("{:?}, {:?}", self.body.source.def_id(), terminator);
            let func_ty = func.ty(self.body, self.tcx);
            // Only after monomorphizing can Instance::resolve work
            let func_ty = self.monimorphizer.monomorphize(func_ty);
            if let ty::FnDef(def_id, substs) = *func_ty.kind() {
                if let Some(callee_instance) =
                    Instance::resolve(self.tcx, self.param_env, def_id, substs)
                        .ok()
                        .flatten()
                {
                    self.callee_sites.push((callee_instance, location));
                } else {
                    dbg!("Cannot resolve: {:?}, {:?}", def_id, substs);
                }
            } else {
                // println!("Unknown call: {:?}, {:?}", *func_ty.kind(), self.body.source_info(location));
            }
        } else if let TerminatorKind::Drop { place, .. } = terminator.kind {
            // println!("{:?}, {:?}", self.body.source.def_id(), terminator);
            // let place_ty = place.ty(self.body, self.tcx);
            // println!("{:?}", place_ty);
        }
    }
}
