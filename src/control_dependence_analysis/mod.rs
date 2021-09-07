use std::collections::{HashSet, VecDeque};

use crate::post_dominators::{post_dominates, post_dominators, ExtNode, PostDominators};
use petgraph::dot::{Config, Dot};
use petgraph::{graphmap::GraphMap, Directed};
use rustc_middle::mir::{BasicBlock, Body, Terminator, TerminatorKind, START_BLOCK};
use rustc_middle::ty::{self, Instance, InstanceDef, Ty, TyCtxt};
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ControlDependenceNode {
    block: BasicBlock,
}

impl Default for ControlDependenceNode {
    fn default() -> Self {
        Self { block: START_BLOCK }
    }
}

impl ControlDependenceNode {
    fn new(block: BasicBlock) -> Self {
        Self { block }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EdgeType {
    Parent,
    Children,
}
pub struct ControlDependenceGraph<'tcx> {
    pub graph: GraphMap<ControlDependenceNode, EdgeType, Directed>,
    pub body: &'tcx Body<'tcx>,
    pub instance: Instance<'tcx>,
    pub tcx: TyCtxt<'tcx>,
}

pub fn should_analyze<'tcx>(instance: &Instance<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    match instance.def {
        InstanceDef::Item(_)
        | InstanceDef::DropGlue(_, _)
        | InstanceDef::ClosureOnceShim { .. } => tcx.is_mir_available(instance.def_id()),
        _ => false,
    }
}

impl<'tcx> ControlDependenceGraph<'tcx> {
    pub fn new(body: &'tcx Body<'tcx>, instance: Instance<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            graph: GraphMap::new(),
            body,
            instance,
            tcx,
        }
    }
    pub fn compute_dependence(&mut self) {
        let pdt = post_dominators(self.body);
        println!("pdt: {:?}", pdt);
        let bbs = self.body.basic_blocks();
        for (bb, _) in bbs.iter_enumerated() {
            self.graph.add_node(ControlDependenceNode::new(bb));
        }
        for (bb, bb_data) in bbs.iter_enumerated() {
            for succ in bb_data.terminator().successors() {
                if bb == *succ || !pdt.is_post_dominated_by(bb, *succ) {
                    if let Some(common) = pdt.find_nearest_common_dominator(bb, *succ) {
                        if bb == common {
                            let node = ControlDependenceNode::new(bb);
                            self.graph.add_edge(node, node, EdgeType::Parent);
                        }
                        let node = ControlDependenceNode::new(bb);
                        let end = pdt.immediate_post_dominator(common);
                        for curr in pdt.post_dominators(*succ) {
                            if ExtNode::Real(Some(curr)) == end {
                                break;
                            }
                            let curr_node = ControlDependenceNode::new(curr);
                            self.graph.add_edge(curr_node, node, EdgeType::Parent);
                        }
                    }
                }
            }
        }
    }

    pub fn influences(&self, from: BasicBlock, to: BasicBlock) -> bool {
        let to_node = ControlDependenceNode::new(to);
        let mut worklist = VecDeque::new();
        worklist.push_front(to_node);
        let mut processed = HashSet::new();
        while let Some(node) = worklist.pop_front() {
            if node.block == from {
                return true;
            }
            processed.insert(node);
            for parent in self.parents(node) {
                if processed.contains(&parent) {
                    continue;
                }
                worklist.push_front(parent);
            }
        }
        return false;
    }

    fn parents(&self, node: ControlDependenceNode) -> Vec<ControlDependenceNode> {
        self.graph
            .edges(node)
            .filter_map(|(_, to, edge_type)| {
                if let EdgeType::Parent = *edge_type {
                    Some(to)
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn dot(&self) {
        println!(
            "{:?}",
            Dot::with_config(&self.graph, &[Config::GraphContentOnly])
        );
    }
}
