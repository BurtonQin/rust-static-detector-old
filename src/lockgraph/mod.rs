//! # lockgraph
//!
//! This module generates a LockGuard graph in LOCAL crate and then maps it to a Lock graph.
//! In the lockGuard graph,
//! Node is of type LockGuard.
//! Edge (A, B, C) means LockGuard A is live when LockGuard B is created at Location C.
//! After replacing LockGuard with its corresponding Mutex Ref (Aliased Mutex Ref is in the same Node), we get a lock graph.
//! If there exists a cycle in the lock graph, then there is possibly a double/conflicting-lock bug.

// use petgraph::dot::{Config, Dot};
// use petgraph::{graphmap::GraphMap, Directed};
// pub struct LockGuardGraph<'tcx> {
//     pub graph: GraphMap<, Location<'tcx>, Directed>,
// }

// impl LockGuardGraph {

// }
