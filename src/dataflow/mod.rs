//! Dataflow analysis
//! Output:
//! 1. MemorySSA
//! 2. Points-to Graph
//! 3. Callgraph (Direct & Indirect)
//! Phases:
//! 1. intra-procedural
//! 2. inter-procedural
//! States:
//! Graph<V, E>, V is MemObj, E is MemObj x MemObj x Tag
//! MemObj can be Static, Constant, Concrete, and Virtual

pub struct IntraProcAnalysis {
    //

}

pub struct InterProcAnalysis {
    //
}