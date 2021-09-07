use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Graph<N: Hash + Eq + Copy + Debug> {
    pub nodes: HashSet<N>,
    pub edges: HashMap<N, HashSet<N>>,
}

impl<N: Hash + Eq + Copy + Debug> Graph<N> {
    pub fn new() -> Self {
        Self {
            nodes: HashSet::new(),
            edges: HashMap::new(),
        }
    }

    pub fn add_node(&mut self, node: N) -> bool {
        self.nodes.insert(node)
    }

    pub fn add_edge(&mut self, from: N, to: N) -> bool {
        let mut changed = self.nodes.insert(from);
        changed |= self.nodes.insert(to);
        changed |= self.edges.entry(from).or_default().insert(to);
        changed
    }

    pub fn remove_node(&mut self, node: N) {
        self.edges.remove(&node);
        self.nodes.remove(&node);
    }

    pub fn remove_all_edges(&mut self, from: N) {
        if let Some(tos) = self.edges.get_mut(&from) {
            tos.clear();
        }
    }

    pub fn debug_print(&self) {
        for (from, tos) in self.edges.iter() {
            println!("{:?}: {:#?}", from, tos);
        }
    }

    pub fn remove_edge(&mut self, from: N, to: N) {
        if let Some(tos) = self.edges.get_mut(&from) {
            tos.remove(&to);
        }
    }

    pub fn update_edge_to(&mut self, from: N, old_to: N, new_to: N) {
        if let Some(tos) = self.edges.get_mut(&from) {
            tos.remove(&old_to);
            tos.insert(new_to);
        }
    }

    pub fn replace_node(&mut self, before: N, after: N) -> bool {
        let mut changed = false;
        if self.nodes.remove(&before) {
            changed |= self.nodes.insert(after);
        }
        if let Some(nodes) = self.edges.get(&before) {
            let tmp = nodes.clone();
            drop(nodes);
            self.edges.insert(after, tmp);
            changed = true;
        }
        for (_, tos) in self.edges.iter_mut() {
            if tos.remove(&before) {
                changed |= tos.insert(after);
            }
        }
        changed
    }

    pub fn union(&mut self, other: Self) -> bool {
        let mut changed = false;
        let old_len = self.nodes.len();
        self.nodes.extend(other.nodes.into_iter());
        if self.nodes.len() != old_len {
            changed = true;
        }
        for (from, tos) in other.edges {
            if let Some(this_tos) = self.edges.get_mut(&from) {
                let old_len = this_tos.len();
                this_tos.extend(tos.into_iter());
                if this_tos.len() != old_len {
                    changed = true;
                }
            } else {
                self.edges.insert(from, tos);
                changed = true;
            }
        }
        changed
    }

    pub fn neighbors(&self, node: N) -> Option<&HashSet<N>> {
        self.edges.get(&node)
    }
}
#[cfg(test)]
mod tests {
    use super::Graph;
    #[test]
    fn test_graph_basic() {
        let mut graph = Graph::new();
        graph.add_node(1);
        graph.add_node(2);
        graph.add_node(3);
        graph.add_node(4);
        graph.add_edge(1, 2);
        graph.add_edge(1, 3);
        graph.add_edge(2, 4);
        graph.add_edge(3, 4);
        graph.debug_print();
    }

    #[test]
    fn test_graph_clone() {
        let mut graph1 = Graph::new();
        graph1.add_node(1);
        graph1.add_node(2);
        graph1.add_node(3);
        graph1.add_edge(1, 2);
        graph1.add_edge(1, 3);

        let mut graph2 = Graph::new();
        graph2.add_node(2);
        graph2.add_node(3);
        graph2.add_node(4);
        graph2.add_edge(2, 4);
        graph2.add_edge(3, 4);

        graph1.union(graph2);
        graph1.debug_print();
    }
}
