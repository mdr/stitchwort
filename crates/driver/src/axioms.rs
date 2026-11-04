//! The axiom report (docs/proposals/map-equality.md §10, D864 and D925):
//! which axioms a declaration depends on, transitively.
//!
//! Today there is one, `Quot.sound`. It's a term former, not a declaration,
//! so following named references isn't enough: the walk scans the checked
//! terms (type and body) of every definition it reaches, and of the data
//! types it reaches (their parameters, indices and constructor fields), at
//! every position, and reports each `Term::Quot(Sound)` node it finds. It
//! doesn't use the runtime's `reachable`, which skips the bodies of erased
//! definitions: a proof is exactly where `Quot.sound` shows up.
//!
//! [`AxiomWalk`] keeps the result for every declaration it has finished, so
//! an audit can walk each definition and data type once and build every
//! theorem's set from what it uses. Dependency graphs may have cycles
//! (mutually recursive definitions and data groups), so it computes strongly
//! connected components (Tarjan, iteratively) and gives each member of a
//! component the union of the component's own axioms and its successors'
//! sets. Memoising a node as its depth-first search finishes would give the
//! earlier members of a cycle too small a set.

use std::collections::BTreeSet;

use stitchwort_core::collections::HashMap;
use stitchwort_core::globals::Globals;
use stitchwort_core::{DataId, DefId, QuotForm, Term};

/// A reusable walk, with the axiom set of every declaration it has finished.
///
/// Its results are only valid for the `Globals` it was filled from: an
/// audit creates one after loading the project, and uses it for all of the
/// project's theorems.
#[derive(Default)]
pub struct AxiomWalk {
    finished: HashMap<Node, BTreeSet<&'static str>>,
}

impl AxiomWalk {
    pub fn new() -> Self {
        Self::default()
    }

    /// The names of the axioms `root` depends on, sorted, walking only what
    /// earlier calls haven't.
    pub fn axioms(&mut self, globals: &Globals, root: DefId) -> BTreeSet<&'static str> {
        let root = Node::Def(root);
        if let Some(found) = self.finished.get(&root) {
            return found.clone();
        }
        self.walk(globals, root);
        self.finished
            .get(&root)
            .cloned()
            .expect("the walk finished the root")
    }

    /// Walks what is reachable from `root` and isn't finished yet, assigning
    /// each strongly connected component its union once all its successors
    /// have theirs.
    fn walk(&mut self, globals: &Globals, root: Node) {
        let defs = globals.env.defs().len();
        let count = defs + globals.env.datas().len();
        let mut tarjan = Tarjan::new(count);
        let root = index(defs, root);
        tarjan.discover(globals, defs, root);
        let mut frames: Vec<(usize, usize)> = vec![(root, 0)];

        while let Some(&(v, child)) = frames.last() {
            let next = tarjan.edges[v]
                .as_ref()
                .and_then(|successors| successors.get(child).copied());
            let Some(w) = next else {
                // Finished `v`: close its component if it is the root of one.
                frames.pop();
                if let Some(&(parent, _)) = frames.last() {
                    tarjan.low[parent] = tarjan.low[parent].min(tarjan.low[v]);
                }
                tarjan.finish(v, defs, &mut self.finished);
                continue;
            };
            frames.last_mut().expect("a frame is open").1 += 1;
            // A finished node is a sink: its result already has everything
            // reachable from it, so there is no need to walk it again.
            if self.finished.contains_key(&node(defs, w)) {
                continue;
            }
            match tarjan.order[w] {
                None => {
                    tarjan.discover(globals, defs, w);
                    frames.push((w, 0));
                }
                Some(w_order) if tarjan.on_stack[w] => {
                    tarjan.low[v] = tarjan.low[v].min(w_order);
                }
                Some(_) => {}
            }
        }
    }
}

/// The index of a node in the walk's arrays.
fn index(defs: usize, node: Node) -> usize {
    match node {
        Node::Def(id) => id.0,
        Node::Data(id) => defs + id.0,
    }
}

/// The node at an index in the walk's arrays.
fn node(defs: usize, index: usize) -> Node {
    match index < defs {
        true => Node::Def(DefId(index)),
        false => Node::Data(DataId(index - defs)),
    }
}

/// Tarjan's algorithm's state for one walk, iterative because the dependency
/// graph can be deep.
struct Tarjan {
    order: Vec<Option<u32>>,
    low: Vec<u32>,
    on_stack: Vec<bool>,
    stack: Vec<usize>,
    /// The successors and own axioms of each node, scanned when it is first
    /// reached. `None` until then.
    edges: Vec<Option<Vec<usize>>>,
    own: Vec<Option<BTreeSet<&'static str>>>,
    component: Vec<Option<usize>>,
    component_results: Vec<BTreeSet<&'static str>>,
    next_order: u32,
}

impl Tarjan {
    fn new(count: usize) -> Self {
        Self {
            order: vec![None; count],
            low: vec![0; count],
            on_stack: vec![false; count],
            stack: Vec::new(),
            edges: vec![None; count],
            own: vec![None; count],
            component: vec![None; count],
            component_results: Vec::new(),
            next_order: 0,
        }
    }

    fn discover(&mut self, globals: &Globals, defs: usize, i: usize) {
        let (found, successors) = scan(globals, node(defs, i));
        self.own[i] = Some(found);
        self.edges[i] = Some(
            successors
                .into_iter()
                .map(|successor| index(defs, successor))
                .collect(),
        );
        self.order[i] = Some(self.next_order);
        self.low[i] = self.next_order;
        self.next_order += 1;
        self.stack.push(i);
        self.on_stack[i] = true;
    }

    /// Pops `v`'s component, if it is one's root, and gives it its axioms.
    fn finish(
        &mut self,
        v: usize,
        defs: usize,
        finished: &mut HashMap<Node, BTreeSet<&'static str>>,
    ) {
        if self.low[v] != self.order[v].expect("a discovered node has an order") {
            return;
        }
        let mut members = Vec::new();
        loop {
            let member = self
                .stack
                .pop()
                .expect("the component's root is on the stack");
            self.on_stack[member] = false;
            members.push(member);
            if member == v {
                break;
            }
        }
        let mut found = BTreeSet::new();
        for &member in &members {
            if let Some(own) = &self.own[member] {
                found.extend(own.iter().copied());
            }
            for &successor in self.edges[member]
                .as_ref()
                .expect("a discovered node has its edges")
            {
                if let Some(result) = finished.get(&node(defs, successor)) {
                    found.extend(result.iter().copied());
                } else if let Some(c) = self.component[successor] {
                    found.extend(self.component_results[c].iter().copied());
                }
                // Otherwise it is another member of this component: it has
                // the same result.
            }
        }
        let c = self.component_results.len();
        self.component_results.push(found.clone());
        for &member in &members {
            self.component[member] = Some(c);
            finished.insert(node(defs, member), found.clone());
        }
    }
}

/// The names of the axioms `root` depends on, sorted.
pub fn axioms(globals: &Globals, root: DefId) -> BTreeSet<&'static str> {
    AxiomWalk::new().axioms(globals, root)
}

/// The walk from scratch, kept for tests that compare [`AxiomWalk`] with it.
#[cfg(test)]
fn from_scratch(globals: &Globals, root: DefId) -> BTreeSet<&'static str> {
    let mut found = BTreeSet::new();
    let mut seen_defs = stitchwort_core::collections::HashSet::default();
    let mut seen_datas = stitchwort_core::collections::HashSet::default();
    let mut pending = vec![Node::Def(root)];
    while let Some(node) = pending.pop() {
        let mut terms: Vec<&Term> = Vec::new();
        match node {
            Node::Def(id) => {
                if !seen_defs.insert(id) {
                    continue;
                }
                let def = globals.def(id);
                terms.push(def.ty());
                terms.extend(def.body().map(|b| &**b));
            }
            Node::Data(id) => {
                if !seen_datas.insert(id) {
                    continue;
                }
                let data = globals.data(id);
                terms.extend(data.params().iter().map(|(_, t)| t));
                terms.extend(data.indices().iter().map(|(_, t)| t));
                for ctor in data.ctors() {
                    terms.extend(ctor.fields.iter().map(|(_, t)| t));
                    terms.extend(ctor.result.iter());
                }
            }
        }
        for term in terms {
            for (sub, _) in term.subterms() {
                match sub {
                    Term::Quot(QuotForm::Sound, _, _) => {
                        found.insert("Quot.sound");
                    }
                    Term::Def(id) => pending.push(Node::Def(*id)),
                    Term::Data(id, _) | Term::Ctor(id, _, _) | Term::Case(_, id, _) => {
                        pending.push(Node::Data(*id));
                    }
                    _ => {}
                }
            }
        }
    }
    found
}

/// A node's own axioms and the declarations it refers to, from its terms.
fn scan(globals: &Globals, node: Node) -> (BTreeSet<&'static str>, Vec<Node>) {
    let mut found = BTreeSet::new();
    let mut successors = Vec::new();
    let mut terms: Vec<&Term> = Vec::new();
    match node {
        Node::Def(id) => {
            let def = globals.def(id);
            terms.push(def.ty());
            terms.extend(def.body().map(|b| &**b));
        }
        Node::Data(id) => {
            let data = globals.data(id);
            terms.extend(data.params().iter().map(|(_, t)| t));
            terms.extend(data.indices().iter().map(|(_, t)| t));
            for ctor in data.ctors() {
                terms.extend(ctor.fields.iter().map(|(_, t)| t));
                terms.extend(ctor.result.iter());
            }
        }
    }
    for term in terms {
        for (sub, _) in term.subterms() {
            match sub {
                Term::Quot(QuotForm::Sound, _, _) => {
                    found.insert("Quot.sound");
                }
                Term::Def(id) => successors.push(Node::Def(*id)),
                Term::Data(id, _) | Term::Ctor(id, _, _) | Term::Case(_, id, _) => {
                    successors.push(Node::Data(*id));
                }
                _ => {}
            }
        }
    }
    (found, successors)
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Node {
    Def(DefId),
    Data(DataId),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver::Session;

    fn load(source: &str) -> Session {
        let mut session = Session::new();
        if let Err(diagnostics) = session.load("test.sw", source) {
            let shown: Vec<String> = diagnostics
                .iter()
                .map(|d| format!("{}: {}", d.code, d.message))
                .collect();
            panic!("{shown:#?}");
        }
        session
    }

    fn def(session: &Session, name: &str) -> DefId {
        session
            .elab
            .lookup_def(name)
            .unwrap_or_else(|| panic!("`{name}` is defined"))
    }

    /// A cycle of definitions where only one uses `Quot.sound`: every
    /// definition's memoised set equals the from-scratch walk's, including
    /// the one before `odd` in the component, whose depth-first search would
    /// finish first.
    #[test]
    fn mutually_recursive_definitions_get_the_cycles_axioms() {
        let session = load(
            r#"def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue
def soundNat: Nat := J (y e => Nat) 7 (Quot.sound Trivial: (Quot.mk False: Q) = Quot.mk True)
def even: Nat → Nat
  | 0 => 0
  | Succ n => odd n
def odd: Nat → Nat
  | 0 => soundNat
  | Succ n => even n
"#,
        );
        let g = &session.elab.globals;
        let mut walk = AxiomWalk::new();
        for name in ["even", "odd", "soundNat"] {
            let id = def(&session, name);
            assert_eq!(
                walk.axioms(g, id),
                from_scratch(g, id),
                "{name}: the memoised walk differs from the walk from scratch"
            );
        }
        assert_eq!(
            walk.axioms(g, def(&session, "even")),
            ["Quot.sound"].into_iter().collect(),
            "`even` reaches `Quot.sound` through `odd`"
        );
    }

    /// Every theorem of the standard library: the result built from the
    /// shared memo equals the one from a fresh walk from scratch.
    #[test]
    fn the_standard_librarys_theorems_match_the_walk_from_scratch() {
        let session = Session::eager();
        let g = &session.elab.globals;
        let theorems = crate::audit::theorems(g, &|_| true);
        assert!(
            !theorems.is_empty(),
            "the standard library declares theorems"
        );
        let mut walk = AxiomWalk::new();
        for (id, name) in theorems {
            assert_eq!(
                walk.axioms(g, id),
                from_scratch(g, id),
                "{name}: the memoised walk differs from the walk from scratch"
            );
        }
    }
}
