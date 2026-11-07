//! The size-change termination algorithm (`stitchwort_core::sct`), tested
//! against an independent reference implementation
//! (docs/proposals/mutual-recursion.md §6.6).
//!
//! The reference is deliberately naive and shares nothing with the module
//! but the [`Label`] type: a graph is an explicit set of arcs `(caller
//! position, callee position, label)`, with any number of arcs into a
//! position; composition is the textbook definition over all pairs of arcs;
//! the closure composes every pair of graphs in the set (not just a graph
//! with a call) until no new graph appears; and the criterion is checked on
//! the whole closure afterwards, with no early exit.

use std::collections::BTreeSet;

use stitchwort_core::Limits;
use stitchwort_core::ResourceError;
use stitchwort_core::budget::Budget;
use stitchwort_core::sct::{Arc, Graph, Group, Label, MAX_GRAPHS, Outcome};

use Label::{Le, Lt};

/// A call: `(caller, callee, arcs)`, each arc `(caller position, callee
/// position, label)`.
type Call = (usize, usize, Vec<(usize, usize, Label)>);

/// A group: the members' arities and the calls between them.
#[derive(Clone, Debug)]
struct Spec {
    arities: Vec<usize>,
    calls: Vec<Call>,
}

// The reference implementation

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct RefGraph {
    from: usize,
    to: usize,
    arcs: BTreeSet<(usize, usize, Label)>,
}

impl RefGraph {
    /// A `<` arc makes a `≤` arc between the same positions redundant.
    fn normalised(from: usize, to: usize, arcs: BTreeSet<(usize, usize, Label)>) -> RefGraph {
        let arcs = arcs
            .iter()
            .copied()
            .filter(|&(i, j, l)| l == Lt || !arcs.contains(&(i, j, Lt)))
            .collect();
        RefGraph { from, to, arcs }
    }

    fn compose(&self, other: &RefGraph) -> Option<RefGraph> {
        if self.to != other.from {
            return None;
        }
        let mut arcs = BTreeSet::new();
        for &(i, j, l1) in &self.arcs {
            for &(j2, k, l2) in &other.arcs {
                if j == j2 {
                    arcs.insert((i, k, if l1 == Lt || l2 == Lt { Lt } else { Le }));
                }
            }
        }
        Some(RefGraph::normalised(self.from, other.to, arcs))
    }
}

fn ref_graph(call: &Call) -> RefGraph {
    RefGraph::normalised(call.0, call.1, call.2.iter().copied().collect())
}

/// The reference closure: every composition of every pair, until nothing new.
fn ref_closure(spec: &Spec) -> BTreeSet<RefGraph> {
    let mut set: BTreeSet<RefGraph> = spec.calls.iter().map(ref_graph).collect();
    loop {
        let mut new = Vec::new();
        for a in &set {
            for b in &set {
                if let Some(c) = a.compose(b)
                    && !set.contains(&c)
                {
                    new.push(c);
                }
            }
        }
        if new.is_empty() {
            return set;
        }
        set.extend(new);
    }
}

fn ref_terminates(spec: &Spec) -> bool {
    ref_closure(spec).iter().all(|g| {
        g.from != g.to
            || g.compose(g).as_ref() != Some(g)
            || g.arcs.iter().any(|&(i, j, l)| i == j && l == Lt)
    })
}

/// A production graph as a set of arcs.
fn as_ref_graph(g: &Graph) -> RefGraph {
    let arcs = g
        .entries()
        .iter()
        .enumerate()
        .filter_map(|(j, e)| e.map(|a| (a.from, j, a.label)))
        .collect();
    RefGraph {
        from: g.from,
        to: g.to,
        arcs,
    }
}

// Running the module

fn group(spec: &Spec) -> Group {
    let mut group = Group::new(spec.arities.clone());
    for (from, to, arcs) in &spec.calls {
        group.call(*from, *to, arcs).expect("a well-formed call");
    }
    group
}

/// Checks the group, and checks any witness: a cycle of calls that composes
/// to an idempotent graph with no strict diagonal arc.
fn outcome(spec: &Spec) -> Outcome {
    let group = group(spec);
    let outcome = group
        .check(&Budget::default(), MAX_GRAPHS)
        .expect("no limits");
    if let Outcome::NoDescent { path, graph } = &outcome {
        let calls = group.calls();
        let first = &calls[path[0]];
        let composed = path[1..].iter().fold(first.clone(), |acc, &c| {
            acc.compose(&calls[c]).expect("the path is connected")
        });
        assert_eq!(&composed, graph, "the witness path composes to its graph");
        // Checked by the reference, not the module's own methods.
        let g = as_ref_graph(graph);
        assert_eq!(g.from, g.to, "the witness is a loop");
        assert_eq!(g.compose(&g), Some(g.clone()), "the witness is idempotent");
        assert!(
            !g.arcs.iter().any(|&(i, j, l)| i == j && l == Lt),
            "the witness has no strict diagonal arc"
        );
    }
    outcome
}

fn terminates(spec: &Spec) -> bool {
    outcome(spec) == Outcome::Terminates
}

/// Production and reference agree.
fn agree(spec: &Spec) {
    assert_eq!(
        terminates(spec),
        ref_terminates(spec),
        "production and reference disagree on {spec:?}"
    );
}

// Generating graphs

/// Every graph from arity `m` to arity `n` with at most one arc into each
/// callee position.
fn all_graphs(m: usize, n: usize) -> Vec<Vec<(usize, usize, Label)>> {
    let mut out = vec![Vec::new()];
    for j in 0..n {
        let mut next = Vec::new();
        for arcs in &out {
            next.push(arcs.clone());
            for i in 0..m {
                for l in [Le, Lt] {
                    let mut arcs = arcs.clone();
                    arcs.push((i, j, l));
                    next.push(arcs);
                }
            }
        }
        out = next;
    }
    out
}

/// xorshift64*: tiny, deterministic, good enough for generating test cases.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn label(&mut self) -> Label {
        if self.below(2) == 0 { Le } else { Lt }
    }

    /// Arcs from arity `m` to arity `n`: at most one into each position
    /// unless `multi`, when there may be several.
    fn arcs(&mut self, m: usize, n: usize, multi: bool) -> Vec<(usize, usize, Label)> {
        let mut arcs = Vec::new();
        if m == 0 {
            return arcs;
        }
        for j in 0..n {
            let count = if multi { self.below(3) } else { self.below(2) };
            for _ in 0..count {
                arcs.push((self.below(m), j, self.label()));
            }
        }
        arcs
    }

    fn spec(&mut self, members: usize, max_arity: usize, max_calls: usize, multi: bool) -> Spec {
        let arities: Vec<usize> = (0..members).map(|_| self.below(max_arity + 1)).collect();
        let calls = (0..1 + self.below(max_calls))
            .map(|_| {
                let (f, g) = (self.below(members), self.below(members));
                (f, g, self.arcs(arities[f], arities[g], multi))
            })
            .collect();
        Spec { arities, calls }
    }
}

// Comparison with the reference

/// Every set of up to three calls between two members of arity at most 2.
/// That's about 230 000 groups: a few seconds optimised, but over a minute
/// in a debug build, which checks every seventh three-call group instead.
/// (`nix flake check` runs the tests optimised, so all of them.)
#[test]
fn agrees_with_the_reference_on_every_small_group() {
    let stride = if cfg!(debug_assertions) { 7 } else { 1 };
    let mut checked = 0;
    for a0 in 0..=2 {
        for a1 in 0..=2 {
            let arities = vec![a0, a1];
            let mut calls: Vec<Call> = Vec::new();
            for f in 0..2 {
                for g in 0..2 {
                    for arcs in all_graphs(arities[f], arities[g]) {
                        calls.push((f, g, arcs));
                    }
                }
            }
            let n = calls.len();
            let spec = |picked: &[usize]| Spec {
                arities: arities.clone(),
                calls: picked.iter().map(|&i| calls[i].clone()).collect(),
            };
            agree(&spec(&[]));
            for x in 0..n {
                agree(&spec(&[x]));
                for y in x..n {
                    agree(&spec(&[x, y]));
                    for z in y..n {
                        if (x + y + z) % stride == 0 {
                            agree(&spec(&[x, y, z]));
                            checked += 1;
                        }
                    }
                }
            }
        }
    }
    assert!(
        checked > 200_000 / stride,
        "only {checked} three-call groups"
    );
}

#[test]
fn agrees_with_the_reference_on_random_groups() {
    let mut rng = Rng(0x5eed_0001);
    let (mut accepted, mut rejected) = (0, 0);
    for _ in 0..3000 {
        let spec = rng.spec(3, 3, 6, false);
        agree(&spec);
        if terminates(&spec) {
            accepted += 1;
        } else {
            rejected += 1;
        }
    }
    // Both verdicts are well represented, so agreement means something.
    assert!(
        accepted > 300 && rejected > 300,
        "{accepted} accepted, {rejected} rejected"
    );
}

/// Given several arcs into one position, the module keeps only the strongest.
/// That can lose information, so it may reject what the reference accepts,
/// but never the other way round.
#[test]
fn keeping_one_arc_per_position_is_conservative() {
    let mut rng = Rng(0x5eed_0002);
    let mut differ = 0;
    for _ in 0..3000 {
        let spec = rng.spec(3, 3, 5, true);
        let (ours, theirs) = (terminates(&spec), ref_terminates(&spec));
        assert!(
            !ours || theirs,
            "accepted, but the reference rejects {spec:?}"
        );
        differ += usize::from(ours != theirs);
    }
    assert!(differ > 0, "the multi-arc cases never mattered");
}

#[test]
fn keeps_the_strongest_arc_into_a_position() {
    let g = Graph::new(0, 2, 0, 1, &[(0, 0, Le), (1, 0, Lt), (0, 0, Lt)]).unwrap();
    assert_eq!(g.entries(), [Some(Arc { from: 1, label: Lt })]);
    let g = Graph::new(0, 2, 0, 1, &[(1, 0, Le), (0, 0, Le)]).unwrap();
    assert_eq!(g.entries(), [Some(Arc { from: 1, label: Le })]);
    // Out of range.
    assert!(Graph::new(0, 1, 0, 1, &[(1, 0, Le)]).is_none());
    assert!(Graph::new(0, 1, 0, 1, &[(0, 1, Le)]).is_none());
    let mut group = Group::new(vec![1]);
    assert!(group.call(0, 1, &[]).is_none());
    assert!(group.calls().is_empty());
}

// Properties

fn random_graph(rng: &mut Rng, from: usize, m: usize, to: usize, n: usize) -> Graph {
    Graph::new(from, m, to, n, &rng.arcs(m, n, false)).unwrap()
}

#[test]
fn composition_is_associative_and_matches_the_reference() {
    let mut rng = Rng(0x5eed_0003);
    for _ in 0..5000 {
        let ar: Vec<usize> = (0..4).map(|_| rng.below(4)).collect();
        let a = random_graph(&mut rng, 0, ar[0], 1, ar[1]);
        let b = random_graph(&mut rng, 1, ar[1], 2, ar[2]);
        let c = random_graph(&mut rng, 2, ar[2], 3, ar[3]);
        let ab = a.compose(&b).unwrap();
        let bc = b.compose(&c).unwrap();
        assert_eq!(ab.compose(&c), a.compose(&bc));
        assert_eq!(ab.entries().len(), ar[2]);
        assert_eq!(ab.from_arity(), ar[0]);
        assert_eq!(
            Some(as_ref_graph(&ab)),
            as_ref_graph(&a).compose(&as_ref_graph(&b))
        );
        // Only matching graphs compose.
        assert_eq!(a.compose(&c), None);
        assert_eq!(b.compose(&a), None);
    }
}

/// Renames the members by `members`, and each member's parameter positions
/// by its permutation in `positions`.
fn rename(spec: &Spec, members: &[usize], positions: &[Vec<usize>]) -> Spec {
    let mut arities = vec![0; spec.arities.len()];
    for (m, &a) in spec.arities.iter().enumerate() {
        arities[members[m]] = a;
    }
    let calls = spec
        .calls
        .iter()
        .map(|(f, g, arcs)| {
            let arcs = arcs
                .iter()
                .map(|&(i, j, l)| (positions[*f][i], positions[*g][j], l))
                .collect();
            (members[*f], members[*g], arcs)
        })
        .collect();
    Spec { arities, calls }
}

fn permutation(rng: &mut Rng, n: usize) -> Vec<usize> {
    let mut p: Vec<usize> = (0..n).collect();
    for i in (1..n).rev() {
        p.swap(i, rng.below(i + 1));
    }
    p
}

#[test]
fn the_verdict_is_invariant_under_renaming() {
    let mut rng = Rng(0x5eed_0004);
    for _ in 0..2000 {
        let spec = rng.spec(3, 3, 6, false);
        let members = permutation(&mut rng, 3);
        let positions: Vec<Vec<usize>> = spec
            .arities
            .iter()
            .map(|&a| permutation(&mut rng, a))
            .collect();
        let renamed = rename(&spec, &members, &positions);
        assert_eq!(
            terminates(&spec),
            terminates(&renamed),
            "{spec:?} vs {renamed:?}"
        );
    }
}

/// Weakening a `<` to `≤`, removing an arc or adding a call never turns a
/// rejection into an acceptance.
#[test]
fn weakening_is_conservative() {
    let mut rng = Rng(0x5eed_0005);
    let mut flipped = 0;
    for _ in 0..3000 {
        let spec = rng.spec(3, 3, 5, false);
        let mut weaker = spec.clone();
        let c = rng.below(weaker.calls.len());
        let arcs = &mut weaker.calls[c].2;
        match rng.below(3) {
            0 if !arcs.is_empty() => {
                let k = rng.below(arcs.len());
                arcs[k].2 = Le;
            }
            1 if !arcs.is_empty() => {
                arcs.remove(rng.below(arcs.len()));
            }
            _ => {
                let (f, g) = (rng.below(3), rng.below(3));
                let arcs = rng.arcs(spec.arities[f], spec.arities[g], false);
                weaker.calls.push((f, g, arcs));
            }
        }
        let (strong, weak) = (terminates(&spec), terminates(&weaker));
        assert!(!weak || strong, "{weaker:?} accepted but {spec:?} rejected");
        flipped += usize::from(strong && !weak);
    }
    assert!(flipped > 100, "weakening rarely mattered: {flipped}");
}

// Programs (docs/proposals/mutual-recursion.md §6.8)

/// Arcs, as in [`Call`].
type Arcs<'a> = &'a [(usize, usize, Label)];

fn spec(arities: &[usize], calls: &[(usize, usize, Arcs)]) -> Spec {
    Spec {
        arities: arities.to_vec(),
        calls: calls
            .iter()
            .map(|(f, g, arcs)| (*f, *g, arcs.to_vec()))
            .collect(),
    }
}

fn accepts(spec: &Spec) {
    agree(spec);
    assert_eq!(outcome(spec), Outcome::Terminates, "{spec:?}");
}

/// Rejects, with a witness going through these calls (in some rotation).
fn rejects(spec: &Spec, cycle: &[usize]) {
    agree(spec);
    let Outcome::NoDescent { path, .. } = outcome(spec) else {
        panic!("accepted {spec:?}");
    };
    let rotations: Vec<Vec<usize>> = (0..cycle.len())
        .map(|r| cycle[r..].iter().chain(&cycle[..r]).copied().collect())
        .collect();
    assert!(
        rotations.contains(&path),
        "witness {path:?}, expected {cycle:?}"
    );
}

#[test]
fn even_and_odd() {
    // even (Succ n) = odd n; odd (Succ n) = even n
    accepts(&spec(
        &[1, 1],
        &[(0, 1, &[(0, 0, Lt)]), (1, 0, &[(0, 0, Lt)])],
    ));
}

#[test]
fn a_wrapper_that_does_not_decrease() {
    // countdown n = step n; step (Succ n) = countdown n
    accepts(&spec(
        &[1, 1],
        &[(0, 1, &[(0, 0, Le)]), (1, 0, &[(0, 0, Lt)])],
    ));
}

#[test]
fn ackermann() {
    // ack (Succ m) Zero = ack m 1
    // ack (Succ m) (Succ n) = ack m (ack (Succ m) n)
    accepts(&spec(
        &[2],
        &[
            (0, 0, &[(0, 0, Lt)]),
            (0, 0, &[(0, 0, Lt)]),
            (0, 0, &[(0, 0, Le), (1, 1, Lt)]),
        ],
    ));
}

#[test]
fn swapped_arguments() {
    // f (Succ x) y = f y x
    let s = spec(&[2], &[(0, 0, &[(0, 1, Lt), (1, 0, Le)])]);
    accepts(&s);
    // The call's own graph isn't idempotent; its square is, and decreases.
    let g = group(&s).calls()[0].clone();
    let g = &g;
    assert!(!g.is_idempotent() && !g.has_strict_diagonal());
    let g2 = g.compose(g).unwrap();
    assert!(g2.is_idempotent() && g2.has_strict_diagonal());
}

#[test]
fn passing_arguments_along_is_rejected() {
    // ping n = pong n; pong n = ping n
    rejects(
        &spec(&[1, 1], &[(0, 1, &[(0, 0, Le)]), (1, 0, &[(0, 0, Le)])]),
        &[0, 1],
    );
}

#[test]
fn alternating_growth_is_rejected() {
    // f (Succ x) y = g x (Succ y); g x (Succ y) = f (Succ (Succ x)) y
    rejects(
        &spec(&[2, 2], &[(0, 1, &[(0, 0, Lt)]), (1, 0, &[(1, 1, Lt)])]),
        &[0, 1],
    );
}

/// Two calls of one function, each decreasing a different argument, are two
/// graphs. Merged into one, they would claim both arguments decrease.
#[test]
fn alternatives_are_not_merged() {
    // f (Succ x) y = f x (Succ y); f x (Succ y) = f (Succ x) y
    let s = spec(&[2], &[(0, 0, &[(0, 0, Lt)]), (0, 0, &[(1, 1, Lt)])]);
    rejects(&s, &[0, 1]);
    assert_eq!(group(&s).calls().len(), 2);
    let merged = spec(&[2], &[(0, 0, &[(0, 0, Lt), (1, 1, Lt)])]);
    accepts(&merged);
}

#[test]
fn rebuilding_the_parameter_is_rejected() {
    // a (Succ n) = b (Succ n); b (Succ n) = a (Succ n)
    rejects(
        &spec(&[1, 1], &[(0, 1, &[(0, 0, Le)]), (1, 0, &[(0, 0, Le)])]),
        &[0, 1],
    );
    // a (Succ n) = b n (a (Succ n)): the inner call is a `≤` loop on `a`.
    rejects(
        &spec(&[1, 2], &[(0, 1, &[(0, 0, Lt)]), (0, 0, &[(0, 0, Le)])]),
        &[1],
    );
}

#[test]
fn cycles_through_arity_zero_are_rejected() {
    // c = d; d = c
    rejects(&spec(&[0, 0], &[(0, 1, &[]), (1, 0, &[])]), &[0, 1]);
    // c = c
    rejects(&spec(&[0], &[(0, 0, &[])]), &[0]);
    // f (Succ n) = c; c = f 0: decreasing into `c` doesn't help.
    rejects(&spec(&[1, 0], &[(0, 1, &[]), (1, 0, &[])]), &[0, 1]);
    // …even alongside a decreasing self-call.
    let s = spec(&[1, 0], &[(0, 0, &[(0, 0, Lt)]), (0, 1, &[]), (1, 0, &[])]);
    rejects(&s, &[1, 2]);
}

#[test]
fn non_square_composition() {
    // Arities 1, 2 and 3 in one chain, and back.
    let a = Graph::new(0, 1, 1, 2, &[(0, 0, Le), (0, 1, Lt)]).unwrap();
    let b = Graph::new(1, 2, 2, 3, &[(1, 0, Le), (0, 2, Le)]).unwrap();
    let c = Graph::new(2, 3, 0, 1, &[(2, 0, Le)]).unwrap();
    let ab = a.compose(&b).unwrap();
    let la = |i| Some(Arc { from: i, label: Lt });
    let le = |i| Some(Arc { from: i, label: Le });
    assert_eq!(ab.entries(), [la(0), None, le(0)]);
    let abc = ab.compose(&c).unwrap();
    assert_eq!(abc.entries(), [le(0)]);
    assert_eq!((abc.from, abc.to), (0, 0));
    // The group: the loop 0 → 1 → 2 → 0 only rebuilds its parameter.
    let s = spec(
        &[1, 2, 3],
        &[
            (0, 1, &[(0, 0, Le), (0, 1, Lt)]),
            (1, 2, &[(1, 0, Le), (0, 2, Le)]),
            (2, 0, &[(2, 0, Le)]),
        ],
    );
    rejects(&s, &[0, 1, 2]);
    // With the last call taking the strictly smaller argument, it decreases.
    let s = spec(
        &[1, 2, 3],
        &[
            (0, 1, &[(0, 0, Le), (0, 1, Lt)]),
            (1, 2, &[(1, 0, Le), (0, 2, Le)]),
            (2, 0, &[(0, 0, Le)]),
        ],
    );
    accepts(&s);
}

#[test]
fn unknown_entries_stay_unknown() {
    // Composing through an unknown entry gives unknown, not `≤`.
    let a = Graph::new(0, 1, 0, 2, &[(0, 0, Lt)]).unwrap();
    assert_eq!(a.entries()[1], None);
    let b = Graph::new(0, 2, 0, 1, &[(1, 0, Le)]).unwrap();
    assert_eq!(a.compose(&b).unwrap().entries(), [None]);
    // A call with every entry unknown, looping: rejected.
    rejects(&spec(&[2], &[(0, 0, &[])]), &[0]);
}

#[test]
fn no_identity_graphs_are_added() {
    // No calls, or calls that don't loop: nothing to check, so accepted. An
    // identity graph in the closure would be idempotent with no `<`.
    accepts(&spec(&[2], &[]));
    accepts(&spec(&[1, 1], &[(0, 1, &[(0, 0, Le)])]));
    let group = group(&spec(&[1, 1], &[(0, 1, &[(0, 0, Le)])]));
    assert_eq!(
        group.check(&Budget::default(), MAX_GRAPHS),
        Ok(Outcome::Terminates)
    );
}

// Resources

fn ackermann_group() -> Group {
    group(&spec(
        &[2],
        &[(0, 0, &[(0, 0, Lt)]), (0, 0, &[(0, 0, Le), (1, 1, Lt)])],
    ))
}

#[test]
fn running_out_is_inconclusive() {
    let budget = Budget::default();
    let group = ackermann_group();
    assert_eq!(group.check(&budget, MAX_GRAPHS), Ok(Outcome::Terminates));
    {
        let _op = budget.operation(Limits {
            work: 1,
            ..Limits::default()
        });
        assert_eq!(group.check(&budget, MAX_GRAPHS), Err(ResourceError::Work));
    }
    assert_eq!(group.check(&budget, 1), Err(ResourceError::Work));
    // Enough of both.
    let _op = budget.operation(Limits::default());
    assert_eq!(group.check(&budget, 100), Ok(Outcome::Terminates));
}
