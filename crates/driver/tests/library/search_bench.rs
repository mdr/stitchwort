//! The benchmarks of `stitchwort search` (docs/proposals/search.md draft 3
//! §6, S1c), as tests over the whole standard library:
//! - self-retrieval: each theorem's own conclusion, and each equation's (and
//!   `Iff`'s) left side, with its variables as holes, must find it, with no
//!   internal error, and put it first (strictly, ties broken by name) for at
//!   least 86% of conclusions and 78% of left sides;
//! - proof uses (all tier only): each lemma used in a std proof, searched
//!   for with the statement it proved there, the proof's variables as holes;
//!   it must be among the first ten for at least half of them.
//!
//! The quick and lane tiers take the theorems whose qualified name hashes to
//! a multiple of 8 (about 300 queries each, with two points of margin on the
//! shares: [`bar`]), so adding a theorem to std adds at most itself to the
//! sample and doesn't reshuffle the rest, as every 8th by declaration order
//! did; the broad tier all of them (about 7 s and 4 s); proof uses take minutes, so only the all tier
//! runs them. The hand queries (draft 3 §6.3) run in every tier.

use std::collections::{BTreeMap, BTreeSet};

use stitchwort_core::{DataId, DefId, Term};
use stitchwort_driver::driver::{Session, Tier, all_tier, tier, with_session};
use stitchwort_elab::search::{Candidate, Item, Kind, Mode, Opts, Pattern, Side};

const STACK: usize = 64 * 1024 * 1024;

/// Loads the whole library, through a check cache the tests of this binary
/// share (the first fills it; writes are atomic).
fn load_library(session: &mut Session) {
    session
        .use_check_cache(&std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("search-cache"));
    session
        .elab
        .load_all_libraries()
        .expect("the library checks");
    // The core's equations, as `search` makes them before it lists.
    session
        .elab
        .generate_deferred_equations()
        .expect("the core's equations");
}

/// What a benchmark found.
#[derive(Default, Debug)]
struct Score {
    queries: usize,
    /// Queries whose theorem was found, and where (1 = first, ties broken
    /// by name, as a client sees them).
    ranks: Vec<usize>,
    missed: Vec<String>,
    internal_errors: usize,
    out_of_budget: usize,
}

impl Score {
    fn share(&self, f: impl Fn(usize) -> bool) -> f64 {
        100.0 * self.ranks.iter().filter(|r| f(**r)).count() as f64 / self.queries.max(1) as f64
    }

    fn report(&self, what: &str) {
        let mrr =
            self.ranks.iter().map(|r| 1.0 / *r as f64).sum::<f64>() / self.queries.max(1) as f64;
        eprintln!(
            "{what}: {} queries, {} not found; strict top-1 {:.1}%, MRR {mrr:.3}, recall@5 {:.1}%, recall@10 {:.1}%; {} out of budget, {} internal errors",
            self.queries,
            self.missed.len(),
            self.share(|r| r == 1),
            self.share(|r| r <= 5),
            self.share(|r| r <= 10),
            self.out_of_budget,
            self.internal_errors,
        );
        for name in self.missed.iter().take(20) {
            eprintln!("  not found: {name}");
        }
    }
}

/// The library's theorems, as search candidates (helpers left out).
fn theorems(session: &Session) -> Vec<Candidate> {
    let g = &session.elab.ev();
    session
        .elab
        .search_candidates(&|item, path| item.kind(g) == Kind::Theorem && !path.contains('%'))
}

fn iff(g: &stitchwort_core::Ev) -> Option<DataId> {
    (0..g.env.datas().len())
        .map(DataId)
        .find(|d| &**g.data(*d).path() == "Std.Iff")
}

/// FNV-1a, 64 bits: a hash fixed by its definition, the same on every Rust
/// version and platform (`DefaultHasher` is neither).
fn fnv1a(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf29ce484222325, |h, b| {
        (h ^ u64::from(*b)).wrapping_mul(0x100000001b3)
    })
}

/// The sample of `items` (each with its fully qualified name) this tier
/// runs: the items whose name hashes to a multiple of the stride.
fn sample<T>(items: Vec<(String, T)>) -> Vec<T> {
    let stride = match tier() {
        Tier::Quick | Tier::Lane => 8,
        Tier::Broad | Tier::All => 1,
    };
    (items.into_iter())
        .filter(|(name, _)| fnv1a(name.as_bytes()).is_multiple_of(stride))
        .map(|(_, item)| item)
        .collect()
}

/// The least strict top-1 share a benchmark must reach: `whole` over every
/// theorem (the broad tier), two points less on the quick and lane tiers'
/// sample of about 300, where one query moves the share by a third of a
/// point (31 Oct 2026: 87.7% of all conclusions, 86.0% of the sample).
fn bar(whole: f64) -> f64 {
    match tier() {
        Tier::Quick | Tier::Lane => whole - 2.0,
        Tier::Broad | Tier::All => whole,
    }
}

/// Searches each query's pattern over `candidates` (but `owner`, the proof a
/// use was taken from) and scores where `wanted` ranks.
fn run(
    session: &mut Session,
    candidates: &[Candidate],
    queries: &[(DefId, Option<DefId>)],
    opts: &Opts,
    make: &dyn Fn(&mut Session, usize) -> Option<Pattern>,
) -> Score {
    let mut score = Score::default();
    for (n, (wanted, owner)) in queries.iter().enumerate() {
        let Some(pattern) = make(session, n) else {
            continue;
        };
        score.queries += 1;
        let keep = |c: &Candidate| Some(c.item) != owner.map(Item::Def);
        let found = session.elab.search(&[pattern], candidates, opts, &keep);
        score.internal_errors += found.stats.internal_errors;
        score.out_of_budget += found.stats.out_of_budget;
        match found.hits.iter().position(|h| h.item == Item::Def(*wanted)) {
            Some(i) => score.ranks.push(i + 1),
            None => score
                .missed
                .push(session.elab.kernel.def(*wanted).path().to_string()),
        }
    }
    score
}

/// Every theorem's conclusion (or, `left`, its equation's left side) as a
/// pattern.
fn self_retrieval(left: bool) -> Score {
    with_session(STACK, Session::for_stack, |session| {
        load_library(session);
        let candidates = theorems(session);
        let g = &session.elab.ev();
        let iff = iff(g);
        // The written theorems: a generated equation (`f.eqK`,
        // docs/proposals/function-equations.md §7.2) is a candidate, not a
        // query.
        let queries: Vec<(DefId, Option<DefId>)> = sample(
            (candidates.iter())
                .filter(|c| !c.item.generated_equation(g))
                .filter_map(|c| match c.item {
                    Item::Def(id) => Some((g.def(id).path().to_string(), (id, None))),
                    Item::Ctor(..) | Item::Part(..) => None,
                })
                .collect(),
        );
        let opts = Opts {
            mode: if left { Mode::Rewrite } else { Mode::Plain },
            anywhere: false,
            iff,
            filter: true,
            deadline: None,
        };
        let side = if left { Side::Left } else { Side::Conclusion };
        run(session, &candidates, &queries, &opts, &|session, n| {
            session.elab.theorem_pattern(queries[n].0, side, iff)
        })
    })
}

#[test]
fn every_conclusion_finds_its_theorem() {
    let score = self_retrieval(false);
    score.report("conclusions");
    assert!(score.queries > 200, "{} queries", score.queries);
    assert_eq!(score.internal_errors, 0);
    assert!(score.missed.is_empty(), "not found: {:?}", score.missed);
    assert!(
        score.share(|r| r == 1) >= bar(86.0),
        "strict top-1 {:.1}%",
        score.share(|r| r == 1)
    );
}

#[test]
fn every_left_side_finds_its_theorem() {
    let score = self_retrieval(true);
    score.report("left sides");
    assert!(score.queries > 150, "{} queries", score.queries);
    assert_eq!(score.internal_errors, 0);
    assert!(score.missed.is_empty(), "not found: {:?}", score.missed);
    assert!(
        score.share(|r| r == 1) >= bar(78.0),
        "strict top-1 {:.1}%",
        score.share(|r| r == 1)
    );
}

/// A use of a lemma in a proof: the proof (or the theorem a helper of it
/// belongs to), the lemma, its arguments and the binders they are under.
type Use = (DefId, DefId, Vec<Term>, usize);

/// The first use of each std theorem in each std proof (and its helpers),
/// applied to all its arguments.
fn lemma_uses(g: &stitchwort_core::Ev, theorems: &BTreeSet<DefId>) -> Vec<Use> {
    let by_path: BTreeMap<String, DefId> = (theorems.iter())
        .map(|id| (g.def(*id).path().to_string(), *id))
        .collect();
    let mut uses = Vec::new();
    let mut seen: BTreeSet<(DefId, DefId)> = BTreeSet::new();
    for i in 0..g.env.defs().len() {
        let id = DefId(i);
        let def = g.def(id);
        let path = def.path().to_string();
        let owner = if theorems.contains(&id) {
            id
        } else if let Some((stem, _)) = path.split_once('%')
            && let Some(o) = by_path.get(stem)
        {
            *o
        } else {
            continue;
        };
        let Some(body) = def.body() else { continue };
        // Applications that are the function part of a larger one.
        let mut inner: BTreeSet<*const Term> = BTreeSet::new();
        for (t, _) in body.subterms() {
            if let Term::App(f, _, _) = t {
                let mut f = f.as_ref();
                loop {
                    inner.insert(f as *const Term);
                    match f {
                        Term::Loc(_, x) | Term::App(x, _, _) => f = x,
                        _ => break,
                    }
                }
            }
        }
        for (t, binders) in body.subterms() {
            if matches!(t, Term::Loc(..)) || inner.contains(&(t as *const Term)) {
                continue;
            }
            let (head, args) = t.spine();
            let Term::Def(lemma) = head else { continue };
            if !theorems.contains(lemma) || *lemma == owner {
                continue;
            }
            if seen.insert((owner, *lemma)) {
                uses.push((owner, *lemma, args.into_iter().cloned().collect(), binders));
            }
        }
    }
    uses
}

#[test]
fn proof_uses_find_their_lemma_among_the_first_ten() {
    if !all_tier("proof_uses_find_their_lemma_among_the_first_ten") {
        return;
    }
    let score = with_session(STACK, Session::for_stack, |session| {
        load_library(session);
        let candidates = theorems(session);
        let g = &session.elab.ev();
        let ids: BTreeSet<DefId> = (candidates.iter())
            .filter_map(|c| match c.item {
                Item::Def(id) => Some(id),
                Item::Ctor(..) | Item::Part(..) => None,
            })
            .collect();
        let uses = lemma_uses(g, &ids);
        let queries: Vec<(DefId, Option<DefId>)> = uses
            .iter()
            .map(|(owner, lemma, _, _)| (*lemma, Some(*owner)))
            .collect();
        let opts = Opts {
            mode: Mode::Plain,
            anywhere: false,
            iff: None,
            filter: true,
            deadline: None,
        };
        run(session, &candidates, &queries, &opts, &|session, n| {
            let (_, lemma, args, depth) = &uses[n];
            let args: Vec<&Term> = args.iter().collect();
            session.elab.use_pattern(*lemma, &args, *depth)
        })
    });
    score.report("proof uses");
    assert!(score.queries > 5000, "{} queries", score.queries);
    assert_eq!(score.internal_errors, 0);
    assert!(
        score.share(|r| r <= 10) >= 50.0,
        "recall@10 {:.1}%",
        score.share(|r| r <= 10)
    );
}

/// A proof use whose arguments mention the proof's variables inside a
/// lambda (`Bool.inspect`'s motive, in `List.takeWhile.induct`) once made the
/// evaluator apply a constructor while unifying with a candidate (SW-2590).
#[test]
fn proof_use_with_lambda_arguments_searches_without_internal_errors() {
    let (internal, hits) = with_session(STACK, Session::for_stack, |session| {
        load_library(session);
        let candidates = theorems(session);
        let g = &session.elab.ev();
        let ids: BTreeSet<DefId> = (candidates.iter())
            .filter_map(|c| match c.item {
                Item::Def(id) => Some(id),
                Item::Ctor(..) | Item::Part(..) => None,
            })
            .collect();
        let uses = lemma_uses(g, &ids);
        let wanted = uses
            .iter()
            .position(|(owner, lemma, _, _)| {
                g.def(*owner).path().to_string() == "Std.List.takeWhile.induct"
                    && g.def(*lemma).path().to_string() == "Std.Bool.inspect"
            })
            .expect("takeWhile.induct uses Bool.inspect");
        let (owner, lemma, args, depth) = &uses[wanted];
        let (owner, lemma) = (*owner, *lemma);
        let args: Vec<&Term> = args.iter().collect();
        let pattern = session
            .elab
            .use_pattern(lemma, &args, *depth)
            .expect("a pattern");
        let opts = Opts {
            mode: Mode::Plain,
            anywhere: false,
            iff: None,
            filter: true,
            deadline: None,
        };
        let keep = |c: &Candidate| Some(c.item) != Some(Item::Def(owner));
        let found = session.elab.search(&[pattern], &candidates, &opts, &keep);
        (found.stats.internal_errors, found.hits.len())
    });
    assert_eq!(internal, 0, "{hits} hits");
}

/// Draft 1's hand queries and draft 3's others (§6.3), through the command's
/// own path (`Session::search`): where each one's lemma must rank.
#[test]
fn hand_queries_rank_their_lemma() {
    use stitchwort_driver::search::{Kinds, Options, Scope};
    let theorems = Options::default();
    let definitions = Options {
        kinds: Kinds {
            theorems: false,
            definitions: true,
            constructors: false,
        },
        ..Options::default()
    };
    let rewrite = Options {
        rewrite: true,
        ..Options::default()
    };
    let cases: [(&str, &Options, &str, usize); 14] = [
        (
            "List.length ((_: List _) ++ _) = _",
            &theorems,
            "Std.List.lengthAppend",
            1,
        ),
        ("_ ∈ List.map _ _", &theorems, "Std.List.memMap", 3),
        ("Nat.min _ _ ≤ _", &theorems, "Std.Nat.minLeLeft", 1),
        ("Ord.compare ?x ?x = _", &theorems, "Std.Ord.compareSelf", 1),
        (
            "⊢ Not (Less = Greater)",
            &theorems,
            "Std.Ordering.lessNotGreater",
            1,
        ),
        (
            "(_: Nat) ≤ _ → _ ≤ _ → _ ≤ _",
            &theorems,
            "Std.Nat.leTrans",
            1,
        ),
        // Named holes under the pattern's binders (S1a).
        (
            "(?a: Nat) ≤ ?b → ?b ≤ ?c → ?a ≤ ?c",
            &theorems,
            "Std.Nat.leTrans",
            1,
        ),
        // The instance double search: `Nat`'s own lemma, and the generic one.
        (
            "Ord.compare (?x: Nat) ?x = _",
            &theorems,
            "Std.Nat.compareSelf",
            1,
        ),
        (
            "Ord.compare (?x: Nat) ?x = _",
            &theorems,
            "Std.Ord.compareSelf",
            10,
        ),
        ("List ?a → Nat → List ?a", &definitions, "Std.List.drop", 1),
        (
            "List.length (List.append _ _)",
            &rewrite,
            "Std.List.lengthAppend",
            1,
        ),
        ("List.map (List.map _ _) _", &rewrite, "Std.List.mapMap", 1),
        // One premise after explicit parameters (SW-993): an interface's
        // law, and a lemma.
        (
            "Ord.compare ?x ?y = Equal → ?x = ?y",
            &theorems,
            "Std.Ord.equal",
            1,
        ),
        ("(?a: Nat) < ?b → ?a ≤ ?b", &theorems, "Std.Nat.lessLe", 1),
    ];
    let failures = with_session(STACK, Session::for_stack, |session| {
        load_library(session);
        let mut failures = Vec::new();
        for (query, options, wanted, at_most) in cases {
            let options = Options {
                limit: usize::MAX,
                ..options.clone()
            };
            let report = session
                .search(query, &options, &Scope::Project(Vec::new()))
                .unwrap_or_else(|d| panic!("{query}: {}", d.message));
            assert_eq!(report.budget.internal_errors, 0, "{query}");
            let rank = report.results.iter().position(|r| r.name == wanted);
            if rank.is_none_or(|r| r >= at_most) {
                let first: Vec<&str> = report
                    .results
                    .iter()
                    .take(5)
                    .map(|r| r.name.as_str())
                    .collect();
                failures.push(format!(
                    "{query}: {wanted} at {rank:?} (wanted ≤ {at_most}); first {first:?}"
                ));
            }
        }
        failures
    });
    assert!(failures.is_empty(), "{failures:#?}");
}
