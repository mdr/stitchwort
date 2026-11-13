//! Stage 2's recall on real goals (SW-915; docs/proposals/search.md §8
//! S2b, review point 5): each std theorem whose proof is one lemma applied
//! (`theorem t (…): … := L a b h`) gives a goal, its statement with its
//! parameters as hypotheses, and a lemma known to close it. `search --at`
//! must find a kernel-checked closer (any) for most of them, and the
//! lemma itself among the closers for many. The theorem itself is left out
//! of the candidates.
//!
//! Every theorem in the all tier (minutes); every 25th in broad; none in
//! the quick and lane tiers, which run `search_at` instead.

use stitchwort_core::{DefId, Name, Term};
use stitchwort_driver::driver::{Session, Tier, tier, with_session};
use stitchwort_driver::search::Scope;
use stitchwort_driver::search_at::{AtOptions, FoundGoal};
use stitchwort_elab::search::Item;
use stitchwort_syntax::{GoalData, Hypothesis};

const STACK: usize = 64 * 1024 * 1024;

/// The lemma a theorem's proof applies, if its whole proof is one
/// application of another theorem (after its parameters' lambdas) to the
/// theorem's own variables, or to closers stage 2 tries (`rfl`): the goals
/// stage 2 is for. Not a helper (`%`), and not a lemma whose conclusion
/// names nothing (`Eq.trans`, `Eq.cong`), which needs a middle term.
fn applied_lemma(session: &Session, id: DefId) -> Option<DefId> {
    let g = &session.elab.ev();
    let def = g.def(id);
    let mut body: &Term = def.body()?.strip_loc();
    let mut ty = def.ty().strip_loc();
    while let (Term::Lam(_, _, b), Term::Pi(_, _, _, cod)) = (body, ty) {
        body = b.strip_loc();
        ty = cod.strip_loc();
    }
    let (head, args) = body.spine();
    let simple = args.iter().all(|a| {
        matches!(a.strip_loc(), Term::Var(_) | Term::Refl)
            || !matches!(a.strip_loc(), Term::App(..) | Term::Lam(..))
    });
    match head.strip_loc() {
        Term::Def(l)
            if *l != id
                && simple
                && !args.is_empty()
                && g.def(*l).theorem()
                && !g.def(*l).path().contains('%')
                // The reflective tactics' own lemmas take a certificate.
                && !g.def(*l).path().starts_with("Std.Ring.")
                && !g.def(*l).path().starts_with("Std.Omega.")
                && names_something(g.def(*l).ty()) =>
        {
            Some(*l)
        }
        _ => None,
    }
}

/// Whether type `ty`'s conclusion names a definition or a data type.
fn names_something(ty: &Term) -> bool {
    let mut t = ty.strip_loc();
    while let Term::Pi(_, _, _, cod) = t {
        t = cod.strip_loc();
    }
    t.subterms()
        .any(|(s, _)| matches!(s, Term::Def(_) | Term::Data(..) | Term::Ctor(..)))
}

/// The goal of theorem `id`'s statement, as `search --at` would read it: its
/// parameters as hypotheses, printed as the session's scope writes them.
fn goal_of(session: &Session, id: DefId) -> Option<FoundGoal> {
    let g = &session.elab.ev();
    let mut names: Vec<Name> = Vec::new();
    let mut hypotheses = Vec::new();
    let mut t = g.def(id).ty().strip_loc();
    while let Term::Pi(name, _, dom, cod) = t {
        let ty = stitchwort_core::pretty::term_in(g, &session.elab, &names, dom);
        let mut fresh = name.to_string();
        if fresh == "_" || fresh.is_empty() || names.iter().any(|n| **n == *fresh) {
            fresh = format!("x{}", names.len());
        }
        hypotheses.push(Hypothesis {
            name: fresh.clone(),
            ty,
            value: None,
            splits: None,
        });
        names.push(fresh.as_str().into());
        t = cod.strip_loc();
    }
    let target = stitchwort_core::pretty::term_in(g, &session.elab, &names, t);
    let unwritable = |s: &str| s.contains(['%', '✝', '?', '…', '\n']);
    if unwritable(&target) || hypotheses.iter().any(|h| unwritable(&h.ty)) {
        return None;
    }
    Some(FoundGoal {
        line: 0,
        column: 0,
        index: 1,
        span: (0, 0),
        file: None,
        data: GoalData {
            hypotheses,
            target,
            written: None,
            prop: Some(true),
            lemma: Some(String::new()),
        },
    })
}

/// Whether the run takes theorem `path`: with `SEARCH_AT_BENCH_ONLY` set
/// to a comma-separated list of theorems, only those, for narrowing a
/// failure down without the whole run (which takes minutes).
fn wanted(path: &str) -> bool {
    std::env::var("SEARCH_AT_BENCH_ONLY").map_or(true, |only| only.split(',').any(|p| p == path))
}

/// What a run found.
struct Recall {
    goals: usize,
    closed: usize,
    lemma_found: usize,
    lemma_first: usize,
    lemma_top5: usize,
    with_lemma: usize,
}

/// Runs stage 2 on the statement of each theorem `pick` selects (every
/// `stride`-th), with the lemma its proof applies, if one is known.
fn run(
    label: &str,
    stride: usize,
    pick: &(dyn Fn(&Session, DefId) -> Option<Option<DefId>> + Sync),
) -> Recall {
    with_session(STACK, Session::for_stack, |session| {
        session.use_check_cache(
            &std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("search-cache"),
        );
        session
            .elab
            .load_all_libraries()
            .expect("the library checks");
        session.import_library_namespaces();
        let g = &session.elab.ev();
        let picked: Vec<(DefId, Option<DefId>)> = (0..g.env.defs().len())
            .map(DefId)
            .filter(|id| g.def(*id).theorem() && g.def(*id).path().starts_with("Std."))
            .filter(|id| !g.def(*id).path().contains('%') && !session.elab.is_unfinished(*id))
            .filter_map(|id| Some((id, pick(session, id)?)))
            .step_by(stride)
            .collect();
        let mut r = Recall {
            goals: 0,
            closed: 0,
            lemma_found: 0,
            lemma_first: 0,
            lemma_top5: 0,
            with_lemma: 0,
        };
        let mut unopened = 0;
        let mut missed = Vec::new();
        let started = std::time::Instant::now();
        for (theorem, lemma) in picked {
            let Some(found) = goal_of(session, theorem) else {
                continue;
            };
            let g = &session.elab.ev();
            let theorem_path = g.def(theorem).path().to_string();
            if !wanted(&theorem_path) {
                continue;
            }
            // Named before the search, so a panic in it says which goal.
            if std::env::var_os("SEARCH_AT_BENCH_TRACE").is_some() {
                eprintln!("goal: {theorem_path}");
            }
            let lemma_path = lemma.map(|l| Item::Def(l).path(g));
            let options = AtOptions {
                exclude: vec![theorem_path.clone()],
                ..AtOptions::default()
            };
            r.goals += 1;
            let Ok(report) = session.search_at(&found, "std", &options, &Scope::File, None) else {
                unopened += 1;
                continue;
            };
            let closing: Vec<_> = (report.results.iter())
                .filter(|s| s.class != "applicable")
                .collect();
            if !closing.is_empty() || !report.tactics.is_empty() {
                r.closed += 1;
            }
            let Some(lemma_path) = lemma_path else {
                continue;
            };
            r.with_lemma += 1;
            match closing.iter().position(|s| s.name == lemma_path) {
                Some(i) => {
                    r.lemma_found += 1;
                    r.lemma_first += usize::from(i == 0);
                    r.lemma_top5 += usize::from(i < 5);
                }
                None => missed.push(format!("{theorem_path} (by {lemma_path})")),
            }
        }
        let share = |n: usize, of: usize| 100.0 * n as f64 / of.max(1) as f64;
        eprintln!(
            "{label}: {} goals ({:.0} s, {unopened} couldn't be opened): a kernel-checked closer \
             (or a tactic alone) for {:.1}%",
            r.goals,
            started.elapsed().as_secs_f64(),
            share(r.closed, r.goals),
        );
        if r.with_lemma > 0 {
            eprintln!(
                "  the lemma the proof applies among the closers: {:.1}%, first {:.1}%, in the first 5 {:.1}%",
                share(r.lemma_found, r.with_lemma),
                share(r.lemma_first, r.with_lemma),
                share(r.lemma_top5, r.with_lemma),
            );
        }
        for m in missed.iter().take(25) {
            eprintln!("  lemma not among the closers: {m}");
        }
        r
    })
}

/// Theorems proved by one lemma applied to their variables: the lemma
/// must be found, checked, for most.
#[test]
fn stage_two_closes_std_goals_with_their_lemma() {
    let stride = match tier() {
        Tier::Lane | Tier::Quick => {
            eprintln!("skipped: broad and all tiers only");
            return;
        }
        Tier::Broad => 4,
        Tier::All => 1,
    };
    let r = run("std theorems proved by one lemma", stride, &|s, id| {
        applied_lemma(s, id).map(Some)
    });
    assert!(r.goals > 0);
    assert!(
        r.lemma_found * 100 >= r.with_lemma * 45,
        "the lemma was among the closers for too few goals"
    );
}

/// Every std theorem's statement as a goal (all tier, a sample): how often
/// something other than the theorem itself closes it. Reported, not
/// asserted beyond a floor: most theorems are new facts.
#[test]
fn stage_two_on_any_std_statement() {
    if tier() != Tier::All {
        eprintln!("skipped: all tier only");
        return;
    }
    let r = run("std statements (every 10th)", 10, &|_, _| Some(None));
    assert!(r.goals > 100);
}
