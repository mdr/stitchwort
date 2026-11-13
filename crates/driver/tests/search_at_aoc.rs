//! `search --at` on real proof goals (SW-915, D2100): each AoC theorem whose
//! proof is one lemma applied to plain arguments (`L a b h`, `L _ _`), or a
//! closer on its own (`rfl`, `omega`), has its proof replaced by `?` in its
//! file (in memory), and `search --at` asked about that goal, in the
//! project, as an agent would. Reported: how often a closer is found (any),
//! how often the original lemma is among the closers, its rank, and the
//! time a goal takes; and the misses, with what the search found instead.
//!
//! The all tier runs every such theorem of the AoC project; the broad tier
//! a sample, in a part of the project (`Aoc.Common` and the 2021 days) so
//! that a cold check cache costs seconds, not the minute the whole project
//! takes to check. The quick and lane tiers skip it.
//!
//! `STITCHWORT_AT_BENCH_ONLY=Year2024/Day06` limits it to the goals whose
//! file path contains that text (any tier but quick and lane).
//! `STITCHWORT_AT_BENCH_SKIP=<n>` and `STITCHWORT_AT_BENCH_LIMIT=<n>` take a
//! slice of those goals, to measure or bisect (the rate assertions then need
//! not hold).
//! `STITCHWORT_AT_BENCH_VERBOSE=1` prints each goal as it starts and, with
//! its time, as it ends, to find the slow ones while it runs.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use stitchwort_driver::driver::{Session, Tier, par_map, par_map_with_at_most, tier};
use stitchwort_driver::project::{DiskFiles, Entry, Files, project_sources};
use stitchwort_driver::search_at::{AtOptions, GoalAt, Overlay, ProjectGoal};
use stitchwort_syntax::ast::{Decl, Expr};
use stitchwort_syntax::{SourceMap, parse_module_recovering};

const STACK: usize = 64 * 1024 * 1024;

// Each goal is a fresh session of the whole library and project (about
// 600 MB), dropped after; with the system allocator macOS keeps what they
// free, and four workers passed 10 GB. Hence mimalloc, as the CLI uses.
use stitchwort_test_alloc as _;

/// A project's files, with only the source folders under `keep` (and the
/// folders above them) visible.
struct Only {
    base: DiskFiles,
    keep: Vec<String>,
}

impl Files for Only {
    fn entries(&self, dir: &str) -> std::io::Result<Vec<Entry>> {
        let shown = |name: &str| {
            let path = if dir.is_empty() {
                name.to_string()
            } else {
                format!("{dir}/{name}")
            };
            self.keep.iter().any(|k| {
                k.starts_with(&format!("{path}/"))
                    || *k == path
                    || path.starts_with(&format!("{k}/"))
            }) || !path.contains('/')
        };
        Ok(self
            .base
            .entries(dir)?
            .into_iter()
            .filter(|e| shown(&e.name))
            .collect())
    }
    fn read(&self, path: &str) -> std::io::Result<String> {
        self.base.read(path)
    }
    fn include_files(&self) -> Option<std::rc::Rc<dyn stitchwort_elab::project::IncludeFiles>> {
        self.base.include_files()
    }
}

/// A goal made from a theorem: its file, the file's text with the proof
/// replaced by `?`, where the `?` is, and what the proof was.
#[derive(Clone, Debug)]
struct Case {
    path: String,
    theorem: String,
    text: String,
    line: usize,
    column: usize,
    /// The proof as written.
    proof: String,
    /// Its head, if it applies a lemma (else it is a closer on its own).
    lemma: Option<String>,
}

const CLOSERS: &[&str] = &["rfl", "omega", "byDecision", "ring", "cases", "trivial"];

/// An argument plain enough that the proof is "one lemma applied".
fn plain(e: &Expr) -> bool {
    match e {
        Expr::Var(_) | Expr::Hole(_) | Expr::Num(..) | Expr::Unit(_) | Expr::Str(..) => true,
        Expr::Bracketed(inner, _) => plain(inner),
        _ => false,
    }
}

/// The head and arguments of an application.
fn spine(e: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut e = e;
    loop {
        match e {
            Expr::App(f, a) => {
                args.push(&**a);
                e = f;
            }
            Expr::Bracketed(inner, _) if args.is_empty() => e = inner,
            _ => break,
        }
    }
    args.reverse();
    (e, args)
}

/// The cases of one file.
fn cases_in(path: &str, text: &str) -> Vec<Case> {
    let mut sources = SourceMap::new();
    let id = sources.add(path, text);
    let (module, _) = parse_module_recovering(id, text, STACK);
    let theorems: Vec<String> = (module.decls.iter())
        .filter_map(|d| match d {
            Decl::Signature {
                name,
                theorem: true,
                ..
            } => Some(name.text.to_string()),
            _ => None,
        })
        .collect();
    let mut out = Vec::new();
    for d in &module.decls {
        let Decl::Equation {
            name,
            rhs: Some(rhs),
            arm: None,
            ..
        } = d
        else {
            continue;
        };
        if !theorems.iter().any(|t| *t == *name.text) {
            continue;
        }
        let (head, args) = spine(rhs);
        let Expr::Var(head) = head else {
            continue;
        };
        let head = head.text.to_string();
        let closer = CLOSERS.contains(&head.as_str());
        if closer && !args.is_empty() {
            continue;
        }
        if !closer && (args.is_empty() || !args.iter().all(|a| plain(a))) {
            continue;
        }
        let span = rhs.span();
        let (start, end) = (span.start as usize, span.end as usize);
        let proof = text[start..end].to_string();
        if proof.contains('\n') {
            continue;
        }
        let before = &text[..start];
        let line = before.matches('\n').count() + 1;
        let column = before.rsplit('\n').next().unwrap_or("").chars().count() + 1;
        out.push(Case {
            path: path.to_string(),
            theorem: name.text.to_string(),
            text: format!("{}?{}", &text[..start], &text[end..]),
            line,
            column,
            proof,
            lemma: (!closer).then_some(head),
        });
    }
    out
}

/// What one case found.
#[derive(Debug)]
struct Outcome {
    case: Case,
    time: Duration,
    /// Something closes it (a lemma, or a tactic alone).
    closed: bool,
    /// The original lemma's place among the closing suggestions (1-based).
    rank: Option<usize>,
    /// The original lemma is among the suggestions that leave goals, or the
    /// rewrites.
    elsewhere: Option<&'static str>,
    /// What closes it instead (the first suggestion), or why nothing was
    /// searched.
    note: String,
    rejected_in_file: usize,
}

fn same_lemma(name: &str, proof: &str, head: &str) -> bool {
    name == head
        || name.ends_with(&format!(".{head}"))
        || proof.split_whitespace().next() == Some(head)
}

fn run(case: &Case, files: &dyn Files, cache: &Path) -> Outcome {
    let started = Instant::now();
    if std::env::var_os("STITCHWORT_AT_BENCH_VERBOSE").is_some() {
        eprintln!("start {}:{} {}", case.path, case.line, case.theorem);
    }
    let overlay = Overlay {
        base: files,
        texts: BTreeMap::from([(case.path.clone(), case.text.clone())]),
    };
    let goal = ProjectGoal {
        project: "aoc",
        files: &overlay,
        path: &case.path,
        cache: Some(cache),
        at: GoalAt::Line(case.line, Some(case.column)),
    };
    let mut session = Session::for_stack(STACK);
    let found = session.search_at_project(&goal, &AtOptions::default());
    drop(session);
    let time = started.elapsed();
    if std::env::var_os("STITCHWORT_AT_BENCH_VERBOSE").is_some() {
        eprintln!(
            "done  {:>6.2} s {}:{} {} := {}",
            time.as_secs_f64(),
            case.path,
            case.line,
            case.theorem,
            case.proof
        );
    }
    let mut outcome = Outcome {
        case: case.clone(),
        time,
        closed: false,
        rank: None,
        elsewhere: None,
        note: String::new(),
        rejected_in_file: 0,
    };
    let report = match found {
        Ok(report) => report,
        Err(d) => {
            outcome.note = format!("[{}] {}", d.code, d.message);
            return outcome;
        }
    };
    outcome.rejected_in_file = report.budget.in_file.map_or(0, |f| f.rejected);
    let closing: Vec<_> = (report.results.iter())
        .filter(|s| s.class != "applicable")
        .collect();
    outcome.closed = !closing.is_empty() || !report.tactics.is_empty();
    if let Some(head) = &case.lemma {
        outcome.rank = (closing.iter())
            .position(|s| same_lemma(&s.name, &s.proof, head))
            .map(|i| i + 1);
        if outcome.rank.is_none() {
            if (report.results.iter())
                .any(|s| s.class == "applicable" && same_lemma(&s.name, &s.proof, head))
            {
                outcome.elsewhere = Some("applicable");
            } else if (report.rewrites.iter()).any(|r| r.name.ends_with(&format!(".{head}"))) {
                outcome.elsewhere = Some("rewrite");
            }
        }
    } else if report.tactics.contains(&case.proof) {
        outcome.rank = Some(1);
    }
    outcome.note = match (report.tactics.first(), closing.first()) {
        (Some(t), _) => format!("{t} alone"),
        (None, Some(s)) => s.proof.clone(),
        (None, None) => format!(
            "nothing closes it: {} matched, {} applicable, {} rewrites{}",
            report.budget.matched,
            report.total.applicable,
            report.total.rewrites,
            if report.budget.exhausted {
                ""
            } else {
                "; out of time"
            }
        ),
    };
    outcome
}

fn aoc() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc")
}

/// The cases of the project, as `files` shows it.
fn cases(files: &dyn Files) -> Vec<Case> {
    let mut sources = SourceMap::new();
    let found = project_sources(files, "aoc", &mut sources).expect("aoc reads");
    let only = std::env::var("STITCHWORT_AT_BENCH_ONLY").ok();
    let mut cases: Vec<Case> = found
        .iter()
        .filter(|(p, _)| only.as_ref().is_none_or(|o| p.contains(o.as_str())))
        .flat_map(|(p, t)| cases_in(p, t))
        .collect();
    let count = |name: &str| {
        std::env::var(name)
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
    };
    if let Some(n) = count("STITCHWORT_AT_BENCH_SKIP") {
        cases.drain(..n.min(cases.len()));
    }
    if let Some(n) = count("STITCHWORT_AT_BENCH_LIMIT") {
        cases.truncate(n);
    }
    cases
}

fn report(label: &str, outcomes: &[Outcome]) {
    let n = outcomes.len();
    let share = |k: usize, of: usize| 100.0 * k as f64 / of.max(1) as f64;
    let lemmas: Vec<&Outcome> = outcomes.iter().filter(|o| o.case.lemma.is_some()).collect();
    let tactics: Vec<&Outcome> = outcomes.iter().filter(|o| o.case.lemma.is_none()).collect();
    let count = |os: &[&Outcome], f: &dyn Fn(&Outcome) -> bool| os.iter().filter(|o| f(o)).count();
    let mut times: Vec<f64> = outcomes.iter().map(|o| o.time.as_secs_f64()).collect();
    times.sort_by(f64::total_cmp);
    let median = times.get(times.len() / 2).copied().unwrap_or(0.0);
    let total: f64 = times.iter().sum();
    eprintln!(
        "{label}: {n} goals ({} one-lemma proofs, {} a closer alone); a time a goal of {median:.2} s median, {:.2} s max, {total:.0} s in all",
        lemmas.len(),
        tactics.len(),
        times.last().copied().unwrap_or(0.0),
    );
    eprintln!(
        "  a closer found (any): {:.1}% of all; one-lemma proofs {:.1}%, closers alone {:.1}%",
        share(
            count(&outcomes.iter().collect::<Vec<_>>(), &|o| o.closed),
            n
        ),
        share(count(&lemmas, &|o| o.closed), lemmas.len()),
        share(count(&tactics, &|o| o.closed), tactics.len()),
    );
    eprintln!(
        "  the original lemma among the closers: {:.1}%, first {:.1}%, in the first 5 {:.1}%; among those that leave goals {}, among the rewrites {}",
        share(count(&lemmas, &|o| o.rank.is_some()), lemmas.len()),
        share(count(&lemmas, &|o| o.rank == Some(1)), lemmas.len()),
        share(
            count(&lemmas, &|o| o.rank.is_some_and(|r| r <= 5)),
            lemmas.len()
        ),
        count(&lemmas, &|o| o.elsewhere == Some("applicable")),
        count(&lemmas, &|o| o.elsewhere == Some("rewrite")),
    );
    eprintln!(
        "  the original closer alone found: {:.1}%",
        share(count(&tactics, &|o| o.rank.is_some()), tactics.len())
    );
    let rejected: usize = outcomes.iter().map(|o| o.rejected_in_file).sum();
    eprintln!("  suggestions checked at the goal that failed in the file: {rejected}");
    for o in outcomes {
        let what = match (&o.case.lemma, o.rank) {
            (_, Some(r)) => format!("found at {r}"),
            (Some(_), None) => match o.elsewhere {
                Some(e) => format!("MISS ({e})"),
                None => "MISS".to_string(),
            },
            (None, None) => "MISS".to_string(),
        };
        eprintln!(
            "  {:<12} {:>5.2} s  {}:{} {} := {}  -> {}",
            what,
            o.time.as_secs_f64(),
            o.case.path.trim_start_matches("src/Aoc/"),
            o.case.line,
            o.case.theorem,
            o.case.proof,
            o.note
        );
    }
}

/// Goals searched at once in [`search_at_on_aoc_goals`].
const MAX_GOAL_WORKERS: usize = 3;

/// Every one-lemma proof of the AoC project (a sample in broad), as a goal.
#[test]
fn search_at_on_aoc_goals() {
    let keep: Option<Vec<String>> = match tier() {
        Tier::Lane | Tier::Quick => {
            eprintln!("skipped: broad and all tiers only");
            return;
        }
        Tier::Broad => Some(vec![
            "src/Aoc/Common".to_string(),
            "src/Aoc/Year2021".to_string(),
        ]),
        Tier::All => None,
    };
    let cache = Path::new(env!("CARGO_TARGET_TMPDIR")).join("search-at-aoc-cache");
    let files: Box<dyn Files + Sync> = match &keep {
        Some(keep) => Box::new(Only {
            base: DiskFiles { root: aoc() },
            keep: keep.clone(),
        }),
        None => Box::new(DiskFiles { root: aoc() }),
    };
    let all = cases(&*files);
    assert!(!all.is_empty(), "no goals found");
    // The first goal alone, to fill the check cache; then the rest at once.
    let (first, rest) = all.split_at(1);
    let mut outcomes = vec![stitchwort_driver::driver::with_stack(STACK, || {
        run(&first[0], &*files, &cache)
    })];
    // Each goal holds a session with the project's files it imports, about
    // 0.7 GB (measured: 5.7 GB on 8 workers, 1.5 GB on 2, SW-2614), so the
    // pool is capped by memory, not by cores.
    outcomes.extend(par_map_with_at_most(
        STACK,
        MAX_GOAL_WORKERS,
        rest,
        || (),
        |(), case| run(case, &*files, &cache),
    ));
    report("AoC theorems proved by one lemma or a closer", &outcomes);
    let lemmas = outcomes.iter().filter(|o| o.case.lemma.is_some()).count();
    let found = (outcomes.iter())
        .filter(|o| o.case.lemma.is_some() && o.rank.is_some())
        .count();
    assert!(
        found * 100 >= lemmas * 30,
        "the original lemma was among the closers for too few goals"
    );
    assert!(
        outcomes.iter().all(|o| o.rejected_in_file == 0),
        "a suggestion checked at the goal failed in the file"
    );
}

/// A real goal of AoC 2021 days 9 to 18 (SW-989): what the proof lanes asked
/// `search --at` about (aoc/NOTES-2021.md, each day's "search" paragraphs,
/// and the friction tickets SW-960 to SW-980), made again by replacing the
/// proof written there with `?` (in memory). Where a later lane replaced the
/// proof by a std lemma (SW-983) or moved it (SW-984), the goal is put back
/// as the lane met it: its theorem written again with `?`, or the `?` where
/// the std lemma now stands, that lemma left out of the search (`exclude`).
struct Real {
    /// The theorem, and what the goal shows (the note's words).
    label: &'static str,
    /// What the notes say went wrong, or `works` for a goal it closed.
    kind: &'static str,
    path: &'static str,
    /// The text replaced: from `from` (it must occur once) to just before
    /// `until`, if given, else `from` alone.
    from: &'static str,
    until: Option<&'static str>,
    /// What replaces it (with a `?` in it: the goal).
    to: &'static str,
    /// What closes it: a lemma's name (a word of a closing proof) or a
    /// tactic. Empty: only that the goal is read (it was refused).
    want: &'static [&'static str],
    /// Declarations not to suggest, by full name: std lemmas added since
    /// (SW-983) whose statement is the goal's own, so that the goal is
    /// asked about as the lane met it.
    exclude: &'static [&'static str],
}

const D: &str = "src/Aoc/Year2021/";

#[rustfmt::skip]
const REAL: &[Real] = &[
    Real { label: "landsFoldDot after `match fold`: `cases`", kind: "context order", path: "Day13/Proofs/Fold.sw",
        from: "| AlongX line => cases", until: None, to: "| AlongX line => ?", want: &["cases"], exclude: &[] },
    Real { label: "widthCovers's `Cons dot rest, Inl same`", kind: "context order", path: "Day13/Proofs/Picture.sw",
        from: "| [dot, ..rest], Inl same => rewrite <- same in omega [widthCons dot rest, Nat.leMaxLeft (dot.x + 1) (width rest)]", until: None,
        to: "| [dot, ..rest], Inl same => ?", want: &[], exclude: &[] },
    Real { label: "widthCons: `List.foldRightCons`", kind: "works", path: "Day13/Proofs/Picture.sw",
        from: "List.foldRightCons rest dot 0 (dot widest => Nat.max (dot.x + 1) widest)", until: None, to: "?", want: &["foldRightCons"], exclude: &[] },
    Real { label: "addToFirstZero's `Cons leaf rest` (a record after `Cons`)", kind: "record after a constructor", path: "Day18/Proofs/Leaves.sw",
        from: "| [leaf, ..rest] => Eq.cong (l => [l, ..rest]) (addZeroLeaf leaf)", until: None, to: "| [leaf, ..rest] => ?", want: &[], exclude: &[] },
    Real { label: "shiftAppend's `Some found` (a record update in `Some`)", kind: "record after a constructor", path: "Day18/Proofs/Explode.sw",
        from: "| Some found => Eq.cong Some (Exploding.ext", until: Some("\n"), to: "| Some found => ?", want: &[], exclude: &[] },
    Real { label: "leavesShallow's `Regular value`", kind: "context order", path: "Day18/Proofs/Reduced.sw",
        from: "| Regular value => And.left (And.left small)", until: None, to: "| Regular value => ?", want: &[], exclude: &[] },
    Real { label: "leavesSmall's `Pair left right` (`split.%match1` in a hypothesis)", kind: "hidden %match name", path: "Day18/Proofs/Reduced.sw",
        from: "match el: split left with", until: Some("\n\ntheorem leavesShallow"), to: "?", want: &[], exclude: &[] },
    Real { label: "memberPairs: `(if i == j then None else Some (x, y)) = Some (x, y)`", kind: "works", path: "Day18/Proofs/Answers.sw",
        from: "atJ) cases)", until: None, to: "atJ) ?)", want: &["cases"], exclude: &[] },
    Real { label: "takeAppendLength: `rewrite <- h in List.takeAppend xs ys`", kind: "hypothesis as a rewrite", path: "../Common/Proofs/BitReader.sw",
        from: "--| `Some` of two pairs", until: None,
        to: "theorem takeAppendLength (xs: List a) (ys: List a) (k: Nat) (h: xs.length = k): (xs ++ ys).take k = xs := ?\n\n--| `Some` of two pairs",
        want: &["takeAppend"], exclude: &["Std.List.takeAppendLength"] },
    Real { label: "groupsValue's `inner` (a lambda's binder named as a variable)", kind: "captured variable", path: "Day16/Proofs/Answers.sw",
        from: "rewrite Nat.fromBitsFrom acc (Nat.toBits 4 group), Nat.fromBitsToBits 4 group fits in rfl", until: None, to: "?", want: &["fromBitsFrom"], exclude: &[] },
    Real { label: "neighboursMono: `List.countLeMem` (count unfolded)", kind: "folded goal", path: "Day11/Proofs/Rounds.sw",
        from: "List.countLeMem cavern.grid.cells (cell => touching at cell.fst", until: Some("\n\n"), to: "?", want: &["countLeMem"], exclude: &[] },
    Real { label: "stepRepresents' calc step: `Eq.sym (List.sumByFlatMap …)`", kind: "symmetric lemma", path: "Day14/Proofs/Counts.sw",
        from: "Eq.sym (List.sumByFlatMap (pairsOf polymer) f (expand rules))", until: None, to: "?", want: &["sumByFlatMap"], exclude: &[] },
    Real { label: "pairsStep's step: `pairsStepCons` and the induction hypothesis", kind: "induction hypothesis", path: "Day14/Proofs/Pairs.sw",
        from: "rewrite pairsStepCons rules a b rest, pairsStep rules [b, ..rest] in rfl", until: None, to: "?", want: &["pairsStepCons", "pairsStep"], exclude: &[] },
    Real { label: "memPositions: `List.memFlatMapIntro` (flatMap unfolded)", kind: "folded goal", path: "../Common/GridGraph.sw",
        from: "List.memFlatMapIntro (row => List.range 0 width", until: Some("\n\n"), to: "?", want: &["memFlatMapIntro"], exclude: &[] },
    Real { label: "candidatesDistinct: `List.distinctFlatMap` (flatMap unfolded)", kind: "folded goal", path: "Day17/Proofs/Answers.sw",
        from: "List.distinctFlatMap (i => List.range 0 (steps target)", until: Some("\n\ntheorem hittingDistinct"), to: "?", want: &["distinctFlatMap"], exclude: &[] },
    Real { label: "hittingDistinct: `List.distinctFilter`", kind: "works", path: "Day17/Proofs/Answers.sw",
        from: "List.distinctFilter (candidates target) (v => hitsWithin target (steps target) (launch v)) (candidatesDistinct target)", until: None, to: "?", want: &["distinctFilter"], exclude: &[] },
    Real { label: "dyAfter's base case: `omega`", kind: "works", path: "Day17/Proofs/Motion.sw",
        from: "| 0 => omega", until: None, to: "| 0 => ?", want: &["omega"], exclude: &[] },
    Real { label: "dyAfter's step: the induction hypothesis", kind: "induction hypothesis", path: "Day17/Proofs/Motion.sw",
        from: "| Succ n => omega [dyAfter n (step probe)]", until: None, to: "| Succ n => ?", want: &["dyAfter"], exclude: &[] },
    Real { label: "differ: `(x == y) = False` from `x ≠ y`", kind: "works", path: "Day12/Proofs/Neighbours.sw",
        from: "match e: x == y with", until: Some("\n\n"), to: "?", want: &["toBoolOfNot", "equalFalse", "soundFalse"], exclude: &[] },
    Real { label: "appendStep: `List.appendAssoc` backwards", kind: "works", path: "Day12/Proofs/Rules.sw",
        from: "Eq.sym (List.appendAssoc sofar.caves [y] more)", until: None, to: "?", want: &["appendAssoc"], exclude: &[] },
    Real { label: "visitsMember's `Cons x rest, Inl same`", kind: "context order", path: "Day12/Proofs/Rules.sw",
        from: "| [x, ..rest], Inl same => rewrite same, DecEq.refl cave in omega", until: None, to: "| [x, ..rest], Inl same => ?", want: &[], exclude: &[] },
    Real { label: "visitsMember's `Cons x rest, Inr later`: the induction hypothesis", kind: "induction hypothesis", path: "Day12/Proofs/Rules.sw",
        from: "| [x, ..rest], Inr later => omega [visitsMember cave rest later]", until: None, to: "| [x, ..rest], Inr later => ?", want: &["visitsMember"], exclude: &[] },
    Real { label: "toNatAtMostOne: `cases`", kind: "works", path: "Day10/Proofs/Middle.sw",
        from: "--| `y < x` is false", until: None,
        to: "theorem toNatAtMostOne: (b: Bool) → Bool.toNat b ≤ 1 := ?\n\n--| `y < x` is false", want: &["cases"], exclude: &["Std.Bool.toNatLeOne"] },
    Real { label: "notBelow: `omega`", kind: "works", path: "Day10/Proofs/Middle.sw",
        from: "(y < x) = False := omega", until: None, to: "(y < x) = False := ?", want: &["omega"], exclude: &[] },
    Real { label: "countAtMostLength's step: `List.countCons` and the induction hypothesis", kind: "induction hypothesis", path: "Day10/Proofs/Middle.sw",
        from: "--| In a sorted list, at most k", until: None,
        to: "theorem countAtMostLength (p: a → Bool): (xs: List a) → xs.count p ≤ xs.length\n  | Nil => Nat.leRefl 0\n  | Cons x rest => ?\n\n--| In a sorted list, at most k",
        want: &["countCons", "countAtMostLength"], exclude: &["Std.List.countLeLength"] },
    Real { label: "basinSizeOpen: `length (keys r) = size r` (`Map.sizeToList`)", kind: "rewrite step", path: "Day09/Proofs/Part2.sw",
        from: "(Map.lengthKeys result)", until: None, to: "?", want: &["sizeToList", "lengthMap"], exclude: &["Std.Map.lengthKeys"] },
];

/// What one real goal found.
struct RealOutcome {
    refused: Option<String>,
    /// Something closes it.
    closed: bool,
    /// A wanted lemma or tactic closes it.
    wanted: bool,
    /// A wanted lemma is a step: among those that leave goals, or the
    /// rewrites.
    step: bool,
    time: Duration,
    first: String,
}

fn has_word(text: &str, word: &str) -> bool {
    text.split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .any(|w| w == word)
}

fn run_real(real: &Real, files: &dyn Files, cache: &Path) -> RealOutcome {
    // `../Common/…`: a file of `Aoc.Common`, where a 2021 proof moved (SW-984).
    let path = match real.path.strip_prefix("../") {
        Some(common) => format!("src/Aoc/{common}"),
        None => format!("{D}{}", real.path),
    };
    let text = files.read(&path).expect("the file reads");
    assert_eq!(
        text.matches(real.from).count(),
        1,
        "{path}: `{}` isn't in it once",
        real.from
    );
    let start = text.find(real.from).expect("found");
    let end = match real.until {
        // The end of the file, if `until` isn't after it.
        Some(until) => start + text[start..].find(until).unwrap_or(text.len() - start),
        None => start + real.from.len(),
    };
    let new = format!("{}{}{}", &text[..start], real.to, &text[end..]);
    let at = start + real.to.find('?').expect("a `?`");
    let line = new[..at].matches('\n').count() + 1;
    let column = new[..at].rsplit('\n').next().unwrap_or("").chars().count() + 1;
    let overlay = Overlay {
        base: files,
        texts: BTreeMap::from([(path.clone(), new)]),
    };
    let goal = ProjectGoal {
        project: "aoc",
        files: &overlay,
        path: &path,
        cache: Some(cache),
        at: GoalAt::Line(line, Some(column)),
    };
    let started = Instant::now();
    let mut session = Session::for_stack(STACK);
    let options = AtOptions {
        exclude: real.exclude.iter().map(|e| e.to_string()).collect(),
        ..AtOptions::default()
    };
    let found = session.search_at_project(&goal, &options);
    drop(session);
    let time = started.elapsed();
    let report = match found {
        Ok(report) => report,
        Err(d) => {
            return RealOutcome {
                refused: Some(format!(
                    "[{}] {} {}",
                    d.code,
                    d.message,
                    d.notes.first().map(String::as_str).unwrap_or("")
                )),
                closed: false,
                wanted: false,
                step: false,
                time,
                first: String::new(),
            };
        }
    };
    let closing: Vec<&str> = (report.results.iter())
        .filter(|s| s.class != "applicable")
        .map(|s| s.proof.as_str())
        .chain(report.tactics.iter().map(String::as_str))
        .collect();
    let steps: Vec<&str> = (report.results.iter())
        .filter(|s| s.class == "applicable")
        .map(|s| s.proof.as_str())
        .chain(report.rewrites.iter().map(|r| r.proof.as_str()))
        // The induction hypothesis offered for a closer to use (SW-993).
        .chain(report.induction.iter().map(String::as_str))
        .collect();
    let wanted =
        |proofs: &[&str]| (proofs.iter()).any(|p| real.want.iter().any(|w| has_word(p, w)));
    RealOutcome {
        refused: None,
        closed: !closing.is_empty(),
        wanted: wanted(&closing),
        step: wanted(&steps),
        time,
        first: (closing.first().or(steps.first())).map_or("nothing".to_string(), |s| s.to_string()),
    }
}

/// The benchmark of real goals (SW-989): AoC 2021 days 9 to 18, in the
/// project (`Aoc.Common`, the 2021 days, and 2024 day 24, which day 12
/// imports). Broad and all tiers; `STITCHWORT_AT_BENCH_ONLY` as above.
/// Reported: how many are refused, read and closed, and how many are closed
/// (or offered a step) by what their proof used; the time of each.
#[test]
fn search_at_on_real_2021_goals() {
    if matches!(tier(), Tier::Lane | Tier::Quick) {
        eprintln!("skipped: broad and all tiers only");
        return;
    }
    let cache = Path::new(env!("CARGO_TARGET_TMPDIR")).join("search-at-aoc-cache");
    let files = Only {
        base: DiskFiles { root: aoc() },
        keep: vec![
            "src/Aoc/Common".to_string(),
            "src/Aoc/Year2021".to_string(),
            "src/Aoc/Year2024/Day24".to_string(),
        ],
    };
    let only = std::env::var("STITCHWORT_AT_BENCH_ONLY").ok();
    let reals: Vec<&Real> = (REAL.iter())
        .filter(|r| only.as_ref().is_none_or(|o| r.path.contains(o.as_str())))
        .collect();
    let (first, rest) = reals.split_at(1);
    let mut outcomes = vec![stitchwort_driver::driver::with_stack(STACK, || {
        run_real(first[0], &files, &cache)
    })];
    outcomes.extend(par_map(STACK, rest, |r| run_real(r, &files, &cache)));
    let n = reals.len();
    let count = |f: &dyn Fn(&RealOutcome) -> bool| outcomes.iter().filter(|o| f(o)).count();
    let with_want = reals.iter().filter(|r| !r.want.is_empty()).count();
    let hit = |r: &Real, o: &RealOutcome| {
        if r.want.is_empty() {
            o.refused.is_none()
        } else {
            o.wanted || o.step
        }
    };
    let hits = (reals.iter().zip(&outcomes))
        .filter(|(r, o)| hit(r, o))
        .count();
    let mut times: Vec<f64> = outcomes.iter().map(|o| o.time.as_secs_f64()).collect();
    times.sort_by(f64::total_cmp);
    eprintln!(
        "real 2021 goals: {n}; refused {}, closed by something {}; of {with_want} with a known closer, closed by it {}, offered it as a step {}; hit rate {hits}/{n} ({:.0}%); a goal {:.1} s median, {:.1} s max",
        count(&|o| o.refused.is_some()),
        count(&|o| o.closed),
        count(&|o| o.wanted),
        count(&|o| !o.wanted && o.step),
        100.0 * hits as f64 / n.max(1) as f64,
        times.get(times.len() / 2).copied().unwrap_or(0.0),
        times.last().copied().unwrap_or(0.0),
    );
    for (r, o) in reals.iter().zip(&outcomes) {
        let what = match (&o.refused, o.wanted, o.step, o.closed) {
            (Some(_), ..) => "REFUSED",
            (None, true, ..) => "closed",
            (None, false, true, _) => "step",
            (None, false, false, true) if r.want.is_empty() => "read, closed",
            (None, false, false, _) if r.want.is_empty() => "read",
            (None, false, false, true) => "MISS (closed otherwise)",
            (None, false, false, false) => "MISS",
        };
        eprintln!(
            "  {what:<24} {:>5.1} s  [{}] {}  -> {}",
            o.time.as_secs_f64(),
            r.kind,
            r.label,
            o.refused.as_deref().unwrap_or(&o.first)
        );
    }
    // 1 November 2026: none refused, 23 of 29 (SW-989); 27 of 29 (SW-993),
    // the bar raised to 80% (a goal near the time limit can miss under load).
    if only.is_none() {
        assert_eq!(count(&|o| o.refused.is_some()), 0, "a goal was refused");
        assert!(hits * 100 >= n * 80, "the hit rate fell below 80%");
    }
}
