//! `search --at` on real proof goals (SW-915, D2100): each AoC theorem whose
//! proof is one lemma applied to plain arguments (`L a b h`, `L _ _`), or a
//! closer on its own (`rfl`, `omega`), has its proof replaced by `?` in its
//! file (in memory), and `search --at` asked about that goal, in the
//! project, as an agent would. Reported: how often a closer is found (any),
//! how often the original lemma is among the closers, its rank, and the
//! time a goal takes; and the misses, with what the search found instead.
//!
//! The full tier runs every such theorem of the AoC project; the daily tier
//! a sample, in a part of the project (`Aoc.Common` and the 2021 days) so
//! that a cold check cache costs seconds, not the minute the whole project
//! takes to check. The merge and lane tiers skip it.
//!
//! `STITCHWORT_AT_BENCH_ONLY=Year2024/Day06` limits it to the goals whose
//! file path contains that text (any tier but merge and lane).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use stitchwort_driver::driver::{Session, Tier, par_map, tier};
use stitchwort_driver::project::{DiskFiles, Entry, Files, project_sources};
use stitchwort_driver::search_at::{AtOptions, GoalAt, Overlay, ProjectGoal};
use stitchwort_syntax::ast::{Decl, Expr};
use stitchwort_syntax::{SourceMap, parse_module_recovering};

const STACK: usize = 64 * 1024 * 1024;

/// Each goal is a fresh session of the whole library and project (about
/// 600 MB), dropped after; with the system allocator macOS keeps what they
/// free, and four workers passed 10 GB. mimalloc, as the CLI uses.
#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

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
    found
        .iter()
        .filter(|(p, _)| only.as_ref().is_none_or(|o| p.contains(o.as_str())))
        .flat_map(|(p, t)| cases_in(p, t))
        .collect()
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

/// Every one-lemma proof of the AoC project (a sample in daily), as a goal.
#[test]
fn search_at_on_aoc_goals() {
    let keep: Option<Vec<String>> = match tier() {
        Tier::Lane | Tier::Merge => {
            eprintln!("skipped: daily and full tiers only");
            return;
        }
        Tier::Daily => Some(vec![
            "src/Aoc/Common".to_string(),
            "src/Aoc/Year2021".to_string(),
        ]),
        Tier::Full => None,
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
    outcomes.extend(par_map(STACK, rest, |case| run(case, &*files, &cache)));
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
