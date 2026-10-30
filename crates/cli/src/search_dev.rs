//! EXPERIMENTAL: `stitchwort dev search`, the measuring prototype of lemma
//! search by type (SW-915, docs/proposals/search.md §4). Hidden, not a
//! stable interface; it prints its timings on standard error.
//!
//! Pattern syntax (a subset of the proposal's): comma-separated parts, each
//! a `"name substring"` or a type pattern (at most one). In the pattern, `_`
//! is any term, `?x` a named hole (every `?x` must match the same term), and
//! a leading `⊢` (or `|-`) matches the conclusion only.
//!
//! Measuring directives (also comma-separated parts, so that `main.rs`
//! needn't change):
//! - `mode:rewrite` matches the two sides of an equation only;
//!   `mode:permute` and `mode:subset` let a function pattern's parameters
//!   match in another order (and, with `subset`, a theorem with more);
//! - `rank:NAME` orders the results by one of [`RANKINGS`];
//! - `tiers:on` finds each match's best relation (draft 3, D2062);
//!   `ho:on` also tries targets headed by a theorem variable (`p x`);
//!   `iff:on` lets `mode:rewrite` take `Iff` conclusions; `filter:either`
//!   and `filter:off` change the constants filter, `data:on` adds data
//!   types to it;
//! - `self:conclusion` or `self:left` runs the self-retrieval benchmark:
//!   every std theorem's own conclusion (or left side, in `mode:rewrite`)
//!   as a pattern, reporting where the theorem ranks under each ranking;
//!   `self:uses` runs the proof-use benchmark (draft 3 §6.2): each lemma
//!   used in a std proof, searched for with the statement it proved there.

use std::collections::{BTreeMap, BTreeSet};
use std::process::ExitCode;
use std::time::Instant;

use stitchwort_cli::driver::Session;
use stitchwort_core::{DataId, DefId, Globals, Term};
use stitchwort_elab::search::{self, Filter, Hit, Index, Mode, Opts, Place, Relation, Side, Stats};
use stitchwort_syntax::Span;

/// The rankings compared in draft 2 §5.1 and draft 3 §5.1, by name.
const RANKINGS: [&str; 10] = [
    "draft1",
    "draft1+hyps",
    "isabelle",
    "rocq",
    "loogle",
    "proposed",
    "proposed+rare",
    "rare-first",
    "tiered",
    "weak-last",
];

/// What the rankings need besides a hit: per constant, how rare it is.
struct Rarity {
    /// `ln(N / df)` for each constant, times 100, where `df` is how many
    /// candidates name it (inverse document frequency, as MaSh weights
    /// features).
    idf: BTreeMap<DefId, i64>,
}

impl Rarity {
    fn new(index: &[Index]) -> Rarity {
        let mut df: BTreeMap<DefId, usize> = Default::default();
        for set in index {
            for c in &set.ty {
                *df.entry(*c).or_default() += 1;
            }
        }
        let n = index.len().max(1) as f64;
        let idf = (df.into_iter())
            .map(|(c, d)| (c, ((n / d as f64).ln() * 100.0).round() as i64))
            .collect();
        Rarity { idf }
    }

    /// The rarity of what the theorem names and the pattern doesn't: the
    /// sum of those constants' weights.
    fn extra(&self, theirs: &BTreeSet<DefId>, ours: &BTreeSet<DefId>) -> i64 {
        (theirs.difference(ours))
            .map(|c| self.idf.get(c).copied().unwrap_or(0))
            .sum()
    }
}

/// The sort key of a hit under ranking `name`, without the final
/// tie-break by name. Smaller is better.
fn key(
    name: &str,
    g: &Globals,
    hit: &Hit,
    theirs: &BTreeSet<DefId>,
    ours: &BTreeSet<DefId>,
    rarity: &Rarity,
) -> Vec<i64> {
    let place = match hit.place {
        // Left and right sides are the same kind of answer.
        Place::Right => Place::Left as i64,
        p => p as i64,
    };
    let relation = hit.relation as i64;
    let (a, i) = (hit.absorbed as i64, hit.instantiated as i64);
    let (size, hyps) = (hit.size as i64, hit.hyps as i64);
    let namelen = g.def(hit.id).path.to_string().len() as i64;
    let extra = rarity.extra(theirs, ours);
    match name {
        // Draft 1 §3.5.
        "draft1" => vec![place, a, i, namelen],
        // Draft 1 §4.3's suggested next tie-breaker.
        "draft1+hyps" => vec![place, a, i, hyps, namelen],
        // Isabelle's find_theorems: size of the theorem, then its
        // premises, then the size of the substitution.
        "isabelle" => vec![size, hyps, a],
        // Rocq's Search: 3 × distinct constants + size.
        "rocq" => vec![3 * theirs.len() as i64 + size],
        // Loogle: module order (here, load order), then size.
        "loogle" => vec![hit.id.0 as i64, size],
        // Draft 2 §5.1: specificity, then Isabelle's premises and size.
        "proposed" => vec![place, a, i, hyps, size],
        // The same with rarity (MePo, MaSh, Hoogle) after specificity.
        "proposed+rare" => vec![place, a, i, extra, hyps, size],
        "rare-first" => vec![place, extra, a, i, hyps, size],
        // Draft 3 §5.1 (D2062): the relation first, then draft 2's.
        "tiered" => vec![relation, place, a, i, hyps, size],
        // Draft 2's, with common-instance matches last.
        "weak-last" => vec![
            (hit.relation == Relation::Common) as i64,
            place,
            a,
            i,
            hyps,
            size,
        ],
        _ => vec![relation, place, a, i, hyps, size],
    }
}

pub struct Args {
    pub pattern: String,
    pub limit: usize,
    pub no_filter: bool,
    pub defs: bool,
    pub json: bool,
    pub repeat: usize,
}

/// What a benchmark measures.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Bench {
    Conclusion,
    Left,
    Uses,
}

/// A pattern split into its parts.
struct Query {
    names: Vec<String>,
    /// The type pattern with each `?x` written as `_`, and the offsets of
    /// each named hole's occurrences.
    pattern: Option<(String, Vec<Vec<u32>>)>,
    opts: Opts,
    ranking: String,
    bench: Option<Bench>,
    /// For `self:uses`: take every Nth use.
    every: usize,
    /// The relaxed second pass (on unless `relax:off`).
    relax: bool,
}

fn parse_query(text: &str) -> Query {
    let mut names = Vec::new();
    let mut pattern = None;
    let mut conclusion_only = false;
    let mut opts = Opts::default();
    let mut ranking = "tiered".to_string();
    let mut bench = None;
    let mut every = 1;
    let mut relax = true;
    for part in split_top(text) {
        let part = part.trim();
        if part.len() >= 2 && part.starts_with('"') && part.ends_with('"') {
            names.push(part[1..part.len() - 1].to_string());
            continue;
        }
        if let Some((key, value)) = part.split_once(':')
            && !key.contains(' ')
            && [
                "mode", "rank", "self", "tiers", "ho", "iff", "filter", "data", "every", "relax",
            ]
            .contains(&key)
        {
            let value = value.trim();
            let on = value == "on";
            match key {
                "mode" => {
                    opts.mode = match value {
                        "rewrite" => Mode::Rewrite,
                        "permute" => Mode::Permute,
                        "subset" => Mode::Subset,
                        _ => Mode::Plain,
                    }
                }
                "rank" => ranking = value.to_string(),
                "self" => {
                    bench = Some(match value {
                        "left" => Bench::Left,
                        "uses" => Bench::Uses,
                        _ => Bench::Conclusion,
                    })
                }
                "tiers" => opts.tiers = on,
                "ho" => opts.ho = on,
                // Filled in once the library is loaded.
                "iff" => opts.iff = on.then_some(DataId(usize::MAX)),
                "filter" => {
                    opts.filter = match value {
                        "off" => Filter::Off,
                        "either" => Filter::Either,
                        _ => Filter::Pattern,
                    }
                }
                "data" => opts.data = on,
                "every" => every = value.parse().unwrap_or(1).max(1),
                "relax" => relax = value != "off",
                _ => {}
            }
            continue;
        }
        let mut p = part.to_string();
        for prefix in ["⊢", "|-"] {
            if let Some(rest) = p.strip_prefix(prefix) {
                conclusion_only = true;
                p = rest.trim_start().to_string();
            }
        }
        // `?x` becomes `_` padded to the same width; remember where.
        let mut groups: Vec<(String, Vec<u32>)> = Vec::new();
        let bytes = p.as_bytes();
        let mut out = String::new();
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'?' {
                let mut j = i + 1;
                while j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_') {
                    j += 1;
                }
                if j > i + 1 {
                    let name = p[i + 1..j].to_string();
                    let offset = out.len() as u32;
                    match groups.iter_mut().find(|(n, _)| *n == name) {
                        Some((_, at)) => at.push(offset),
                        None => groups.push((name, vec![offset])),
                    }
                    out.push('_');
                    out.push_str(&" ".repeat(j - i - 1));
                    i = j;
                    continue;
                }
            }
            let c = p[i..].chars().next().expect("in bounds");
            out.push(c);
            i += c.len_utf8();
        }
        pattern = Some((out, groups.into_iter().map(|(_, at)| at).collect()));
    }
    opts.anywhere = !conclusion_only;
    Query {
        names,
        pattern,
        opts,
        ranking,
        bench,
        every,
        relax,
    }
}

/// One benchmark query: how to make its pattern, the theorem it must find,
/// and a theorem to leave out (the proof it was taken from).
struct BenchQuery {
    owner: DefId,
    wanted: DefId,
    make: Make,
}

enum Make {
    Own(DefId, Side),
    Use(DefId, Vec<Term>, usize),
}

/// A use: the proof, the lemma, its arguments, and the binders they are
/// under.
type Use = (DefId, DefId, Vec<Term>, usize);

/// The uses of theorems in the proofs of std's theorems (and their
/// helpers): the first use of each lemma in each proof, with all its
/// arguments, and how many uses there were in all.
fn lemma_uses(g: &Globals, candidates: &[DefId]) -> (Vec<Use>, usize) {
    let wanted: BTreeSet<DefId> = candidates
        .iter()
        .copied()
        .filter(|id| g.def(*id).theorem)
        .collect();
    let by_path: BTreeMap<String, DefId> = wanted
        .iter()
        .map(|id| (g.def(*id).path.to_string(), *id))
        .collect();
    let mut uses = Vec::new();
    let mut seen: BTreeSet<(DefId, DefId)> = BTreeSet::new();
    let mut all = 0;
    for i in 0..g.defs.len() {
        let id = DefId(i);
        let def = g.def(id);
        let path = def.path.to_string();
        let owner = if wanted.contains(&id) {
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
                        Term::Loc(_, x) => f = x,
                        Term::App(x, _, _) => f = x,
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
            if !wanted.contains(lemma) || *lemma == owner {
                continue;
            }
            all += 1;
            if seen.insert((owner, *lemma)) {
                uses.push((owner, *lemma, args.into_iter().cloned().collect(), binders));
            }
        }
    }
    (uses, all)
}

/// Where the wanted theorem ranks among `hits` under each ranking:
/// `(ties for it, ties against it, ties broken by name)`.
type Ranks = (usize, usize, usize);

/// The self-retrieval and proof-use benchmarks (draft 2 §6.1, draft 3
/// §6): each query's pattern searched over every theorem; where does the
/// wanted theorem rank?
fn benchmark(
    session: &mut Session,
    candidates: &[DefId],
    index: &[Index],
    bench: Bench,
    opts: &Opts,
    every: usize,
    relax: bool,
) {
    let start = Instant::now();
    let rarity = Rarity::new(index);
    let g = &session.elab.globals;
    let mut opts = *opts;
    if bench == Bench::Left {
        opts.mode = Mode::Rewrite;
    }
    opts.anywhere = false;
    let (uses, all_uses) = if bench == Bench::Uses {
        lemma_uses(g, candidates)
    } else {
        (Vec::new(), 0)
    };
    let queries: Vec<BenchQuery> = match bench {
        Bench::Uses => uses
            .into_iter()
            .enumerate()
            .filter(|(n, _)| n % every == 0)
            .map(|(_, (owner, lemma, args, depth))| BenchQuery {
                owner,
                wanted: lemma,
                make: Make::Use(lemma, args, depth),
            })
            .collect(),
        _ => candidates
            .iter()
            .filter(|id| g.def(**id).theorem)
            .map(|id| BenchQuery {
                owner: DefId(usize::MAX),
                wanted: *id,
                make: Make::Own(
                    *id,
                    if bench == Bench::Left {
                        Side::Left
                    } else {
                        Side::Conclusion
                    },
                ),
            })
            .collect(),
    };
    let position: BTreeMap<DefId, usize> = candidates
        .iter()
        .enumerate()
        .map(|(i, id)| (*id, i))
        .collect();
    // Per ranking, per query: the wanted theorem's ranks, or `None`.
    let mut ranks: Vec<Vec<Option<Ranks>>> = vec![Vec::new(); RANKINGS.len()];
    let mut relations: BTreeMap<String, usize> = BTreeMap::new();
    let mut n_queries = 0;
    let mut skipped = 0;
    let mut missed: Vec<String> = Vec::new();
    let mut hit_counts: Vec<usize> = Vec::new();
    let mut stats = Stats::default();
    let mut panics: Vec<String> = Vec::new();
    let mut truncated_queries = 0;
    let mut relaxed = 0;
    let mut relaxed_found = 0;
    let mut lost_to_filter = 0;
    let mut no_match = 0;
    let mut no_match_kinds: BTreeMap<&str, usize> = BTreeMap::new();
    let mut no_match_examples: Vec<String> = Vec::new();
    let mut query_ms: Vec<f64> = Vec::new();
    std::panic::set_hook(Box::new(|_| {}));
    for q in &queries {
        let remake = |session: &mut Session| match &q.make {
            Make::Own(id, side) => session.elab.theorem_pattern(*id, *side, opts.iff),
            Make::Use(lemma, args, depth) => {
                let args: Vec<&Term> = args.iter().collect();
                session.elab.use_pattern(*lemma, &args, *depth)
            }
        };
        let Some(pattern) = remake(session) else {
            skipped += 1;
            continue;
        };
        n_queries += 1;
        let began = Instant::now();
        let mut run = |session: &mut Session, filter: bool| {
            let mut hits: Vec<(Hit, usize)> = Vec::new();
            let mut outs = 0;
            for (i, other) in candidates.iter().enumerate() {
                if !session.elab.globals.def(*other).theorem || *other == q.owner {
                    continue;
                }
                // An internal error in one comparison is counted, not
                // fatal: the benchmark is also a robustness test.
                let elab = &session.elab;
                let attempt = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let mut s = Stats::default();
                    let hit =
                        elab.search_one(&pattern, *other, &opts, filter.then(|| &index[i]), &mut s);
                    (hit, s)
                }));
                match attempt {
                    Ok((hit, s)) => {
                        stats.unifications += s.unifications;
                        stats.resource_outs += s.resource_outs;
                        stats.upgraded += s.upgraded;
                        outs += s.resource_outs;
                        if let Some(hit) = hit {
                            hits.push((hit, i));
                        }
                    }
                    Err(_) => {
                        let g = &session.elab.globals;
                        panics.push(format!(
                            "{} against {}",
                            g.def(q.wanted).path,
                            g.def(*other).path
                        ));
                        // Leave the session as a failed attempt would.
                        let _ = remake(session);
                    }
                }
            }
            (hits, outs)
        };
        let filtered = opts.filter != Filter::Off;
        let (mut hits, mut outs) = run(session, filtered);
        if filtered && hits.is_empty() && relax {
            // Draft 3's relaxed second pass.
            relaxed += 1;
            (hits, outs) = run(session, false);
            if hits.iter().any(|(h, _)| h.id == q.wanted) {
                relaxed_found += 1;
            }
        }
        query_ms.push(began.elapsed().as_secs_f64() * 1000.0);
        if outs > 0 {
            truncated_queries += 1;
        }
        hit_counts.push(hits.len());
        let g = &session.elab.globals;
        let Some((own, own_i)) = hits.iter().find(|(h, _)| h.id == q.wanted) else {
            missed.push(g.def(q.wanted).path.to_string());
            // Why: filtered out (and unfiltered matching finds it), or no
            // match at all.
            let i = position[&q.wanted];
            let mut s = Stats::default();
            let mut o = opts;
            o.filter = Filter::Off;
            let matches = session
                .elab
                .search_one(&pattern, q.wanted, &o, None, &mut s)
                .is_some();
            let g = &session.elab.globals;
            if matches && !search::passes(&pattern, &index[i], &opts) {
                lost_to_filter += 1;
            } else if !matches {
                no_match += 1;
                let shown = pattern.show(g);
                let kind = if shown == "Void" {
                    "goal Void (a negation applied)"
                } else if g.def(q.wanted).path.to_string() == "Std.Eq.cong" {
                    "Eq.cong on a computed goal"
                } else {
                    "other"
                };
                *no_match_kinds.entry(kind).or_default() += 1;
                if kind == "other" && no_match_examples.len() < 40 {
                    no_match_examples.push(format!(
                        "{} in {}: {}",
                        g.def(q.wanted).path,
                        if q.owner.0 == usize::MAX {
                            String::new()
                        } else {
                            g.def(q.owner).path.to_string()
                        },
                        pattern.show(g)
                    ));
                }
            }
            for r in ranks.iter_mut() {
                r.push(None);
            }
            continue;
        };
        *relations.entry(format!("{:?}", own.relation)).or_default() += 1;
        let names: Vec<String> = hits
            .iter()
            .map(|(h, _)| g.def(h.id).path.to_string())
            .collect();
        let mine_name = g.def(own.id).path.to_string();
        for (r, name) in RANKINGS.iter().enumerate() {
            let k = |h: &Hit, i: usize| key(name, g, h, &index[i].ty, &pattern.constants, &rarity);
            let mine = k(own, *own_i);
            let keys: Vec<Vec<i64>> = hits.iter().map(|(h, i)| k(h, *i)).collect();
            let before = keys.iter().filter(|x| **x < mine).count();
            let not_after = keys.iter().filter(|x| **x <= mine).count();
            let strict = (keys.iter().zip(&names))
                .filter(|(x, n)| (*x, *n) < (&mine, &mine_name))
                .count();
            ranks[r].push(Some((before + 1, not_after, strict + 1)));
        }
    }
    let ms = start.elapsed().as_secs_f64() * 1000.0;
    hit_counts.sort();
    let pct = |v: &[usize], p: f64| {
        v.get(((v.len() as f64 - 1.0) * p) as usize)
            .copied()
            .unwrap_or(0)
    };
    query_ms.sort_by(f64::total_cmp);
    let pctf = |p: f64| {
        query_ms
            .get(((query_ms.len() as f64 - 1.0) * p) as usize)
            .copied()
            .unwrap_or(0.0)
    };
    if bench == Bench::Uses {
        println!(
            "proof uses: {all_uses} uses of std theorems in std proofs, {} distinct (proof, lemma) pairs, every {every}th taken",
            queries.len() * every
        );
    }
    println!(
        "benchmark ({:?}; {:?}): {n_queries} queries ({skipped} skipped: no pattern), {} not found, {ms:.0} ms",
        bench,
        opts,
        missed.len()
    );
    println!(
        "hits per query: median {}, p90 {}, p99 {}, max {}",
        pct(&hit_counts, 0.5),
        pct(&hit_counts, 0.9),
        pct(&hit_counts, 0.99),
        pct(&hit_counts, 1.0)
    );
    println!(
        "time per query: median {:.1} ms, p90 {:.1} ms, p99 {:.1} ms, max {:.1} ms",
        pctf(0.5),
        pctf(0.9),
        pctf(0.99),
        pctf(1.0)
    );
    println!(
        "stats: unifications {}, out of budget {} (queries with any: {truncated_queries}), upgraded by a one-way retry {}",
        stats.unifications, stats.resource_outs, stats.upgraded
    );
    println!(
        "relaxed second pass (filtered search empty): {relaxed} queries, wanted found by it in {relaxed_found}; not found: {lost_to_filter} filtered out (unfiltered matching finds them), {no_match} no match at all"
    );
    println!("no match, by kind: {no_match_kinds:?}");
    for e in &no_match_examples {
        println!("no match: {e}");
    }
    println!("relation of the wanted theorem's match: {relations:?}");
    println!(
        "over all {n_queries} queries (not found = no rank):\nranking       top1-strict  top1-ties  MRR-strict  R@5-strict  R@10-strict | found: top1-ties  MRR-ties  mean-pess"
    );
    for (r, name) in RANKINGS.iter().enumerate() {
        let v = &ranks[r];
        let n = v.len().max(1) as f64;
        let found: Vec<&Ranks> = v.iter().flatten().collect();
        let nf = found.len().max(1) as f64;
        let share =
            |f: &dyn Fn(&Ranks) -> bool| 100.0 * found.iter().filter(|x| f(x)).count() as f64 / n;
        let share_found =
            |f: &dyn Fn(&Ranks) -> bool| 100.0 * found.iter().filter(|x| f(x)).count() as f64 / nf;
        let mrr_strict = found.iter().map(|x| 1.0 / x.2 as f64).sum::<f64>() / n;
        let mrr_opt_found = found.iter().map(|x| 1.0 / x.0 as f64).sum::<f64>() / nf;
        let mean_pess = found.iter().map(|x| x.1 as f64).sum::<f64>() / nf;
        println!(
            "{name:<13} {:>10.1}%  {:>8.1}%  {:>10.3}  {:>9.1}%  {:>10.1}% | {:>9.1}%  {:>8.3}  {:>9.2}",
            share(&|x| x.2 == 1),
            share(&|x| x.0 == 1),
            mrr_strict,
            share(&|x| x.2 <= 5),
            share(&|x| x.2 <= 10),
            share_found(&|x| x.0 == 1),
            mrr_opt_found,
            mean_pess,
        );
    }
    println!("internal errors (panics): {}", panics.len());
    for p in panics.iter().take(25) {
        println!("panic: {p}");
    }
    for name in missed.iter().take(40) {
        println!("not found: {name}");
    }
}

/// Splits at commas outside brackets and quotes.
fn split_top(text: &str) -> Vec<String> {
    let mut parts = vec![String::new()];
    let mut depth = 0i32;
    let mut quoted = false;
    for c in text.chars() {
        match c {
            '"' => quoted = !quoted,
            '(' | '[' | '{' if !quoted => depth += 1,
            ')' | ']' | '}' if !quoted => depth -= 1,
            ',' if !quoted && depth == 0 => {
                parts.push(String::new());
                continue;
            }
            _ => {}
        }
        parts.last_mut().expect("one").push(c);
    }
    parts
}

fn ms(since: Instant) -> f64 {
    since.elapsed().as_secs_f64() * 1000.0
}

fn relation_name(r: Relation) -> &'static str {
    match r {
        Relation::Instance => "instance",
        Relation::Generalisation => "generalisation",
        Relation::Common => "commonInstance",
    }
}

fn place_name(p: Place) -> &'static str {
    match p {
        Place::Whole => "whole",
        Place::Reordered => "reordered",
        Place::Conclusion => "conclusion",
        Place::Left => "left",
        Place::Right => "right",
        Place::Hypothesis => "premise",
        Place::Inside => "subterm",
    }
}

pub fn run(session: &mut Session, args: &Args) -> ExitCode {
    let start = Instant::now();
    if let Err(diagnostics) = session.elab.load_all_libraries() {
        eprintln!(
            "error: loading the library: {} diagnostics",
            diagnostics.len()
        );
        return ExitCode::FAILURE;
    }
    let loaded = ms(start);
    // Every top-level namespace of the library, imported, so a pattern can
    // say `List.length`.
    let start = Instant::now();
    let g = &session.elab.globals;
    let mut namespaces: Vec<String> = (0..g.defs.len())
        .filter_map(|i| {
            let path = g.def(DefId(i)).path.to_string();
            let rest = path.strip_prefix("Std.")?;
            let (top, _) = rest.split_once('.')?;
            Some(top.to_string())
        })
        .collect();
    namespaces.sort();
    namespaces.dedup();
    let imports = format!("import Std ({})\n", namespaces.join(", "));
    let reported = session.add_imports("<search imports>", &imports);
    if reported
        .iter()
        .any(|d| d.severity == stitchwort_syntax::Severity::Error)
    {
        for d in &reported {
            eprintln!(
                "{}",
                stitchwort_cli::render::render(&session.sources, d, false)
            );
        }
    }
    let imported = ms(start);
    // The candidates and, per candidate, what its type names.
    let start = Instant::now();
    let g = &session.elab.globals;
    let candidates: Vec<DefId> = (0..g.defs.len())
        .map(DefId)
        .filter(|id| {
            let def = g.def(*id);
            let path = def.path.to_string();
            (def.theorem || args.defs) && !path.contains('%') && !path.contains("<input")
        })
        .collect();
    let theorems = candidates.iter().filter(|id| g.def(**id).theorem).count();
    let enumerated = ms(start);
    let start = Instant::now();
    let index: Vec<Index> = candidates
        .iter()
        .map(|id| session.elab.type_index(*id))
        .collect();
    let indexed = ms(start);
    let mut query = parse_query(&args.pattern);
    if args.no_filter {
        query.opts.filter = Filter::Off;
    }
    if query.opts.iff.is_some() {
        let g = &session.elab.globals;
        query.opts.iff = (0..g.datas.len())
            .map(DataId)
            .find(|d| g.data(*d).path.to_string() == "Std.Iff");
    }
    if let Some(bench) = query.bench {
        eprintln!("timing: load-all-std {loaded:.1} ms; constants index {indexed:.1} ms");
        benchmark(
            session,
            &candidates,
            &index,
            bench,
            &query.opts,
            query.every,
            query.relax,
        );
        return ExitCode::SUCCESS;
    }
    let rarity = Rarity::new(&index);
    let position: BTreeMap<DefId, usize> = candidates
        .iter()
        .enumerate()
        .map(|(i, id)| (*id, i))
        .collect();
    let start = Instant::now();
    let pattern = match &query.pattern {
        None => None,
        Some((text, groups)) => {
            let expr = match session.parse_expression("<pattern>", text) {
                Ok(expr) => expr,
                Err(d) => {
                    eprintln!(
                        "{}",
                        stitchwort_cli::render::render(&session.sources, &d, false)
                    );
                    return ExitCode::FAILURE;
                }
            };
            let file = expr.span().file;
            let named: Vec<Vec<Span>> = (groups.iter())
                .map(|at| at.iter().map(|o| Span::new(file, *o, *o + 1)).collect())
                .collect();
            match session.elab.search_pattern(&expr, &named) {
                Ok(p) => Some(p),
                Err(d) => {
                    eprintln!(
                        "{}",
                        stitchwort_cli::render::render(&session.sources, &d, false)
                    );
                    return ExitCode::FAILURE;
                }
            }
        }
    };
    let elaborated = ms(start);
    let mut hits = Vec::new();
    let mut stats = Stats::default();
    let mut matching = Vec::new();
    let mut tier = "filtered";
    for _ in 0..args.repeat.max(1) {
        let start = Instant::now();
        let mut opts = query.opts;
        tier = if opts.filter == Filter::Off {
            "unfiltered"
        } else {
            "filtered"
        };
        // The relaxed second pass: unfiltered, if the filtered search
        // found nothing.
        for pass in 0..2 {
            hits.clear();
            stats = Stats::default();
            let g = &session.elab.globals;
            for (i, id) in candidates.iter().enumerate() {
                let path = g.def(*id).path.to_string();
                if !query.names.iter().all(|n| path.contains(n.as_str())) {
                    continue;
                }
                match &pattern {
                    None => {
                        let (size, hyps) = search::shape(g, *id);
                        hits.push(search::Hit {
                            id: *id,
                            place: Place::Conclusion,
                            relation: Relation::Instance,
                            iff: false,
                            absorbed: 0,
                            instantiated: 0,
                            size,
                            hyps,
                        })
                    }
                    Some(p) => {
                        if let Some(hit) =
                            session
                                .elab
                                .search_one(p, *id, &opts, Some(&index[i]), &mut stats)
                        {
                            hits.push(hit);
                        }
                    }
                }
            }
            if pass == 0 && hits.is_empty() && opts.filter != Filter::Off && pattern.is_some() {
                opts.filter = Filter::Off;
                tier = "relaxed";
                continue;
            }
            break;
        }
        let g = &session.elab.globals;
        if query.ranking == "tiered" {
            search::rank(g, &mut hits);
        } else {
            let none = BTreeSet::new();
            let ours = pattern.as_ref().map(|p| &p.constants).unwrap_or(&none);
            hits.sort_by_cached_key(|h| {
                let k = key(
                    &query.ranking,
                    g,
                    h,
                    &index[position[&h.id]].ty,
                    ours,
                    &rarity,
                );
                (k, g.def(h.id).path.to_string())
            });
        }
        matching.push(ms(start));
    }
    let g = &session.elab.globals;
    let shown: Vec<serde_json::Value> = hits
        .iter()
        .take(args.limit)
        .map(|hit| {
            let def = g.def(hit.id);
            let file = session.sources.get(def.span.file);
            let line = file.text[..(def.span.start as usize).min(file.text.len())]
                .matches('\n')
                .count()
                + 1;
            let path = def.path.to_string();
            let namespace = path
                .strip_prefix("Std.")
                .and_then(|r| r.split_once('.'))
                .map(|(top, _)| format!("import Std ({top})"));
            let mut v = serde_json::json!({
                "name": path,
                "type": stitchwort_core::pretty::term(g, &[], &def.ty),
                "file": file.name,
                "line": line,
                "import": namespace,
                "relation": relation_name(hit.relation),
                "place": place_name(hit.place),
                "absorbed": hit.absorbed,
                "instantiated": hit.instantiated,
                "premises": hit.hyps,
                "size": hit.size,
            });
            if query.opts.mode == Mode::Rewrite {
                v["equation"] = (if hit.iff { "iff" } else { "eq" }).into();
            }
            v
        })
        .collect();
    let budget = serde_json::json!({
        "candidates": stats.candidates,
        "compared": stats.candidates - stats.filtered_out,
        "outOfBudget": stats.resource_outs,
        "truncated": hits.len() > args.limit,
    });
    if args.json {
        println!(
            "{}",
            serde_json::json!({"version": 0, "experimental": true, "searchTier": tier,
                "results": shown, "total": hits.len(), "budget": budget})
        );
    } else {
        for (rank, s) in shown.iter().enumerate() {
            println!(
                "{:>2}. {} : {}\n    {}:{}  [{} {} {} {}]",
                rank + 1,
                s["name"].as_str().unwrap_or(""),
                s["type"].as_str().unwrap_or(""),
                s["file"].as_str().unwrap_or(""),
                s["line"],
                s["relation"].as_str().unwrap_or(""),
                s["place"].as_str().unwrap_or(""),
                s["absorbed"],
                s["instantiated"],
            );
        }
        println!("{} matches ({tier})", hits.len());
    }
    let total_constants: usize = index.iter().map(|s| s.ty.len()).sum();
    let mut sorted = matching.clone();
    sorted.sort_by(f64::total_cmp);
    eprintln!(
        "timing: load-all-std {loaded:.1} ms; imports {imported:.1} ms; enumerate {} candidates ({theorems} theorems) {enumerated:.2} ms; constants index ({total_constants} entries) {indexed:.1} ms; pattern {elaborated:.1} ms; match median {:.1} ms (min {:.1}, max {:.1}, {} runs)",
        candidates.len(),
        sorted[sorted.len() / 2],
        sorted[0],
        sorted[sorted.len() - 1],
        sorted.len(),
    );
    eprintln!(
        "stats: candidates {}, skipped by the constants filter {}, unifications {}, out of budget {}, upgraded {}",
        stats.candidates,
        stats.filtered_out,
        stats.unifications,
        stats.resource_outs,
        stats.upgraded
    );
    if let Some(p) = &pattern {
        let g = &session.elab.globals;
        let names: Vec<String> = (p.constants.iter())
            .map(|id| g.def(*id).path.to_string())
            .collect();
        eprintln!(
            "pattern: constants {names:?}; named holes' unknowns {:?}",
            p.groups
        );
    }
    ExitCode::SUCCESS
}
