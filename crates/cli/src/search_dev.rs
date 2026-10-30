//! EXPERIMENTAL: `stitchwort dev search`, the measuring prototype of lemma
//! search by type (SW-915, docs/proposals/search.md §4). Hidden, not a
//! stable interface; it prints its timings on standard error.
//!
//! Pattern syntax (a subset of the proposal's): comma-separated parts, each
//! a `"name substring"` or a type pattern (at most one). In the pattern, `_`
//! is any term, `?x` a named hole (every `?x` must match the same term), and
//! a leading `⊢` (or `|-`) matches the conclusion only.
//!
//! Draft 2's measuring directives (also comma-separated parts, so that
//! `main.rs` needn't change):
//! - `mode:rewrite` matches the two sides of an equation only;
//!   `mode:permute` and `mode:subset` let a function pattern's parameters
//!   match in another order (and, with `subset`, a theorem with more);
//! - `rank:NAME` orders the results by one of [`RANKINGS`];
//! - `self:conclusion` or `self:left` runs the self-retrieval benchmark:
//!   every std theorem's own conclusion (or left side, in `mode:rewrite`)
//!   as a pattern, reporting where the theorem ranks under each ranking.

use std::collections::BTreeSet;
use std::process::ExitCode;
use std::time::Instant;

use stitchwort_cli::driver::Session;
use stitchwort_core::{DefId, Globals};
use stitchwort_elab::search::{self, Hit, Mode, Place, Side, Stats};
use stitchwort_syntax::Span;

/// The rankings compared in draft 2 §5.1, by name.
const RANKINGS: [&str; 8] = [
    "draft1",
    "draft1+hyps",
    "isabelle",
    "rocq",
    "loogle",
    "proposed",
    "proposed+rare",
    "rare-first",
];

/// What the rankings need besides a hit: per candidate, the constants its
/// type names, and per constant, how rare it is.
struct Rarity {
    /// `ln(N / df)` for each constant, times 100, where `df` is how many
    /// candidates name it (inverse document frequency, as MaSh weights
    /// features).
    idf: std::collections::BTreeMap<DefId, i64>,
}

impl Rarity {
    fn new(index: &[BTreeSet<DefId>]) -> Rarity {
        let mut df: std::collections::BTreeMap<DefId, usize> = Default::default();
        for set in index {
            for c in set {
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
        _ => vec![place, a, i, namelen],
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

/// A pattern split into its parts.
struct Query {
    names: Vec<String>,
    /// The type pattern with each `?x` written as `_`, and the offsets of
    /// each named hole's occurrences.
    pattern: Option<(String, Vec<Vec<u32>>)>,
    conclusion_only: bool,
    mode: Mode,
    ranking: String,
    self_retrieval: Option<Side>,
}

fn parse_query(text: &str) -> Query {
    let mut names = Vec::new();
    let mut pattern = None;
    let mut conclusion_only = false;
    let mut mode = Mode::Plain;
    let mut ranking = "draft1".to_string();
    let mut self_retrieval = None;
    for part in split_top(text) {
        let part = part.trim();
        if part.len() >= 2 && part.starts_with('"') && part.ends_with('"') {
            names.push(part[1..part.len() - 1].to_string());
            continue;
        }
        if let Some(m) = part.strip_prefix("mode:") {
            mode = match m.trim() {
                "rewrite" => Mode::Rewrite,
                "permute" => Mode::Permute,
                "subset" => Mode::Subset,
                _ => Mode::Plain,
            };
            continue;
        }
        if let Some(r) = part.strip_prefix("rank:") {
            ranking = r.trim().to_string();
            continue;
        }
        if let Some(s) = part.strip_prefix("self:") {
            self_retrieval = Some(if s.trim() == "left" {
                Side::Left
            } else {
                Side::Conclusion
            });
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
    Query {
        names,
        pattern,
        conclusion_only,
        mode,
        ranking,
        self_retrieval,
    }
}

/// The self-retrieval benchmark (draft 2 §6.1): each theorem's own
/// conclusion (or left side) as a pattern; where does the theorem rank?
fn self_retrieval(
    session: &mut Session,
    candidates: &[DefId],
    index: &[BTreeSet<DefId>],
    side: Side,
    no_filter: bool,
) {
    let start = Instant::now();
    let rarity = Rarity::new(index);
    let mode = if side == Side::Left {
        Mode::Rewrite
    } else {
        Mode::Plain
    };
    // Per ranking: each query's optimistic rank (1 + hits strictly before
    // it) and pessimistic rank (hits not after it, itself included).
    let mut ranks: Vec<Vec<(usize, usize)>> = vec![Vec::new(); RANKINGS.len()];
    let mut queries = 0;
    let mut skipped = 0;
    let mut missed: Vec<String> = Vec::new();
    let mut hit_counts: Vec<usize> = Vec::new();
    let mut stats = Stats::default();
    let mut panics: Vec<String> = Vec::new();
    std::panic::set_hook(Box::new(|_| {}));
    for (t, id) in candidates.iter().enumerate() {
        if !session.elab.globals.def(*id).theorem {
            continue;
        }
        let Some(pattern) = session.elab.theorem_pattern(*id, side) else {
            skipped += 1;
            continue;
        };
        queries += 1;
        let mut hits: Vec<(Hit, usize)> = Vec::new();
        for (i, other) in candidates.iter().enumerate() {
            if !session.elab.globals.def(*other).theorem {
                continue;
            }
            // An internal error in one comparison is counted, not fatal:
            // the benchmark is also a robustness test.
            let elab = &session.elab;
            let attempt = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let mut s = Stats::default();
                let hit = elab.search_one(
                    &pattern,
                    *other,
                    false,
                    mode,
                    (!no_filter).then(|| &index[i]),
                    &mut s,
                );
                (hit, s)
            }));
            match attempt {
                Ok((hit, s)) => {
                    stats.unifications += s.unifications;
                    stats.resource_outs += s.resource_outs;
                    if let Some(hit) = hit {
                        hits.push((hit, i));
                    }
                }
                Err(_) => {
                    let g = &session.elab.globals;
                    panics.push(format!(
                        "{} against {}",
                        g.def(*id).path,
                        g.def(*other).path
                    ));
                    // Leave the session as a failed attempt would.
                    let _ = session.elab.theorem_pattern(*id, side);
                }
            }
        }
        hit_counts.push(hits.len());
        let g = &session.elab.globals;
        let Some((own, _)) = hits.iter().find(|(h, _)| h.id == *id) else {
            missed.push(g.def(*id).path.to_string());
            continue;
        };
        for (r, name) in RANKINGS.iter().enumerate() {
            let k = |h: &Hit, i: usize| key(name, g, h, &index[i], &pattern.constants, &rarity);
            let mine = k(own, t);
            let before = hits.iter().filter(|(h, i)| k(h, *i) < mine).count();
            let not_after = hits.iter().filter(|(h, i)| k(h, *i) <= mine).count();
            ranks[r].push((before + 1, not_after));
        }
    }
    let ms = start.elapsed().as_secs_f64() * 1000.0;
    hit_counts.sort();
    let pct = |p: f64| {
        hit_counts
            .get(((hit_counts.len() as f64 - 1.0) * p) as usize)
            .copied()
            .unwrap_or(0)
    };
    println!(
        "self-retrieval ({:?}): {queries} queries ({skipped} theorems skipped: no pattern), {} not found, {ms:.0} ms",
        side,
        missed.len()
    );
    println!(
        "hits per query: median {}, p90 {}, p99 {}, max {}",
        pct(0.5),
        pct(0.9),
        pct(0.99),
        pct(1.0)
    );
    println!(
        "stats: unifications {}, out of budget {}",
        stats.unifications, stats.resource_outs
    );
    println!("ranking       rank1(opt)  top3(opt)  top10(opt)  MRR(opt)  rank1(pess)  mean-pess");
    for (r, name) in RANKINGS.iter().enumerate() {
        let v = &ranks[r];
        let n = v.len().max(1) as f64;
        let share = |f: &dyn Fn(&(usize, usize)) -> bool| {
            100.0 * v.iter().filter(|x| f(x)).count() as f64 / n
        };
        let mrr = v.iter().map(|(o, _)| 1.0 / *o as f64).sum::<f64>() / n;
        let mean_pess = v.iter().map(|(_, p)| *p as f64).sum::<f64>() / n;
        println!(
            "{name:<13} {:>9.1}%  {:>8.1}%  {:>9.1}%  {:>8.3}  {:>10.1}%  {:>9.2}",
            share(&|x| x.0 == 1),
            share(&|x| x.0 <= 3),
            share(&|x| x.0 <= 10),
            mrr,
            share(&|x| x.1 == 1),
            mean_pess,
        );
    }
    println!("internal errors (panics): {}", panics.len());
    for p in panics.iter().take(25) {
        println!("panic: {p}");
    }
    for name in missed.iter().take(25) {
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
    // The candidates and, per candidate, the constants its type names.
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
    let index: Vec<std::collections::BTreeSet<DefId>> = candidates
        .iter()
        .map(|id| session.elab.type_constants(*id))
        .collect();
    let indexed = ms(start);
    let query = parse_query(&args.pattern);
    if let Some(side) = query.self_retrieval {
        eprintln!("timing: load-all-std {loaded:.1} ms; constants index {indexed:.1} ms");
        self_retrieval(session, &candidates, &index, side, args.no_filter);
        return ExitCode::SUCCESS;
    }
    let rarity = Rarity::new(&index);
    let position: std::collections::BTreeMap<DefId, usize> = candidates
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
    for _ in 0..args.repeat.max(1) {
        let start = Instant::now();
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
                        absorbed: 0,
                        instantiated: 0,
                        size,
                        hyps,
                    })
                }
                Some(p) => {
                    if let Some(hit) = session.elab.search_one(
                        p,
                        *id,
                        !query.conclusion_only,
                        query.mode,
                        (!args.no_filter).then(|| &index[i]),
                        &mut stats,
                    ) {
                        hits.push(hit);
                    }
                }
            }
        }
        if query.ranking == "draft1" {
            search::rank(g, &mut hits);
        } else {
            let none = BTreeSet::new();
            let ours = pattern.as_ref().map(|p| &p.constants).unwrap_or(&none);
            hits.sort_by_cached_key(|h| {
                let k = key(&query.ranking, g, h, &index[position[&h.id]], ours, &rarity);
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
            serde_json::json!({
                "name": path,
                "type": stitchwort_core::pretty::term(g, &[], &def.ty),
                "file": file.name,
                "line": line,
                "import": namespace,
                "place": format!("{:?}", hit.place).to_lowercase(),
                "absorbed": hit.absorbed,
                "instantiated": hit.instantiated,
            })
        })
        .collect();
    if args.json {
        println!(
            "{}",
            serde_json::json!({"version": 0, "experimental": true, "results": shown, "total": hits.len()})
        );
    } else {
        for (rank, s) in shown.iter().enumerate() {
            println!(
                "{:>2}. {} : {}\n    {}:{}  [{} {} {}]",
                rank + 1,
                s["name"].as_str().unwrap_or(""),
                s["type"].as_str().unwrap_or(""),
                s["file"].as_str().unwrap_or(""),
                s["line"],
                s["place"].as_str().unwrap_or(""),
                s["absorbed"],
                s["instantiated"],
            );
        }
        println!("{} matches", hits.len());
    }
    let total_constants: usize = index.iter().map(|s| s.len()).sum();
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
        "stats: candidates {}, skipped by the constants filter {}, unifications {}, out of budget {}",
        stats.candidates, stats.filtered_out, stats.unifications, stats.resource_outs
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
