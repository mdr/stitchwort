//! EXPERIMENTAL: `stitchwort dev search`, the measuring prototype of lemma
//! search by type (SW-915, docs/proposals/search.md §4). Hidden, not a
//! stable interface; it prints its timings on standard error.
//!
//! Pattern syntax (a subset of the proposal's): comma-separated parts, each
//! a `"name substring"` or a type pattern (at most one). In the pattern, `_`
//! is any term, `?x` a named hole (every `?x` must match the same term), and
//! a leading `⊢` (or `|-`) matches the conclusion only.

use std::process::ExitCode;
use std::time::Instant;

use stitchwort_cli::driver::Session;
use stitchwort_core::DefId;
use stitchwort_elab::search::{self, Place, Stats};
use stitchwort_syntax::Span;

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
}

fn parse_query(text: &str) -> Query {
    let mut names = Vec::new();
    let mut pattern = None;
    let mut conclusion_only = false;
    for part in split_top(text) {
        let part = part.trim();
        if part.len() >= 2 && part.starts_with('"') && part.ends_with('"') {
            names.push(part[1..part.len() - 1].to_string());
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
                None => hits.push(search::Hit {
                    id: *id,
                    place: Place::Conclusion,
                    absorbed: 0,
                    instantiated: 0,
                }),
                Some(p) => {
                    if let Some(hit) = session.elab.search_one(
                        p,
                        *id,
                        !query.conclusion_only,
                        (!args.no_filter).then(|| &index[i]),
                        &mut stats,
                    ) {
                        hits.push(hit);
                    }
                }
            }
        }
        search::rank(g, &mut hits);
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
