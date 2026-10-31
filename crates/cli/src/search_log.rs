//! The opt-in query log of `stitchwort search` (SW-915, SW-927;
//! docs/proposals/search.md §8 S1d): with `--log FILE`, or the environment
//! variable `STITCHWORT_SEARCH_LOG`, each search appends one line of JSON
//! to the file, so that what agents search for, and what they find, can be
//! read later (stage 3 tunes the ranking from it).
//!
//! Each line is an object with `log` (the format's version, 1) and `event`.
//! A later command may add other events (the lemma a proof then used); a
//! reader skips the events it doesn't know, and fields it doesn't know.

use std::io::Write;
use std::path::Path;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use serde_json::{Value, json};
use stitchwort_driver::search::{Options, Report};
use stitchwort_driver::search_at::AtReport;
use stitchwort_syntax::Diagnostic;

/// The log format's version: it changes when a field changes meaning or
/// goes, not when one is added.
pub const VERSION: u32 = 1;

fn now() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_secs())
}

fn base(event: &str, query: &str, started: Instant) -> serde_json::Map<String, Value> {
    let mut entry = serde_json::Map::new();
    entry.insert("log".into(), json!(VERSION));
    entry.insert("event".into(), json!(event));
    entry.insert("time".into(), json!(now()));
    entry.insert("ms".into(), json!(started.elapsed().as_millis() as u64));
    if let Ok(cwd) = std::env::current_dir() {
        entry.insert("cwd".into(), json!(cwd.display().to_string()));
    }
    entry.insert("query".into(), json!(query));
    entry
}

/// The line for a search that ran: `event: "search"`, the query and what it
/// elaborated to (each reading, for overloaded operators), the options, the
/// scope, and every result shown, with its rank (1 first), kind, relation
/// and place.
pub fn entry(report: &Report, options: &Options, scope: Value, started: Instant) -> Value {
    let mut entry = base("search", &report.query.text, started);
    let elaborated: Vec<&String> = if report.query.resolutions.is_empty() {
        report.query.elaborated.iter().collect()
    } else {
        report.query.resolutions.iter().collect()
    };
    entry.insert("elaborated".into(), json!(elaborated));
    entry.insert(
        "options".into(),
        json!({
            "rewrite": options.rewrite,
            "kinds": report.query.kinds,
            "all": options.all,
            "limit": options.limit,
        }),
    );
    entry.insert("scope".into(), scope);
    entry.insert("searchTier".into(), json!(report.search_tier));
    entry.insert("total".into(), json!(report.total));
    let results: Vec<Value> = (report.results.iter().enumerate())
        .map(|(i, r)| {
            json!({
                "rank": i + 1,
                "name": r.name,
                "kind": r.kind,
                "relation": r.relation,
                "place": r.place,
            })
        })
        .collect();
    entry.insert("results".into(), json!(results));
    entry.insert(
        "budget".into(),
        json!({
            "compared": report.budget.compared,
            "outOfBudget": report.budget.out_of_budget,
            "internalErrors": report.budget.internal_errors,
        }),
    );
    Value::Object(entry)
}

/// The line for `search --at`: `event: "at"`, `query` the `--at` text, the
/// goal, and each suggestion with its rank, class, name and proof.
pub fn at_entry(at: &str, report: &AtReport, started: Instant) -> Value {
    let mut entry = base("at", at, started);
    entry.insert(
        "goal".into(),
        json!({"hypotheses": report.goal.hypotheses.len(), "target": report.goal.target}),
    );
    let results: Vec<Value> = (report.results.iter().enumerate())
        .map(|(i, s)| {
            json!({"rank": i + 1, "class": s.class, "name": s.name, "proof": s.proof,
                   "goals": s.goals.len()})
        })
        .collect();
    entry.insert("results".into(), json!(results));
    let rewrites: Vec<Value> = (report.rewrites.iter().enumerate())
        .map(|(i, r)| json!({"rank": i + 1, "name": r.name, "proof": r.proof, "closes": r.closes}))
        .collect();
    entry.insert("rewrites".into(), json!(rewrites));
    entry.insert("total".into(), json!(report.total));
    entry.insert(
        "budget".into(),
        json!({"matched": report.budget.matched, "tried": report.budget.tried,
               "checks": report.budget.checks, "exhausted": report.budget.exhausted}),
    );
    Value::Object(entry)
}

/// The line for a query that didn't parse or elaborate: `event: "search"`,
/// with `error` (its code and message) in place of results.
pub fn error_entry(query: &str, d: &Diagnostic, started: Instant) -> Value {
    let mut entry = base("search", query, started);
    entry.insert(
        "error".into(),
        json!({"code": d.code, "message": d.message}),
    );
    Value::Object(entry)
}

/// Appends `entry` as one line to `path`. A log that can't be written is a
/// warning, never a failed search.
pub fn append(path: &Path, entry: &Value) {
    let written = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .and_then(|mut f| writeln!(f, "{entry}"));
    if let Err(err) = written {
        eprintln!(
            "warning: can't write the search log {}: {err}",
            path.display()
        );
    }
}
