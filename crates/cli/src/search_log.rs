//! The opt-in query log of `stitchwort search` (SW-915, SW-927;
//! docs/proposals/search.md §8 S1d): with `--log FILE`, or the environment
//! variable `STITCHWORT_SEARCH_LOG`, each search appends one line of JSON
//! to the file, so that what agents search for, and what they find, can be
//! read later (stage 3 tunes the ranking from it).
//!
//! Each line is an object with `log` (the format's version, 2) and `event`.
//! A later command may add other events (the lemma a proof then used); a
//! reader skips the events it doesn't know, and fields it doesn't know.
//!
//! Nothing personal is written (SW-993): no folder the command ran in
//! (version 1's `cwd`, which named the user's home), and a file's path is
//! written relative to the folder the command ran in, or as its name alone
//! when it is outside that folder. The log is a local file; nothing is
//! sent anywhere.

use std::io::Write;
use std::path::Path;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use serde_json::{Value, json};
use stitchwort_driver::search::{Options, Report};
use stitchwort_driver::search_at::AtReport;
use stitchwort_syntax::Diagnostic;

/// The log format's version: it changes when a field changes meaning or
/// goes, not when one is added. 2: `cwd` gone, paths relative (SW-993).
pub const VERSION: u32 = 2;

/// `path` as the log writes it: relative to the current folder if it is
/// inside it, else its file name alone (an absolute path names the user's
/// folders).
pub fn private_path(path: &str) -> String {
    let p = Path::new(path);
    if !p.is_absolute() {
        return path.to_string();
    }
    let inside = (std::env::current_dir().ok())
        .and_then(|cwd| p.strip_prefix(&cwd).ok().map(|r| r.display().to_string()));
    inside.unwrap_or_else(|| {
        (p.file_name()).map_or_else(String::new, |n| n.to_string_lossy().into_owned())
    })
}

/// `--at`'s text, `FILE[:LINE[:COL]]`, its file as [`private_path`] writes it.
pub fn private_at(at: &str) -> String {
    let mut file = at;
    let mut tail = String::new();
    for _ in 0..2 {
        match file.rsplit_once(':') {
            Some((head, number)) if number.parse::<usize>().is_ok() => {
                tail = format!(":{number}{tail}");
                file = head;
            }
            _ => break,
        }
    }
    format!("{}{tail}", private_path(file))
}

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
            "in": options.within,
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
    let mut entry = base("at", &private_at(at), started);
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
    // A message may name a file by its full path.
    let message = d.message.replace(
        &(std::env::current_dir().map(|c| format!("{}/", c.display()))).unwrap_or_default(),
        "",
    );
    entry.insert("error".into(), json!({"code": d.code, "message": message}));
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

#[cfg(test)]
mod tests {
    use super::*;

    /// No path the log writes names a folder outside the one the command
    /// ran in (SW-993).
    #[test]
    fn paths_are_written_relative_or_as_a_name() {
        let cwd = std::env::current_dir().expect("a current folder");
        let inside = cwd.join("src").join("Day.sw");
        assert_eq!(private_path(&inside.display().to_string()), "src/Day.sw");
        assert_eq!(private_path("/elsewhere/home/someone/goals.sw"), "goals.sw");
        assert_eq!(private_path("src/Day.sw"), "src/Day.sw");
        assert_eq!(
            private_at("/elsewhere/someone/goals.sw:3:7"),
            "goals.sw:3:7"
        );
        assert_eq!(private_at("goals.sw:3"), "goals.sw:3");
    }
}
