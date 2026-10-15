//! The recorded baseline (`bench/baseline.toml`), and comparing a run with
//! it.
//!
//! The file is a small subset of TOML, one table per benchmark, so that a
//! change to it reads well in a diff:
//!
//! ```toml
//! [eval-lengths]
//! steps = 12345678
//! visits = 234567
//! allocations = 2345678
//! peak_bytes = 3456789
//! time_ms = 950.2
//! ```

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use crate::{Counts, Record};

/// Where the baseline is kept.
pub fn default_path() -> PathBuf {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).ancestors().nth(2);
    root.expect("the workspace").join("bench/baseline.toml")
}

/// A count more than this fraction above the baseline is a regression.
pub const COUNT_THRESHOLD: f64 = 0.10;
/// A time more than this fraction above the baseline, and more than
/// [`TIME_FLOOR_MS`] above it, is a regression.
pub const TIME_THRESHOLD: f64 = 0.50;
/// Below this, a difference in time is noise whatever its ratio.
pub const TIME_FLOOR_MS: f64 = 20.0;

/// Benchmark records by name, in the order they're written.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Baseline {
    pub records: Vec<(String, Record)>,
}

const HEADER: &str = "\
# Benchmark baseline (docs/testing.md, \"Benchmarks\"). Written by
#   cargo run --release -p stitchwort-bench -- --update
# steps, visits, allocations and peak_bytes are deterministic: the same on
# every run.
# time_ms is the median wall time on the machine that recorded it.
";

impl Baseline {
    pub fn get(&self, name: &str) -> Option<&Record> {
        self.records.iter().find(|(n, _)| n == name).map(|(_, r)| r)
    }

    /// Replaces the record for `name`, or adds it at the end.
    pub fn set(&mut self, name: &str, record: Record) {
        match self.records.iter_mut().find(|(n, _)| n == name) {
            Some((_, r)) => *r = record,
            None => self.records.push((name.to_string(), record)),
        }
    }

    pub fn to_toml(&self) -> String {
        let mut out = HEADER.to_string();
        for (name, r) in &self.records {
            let _ = writeln!(out, "\n[{name}]");
            if let Some(inputs) = &r.inputs {
                let _ = writeln!(out, "inputs = \"{inputs}\"");
            }
            let _ = writeln!(out, "steps = {}", r.counts.steps);
            let _ = writeln!(out, "visits = {}", r.counts.visits);
            let _ = writeln!(out, "allocations = {}", r.counts.allocations);
            let _ = writeln!(out, "peak_bytes = {}", r.counts.peak_bytes);
            if let Some(ms) = r.time_ms {
                let _ = writeln!(out, "time_ms = {ms:.1}");
            }
        }
        out
    }

    pub fn parse(text: &str) -> Result<Baseline, String> {
        let mut baseline = Baseline::default();
        // The table being read, and its fields so far.
        let mut table: Option<(String, Fields)> = None;
        for (i, line) in text.lines().enumerate() {
            let line = line.trim();
            let error = |what: &str| format!("line {}: {what}: {line}", i + 1);
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if let Some(name) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
                if let Some((name, fields)) = table.take() {
                    baseline.records.push((name.clone(), fields.record(&name)?));
                }
                table = Some((name.to_string(), Fields::default()));
                continue;
            }
            let Some((_, fields)) = &mut table else {
                return Err(error("a field outside a table"));
            };
            let Some((key, value)) = line.split_once('=') else {
                return Err(error("expected `key = value`"));
            };
            let value = value.trim();
            let int = || value.parse::<u64>().map_err(|_| error("expected a count"));
            match key.trim() {
                "inputs" => {
                    let s = value.strip_prefix('"').and_then(|v| v.strip_suffix('"'));
                    fields.inputs = Some(s.ok_or_else(|| error("expected a string"))?.into());
                }
                "steps" => fields.steps = Some(int()?),
                "visits" => fields.visits = Some(int()?),
                "allocations" => fields.allocations = Some(int()?),
                "peak_bytes" => fields.peak_bytes = Some(int()?),
                "time_ms" => {
                    let ms = value
                        .parse::<f64>()
                        .map_err(|_| error("expected a number"))?;
                    fields.time_ms = Some(ms);
                }
                _ => return Err(error("unknown field")),
            }
        }
        if let Some((name, fields)) = table {
            baseline.records.push((name.clone(), fields.record(&name)?));
        }
        Ok(baseline)
    }

    /// Reads the baseline at `path`: empty if there's no file.
    pub fn read(path: &Path) -> Result<Baseline, String> {
        match std::fs::read_to_string(path) {
            Ok(text) => Baseline::parse(&text).map_err(|e| format!("{}: {e}", path.display())),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(Baseline::default()),
            Err(e) => Err(format!("{}: {e}", path.display())),
        }
    }
}

#[derive(Default)]
struct Fields {
    inputs: Option<String>,
    steps: Option<u64>,
    visits: Option<u64>,
    allocations: Option<u64>,
    peak_bytes: Option<u64>,
    time_ms: Option<f64>,
}

impl Fields {
    fn record(self, name: &str) -> Result<Record, String> {
        let missing = |field: &str| format!("[{name}] has no `{field}`");
        Ok(Record {
            counts: Counts {
                steps: self.steps.ok_or_else(|| missing("steps"))?,
                visits: self.visits.ok_or_else(|| missing("visits"))?,
                allocations: self.allocations.ok_or_else(|| missing("allocations"))?,
                peak_bytes: self.peak_bytes.ok_or_else(|| missing("peak_bytes"))?,
            },
            inputs: self.inputs,
            time_ms: self.time_ms,
        })
    }
}

/// How a run compares with the baseline.
#[derive(Default)]
pub struct Comparison {
    /// A table of every benchmark's measures and their changes.
    pub table: String,
    /// Changes past a threshold, and other problems: each fails the run.
    pub regressions: Vec<String>,
    /// Things worth knowing that don't fail the run.
    pub notes: Vec<String>,
}

impl Comparison {
    pub fn failed(&self) -> bool {
        !self.regressions.is_empty()
    }
}

impl std::fmt::Display for Comparison {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.table)?;
        for note in &self.notes {
            writeln!(f, "note: {note}")?;
        }
        for regression in &self.regressions {
            writeln!(f, "REGRESSION: {regression}")?;
        }
        Ok(())
    }
}

/// `n` with thousands separators.
fn count(n: u64) -> String {
    let digits = n.to_string();
    let mut out = String::new();
    for (i, c) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(c);
    }
    out
}

fn megabytes(bytes: u64) -> String {
    if bytes < 1_000_000 {
        format!("{:.0} kB", bytes as f64 / 1e3)
    } else {
        format!("{:.1} MB", bytes as f64 / 1e6)
    }
}

fn change(now: f64, base: f64) -> f64 {
    if base == 0.0 {
        if now == 0.0 { 0.0 } else { f64::INFINITY }
    } else {
        now / base - 1.0
    }
}

fn percent(change: f64) -> String {
    format!("{:+.1}%", change * 100.0)
}

/// The counts, as (name in the file and table, value, whether it's bytes).
fn counts(c: &Counts) -> [(&'static str, u64, bool); 4] {
    [
        ("steps", c.steps, false),
        ("visits", c.visits, false),
        ("allocations", c.allocations, false),
        ("peak heap", c.peak_bytes, true),
    ]
}

/// Columns: a value and its change.
const WIDTHS: [usize; 5] = [14, 13, 12, 9, 8];

/// Compares `results` (by benchmark name, in suite order) with `baseline`.
/// Measures are compared only for the same inputs, and times only if both
/// have one. Unless `partial`, every benchmark in the baseline should have
/// been run.
pub fn compare(baseline: &Baseline, results: &[(&str, &Record)], partial: bool) -> Comparison {
    let mut c = Comparison::default();
    let width = results.iter().map(|(n, _)| n.len()).max().unwrap_or(0);
    let mut header = format!("{:width$}", "");
    for (label, w) in ["steps", "visits", "allocations", "peak heap", "time"]
        .into_iter()
        .zip(WIDTHS)
    {
        let _ = write!(header, "  {label:>w$} {:7}", "");
    }
    let _ = writeln!(c.table, "{}", header.trim_end());
    for &(name, now) in results {
        let base = baseline.get(name);
        let comparable = base.filter(|b| b.inputs == now.inputs);
        match base {
            None => c.notes.push(format!("{name} isn't in the baseline")),
            Some(b) if comparable.is_none() => c.notes.push(format!(
                "{name}: the inputs have changed (baseline: {}; now: {}), so it wasn't \
                 compared; update the baseline",
                b.inputs.as_deref().unwrap_or("none"),
                now.inputs.as_deref().unwrap_or("none"),
            )),
            Some(_) => {}
        }
        let mut row = format!("{name:width$}");
        let before = comparable.map(|b| counts(&b.counts));
        for (i, (what, n, bytes)) in counts(&now.counts).into_iter().enumerate() {
            let show = |n: u64| if bytes { megabytes(n) } else { count(n) };
            let b = before.map(|b| b[i].1);
            let delta = b.map(|b| change(n as f64, b as f64));
            let w = WIDTHS[i];
            let _ = write!(
                row,
                "  {:>w$} {:>7}",
                show(n),
                delta.map_or(String::new(), percent)
            );
            let Some((b, delta)) = b.zip(delta) else {
                continue;
            };
            if delta > COUNT_THRESHOLD {
                c.regressions.push(format!(
                    "{name}: {what} {} ({} → {}), over the {} threshold",
                    percent(delta),
                    show(b),
                    show(n),
                    percent(COUNT_THRESHOLD)
                ));
            } else if delta < -COUNT_THRESHOLD {
                c.notes.push(format!(
                    "{name}: {what} {} ({} → {}): an improvement; update the baseline to keep it",
                    percent(delta),
                    show(b),
                    show(n)
                ));
            }
        }
        if let Some(ms) = now.time_ms {
            let b = comparable.and_then(|b| b.time_ms);
            let delta = b.map(|b| change(ms, b));
            let w = WIDTHS[4];
            let _ = write!(
                row,
                "  {:>w$} {:>7}",
                format!("{ms:.0} ms"),
                delta.map_or(String::new(), percent)
            );
            if let Some((b, delta)) = b.zip(delta)
                && delta > TIME_THRESHOLD
                && ms - b > TIME_FLOOR_MS
            {
                c.regressions.push(format!(
                    "{name}: time {} ({b:.0} ms → {ms:.0} ms), over the {} threshold \
                     (time is noisy: if no count has changed, run it again on a quiet machine)",
                    percent(delta),
                    percent(TIME_THRESHOLD)
                ));
            }
        }
        let _ = writeln!(c.table, "{}", row.trim_end());
    }
    for (name, _) in &baseline.records {
        if !partial && !results.iter().any(|(n, _)| n == name) {
            c.notes
                .push(format!("{name} is in the baseline but wasn't run"));
        }
    }
    c
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(steps: u64, allocations: u64, peak_bytes: u64, time_ms: Option<f64>) -> Record {
        Record {
            counts: Counts {
                steps,
                visits: 500,
                allocations,
                peak_bytes,
            },
            inputs: None,
            time_ms,
        }
    }

    fn baseline() -> Baseline {
        let mut b = Baseline::default();
        b.set("a", record(1000, 2000, 3000, Some(100.0)));
        b.set(
            "b",
            Record {
                inputs: Some("3 files, 0123456789abcdef".into()),
                ..record(10, 20, 30, None)
            },
        );
        b
    }

    #[test]
    fn the_file_format_round_trips() {
        let b = baseline();
        assert_eq!(Baseline::parse(&b.to_toml()), Ok(b));
    }

    #[test]
    fn malformed_files_are_errors() {
        assert!(Baseline::parse("steps = 1").is_err());
        assert!(Baseline::parse("[a]\nsteps = 1\n").is_err());
        assert!(Baseline::parse("[a]\nsteps = x\n").is_err());
        let complete = "[a]\nsteps = 1\nvisits = 2\nallocations = 3\npeak_bytes = 4\n";
        assert!(Baseline::parse(complete).is_ok());
        assert!(Baseline::parse(&format!("{complete}more = 5\n")).is_err());
    }

    #[test]
    fn counts_just_past_the_threshold_are_regressions() {
        let b = baseline();
        let within = record(1099, 2000, 3000, None);
        assert!(!compare(&b, &[("a", &within)], true).failed());
        let past = record(1000, 2201, 3000, None);
        let c = compare(&b, &[("a", &past)], true);
        assert!(c.failed());
        assert!(c.regressions[0].contains("allocations +10.1%"), "{c}");
    }

    #[test]
    fn improvements_are_notes() {
        let c = compare(&baseline(), &[("a", &record(10, 20, 30, None))], true);
        assert!(!c.failed());
        assert_eq!(c.notes.len(), 3, "{c}");
    }

    #[test]
    fn time_needs_both_the_ratio_and_the_floor() {
        let b = baseline();
        // +60% but only 60 ms more: over both.
        assert!(compare(&b, &[("a", &record(1000, 2000, 3000, Some(160.0)))], true).failed());
        // +40%: under the ratio.
        assert!(!compare(&b, &[("a", &record(1000, 2000, 3000, Some(140.0)))], true).failed());
        let mut small = Baseline::default();
        small.set("a", record(1000, 2000, 3000, Some(10.0)));
        // +100% but only 10 ms more: under the floor.
        assert!(
            !compare(
                &small,
                &[("a", &record(1000, 2000, 3000, Some(20.0)))],
                true
            )
            .failed()
        );
    }

    #[test]
    fn counts_for_other_inputs_are_not_compared() {
        let now = Record {
            inputs: Some("4 files, fedcba9876543210".into()),
            ..record(1000, 2000, 3000, None)
        };
        let c = compare(&baseline(), &[("b", &now)], true);
        assert!(!c.failed());
        assert!(c.notes[0].contains("inputs have changed"), "{c}");
    }

    #[test]
    fn counts_have_separators() {
        assert_eq!(count(0), "0");
        assert_eq!(count(999), "999");
        assert_eq!(count(1000), "1,000");
        assert_eq!(count(1234567), "1,234,567");
    }
}
