//! Read-only tools for reasoning about check-cache keys: `stitchwort dev
//! keys` (each namespace's entry key and what it was made from) and `dev
//! cache-compare` (which entries two cache folders share), SW-4822 and
//! SW-4839. They change no key, entry or result.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use stitchwort_syntax::Diagnostic;

use crate::driver::Session;
use crate::project::{Files, Load, Target, analyse, canonical_order, closure, project_sources};

/// One namespace of a project: what it uses and its entry.
pub struct KeyLine {
    pub namespace: String,
    /// The namespaces it uses directly.
    pub uses: Vec<String>,
    /// Every namespace it depends on, in canonical order: the ones its key
    /// takes a digest (or text key) of.
    pub closure: Vec<String>,
    /// The entry's unit and key, as in its file name; `None` if the
    /// namespace has syntax errors or its key couldn't be made.
    pub entry: Option<(String, String)>,
    /// The entry's digest (what dependents' keys take of it); `None` if the
    /// entry wasn't written or replayed.
    pub digest: Option<String>,
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Checks the project in `files` with `session` (which may use a check
/// cache), as a plain `check` of every namespace does, and says for each
/// namespace what it uses and its cache key, in canonical order. The
/// diagnostics of the check are not reported: only the keys.
pub fn explain_keys(
    session: &mut Session,
    files: &dyn Files,
    project: &str,
) -> Result<Vec<KeyLine>, Vec<Diagnostic>> {
    let sources = project_sources(files, project, &mut session.sources)?;
    let analysis = analyse(session, project, sources);
    let all: BTreeSet<String> = analysis.namespaces.iter().map(|n| n.name.clone()).collect();
    let order = canonical_order(&analysis, &all).map_err(|_| {
        vec![Diagnostic::error(
            "E-NAMESPACE-CYCLE",
            "the project's namespaces use each other in a cycle",
        )]
    })?;
    let mut lines: Vec<KeyLine> = Vec::new();
    for name in &order {
        let ns = analysis.namespace(name).expect("a namespace");
        let uses: BTreeSet<String> = ns.edges.iter().map(|e| e.target.clone()).collect();
        let deps: BTreeSet<String> = closure(&analysis, std::slice::from_ref(name))
            .into_iter()
            .filter(|n| n != name)
            .collect();
        lines.push(KeyLine {
            namespace: name.clone(),
            uses: uses.into_iter().collect(),
            closure: canonical_order(&analysis, &deps).unwrap_or_default(),
            entry: None,
            digest: None,
        });
    }
    // The check's outcome (diagnostics) doesn't matter here; the keys it
    // recorded do.
    let _ = session.load_analysis_for(project, analysis, &Target::Everything, Load::Diagnostics);
    let keys = session.elab.namespace_key_report();
    for line in &mut lines {
        if let Some(report) = keys.get(&line.namespace) {
            line.entry = Some((report.unit.clone(), hex(&report.key)));
            line.digest = report.digest.as_ref().map(|d| hex(d));
        }
    }
    Ok(lines)
}

/// [`explain_keys`]' lines as text: one line a namespace, then what it
/// uses. `entry` is the entry's file name without the build prefix.
pub fn render_keys(lines: &[KeyLine]) -> String {
    let mut out = String::new();
    for line in lines {
        let entry = match &line.entry {
            Some((unit, key)) => format!("{unit}-{key}"),
            None => "no key".to_string(),
        };
        let digest = line.digest.as_deref().unwrap_or("none");
        out.push_str(&format!(
            "{}\tentry {entry}\tdigest {digest}\n",
            line.namespace
        ));
        let list = |names: &[String]| {
            if names.is_empty() {
                "nothing".to_string()
            } else {
                names.join(", ")
            }
        };
        out.push_str(&format!("\tuses {}\n", list(&line.uses)));
        out.push_str(&format!("\tdepends on {}\n", list(&line.closure)));
    }
    out
}

/// The entries of the check cache in `dir` (a cache folder, or its `check`
/// folder): (unit, key) of each entry file, with the build prefix
/// stripped, and how many files of each unit kind that are left out:
/// `scan…` and `ran…` entries (their keys are salted by the folder, so
/// they say nothing about a change) and anything else that isn't a
/// namespace's or a library file's.
pub struct Entries {
    pub entries: BTreeSet<(String, String)>,
    pub left_out: BTreeMap<String, usize>,
}

pub fn read_entries(dir: &Path) -> std::io::Result<Entries> {
    let check = if dir.join("check").is_dir() {
        dir.join("check")
    } else {
        dir.to_path_buf()
    };
    let mut entries = BTreeSet::new();
    let mut left_out: BTreeMap<String, usize> = BTreeMap::new();
    for entry in std::fs::read_dir(&check)? {
        let name = entry?.file_name().to_string_lossy().into_owned();
        if name == "header" || name.contains(".tmp") {
            continue;
        }
        // `{build}-{unit}-{key}`: the build and the key have no `-`.
        let Some((_, rest)) = name.split_once('-') else {
            continue;
        };
        let Some((unit, key)) = rest.rsplit_once('-') else {
            continue;
        };
        if unit.starts_with("ns.") || unit.starts_with("std.") {
            entries.insert((unit.to_string(), key.to_string()));
        } else {
            let kind = if unit.starts_with("scan") {
                "scan"
            } else if unit.starts_with("ran") {
                "ran"
            } else {
                "other"
            };
            *left_out.entry(kind.to_string()).or_default() += 1;
        }
    }
    Ok(Entries { entries, left_out })
}

/// What two cache folders hold, entries compared by unit and key.
pub struct Comparison {
    pub only_in_a: Vec<(String, String)>,
    pub only_in_b: Vec<(String, String)>,
    pub same: usize,
    pub left_out_a: BTreeMap<String, usize>,
    pub left_out_b: BTreeMap<String, usize>,
}

pub fn compare(a: &Path, b: &Path) -> std::io::Result<Comparison> {
    let (ea, eb) = (read_entries(a)?, read_entries(b)?);
    Ok(Comparison {
        only_in_a: ea.entries.difference(&eb.entries).cloned().collect(),
        only_in_b: eb.entries.difference(&ea.entries).cloned().collect(),
        same: ea.entries.intersection(&eb.entries).count(),
        left_out_a: ea.left_out,
        left_out_b: eb.left_out,
    })
}

impl Comparison {
    pub fn identical(&self) -> bool {
        self.only_in_a.is_empty() && self.only_in_b.is_empty()
    }

    pub fn render(&self) -> String {
        let mut out = String::new();
        let mut section = |title: &str, list: &[(String, String)]| {
            out.push_str(&format!("only in {title}: {}\n", list.len()));
            for (unit, key) in list {
                out.push_str(&format!("  {unit}-{key}\n"));
            }
        };
        section("A", &self.only_in_a);
        section("B", &self.only_in_b);
        out.push_str(&format!("same: {}\n", self.same));
        let left = |m: &BTreeMap<String, usize>| {
            if m.is_empty() {
                "none".to_string()
            } else {
                (m.iter())
                    .map(|(k, n)| format!("{n} {k}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            }
        };
        out.push_str(&format!(
            "left out (build-specific): A {}; B {}\n",
            left(&self.left_out_a),
            left(&self.left_out_b)
        ));
        out
    }
}
