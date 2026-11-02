//! `stitchwort doc --coverage` (SW-1025, docs/proposals/documentation.md
//! §6.2, D2138, D2148): how much of a namespace is documented, from parsing
//! alone.
//!
//! Definitions, types, interfaces and abilities are counted together;
//! theorems are counted apart and never mixed into that figure. A doc that
//! repeats the name, or is under four words, counts as missing (D2148). Only
//! `--|` lines make a doc: a plain `--` comment above a declaration counts as
//! no doc (SW-1044).

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;
use stitchwort_syntax::docs::Doc;

use super::{Decls, Kind, Within};

/// A doc shorter than this many words counts as missing (D2148).
const MIN_WORDS: usize = 4;

/// Counts for one kind of figure.
#[derive(Serialize, Debug, Default, Clone)]
#[serde(rename_all = "camelCase")]
pub struct Counts {
    pub total: usize,
    /// With a doc that counts (not missing, not too short, not the name).
    pub documented: usize,
    /// With an example attached by name; not for theorems.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub with_example: Option<usize>,
}

/// A declaration whose doc is missing, or doesn't count.
#[derive(Serialize, Debug, Clone)]
pub struct Missing {
    pub name: String,
    pub kind: &'static str,
    pub file: String,
    pub line: usize,
    /// `no doc`, `too short` or `repeats the name`.
    pub reason: &'static str,
}

/// An `…Example` theorem whose base name is not a definition or theorem.
#[derive(Serialize, Debug, Clone)]
pub struct Unattached {
    pub name: String,
    pub file: String,
    pub line: usize,
}

/// One namespace's coverage.
#[derive(Serialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct NamespaceCoverage {
    pub namespace: String,
    /// Whether documenting everything is the aim here: true for the library
    /// (`Std.*`), false for a project's code, which is documented
    /// sparingly (SW-1100).
    pub target: bool,
    /// Definitions, types, interfaces and abilities.
    pub declarations: Counts,
    /// Theorems, apart.
    pub theorems: Counts,
    /// The declarations with no doc that counts.
    pub undocumented: Vec<Missing>,
    /// The theorems with no doc that counts.
    pub undocumented_theorems: Vec<Missing>,
    pub unattached_examples: Vec<Unattached>,
}

/// The JSON contract of `doc --coverage`, version 1.
#[derive(Serialize, Debug)]
pub struct Coverage {
    pub version: u32,
    pub namespaces: Vec<NamespaceCoverage>,
    /// Over all of them together, each declaration once; with more than one.
    pub total: Option<NamespaceCoverage>,
}

/// Why a doc doesn't count, if it doesn't (D2148).
fn weak(path: &str, doc: &Doc) -> Option<&'static str> {
    let squash = |s: &str| -> String {
        (s.chars().filter(|c| c.is_alphanumeric()))
            .flat_map(char::to_lowercase)
            .collect()
    };
    let last = path.rsplit('.').next().unwrap_or(path);
    if squash(&doc.text) == squash(last) {
        return Some("repeats the name");
    }
    let words = (doc.text.split_whitespace())
        .filter(|w| w.chars().any(char::is_alphanumeric))
        .count();
    (words < MIN_WORDS).then_some("too short")
}

impl Decls {
    /// Whether entry `i` is counted: listed, or a theorem, and not generated.
    fn counted(&self, i: usize) -> bool {
        let e = &self.entries[i];
        (e.kind.is_listed() || e.kind == Kind::Theorem) && !e.path.contains('%')
    }

    /// The counted declarations of namespace `ns`, as `members_of` reads it.
    fn counted_in(&self, ns: &str) -> BTreeSet<usize> {
        let project = self.project.contains(ns);
        (0..self.entries.len())
            .filter(|&i| {
                let e = &self.entries[i];
                let file = &self.files[e.file];
                self.counted(i)
                    && if project {
                        file.namespace.as_deref() == Some(ns)
                    } else {
                        file.std.is_some()
                            && (e.path.strip_prefix(ns)).is_some_and(|rest| rest.starts_with('.'))
                    }
            })
            .collect()
    }

    /// The coverage of the namespaces `names` (in full, as `resolve` gives
    /// them).
    pub fn coverage(&self, names: &[String]) -> Coverage {
        let groups = names
            .iter()
            .map(|ns| (ns.clone(), self.counted_in(ns)))
            .collect();
        self.coverage_of(groups)
    }

    /// The coverage with no namespace given: each of the program's, or when
    /// there is no program, the library's by its first component (what is
    /// directly under `Std` is `Std`).
    pub fn default_coverage(&self, program: bool) -> Coverage {
        let mut groups: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
        if program {
            for ns in &self.project {
                groups.insert(ns.clone(), self.counted_in(ns));
            }
        } else {
            for i in (0..self.entries.len()).filter(|&i| self.counted(i)) {
                if self.files[self.entries[i].file].std.is_none() {
                    continue;
                }
                let mut parts = self.entries[i].path.split('.');
                let key = match (parts.next(), parts.next(), parts.next()) {
                    (Some(root), Some(group), Some(_)) => format!("{root}.{group}"),
                    (Some(root), ..) => root.to_string(),
                    _ => continue,
                };
                groups.entry(key).or_default().insert(i);
            }
        }
        self.coverage_of(groups.into_iter().collect())
    }

    fn coverage_of(&self, groups: Vec<(String, BTreeSet<usize>)>) -> Coverage {
        let namespaces: Vec<NamespaceCoverage> = groups
            .iter()
            .map(|(ns, set)| self.coverage_set(ns, set))
            .collect();
        let total = (groups.len() > 1).then(|| {
            let all: BTreeSet<usize> = groups.iter().flat_map(|(_, s)| s.iter().copied()).collect();
            self.coverage_set("total", &all)
        });
        Coverage {
            version: 1,
            namespaces,
            total,
        }
    }

    fn coverage_set(&self, namespace: &str, set: &BTreeSet<usize>) -> NamespaceCoverage {
        let mut out = NamespaceCoverage {
            namespace: namespace.to_string(),
            target: set
                .iter()
                .all(|&i| self.files[self.entries[i].file].std.is_some()),
            declarations: Counts {
                with_example: Some(0),
                ..Counts::default()
            },
            theorems: Counts::default(),
            undocumented: Vec::new(),
            undocumented_theorems: Vec::new(),
            unattached_examples: Vec::new(),
        };
        for &i in set {
            let e = &self.entries[i];
            let theorem = e.kind == Kind::Theorem;
            let doc = self.doc(i);
            let verdict = match &doc {
                None => Some("no doc"),
                Some(d) => weak(&e.path, d),
            };
            let counts = if theorem {
                &mut out.theorems
            } else {
                &mut out.declarations
            };
            counts.total += 1;
            match verdict {
                None => {
                    counts.documented += 1;
                }
                Some(reason) => {
                    let (file, line) = self.location(i);
                    let missing = Missing {
                        name: e.path.clone(),
                        kind: e.kind.name(),
                        file,
                        line,
                        reason,
                    };
                    if theorem {
                        out.undocumented_theorems.push(missing);
                    } else {
                        out.undocumented.push(missing);
                    }
                }
            }
            if !theorem {
                // The examples of std are looked for in std, a program's in
                // the program (D2146).
                let in_std = self.files[e.file].std.is_some();
                let within = Within {
                    std: in_std,
                    project: !in_std,
                    namespaces: None,
                };
                if !self.example_decls(i, &within, false).is_empty() {
                    *out.declarations.with_example.get_or_insert(0) += 1;
                }
            } else if let Some(base) = example_base(&e.path)
                && !self.by_path.get(base).is_some_and(|found| {
                    found
                        .iter()
                        .any(|&j| matches!(self.entries[j].kind, Kind::Definition | Kind::Theorem))
                })
            {
                let (file, line) = self.location(i);
                out.unattached_examples.push(Unattached {
                    name: e.path.clone(),
                    file,
                    line,
                });
            }
        }
        out
    }
}

/// `X.y` for a theorem named `X.yExample` or `X.yExample2`.
fn example_base(path: &str) -> Option<&str> {
    let base = path
        .trim_end_matches(|c: char| c.is_ascii_digit())
        .strip_suffix("Example")?;
    (!base.is_empty() && !base.ends_with('.')).then_some(base)
}

fn percent(part: usize, whole: usize) -> String {
    match (part * 100 + whole / 2).checked_div(whole) {
        Some(p) => format!("{p}%"),
        None => "-".to_string(),
    }
}

/// The report as text. For the library (a target), the figures with
/// percentages and the undocumented names. For a project, plain counts, and
/// the names that have no doc only when `list` is set (SW-1100). The
/// unattached examples are listed for both.
pub fn render_coverage(c: &Coverage, list: bool) -> String {
    let mut out = String::new();
    for (i, ns) in c.namespaces.iter().chain(c.total.as_ref()).enumerate() {
        if i > 0 {
            out.push('\n');
        }
        out.push_str(&format!("{}\n", ns.namespace));
        let d = &ns.declarations;
        let t = &ns.theorems;
        let with_example = d.with_example.unwrap_or(0);
        if ns.target {
            out.push_str(&format!(
                "  documented: {} / {} ({})\n",
                d.documented,
                d.total,
                percent(d.documented, d.total)
            ));
            out.push_str(&format!(
                "  with an example: {with_example} / {} ({})\n",
                d.total,
                percent(with_example, d.total)
            ));
            out.push_str(&format!(
                "  theorems documented (counted apart): {} / {} ({})\n",
                t.documented,
                t.total,
                percent(t.documented, t.total)
            ));
        } else {
            out.push_str(&format!(
                "  with a doc: {} of {} declarations\n",
                d.documented, d.total
            ));
            out.push_str(&format!(
                "  with an example: {with_example} of {} declarations\n",
                d.total
            ));
            out.push_str(&format!(
                "  theorems with a doc (counted apart): {} of {}\n",
                t.documented, t.total
            ));
        }
        if (ns.target || list) && !ns.undocumented.is_empty() {
            let word = if ns.target {
                "undocumented"
            } else {
                "without a doc that counts"
            };
            out.push_str(&format!("  {word} ({}):\n", ns.undocumented.len()));
            for m in &ns.undocumented {
                out.push_str(&format!(
                    "    {}  {}  {}:{}  ({})\n",
                    m.name, m.kind, m.file, m.line, m.reason
                ));
            }
        }
        if !ns.unattached_examples.is_empty() {
            out.push_str(&format!(
                "  `…Example` theorems with no definition to attach to ({}), to rename:\n",
                ns.unattached_examples.len()
            ));
            for u in &ns.unattached_examples {
                out.push_str(&format!("    {}  {}:{}\n", u.name, u.file, u.line));
            }
        }
    }
    if c.namespaces.is_empty() {
        out.push_str("(no namespaces)\n");
    }
    out
}
