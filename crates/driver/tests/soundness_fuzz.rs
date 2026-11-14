//! Soundness fuzzing (SW-687): looks for a false theorem that the checker
//! accepts.
//!
//! **Statement mutation** (`mutated_theorems_have_no_counterexample`). It
//! takes the theorems of `examples/accept`, the AoC project and the
//! roguelike, changes each theorem's *statement* in one place (a numeral by
//! one, `<` and `≤`, `=` and `≠`, `∧` and `∨`, `+` and `*`, `True` and
//! `False`, two variables swapped, a hypothesis dropped) and keeps its proof,
//! or keeps the statement and changes the *proof* (a lemma swapped for
//! another of the same namespace, the proof replaced by a closer: `rfl`,
//! `omega`, `cases`, `ring`, `byDecision`), or does both. Each mutant is
//! checked in full (elaborator and kernel). A mutant that is still accepted
//! is searched for a counterexample, as `stitchwort audit` does
//! (`Session::audit`): an accepted theorem with a counterexample is a
//! soundness bug (or a bug in the search), and fails the test. An accepted
//! mutant with none is fine: the changed statement may still be true.
//!
//! **Attempts to prove `Void`** (`void_attempts_are_rejected`): small
//! programs, generated from templates of known paradox shapes (Girard and
//! Hurkens' universe tricks, non-positive types, non-terminating
//! definitions, handler tricks, quotient misuse, `Prop` elimination, opaque
//! leaks, closers on false goals, big numerals, the `+` rules), each ending
//! in `theorem boom: <false statement>`. Every one must be rejected; and the
//! `examples/soundness` programs, mutated token by token as the elaborator
//! fuzzer does, must never give an accepted theorem with a counterexample or
//! an accepted `boom`.
//!
//! The seed is fixed, so a run is reproducible. The broad tier checks
//! `MUTANTS` mutants of the examples and std, every second generated attempt
//! and `VOIDS` mutated soundness examples (about 20 s); the all tier four
//! times as many, from every corpus, and every attempt. `SOUND_MUTANTS`,
//! `SOUND_VOID` (counts; `SOUND_VOID` also means every generated attempt),
//! `SOUND_SEED` (decimal or `0x…`) and `SOUND_CORPUS` (`examples`, `std`,
//! `aoc`, `rogue`, a comma-separated list, or `all`) set a longer or
//! different run (`task fuzz:soundness`). `SOUND_VERBOSE=1` prints every
//! case (`2`: with each mutant's text). `SOUND_ONLY=text` checks only the
//! theorems whose label (`file: Namespace.name`) contains `text`, and every
//! mutation of each (not the few that `SOUND_MUTANTS` would choose), with
//! each statement mutation paired with each closer. A finding prints the
//! program and writes it to `target/soundness-fuzz/` of the checkout the test
//! was built from, not the cargo target dir (so in a lane's worktree, it goes
//! with `task worktree:rm`: copy a saved file out first). The report prints
//! the file's absolute path. Files are named `<seed>-<theorem number>-<mutant
//! number>[-expensive].sw`; the mutant number counts the theorem's mutants
//! in order, so it is stable for a `SOUND_ONLY` run with the same corpus.
//!
//! A mutant whose check holds more than `MEM_CAP` of heap (`SOUND_MEM_CAP_MB`)
//! or runs longer than `MUTANT_TIME` (`SOUND_MUTANT_SECS`) is stopped, counted
//! as "too expensive to check" with its text saved to `target/soundness-fuzz/`,
//! and the run goes on (SW-2576; the mechanism is `support/heap_cap.rs`, as in
//! `fuzz_elab.rs`). It is not a finding: nothing was accepted.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use stitchwort_core::DefId;
use stitchwort_core::budget::{Budget as CoreBudget, Limits};
use stitchwort_driver::audit::{Check, Options, Severity, Status, TheoremAudit};
use stitchwort_driver::counterexample::Verdict;
use stitchwort_driver::driver::{Session, Tier, test_threads, tier, tier_sample};
use stitchwort_driver::project::{DiskFiles, Target, project_sources};
use stitchwort_elab::counterexample::Budget;
use stitchwort_syntax::SourceMap;

#[path = "support/heap_cap.rs"]
mod heap_cap;

#[global_allocator]
static ALLOCATOR: heap_cap::Counting = heap_cap::Counting;

const SEED: u64 = 0x5eed_0687_50fd_0001;
/// Statement and proof mutants checked by default, from `examples/accept`
/// and std (about 8 s). The all tier checks four times as many, from every
/// corpus, AoC and the roguelike too.
const MUTANTS: usize = 60;
/// Mutated soundness examples checked by default (the all tier: four times
/// as many). The broad tier checks every second generated attempt, the all
/// tier all of them.
const VOIDS: usize = 30;
const STACK: usize = 64 * 1024 * 1024;
/// Evaluation steps a check may spend.
const WORK: u64 = 300_000_000;
/// The search on an accepted mutant: inputs, untimed (a fixed count, so a
/// run is reproducible).
const SEARCH: Budget = Budget {
    inputs: 2000,
    millis: 2000,
};
/// The most heap one mutant's check may hold (`SOUND_MEM_CAP_MB` sets
/// another). Mutants take 0.2 to 1.5 GB; the one that prompted the cap held
/// 7 GB for a minute (SW-2576). Four checks run at once.
const MEM_CAP: i64 = 2 << 30;
/// The longest one mutant's check may take (`SOUND_MUTANT_SECS`). The
/// slowest ordinary ones take 30 s.
const MUTANT_TIME: Duration = Duration::from_secs(90);
/// At most this many mutants of one theorem.
const PER_THEOREM: usize = 3;

// --- tokens --------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Debug)]
enum Kind {
    Ident,
    Number,
    Space,
    Comment,
    Str,
    Punct,
}

type Tok = (Kind, String);

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

/// Operators of two characters, kept as one token.
const DOUBLE: &[&str] = &[
    ":=", "<=", ">=", "!=", "==", "->", "=>", "++", "|>", "&&", "||", "<-",
];

/// Splits `text` into tokens that concatenate back to it exactly.
fn tokenize(text: &str) -> Vec<Tok> {
    let chars: Vec<char> = text.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        let start = i;
        let kind = if c.is_whitespace() {
            while i < chars.len() && chars[i].is_whitespace() && (chars[i] != '\n' || i == start) {
                i += 1;
            }
            Kind::Space
        } else if c == '-' && chars.get(i + 1) == Some(&'-') {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            Kind::Comment
        } else if c == '"' {
            i += 1;
            while i < chars.len() && chars[i] != '"' && chars[i] != '\n' {
                if chars[i] == '\\' {
                    i += 1;
                }
                i += 1;
            }
            i = (i + 1).min(chars.len());
            Kind::Str
        } else if c.is_ascii_digit() {
            while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '_') {
                i += 1;
            }
            Kind::Number
        } else if is_ident_char(c) {
            while i < chars.len() && is_ident_char(chars[i]) {
                i += 1;
            }
            Kind::Ident
        } else {
            let two: String = chars[i..(i + 2).min(chars.len())].iter().collect();
            i += if DOUBLE.contains(&two.as_str()) { 2 } else { 1 };
            Kind::Punct
        };
        out.push((kind, chars[start..i].iter().collect()));
    }
    out
}

fn join(tokens: &[Tok]) -> String {
    tokens.iter().map(|t| t.1.as_str()).collect()
}

/// xorshift64*, as in the other fuzzers.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n.max(1) as u64) as usize
    }

    fn shuffle<T>(&mut self, items: &mut [T]) {
        for i in (1..items.len()).rev() {
            let j = self.below(i + 1);
            items.swap(i, j);
        }
    }
}

/// An environment variable, if set and not empty (a task passes an unset
/// variable on as empty).
fn env_text(name: &str) -> Option<String> {
    std::env::var(name).ok().filter(|v| !v.is_empty())
}

fn env_number(name: &str) -> Option<u64> {
    let value = env_text(name)?;
    match value.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16).ok(),
        None => value.parse().ok(),
    }
}

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

// --- the corpus ------------------------------------------------------------

/// Where a theorem lives: a file on its own, or a file of a project.
#[derive(Clone)]
enum Home {
    File {
        name: String,
    },
    /// A file of the standard library (not the core): its path under `std/`.
    Std {
        path: String,
    },
    Project {
        /// Index into `Corpus::projects`.
        project: usize,
        /// Path within the project.
        path: String,
        namespace: String,
    },
}

struct Project {
    name: String,
    dir: PathBuf,
    files: Vec<(String, String)>,
}

/// A theorem of the corpus: its file's text and where the declaration, its
/// statement (after the name) and its proof are, in tokens.
struct Site {
    home: Home,
    text: String,
    /// Byte offsets of the declaration in `text`.
    decl: Range<usize>,
    /// The declaration's tokens.
    tokens: Vec<Tok>,
    name: String,
    /// Token range of the statement: after the name, up to `:=`, the first
    /// arm or `decreasing`.
    statement: Range<usize>,
}

impl Site {
    fn label(&self) -> String {
        match &self.home {
            Home::File { name } => format!("{name}: {}", self.name),
            Home::Std { path } => format!("std/{path}: Std.{}", self.name),
            Home::Project {
                path, namespace, ..
            } => format!("{path}: {namespace}.{}", self.name),
        }
    }
}

/// The `theorem` declarations at the start of a line of `text`.
fn sites_of(home: &Home, text: &str) -> Vec<Site> {
    let mut starts: Vec<usize> = Vec::new();
    let line_starts: Vec<usize> = std::iter::once(0)
        .chain(text.match_indices('\n').map(|(i, _)| i + 1))
        .filter(|&i| i < text.len())
        .collect();
    for &start in &line_starts {
        if text[start..].starts_with("theorem ") {
            starts.push(start);
        }
    }
    let mut out = Vec::new();
    for start in starts {
        // The declaration ends at the next line that starts in column 0 and
        // isn't blank.
        let end = line_starts
            .iter()
            .copied()
            .filter(|&l| l > start)
            .find(|&l| {
                let c = text[l..].chars().next().unwrap_or(' ');
                !c.is_whitespace()
            })
            .unwrap_or(text.len());
        let decl_text = &text[start..end];
        let tokens = tokenize(decl_text);
        let Some(name_at) = tokens
            .iter()
            .position(|t| t.0 == Kind::Ident && t.1 != "theorem")
        else {
            continue;
        };
        // A name may be dotted: `List.lengthAppend`.
        let mut name = tokens[name_at].1.clone();
        let mut name_end = name_at + 1;
        while name_end + 1 < tokens.len()
            && tokens[name_end].1 == "."
            && tokens[name_end + 1].0 == Kind::Ident
        {
            name.push('.');
            name.push_str(&tokens[name_end + 1].1);
            name_end += 2;
        }
        let mut depth = 0i32;
        let mut stop = None;
        for i in name_end..tokens.len() {
            let s = tokens[i].1.as_str();
            match s {
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" => depth -= 1,
                _ => {}
            }
            if depth != 0 {
                continue;
            }
            let arm = s.contains('\n')
                && tokens[i + 1..]
                    .iter()
                    .find(|t| t.0 != Kind::Space)
                    .is_some_and(|t| t.1 == "|");
            if s == ":=" || s == "decreasing" || s == "unfolding" || arm {
                stop = Some(i);
                break;
            }
        }
        let Some(stop) = stop else { continue };
        out.push(Site {
            home: home.clone(),
            text: text.to_string(),
            decl: start..end,
            tokens,
            name,
            statement: name_end..stop,
        });
    }
    out
}

struct Corpus {
    projects: Vec<Project>,
    sites: Vec<Site>,
    /// Every `Namespace.member` written in the corpus, by namespace: the
    /// lemmas a swapped lemma is drawn from.
    members: BTreeMap<String, BTreeSet<String>>,
}

fn read_dir_sorted(dir: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("can't read {}: {e}", dir.display()))
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "sw"))
        .collect();
    files.sort();
    files
}

fn read_corpus(parts: &[String]) -> Corpus {
    let mut corpus = Corpus {
        projects: Vec::new(),
        sites: Vec::new(),
        members: BTreeMap::new(),
    };
    let want = |p: &str| parts.is_empty() || parts.iter().any(|x| x == p);
    let mut texts: Vec<String> = Vec::new();
    if want("examples") {
        for file in read_dir_sorted(&root().join("examples/accept")) {
            let text = std::fs::read_to_string(&file).unwrap();
            let name = format!("accept/{}", file.file_name().unwrap().to_string_lossy());
            // Files that include others, or need a project, are left out.
            if text.contains("include ") {
                continue;
            }
            corpus.sites.extend(sites_of(&Home::File { name }, &text));
            texts.push(text);
        }
    }
    if want("std") {
        for (path, text) in stitchwort_elab::library_files() {
            let home = Home::Std {
                path: path.to_string(),
            };
            corpus.sites.extend(sites_of(&home, text));
            texts.push(text.to_string());
        }
    }
    for (part, dir) in [("aoc", "aoc"), ("rogue", "games/rogue")] {
        if !want(part) {
            continue;
        }
        let dir = root().join(dir);
        let mut sources = SourceMap::new();
        let files = project_sources(&DiskFiles { root: dir.clone() }, part, &mut sources)
            .unwrap_or_else(|_| panic!("can't read the {part} project"));
        let namespace_of = |text: &str| {
            text.lines()
                .find_map(|l| l.strip_prefix("namespace "))
                .map(|n| n.trim().to_string())
                .unwrap_or_default()
        };
        let project = corpus.projects.len();
        for (path, text) in &files {
            let namespace = namespace_of(text);
            let home = Home::Project {
                project,
                path: path.clone(),
                namespace,
            };
            corpus.sites.extend(sites_of(&home, text));
            texts.push(text.clone());
        }
        corpus.projects.push(Project {
            name: part.to_string(),
            dir,
            files,
        });
    }
    for text in &texts {
        let tokens = tokenize(text);
        for w in tokens.windows(3) {
            if w[0].0 == Kind::Ident
                && is_upper(&w[0].1)
                && w[1].1 == "."
                && w[2].0 == Kind::Ident
                && !is_upper(&w[2].1)
            {
                corpus
                    .members
                    .entry(w[0].1.clone())
                    .or_default()
                    .insert(w[2].1.clone());
            }
        }
    }
    corpus
}

fn is_upper(s: &str) -> bool {
    s.chars().next().is_some_and(char::is_uppercase)
}

// --- mutations -------------------------------------------------------------

/// One change to a theorem.
#[derive(Clone, Debug)]
enum Mutation {
    /// Replace tokens `range` of the declaration with `with`.
    Replace {
        what: &'static str,
        range: Range<usize>,
        with: String,
    },
    /// Swap tokens `a` and `b`.
    Swap { a: usize, b: usize },
    /// The proof replaced by a closer.
    Closer(&'static str),
    /// A statement mutation and a closer.
    Both(Box<Mutation>, &'static str),
}

impl Mutation {
    fn kind(&self) -> &'static str {
        match self {
            Mutation::Replace { what, .. } => what,
            Mutation::Swap { .. } => "swap",
            Mutation::Closer(_) => "closer",
            Mutation::Both(..) => "statement+closer",
        }
    }

    /// Whether it changes the statement.
    fn changes_statement(&self, site: &Site) -> bool {
        match self {
            Mutation::Replace { range, .. } => range.start < site.statement.end,
            Mutation::Swap { .. } | Mutation::Both(..) => true,
            Mutation::Closer(_) => false,
        }
    }
}

const CLOSERS: &[&str] = &["rfl", "omega", "cases", "ring", "Std.byDecision"];

/// Relations and connectives, and what each may become.
const OPERATORS: &[(&str, &[&str])] = &[
    ("<", &["≤", ">"]),
    ("≤", &["<", "≥"]),
    ("<=", &["<", ">="]),
    (">", &["≥", "<"]),
    ("≥", &[">"]),
    (">=", &[">"]),
    ("=", &["≠"]),
    ("≠", &["="]),
    ("!=", &["=="]),
    ("==", &["!="]),
    ("∧", &["∨"]),
    ("∨", &["∧"]),
    ("&&", &["||"]),
    ("||", &["&&"]),
    ("+", &["*", "-"]),
    ("*", &["+"]),
    ("-", &["+"]),
    ("∈", &["∉"]),
    ("∉", &["∈"]),
    ("++", &[]),
];

const CONSTRUCTORS: &[(&str, &str)] = &[
    ("True", "False"),
    ("False", "True"),
    ("Less", "Greater"),
    ("Greater", "Less"),
    ("Zero", "Succ Zero"),
];

/// The relations a hypothesis's type contains.
const RELATIONS: &[&str] = &[
    "=", "<", "≤", "<=", ">", "≥", ">=", "≠", "!=", "∈", "∉", "==",
];

/// Every single mutation of `site`, statement and proof.
fn mutations_of(site: &Site, members: &BTreeMap<String, BTreeSet<String>>) -> Vec<Mutation> {
    let tokens = &site.tokens;
    let st = site.statement.clone();
    let mut out = Vec::new();
    // Binder groups at depth 0 of the statement: `(names: type)`, and the
    // names they bind.
    let mut groups: Vec<(Range<usize>, Vec<usize>, bool)> = Vec::new();
    // Each bound name's type, as written.
    let mut types: BTreeMap<&str, String> = BTreeMap::new();
    {
        let mut i = st.start;
        while i < st.end {
            if tokens[i].1 == "(" {
                let mut depth = 0;
                let mut j = i;
                while j < st.end {
                    match tokens[j].1.as_str() {
                        "(" | "[" | "{" => depth += 1,
                        ")" | "]" | "}" => depth -= 1,
                        _ => {}
                    }
                    if depth == 0 {
                        break;
                    }
                    j += 1;
                }
                let inner = i + 1..j;
                if let Some(colon) = inner.clone().find(|&k| tokens[k].1 == ":") {
                    let names: Vec<usize> = (inner.start..colon)
                        .filter(|&k| tokens[k].0 == Kind::Ident)
                        .collect();
                    let relational = (colon..j).any(|k| RELATIONS.contains(&tokens[k].1.as_str()));
                    let ty = join(&tokens[colon + 1..j]).trim().to_string();
                    for &k in &names {
                        types.insert(tokens[k].1.as_str(), ty.clone());
                    }
                    if !names.is_empty() {
                        groups.push((i..j + 1, names, relational));
                    }
                }
                i = j + 1;
            } else {
                i += 1;
            }
        }
    }
    let binder_positions: BTreeSet<usize> =
        groups.iter().flat_map(|g| g.1.iter().copied()).collect();
    let bound: BTreeSet<&str> = binder_positions
        .iter()
        .map(|&k| tokens[k].1.as_str())
        .collect();
    let prev_is_type = |i: usize| {
        tokens[..i]
            .iter()
            .rev()
            .find(|t| t.0 != Kind::Space)
            .is_some_and(|t| t.1 == "Type")
    };
    for i in st.clone() {
        let (kind, s) = (&tokens[i].0, tokens[i].1.as_str());
        match kind {
            Kind::Number if !prev_is_type(i) => {
                let Ok(n) = s.replace('_', "").parse::<u128>() else {
                    continue;
                };
                out.push(Mutation::Replace {
                    what: "numeral",
                    range: i..i + 1,
                    with: (n + 1).to_string(),
                });
                if n > 0 {
                    out.push(Mutation::Replace {
                        what: "numeral",
                        range: i..i + 1,
                        with: (n - 1).to_string(),
                    });
                }
            }
            Kind::Punct | Kind::Ident => {
                if let Some((_, to)) = OPERATORS.iter().find(|(from, _)| *from == s) {
                    for to in *to {
                        out.push(Mutation::Replace {
                            what: "operator",
                            range: i..i + 1,
                            with: to.to_string(),
                        });
                    }
                }
                if let Some((_, to)) = CONSTRUCTORS.iter().find(|(from, _)| *from == s) {
                    out.push(Mutation::Replace {
                        what: "constructor",
                        range: i..i + 1,
                        with: to.to_string(),
                    });
                }
            }
            _ => {}
        }
    }
    // Two different bound variables of the same type, each at one use,
    // swapped.
    let uses: Vec<usize> = st
        .clone()
        .filter(|&k| {
            tokens[k].0 == Kind::Ident
                && bound.contains(tokens[k].1.as_str())
                && !binder_positions.contains(&k)
                && (k == 0 || tokens[k - 1].1 != ".")
        })
        .collect();
    for (x, &a) in uses.iter().enumerate() {
        for &b in &uses[x + 1..] {
            let (x, y) = (tokens[a].1.as_str(), tokens[b].1.as_str());
            if x != y && types.get(x).is_some_and(|t| types.get(y) == Some(t)) {
                out.push(Mutation::Swap { a, b });
            }
        }
    }
    // A hypothesis dropped.
    for (range, _, relational) in &groups {
        if *relational {
            let mut end = range.end;
            if end < st.end && tokens[end].0 == Kind::Space && !tokens[end].1.contains('\n') {
                end += 1;
            }
            out.push(Mutation::Replace {
                what: "drop-hypothesis",
                range: range.start..end,
                with: String::new(),
            });
        }
    }
    // The proof: a lemma swapped for another of its namespace.
    for i in st.end + 2..tokens.len() {
        if tokens[i].0 == Kind::Ident
            && !is_upper(&tokens[i].1)
            && tokens[i - 1].1 == "."
            && tokens[i - 2].0 == Kind::Ident
            && is_upper(&tokens[i - 2].1)
            && let Some(others) = members.get(&tokens[i - 2].1)
        {
            // The neighbours of the name in sorted order: the most alike.
            let all: Vec<&String> = others.iter().collect();
            if let Some(at) = all.iter().position(|m| **m == tokens[i].1) {
                for k in [at.wrapping_sub(1), at + 1] {
                    if let Some(other) = all.get(k) {
                        out.push(Mutation::Replace {
                            what: "lemma",
                            range: i..i + 1,
                            with: other.to_string(),
                        });
                    }
                }
            }
        }
    }
    // The proof replaced by a closer.
    for closer in CLOSERS {
        out.push(Mutation::Closer(closer));
    }
    out
}

/// The declaration's text after `mutation`.
fn render(site: &Site, mutation: &Mutation) -> String {
    let tokens = &site.tokens;
    match mutation {
        Mutation::Replace { range, with, .. } => {
            let mut out = join(&tokens[..range.start]);
            out.push_str(with);
            out.push_str(&join(&tokens[range.end..]));
            out
        }
        Mutation::Swap { a, b } => {
            let mut t = tokens.clone();
            let (x, y) = (t[*a].1.clone(), t[*b].1.clone());
            t[*a].1 = y;
            t[*b].1 = x;
            join(&t)
        }
        Mutation::Closer(closer) => {
            let statement = join(&tokens[..site.statement.end]);
            format!("{} := {closer}\n", statement.trim_end())
        }
        Mutation::Both(inner, closer) => {
            let changed = render(site, inner);
            let again = Site {
                home: site.home.clone(),
                text: String::new(),
                decl: 0..0,
                tokens: tokenize(&changed),
                name: site.name.clone(),
                statement: 0..0,
            };
            // The statement ends where it did, shifted by the change in
            // its token count.
            let shift = again.tokens.len() as isize - tokens.len() as isize;
            let end = (site.statement.end as isize + shift) as usize;
            let statement = join(&again.tokens[..end.min(again.tokens.len())]);
            format!("{} := {closer}\n", statement.trim_end())
        }
    }
}

// --- checking ------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Outcome {
    /// The mutant didn't check.
    Rejected,
    /// Accepted; the search found no counterexample (or didn't apply).
    Accepted(Verdict2),
    /// Accepted, and the search found a counterexample: a finding.
    Counterexample,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Verdict2 {
    NoneFound,
    NotSearched,
}

fn session() -> Session {
    let mut session = Session::for_stack(STACK);
    configure(&mut session);
    session
}

fn configure(session: &mut Session) {
    session.elab.options.limits = Limits {
        work: WORK,
        ..Limits::for_stack(STACK)
    };
    session.elab.options.untimed_counterexamples = true;
    // No search on a failing proof: most mutants fail.
    session.elab.options.no_counterexamples = true;
    // The caps (`heap_cap`) stop a check through the budget's cancel hook.
    let budget = &session.elab.kernel.machine.budget;
    budget.set_cancel_flag(Default::default());
    budget.watch_cancel(true);
}

/// The theorem `name` of namespace `namespace` (or any, for a file), if
/// it was declared.
fn find_theorem(
    g: &stitchwort_core::Ev,
    namespace: Option<&str>,
    name: &str,
) -> Option<(DefId, String)> {
    let found = stitchwort_driver::audit::theorems(g, &|path: &str| match namespace {
        Some(ns) => path == format!("{ns}.{name}"),
        None => !path.starts_with("Std.") && (path == name || path.ends_with(&format!(".{name}"))),
    });
    found.last().cloned()
}

/// Checks `site` with its declaration replaced by `decl`, and audits the
/// theorem with the search.
fn check_site(corpus: &Corpus, site: &Site, decl: &str, cache: &Path, search: bool) -> Checked {
    let rejected = Checked {
        audit: None,
        refuted: false,
        load_error: None,
        too_expensive: None,
        peak: 0,
    };
    let mut session = match &site.home {
        Home::Std { path } => {
            // The library with this file changed.
            let changed = format!(
                "{}{}{}",
                &site.text[..site.decl.start],
                decl,
                &site.text[site.decl.end..]
            );
            let files: Vec<(&str, &str)> = stitchwort_elab::library_files()
                .iter()
                .map(|&(p, t)| {
                    if p == path {
                        (p, changed.as_str())
                    } else {
                        (p, t)
                    }
                })
                .collect();
            let Ok(mut session) = Session::with_library_files(&files, false, false) else {
                return rejected;
            };
            configure(&mut session);
            session
        }
        _ => session(),
    };
    session.use_check_cache(cache);
    let mut load_error = None;
    let first_line = |errors: Vec<stitchwort_syntax::Diagnostic>| {
        errors
            .first()
            .and_then(|d| d.message.lines().next())
            .map(|line| format!("{}: {line}", errors[0].code))
    };
    let namespace = match &site.home {
        Home::File { name } => {
            let text = format!(
                "{}{}{}",
                &site.text[..site.decl.start],
                decl,
                &site.text[site.decl.end..]
            );
            load_error = session.load(name, &text).err().and_then(first_line);
            None
        }
        Home::Std { .. } => {
            // The library loads as far as the theorem needs: using its name
            // loads its file.
            let _ = session.parse_expression("probe.sw", &format!("Std.{}", site.name));
            Some("Std")
        }
        Home::Project {
            project,
            path,
            namespace,
        } => {
            let project = &corpus.projects[*project];
            session.include_from(std::rc::Rc::new(DiskFiles {
                root: project.dir.clone(),
            }));
            let files: Vec<(String, String)> = project
                .files
                .iter()
                .map(|(p, t)| {
                    if p == path {
                        // The declarations after the theorem stay: it may
                        // use them. They can't make a mutant check: a
                        // definition is final only once everything it uses
                        // is.
                        (
                            p.clone(),
                            format!(
                                "{}{}{}",
                                &site.text[..site.decl.start],
                                decl,
                                &site.text[site.decl.end..]
                            ),
                        )
                    } else {
                        (p.clone(), t.clone())
                    }
                })
                .collect();
            load_error = session
                .load_project_sources(
                    &project.name,
                    files,
                    &Target::Namespaces(vec![namespace.clone()]),
                )
                .err()
                .and_then(first_line);
            Some(namespace.as_str())
        }
    };
    let Some((id, name)) = find_theorem(&session.elab.ev(), namespace, &site.name) else {
        return Checked {
            load_error,
            ..rejected
        };
    };
    let options = Options {
        allowed: ["Quot.sound".to_string()].into_iter().collect(),
        search: search.then_some(SEARCH),
    };
    let audit = session.audit(&[(id, name.clone())], &options).pop();
    // A rejected mutant's statement is searched too: that the search refutes
    // many of them shows the oracle has teeth.
    let refuted = search
        && audit.as_ref().is_some_and(|a| a.status == Status::Failed)
        && session.search_theorem(id, &name, false, SEARCH).verdict().0 == Verdict::False;
    Checked {
        audit,
        refuted,
        load_error,
        too_expensive: None,
        peak: 0,
    }
}

struct Checked {
    audit: Option<TheoremAudit>,
    /// It was rejected, and the search refuted its statement.
    refuted: bool,
    /// The first line of the first error that loading the files gave, if any.
    load_error: Option<String>,
    /// Stopped for holding more heap, or taking longer, than the caps allow
    /// (set by [`check_one`]); the rest of this is then not a result.
    too_expensive: Option<heap_cap::Tripped>,
    /// The most heap the check held at once, in bytes (set by [`check_one`]).
    peak: i64,
}

fn outcome_of(checked: &Checked) -> Outcome {
    let Some(audit) = &checked.audit else {
        return Outcome::Rejected;
    };
    if audit.status != Status::Checked {
        return Outcome::Rejected;
    }
    // An axiom the audit refuses is the user's, not the checker's: a
    // counterexample to such a theorem is no soundness finding.
    if (audit.findings.iter()).any(|f| f.check == Check::Axioms && f.severity == Severity::Fail) {
        return Outcome::Rejected;
    }
    match audit.search.as_ref().map(|s| s.verdict) {
        Some(Verdict::False) => Outcome::Counterexample,
        None | Some(Verdict::NotApplicable) => Outcome::Accepted(Verdict2::NotSearched),
        Some(_) => Outcome::Accepted(Verdict2::NoneFound),
    }
}

/// Runs `f` on a thread of its own with `STACK` (the stack the session is
/// told it has), catching a panic.
fn on_thread<T: Send>(f: impl FnOnce() -> T + Send) -> Result<T, String> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(STACK)
            .spawn_scoped(scope, move || catch_unwind(AssertUnwindSafe(f)))
            .expect("spawn")
            .join()
            .unwrap_or_else(|_| Err(Box::new("thread died")))
            .map_err(|payload| {
                payload
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_else(|| "<non-string panic>".into())
            })
    })
}

fn scratch(tag: &str) -> PathBuf {
    let dir =
        std::env::temp_dir().join(format!("stitchwort-soundness-{}-{tag}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn save_finding(tag: &str, text: &str) -> PathBuf {
    let dir = root().join("target/soundness-fuzz");
    let _ = std::fs::create_dir_all(&dir);
    // Absolute and without `..`, so the report's path can be pasted.
    let dir = dir.canonicalize().unwrap_or(dir);
    let path = dir.join(format!("{tag}.sw"));
    let _ = std::fs::write(&path, text);
    path
}

/// Runs `work` over `items` on up to four threads of `STACK`, each with a
/// check cache of its own.
fn run_parallel<T: Sync, R: Send>(items: &[T], work: impl Fn(&T, &Path) -> R + Sync) -> Vec<R> {
    let next = Mutex::new(0usize);
    let results: Mutex<Vec<(usize, R)>> = Mutex::new(Vec::new());
    // One check cache for all: its writes are atomic renames.
    let cache = scratch("cache");
    std::thread::scope(|scope| {
        for _ in 0..test_threads().min(4) {
            let (next, results, work, cache) = (&next, &results, &work, &cache);
            std::thread::Builder::new()
                .stack_size(STACK)
                .spawn_scoped(scope, move || {
                    loop {
                        let i = {
                            let mut n = next.lock().unwrap();
                            *n += 1;
                            *n - 1
                        };
                        let Some(item) = items.get(i) else { break };
                        let r = work(item, cache);
                        results.lock().unwrap().push((i, r));
                    }
                })
                .expect("spawn a worker");
        }
    });
    let _ = std::fs::remove_dir_all(&cache);
    let mut results = results.into_inner().unwrap();
    results.sort_by_key(|(i, _)| *i);
    results.into_iter().map(|(_, r)| r).collect()
}

// --- part 1: statement and proof mutation ----------------------------------

struct Job {
    site: usize,
    mutations: Vec<Mutation>,
}

struct JobResult {
    /// The unmutated theorem checked, so its mutants count.
    calibrated: bool,
    /// Rejected mutants whose statement the search refuted.
    refuted: usize,
    results: Vec<(Mutation, Outcome, String)>,
    /// Mutants that formatted the same as the original, so weren't checked.
    no_ops: usize,
    failures: Vec<String>,
    /// Mutants stopped by a cap, not checked: not findings.
    too_expensive: Vec<String>,
}

#[test]
fn mutated_theorems_have_no_counterexample() {
    let started = Instant::now();
    let default = if tier() == Tier::All {
        4 * MUTANTS
    } else {
        MUTANTS
    };
    let wanted = env_number("SOUND_MUTANTS").map_or(default, |n| n as usize);
    let seed = env_number("SOUND_SEED").unwrap_or(SEED);
    // AoC and the roguelike cost about a second a mutant (a namespace is
    // checked again), so only the all tier and a run that asks take them.
    let parts: Vec<String> = match env_text("SOUND_CORPUS") {
        Some(v) if v != "all" => v.split(',').map(|s| s.trim().to_string()).collect(),
        Some(_) => Vec::new(),
        None if tier() == Tier::All => Vec::new(),
        None => vec!["examples".to_string(), "std".to_string()],
    };
    let corpus = read_corpus(&parts);
    assert!(!corpus.sites.is_empty(), "no theorems in the corpus");

    // Theorems in random order, each with up to PER_THEOREM mutations, until
    // there are enough.
    let only = env_text("SOUND_ONLY");
    let mut rng = Rng(seed);
    let mut order: Vec<usize> = (0..corpus.sites.len()).collect();
    rng.shuffle(&mut order);
    let mut jobs = Vec::new();
    let mut count = 0;
    for &s in &order {
        let site = &corpus.sites[s];
        if let Some(only) = &only {
            // Every mutation of the theorems asked for, none of the rest.
            if site.label().contains(only) {
                let mut mutations = mutations_of(site, &corpus.members);
                // Each statement mutation with each closer, as the sampler
                // pairs them (SW-2610).
                let paired: Vec<Mutation> = mutations
                    .iter()
                    .filter(|m| m.changes_statement(site))
                    .flat_map(|m| {
                        CLOSERS
                            .iter()
                            .map(|c| Mutation::Both(Box::new(m.clone()), c))
                    })
                    .collect();
                mutations.extend(paired);
                jobs.push(Job { site: s, mutations });
            }
            continue;
        }
        if count >= wanted {
            break;
        }
        let mut all = mutations_of(site, &corpus.members);
        if all.is_empty() {
            continue;
        }
        // One mutation of each of up to PER_THEOREM kinds (closers apart),
        // so no kind crowds out the others.
        rng.shuffle(&mut all);
        let mut kinds: Vec<&str> = Vec::new();
        let mut chosen: Vec<Mutation> = Vec::new();
        for m in &all {
            if !matches!(m, Mutation::Closer(_))
                && !kinds.contains(&m.kind())
                && kinds.len() < PER_THEOREM
            {
                kinds.push(m.kind());
                chosen.push(m.clone());
            }
        }
        // Now and then the proof replaced by a closer, and a statement
        // mutation with a closer.
        if rng.below(2) == 0 {
            chosen.push(Mutation::Closer(CLOSERS[rng.below(CLOSERS.len())]));
        }
        if let Some(m) = chosen.iter().find(|m| m.changes_statement(site))
            && rng.below(2) == 0
        {
            let closer = CLOSERS[rng.below(CLOSERS.len())];
            chosen.push(Mutation::Both(Box::new(m.clone()), closer));
        }
        if chosen.is_empty() {
            continue;
        }
        count += chosen.len();
        jobs.push(Job {
            site: s,
            mutations: chosen,
        });
    }

    let corpus = Arc::new(corpus);
    let results: Vec<JobResult> = run_parallel(&jobs, |job, cache| {
        let corpus = &corpus;
        let site = &corpus.sites[job.site];
        let mut out = JobResult {
            calibrated: false,
            refuted: 0,
            no_ops: 0,
            results: Vec::new(),
            failures: Vec::new(),
            too_expensive: Vec::new(),
        };
        let original = site.text[site.decl.clone()].to_string();
        let base = check_one(corpus, site, &original, cache, false, true);
        match base {
            Ok(Checked {
                too_expensive: Some(tripped),
                ..
            }) => {
                let what = match tripped {
                    heap_cap::Tripped::Time => "time",
                    _ => "heap",
                };
                eprintln!(
                    "skipped, the unmutated check ran out of {what} (even the default limits \
                     of {} MB heap and {} s): {}",
                    MEM_CAP >> 20,
                    MUTANT_TIME.as_secs(),
                    site.label()
                );
                return out;
            }
            Ok(checked) if outcome_of(&checked) != Outcome::Rejected => out.calibrated = true,
            Ok(checked) => {
                let why = match &checked.audit {
                    None => match &checked.load_error {
                        Some(error) => format!("the theorem was not found after loading: {error}"),
                        None => "the theorem was not found after loading".to_string(),
                    },
                    Some(a) => format!(
                        "status {:?}: {}{}",
                        a.status,
                        a.findings
                            .first()
                            .and_then(|f| f.message.lines().next())
                            .unwrap_or("no finding"),
                        checked
                            .load_error
                            .as_ref()
                            .map(|e| format!(" (loading: {e})"))
                            .unwrap_or_default()
                    ),
                };
                eprintln!("skipped, unmutated check rejected: {}: {why}", site.label());
                return out;
            }
            Err(panic) => {
                out.failures.push(format!(
                    "{}: the unmutated theorem panicked: {panic}",
                    site.label()
                ));
                return out;
            }
        }
        let mut refuted = 0;
        for (index, m) in job.mutations.iter().enumerate() {
            let decl = render(site, m);
            if same_after_formatting(&decl, &original) {
                out.no_ops += 1;
                continue;
            }
            let began = Instant::now();
            let checked = check_one(corpus, site, &decl, cache, true, false);
            if env_text("SOUND_VERBOSE").is_some() {
                let shown = checked.as_ref().map(outcome_of);
                let peak = checked.as_ref().map_or(0, |c| c.peak) >> 20;
                println!(
                    "{:.2}s {peak} MB {} ({}): {shown:?}",
                    began.elapsed().as_secs_f64(),
                    site.label(),
                    m.kind()
                );
                if env_text("SOUND_VERBOSE").is_some_and(|v| v == "2") {
                    println!("{decl}");
                }
            }
            match checked {
                Ok(Checked {
                    too_expensive: Some(tripped),
                    ..
                }) => {
                    let tag = format!("{seed:x}-{}-{index}-expensive", job.site);
                    let saved = save_finding(&tag, &decl);
                    let line = format!(
                        "{} ({}): stopped after {:.1}s by the {} cap; mutant declaration saved to {}",
                        site.label(),
                        m.kind(),
                        began.elapsed().as_secs_f64(),
                        match tripped {
                            heap_cap::Tripped::Time =>
                                format!("{} s time", mutant_time().as_secs()),
                            _ => format!("{} MB heap", mem_cap() >> 20),
                        },
                        saved.display()
                    );
                    eprintln!("soundness_fuzz: too expensive: {line}");
                    out.too_expensive.push(line);
                }
                Ok(checked) => {
                    let outcome = outcome_of(&checked);
                    refuted += usize::from(checked.refuted);
                    if outcome == Outcome::Counterexample {
                        let line = checked
                            .audit
                            .as_ref()
                            .and_then(|a| a.search.as_ref())
                            .map(|s| s.line.clone())
                            .unwrap_or_default();
                        let tag = format!("{seed:x}-{}-{index}", job.site);
                        let saved = save_finding(&tag, &decl);
                        out.failures.push(format!(
                            "SOUNDNESS: {} ({}) accepted with a counterexample: {line}\n  \
                             mutant declaration saved to {}:\n{decl}",
                            site.label(),
                            m.kind(),
                            saved.display()
                        ));
                    }
                    out.results.push((m.clone(), outcome, decl));
                }
                Err(panic) => out.failures.push(format!(
                    "{} ({}): panicked: {panic}\n{decl}",
                    site.label(),
                    m.kind()
                )),
            }
        }
        out.refuted = refuted;
        out
    });

    // The tally.
    let mut by_kind: BTreeMap<&str, [usize; 4]> = BTreeMap::new();
    let mut calibrated = 0;
    let refuted: usize = results.iter().map(|r| r.refuted).sum();
    let no_ops: usize = results.iter().map(|r| r.no_ops).sum();
    let mut failures = Vec::new();
    let mut too_expensive = Vec::new();
    for (job, r) in jobs.iter().zip(&results) {
        calibrated += usize::from(r.calibrated);
        failures.extend(r.failures.iter().cloned());
        too_expensive.extend(r.too_expensive.iter().cloned());
        let site = &corpus.sites[job.site];
        for (m, outcome, _) in &r.results {
            let row = by_kind.entry(m.kind()).or_default();
            row[0] += 1;
            match outcome {
                Outcome::Rejected => row[1] += 1,
                Outcome::Accepted(Verdict2::NotSearched) => row[2] += 1,
                Outcome::Accepted(Verdict2::NoneFound) => row[3] += 1,
                Outcome::Counterexample => {}
            }
            let _ = site;
        }
    }
    let total: usize = by_kind.values().map(|r| r[0]).sum();
    let rejected: usize = by_kind.values().map(|r| r[1]).sum();
    let unsearched: usize = by_kind.values().map(|r| r[2]).sum();
    let searched: usize = by_kind.values().map(|r| r[3]).sum();
    println!(
        "soundness_fuzz mutants: seed {seed:#x}, {:.1}s, {} theorems ({calibrated} checked unmutated), \
         {total} mutants: {rejected} rejected ({refuted} of them refuted by the search), {} accepted ({searched} searched with no \
         counterexample, {unsearched} out of the search's scope), {no_ops} no-op mutants skipped, {} too expensive to check, {} findings",
        started.elapsed().as_secs_f64(),
        jobs.len(),
        total - rejected,
        too_expensive.len(),
        failures.len()
    );
    for line in &too_expensive {
        println!("  too expensive: {line}");
    }
    for (kind, r) in &by_kind {
        println!(
            "  {kind:18} {:5} mutants, {:5} rejected, {:4} accepted unsearched, {:4} accepted searched",
            r[0], r[1], r[2], r[3]
        );
    }
    assert!(
        failures.is_empty(),
        "{} finding(s):\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
    assert!(
        jobs.len() < 10 || calibrated * 2 > jobs.len(),
        "under half the theorems checked unmutated: the harness is broken"
    );
}

/// Whether the formatter makes the two declarations the same text: a mutant
/// that is the source again checks as it does, and isn't a mutant.
fn same_after_formatting(a: &str, b: &str) -> bool {
    a == b
        || matches!(
            (stitchwort_fmt::format(a), stitchwort_fmt::format(b)),
            (Ok(x), Ok(y)) if x == y
        )
}

fn check_one(
    corpus: &Corpus,
    site: &Site,
    decl: &str,
    cache: &Path,
    search: bool,
    calibration: bool,
) -> Result<Checked, String> {
    // The unmutated check is not a mutant: it gets the default limits, not
    // the per-mutant ones, so a low cap shows up as expensive mutants and
    // not as a skipped theorem.
    let (heap, time) = if calibration {
        (MEM_CAP.max(mem_cap()), MUTANT_TIME.max(mutant_time()))
    } else {
        (mem_cap(), mutant_time())
    };
    on_thread(|| {
        CoreBudget::set_cancel_hook(heap_cap::over_cap);
        let before = heap_cap::start(heap, Some(Instant::now() + time));
        let mut checked = check_site(corpus, site, decl, cache, search);
        checked.peak = heap_cap::peak_since(before);
        match heap_cap::tripped() {
            heap_cap::Tripped::No => {}
            tripped => checked.too_expensive = Some(tripped),
        }
        checked
    })
}

/// The heap cap in bytes: `SOUND_MEM_CAP_MB` or [`MEM_CAP`].
fn mem_cap() -> i64 {
    env_number("SOUND_MEM_CAP_MB").map_or(MEM_CAP, |mb| (mb as i64) << 20)
}

/// The time cap: `SOUND_MUTANT_SECS` or [`MUTANT_TIME`].
fn mutant_time() -> Duration {
    env_number("SOUND_MUTANT_SECS").map_or(MUTANT_TIME, Duration::from_secs)
}

// --- part 2: attempts to prove `Void` --------------------------------------

/// What every generated program starts with.
const PREAMBLE: &str = "import Std (Float, Nat, Int, List, byDecision, Finite, Decidable, Exists, Eq)\n\
                        import Std.Effect (Comp)\n\n";

/// An attempt: its family, and the program.
struct Attempt {
    family: &'static str,
    text: String,
}

fn attempt(family: &'static str, body: String) -> Attempt {
    Attempt {
        family,
        text: format!("{PREAMBLE}{body}\n"),
    }
}

/// The generated attempts, family by family. Each ends in a theorem `boom`
/// whose statement is false (most of them `Void`), so each must be
/// rejected.
fn void_attempts() -> Vec<Attempt> {
    let mut out = Vec::new();

    // Non-positive types, through containers and sorts.
    for sort in ["Type", "Prop", "Type 1"] {
        for field in [
            "Bad → Void",
            "Bad → Nat",
            "(Bad → Void) → Void",
            "List (Bad → Void)",
            "Option (Bad → Void)",
            "Pair Nat (Bad → Void)",
            "(Nat → Bad) → Void",
            "Comp Bool (b => Bad) Void",
            "Bad → Bad",
        ] {
            out.push(attempt(
                "non-positive",
                format!(
                    "type Bad: {sort} =\n  | MkBad (f: {field})\n\n\
                     def selfApp (b: Bad): Void :=\n  match b with\n    | MkBad f => f b\n\n\
                     theorem boom: Void := selfApp (MkBad selfApp)"
                ),
            ));
        }
    }
    // Non-positive through a sibling, and through an index.
    out.push(attempt(
        "non-positive",
        "type Bad1: Type =\n  | MkBad1 (f: Bad2 → Void)\n\ntype Bad2: Type =\n  | MkBad2 (b: Bad1)\n\n\
         def app (b: Bad1): Void :=\n  match b with\n    | MkBad1 f => f (MkBad2 b)\n\n\
         theorem boom: Void := app (MkBad1 (x => match x with | MkBad2 b => app b))"
            .to_string(),
    ));
    for index in [
        "(Bad n → Void)",
        "(Bad (Succ n) → Void)",
        "(Nat → Bad n → Void)",
    ] {
        out.push(attempt(
            "non-positive",
            format!(
                "type Bad: Nat → Type =\n  | MkBad (n: Nat) (f: {index}): Bad n\n\n\
                 theorem boom: Void := boom"
            ),
        ));
    }

    // Non-terminating definitions: an argument that isn't smaller, in many
    // disguises.
    for arg in [
        "n",
        "(Succ n)",
        "(n + 1)",
        "(n + 0)",
        "(0 + n)",
        "(n * 1)",
        "(n - 0)",
        "(Nat.pred (Succ n))",
        "((x => x) n)",
        "(if True then n else 0)",
        "(match n with | k => k)",
        "(n / 1)",
        "(Nat.max n n)",
        "(n |> (x => x))",
    ] {
        out.push(attempt(
            "non-terminating",
            format!("def loop (n: Nat): Void := loop {arg}\n\ntheorem boom: Void := loop 0"),
        ));
        // The same, with `n` bound by a pattern.
        out.push(attempt(
            "non-terminating",
            format!(
                "def loop: Nat → Void\n  | Zero => loop 1\n  | n => loop {arg}\n\n\
                 theorem boom: Void := loop 0"
            ),
        ));
        out.push(attempt(
            "non-terminating",
            format!(
                "def f (n: Nat): Void := g {arg}\n\ndef g (n: Nat): Void := f n\n\n\
                 theorem boom: Void := f 0"
            ),
        ));
    }
    for (pattern, arg) in [
        ("Succ m", "(Succ m)"),
        ("Succ m", "(m + 1)"),
        ("Succ m", "(Succ (Nat.pred (Succ m)))"),
        ("Succ (Succ m)", "(Succ m + 1)"),
        ("Succ m", "(Nat.max m (Succ m))"),
    ] {
        out.push(attempt(
            "non-terminating",
            format!(
                "def loop: Nat → Void\n  | Zero => loop 1\n  | {pattern} => loop {arg}\n  | _ => loop 1\n\n\
                 theorem boom: Void := loop 0"
            ),
        ));
    }
    for arg in [
        "xs",
        "(xs ++ [])",
        "(List.drop xs 0)",
        "(List.reverse xs)",
        "(match Cons 0 xs with | Cons _ t => t | Nil => xs)",
        "(List.map xs (x => x))",
        "(List.take xs (List.length xs))",
    ] {
        out.push(attempt(
            "non-terminating",
            format!("def loop (xs: List Nat): Void := loop {arg}\n\ntheorem boom: Void := loop []"),
        ));
    }
    // A recursive function hidden behind a higher-order call.
    for call in [
        "apply loop n",
        "apply (x => loop x) n",
        "(loop: Nat → Void) n",
        "List.foldLeft [n] (absurdNat n) (acc x => loop x)",
        "let g := loop\n  g n",
        "n |> loop",
        "apply (x => loop (x + 0)) n",
        "twice (x => loop x) n",
    ] {
        out.push(attempt(
            "higher-order",
            format!(
                "def apply (f: Nat → Void) (n: Nat): Void := f n\n\n\
                 def twice (f: Nat → Void) (n: Nat): Void := f n\n\n\
                 def absurdNat (n: Nat): Void := absurdNat n\n\n\
                 def loop (n: Nat): Void :=\n  {call}\n\ntheorem boom: Void := loop 0"
            ),
        ));
    }
    // Well-founded recursion with a measure that doesn't go down.
    for (cond, arg) in [
        ("n < n", "n"),
        ("0 < n", "(n - 1)"),
        ("True = True", "(n - 1)"),
        ("n ≤ n", "n"),
        ("n < n + 1", "n"),
        ("0 < n", "(n + 1)"),
    ] {
        out.push(attempt(
            "decreasing",
            format!(
                "def loop (n: Nat): Void\n    decreasing n\n:=\n  \
                 if h: {cond} then loop {arg} else loop (n - 1)\n\ntheorem boom: Void := loop 5"
            ),
        ));
    }

    // Universes: Type in Type, large fields, Russell and Hurkens shapes.
    for (lower, upper) in [
        ("Type", "Type"),
        ("Type", "Type 1"),
        ("Type 1", "Type 1"),
        ("Type 1", "Type 2"),
        ("Type 0", "Type 65535"),
        ("Prop", "Type"),
        ("Type 65535", "Type 65535"),
    ] {
        out.push(attempt(
            "universe",
            format!("def u: {lower} := {upper}\n\ntheorem boom: Void := boom"),
        ));
    }
    for (sort, field) in [
        ("Type", "Type"),
        ("Type", "(a: Type) → a"),
        ("Type 1", "Type 1"),
        ("Prop", "Type"),
        ("Type", "Prop → Type"),
    ] {
        out.push(attempt(
            "universe",
            format!(
                "type V: {sort} =\n  | Sup (a: {field}) (f: Nat → V)\n\n\
                 theorem boom: Void := boom"
            ),
        ));
    }
    // Russell's paradox through a set type that contains its own type.
    for sort in ["Type", "Prop", "Type 1"] {
        out.push(attempt(
            "universe",
            format!(
                "type Set: {sort} =\n  | MkSet (a: Type) (f: a → Set)\n\n\
                 def notIn (s: Set): Prop :=\n  match s with\n    | MkSet a f => (x: a) → f x = s → Void\n\n\
                 theorem boom: Void := boom"
            ),
        ));
    }
    // Impredicative `Prop` with a large elimination (the first step of
    // Coquand's paradox).
    out.push(attempt(
        "prop-elim",
        "type U: Prop =\n  | MkU (a: Prop) (f: a → U)\n\n\
         def El: U → Prop\n  | MkU a f => a\n\n\
         theorem boom: Void := boom"
            .to_string(),
    ));
    for field in ["Bool", "Nat", "Type", "Prop", "List Nat", "Nat → Nat"] {
        out.push(attempt(
            "prop-elim",
            format!(
                "type Hide: Prop =\n  | H1 (x: {field})\n  | H2 (x: {field})\n\n\
                 def which: Hide → Bool\n  | H1 x => True\n  | H2 x => False\n\n\
                 def get: Hide → {field}\n  | H1 x => x\n  | H2 x => x\n\n\
                 theorem boom: Void := boom"
            ),
        ));
    }
    for (prop, pat) in [
        ("Or (0 = 0) (0 = 0)", "Inl h"),
        ("exists (n: Nat) => n = 5", "Witness n h"),
    ] {
        out.push(attempt(
            "prop-elim",
            format!(
                "def which (p: {prop}): Bool :=\n  match p with\n    | {pat} => True\n    | _ => False\n\n\
                 theorem boom: Void := boom"
            ),
        ));
    }
    // Two proofs of one proposition told apart by an index or a match.
    for p in ["Prop", "Type"] {
        out.push(attempt(
            "proof-irrelevance",
            format!(
                "type P: Prop =\n  | A\n  | B\n\ntype SameP (x: P): P → {p} =\n  | R: SameP x x\n\n\
                 theorem noAB: SameP A B → Void\n  | ()\n\n\
                 theorem boom: Void := noAB R"
            ),
        ));
    }
    out.push(attempt(
        "proof-irrelevance",
        "type P: Prop =\n  | A\n  | B\n\ntheorem noAB: A = B → Void\n  | ()\n\n\
         theorem boom: Void := noAB rfl"
            .to_string(),
    ));

    // Equations no closer may prove.
    let falsehoods: &[&str] = &[
        "(Zero: Nat) = Succ Zero",
        "2 + 2 = 5",
        "18446744073709551615 + 1 = 0",
        "18446744073709551616 = 0",
        "4294967296 * 4294967296 = 0",
        "9223372036854775807 + 1 = 9223372036854775807",
        "Nat.sub 0 1 = 1",
        "7 / 2 = 4",
        "7 % 2 = 0",
        "(0 - 1: Int) = 0",
        "(-9223372036854775808: Int) - 1 = 9223372036854775807",
        "(3: Int) * (-3) = 9",
        "Nat.pow 2 64 = 0",
        "Nat.pow 2 64 + 1 = Nat.pow 2 64",
        "\"a\" = \"b\"",
        "\"ab\".length = 3",
        "'a' = 'b'",
        "(0.1: Float) + 0.2 = 0.3",
        "(3.0: Float) * 0.1 = 0.3",
        "(0.0: Float) = -0.0",
        "(1.0: Float) / 0.0 = 0.0",
        "True = False",
        "[1, 2] = [2, 1]",
        "List.length [1, 2, 3] = 2",
        "(5: Nat) < 5",
        "(6: Nat) ≤ 5",
        "(1000000000000000000000 + 1: Nat) = 1000000000000000000000",
        "Nat.pow 3 100 = Nat.pow 3 100 + 1",
    ];
    for f in falsehoods {
        for closer in ["rfl", "omega", "cases", "ring", "byDecision"] {
            out.push(attempt(
                "false-equation",
                format!("theorem boom: {f} := {closer}"),
            ));
        }
    }
    // Statements false for some values, against the closers.
    let open: &[&str] = &[
        "(n: Nat): n - 1 + 1 = n",
        "(n: Nat): n / 2 * 2 = n",
        "(n: Nat): n % 2 = 0",
        "(n: Nat): n * n ≥ n + 1",
        "(n: Nat): n + 1 = n",
        "(n: Nat): Succ n + n = n + n",
        "(n: Nat): n + Succ Zero = n",
        "(n: Nat) (m: Nat): n + m = n",
        "(n: Nat) (m: Nat) (h: n ≤ m): m ≤ n",
        "(n: Nat) (h: n ≠ 0): n = 1",
        "(n: Int): n * n > 0",
        "(n: Int): n - 1 < 0",
        "(n: Int): n / 2 * 2 = n",
        "(b: Bool): (b && !b) = True",
        "(b: Bool) (c: Bool): (b || c) = (b && c)",
        "(xs: List Nat): xs ++ [0] = [0] ++ xs",
        "(y: Nat) (h: 0 = y): y = 5",
        "(x: Nat) (y: Nat) (h: x * y = 0): x = 0",
        "(n: Nat): Nat.pow 2 n > n * n",
    ];
    for s in open {
        for closer in ["rfl", "omega", "cases", "ring", "byDecision"] {
            out.push(attempt(
                "false-for-some",
                format!("theorem boom {s} := {closer}"),
            ));
        }
    }
    // The kernel's own arithmetic: natives on numbers and on `Succ`s around
    // them, the `k + x` form, folded `k * x`, the `+` rules R3 and R4,
    // compact text and the float primitives (docs/core.md, Numbers).
    let kernel_arith: &[&str] = &[
        ": Succ (Succ 5) = 8",
        ": Nat.sub 5 (Succ 2) = 3",
        ": Nat.leq (Succ 3) 3 = True",
        ": Nat.equal 18446744073709551616 0 = True",
        ": Nat.equal (Succ 18446744073709551615) 18446744073709551615 = True",
        ": Nat.mul 18446744073709551616 18446744073709551616 = 18446744073709551616",
        ": Nat.sub 18446744073709551616 1 = 18446744073709551616",
        ": 340282366920938463463374607431768211456 / 18446744073709551616 = 18446744073709551615",
        ": 340282366920938463463374607431768211457 % 18446744073709551616 = 0",
        " (x: Nat): 3 + x = x + 2",
        " (x: Nat): x + 3 = Succ (Succ x)",
        " (x: Nat): 2 * x = x + x + 1",
        " (x: Nat): 100000 * x = 99999 * x",
        " (x: Nat): 100000 * x = 100000 * (x + 1)",
        " (x: Nat): (x + 2) - 1 = x",
        " (x: Nat): Nat.sub (x + 3) 3 = x + 1",
        " (x: Nat): Nat.leq (x + 3) (x + 2) = True",
        " (x: Nat): Nat.equal (x + 1) (x + 2) = True",
        " (x: Nat) (y: Nat): x + (y + 2) = (x + y) + 3",
        " (x: Nat) (y: Nat): x + Succ y = Succ (Succ (x + y))",
        " (x: Nat): x + 0 = Succ x",
        ": \"abc\" = MkText (Cons 'a' (Cons 'b' Nil))",
        ": \"abc\" = MkText (Cons 'a' (Cons 'b' (Cons 'd' Nil)))",
        ": Text.toList \"ab\" = Cons 'b' (Cons 'a' Nil)",
        ": \"ab\" ++ \"c\" = \"abd\"",
        ": \"é\".length = 2",
        ": \"\\u{1F600}\".length = 2",
        ": \"a\\u{0}\" = \"a\"",
        ": Float.floor 2.5 = 3.0",
        ": Float.round 2.5 = 2.0",
        ": Float.round (-2.5) = -3.0",
        ": Float.ofNat 9007199254740993 = 9007199254740994.0",
        ": Float.trunc (-0.5) = 0.0",
        ": Float.rem 5.5 2.0 = 1.0",
        ": (0.0: Float) / 0.0 = 1.0 / 0.0",
        ": (1e308: Float) * 10.0 = 1e308",
        ": Float.ofInt (-1) = 1.0",
        ": (0.1: Float) + 0.2 - 0.3 = 0.0",
    ];
    for s in kernel_arith {
        for closer in ["rfl", "byDecision", "cases"] {
            out.push(attempt(
                "kernel arithmetic",
                format!("theorem boom{s} := {closer}"),
            ));
        }
    }
    out.push(attempt(
        "kernel arithmetic",
        "def first: Text → Char\n  | MkText (Cons c _) => c\n  | MkText Nil => 'z'\n\n\
         theorem boom: first \"abc\" = 'b' := rfl"
            .to_string(),
    ));
    // Number patterns and termination.
    for arms in [
        "  | 0 => loop 0\n  | n => loop (n - 1)",
        "  | 1 => loop 2\n  | n => loop (n - 1)",
        "  | 0 => loop 1\n  | 1 => loop 0\n  | n => loop 0",
        "  | 5 => loop 6\n  | n => loop (n + 1)",
        "  | 0 => loop 3\n  | Succ k => loop k",
    ] {
        out.push(attempt(
            "non-terminating",
            format!("def loop: Nat → Void\n{arms}\n\ntheorem boom: Void := loop 0"),
        ));
    }

    // `J` on a hypothesis, and conversion shapes from other kernels' bugs
    // (docs/research/kernel.md §5.4).
    out.push(attempt(
        "conversion",
        "theorem boom (y: Nat): ((x: Nat) => x) = (z => y) := rfl".to_string(),
    ));
    out.push(attempt(
        "conversion",
        "theorem boom (f: Nat → Nat) (x: Nat) (y: Nat): MkPair (f x) (f y) = MkPair (f x) (f x) := rfl"
            .to_string(),
    ));

    // Partial code where total code is needed.
    for call in ["loop n", "(loop n: Nat)", "match loop n with | v => v"] {
        out.push(attempt(
            "partial",
            format!(
                "def loop (n: Nat): {{Partial}} Nat := loop n\n\n\
                 def count (n: Nat): Nat := {call}\n\n\
                 theorem boom: count 0 = count 0 + 1 := omega"
            ),
        ));
    }
    // Handlers that restart their computation, and Landin's knot.
    out.push(attempt(
        "handler",
        "ability Ping where\n  ping: () → {Ping} ()\n\n\
         def forever (prog: () → {Ping} Nat): Nat :=\n  handle prog() with\n    \
         | return x => x\n    | ping(), k => forever prog\n\n\
         theorem boom: forever (() => ping()) = 0 + 1 := rfl"
            .to_string(),
    ));
    out.push(attempt(
        "handler",
        "ability Store where\n  store: (Nat → {Store} Nat) → {Store} ()\n\n\
         theorem boom: Void := boom"
            .to_string(),
    ));
    for body in [
        "drain (Call Later (v => Done (forever u)))",
        "drain (Call Later (v => Call Later (w => Done (forever u))))",
    ] {
        out.push(attempt(
            "handler",
            format!(
                "type LaterOp: Type =\n  | Later\n\ntype Unit1: Type =\n  | MkUnit\n\n\
                 def LaterRes: LaterOp → Type\n  | Later => Unit1\n\n\
                 def drain: Comp LaterOp LaterRes Prop → Prop\n  | Done x => x\n  | Call Later rest => drain (rest MkUnit)\n\n\
                 def forever (u: Unit1): Prop := {body}\n\n\
                 theorem boom: forever MkUnit := boom"
            ),
        ));
    }

    // Quotients: lifting a function that doesn't respect the relation,
    // matching, forging.
    for (lift, proof) in [
        ("(b => b)", "(x y related => rfl)"),
        ("(b => b)", "(x y related => related)"),
        ("(b => !b)", "(x y related => rfl)"),
    ] {
        out.push(attempt(
            "quotient",
            format!(
                "def AllTrue (x: Bool) (y: Bool): Prop := Unit\ndef Q: Type := Quot Bool AllTrue\n\n\
                 def back (q: Q): Bool := Quot.lift {lift} {proof} q\n\n\
                 theorem boom: back (Quot.mk False) = back (Quot.mk True) := Eq.cong back (Quot.sound Trivial)"
            ),
        ));
    }
    out.push(attempt(
        "quotient",
        "def AllTrue (x: Bool) (y: Bool): Prop := Unit\ndef Q: Type := Quot Bool AllTrue\n\n\
         def rep (q: Q): Bool :=\n  match q with\n    | Quot.mk b => b\n\n\
         theorem boom: rep (Quot.mk False) = rep (Quot.mk True) := Eq.cong rep (Quot.sound Trivial)"
            .to_string(),
    ));
    out.push(attempt(
        "quotient",
        "def AllTrue (x: Bool) (y: Bool): Prop := Unit\ndef Q: Type := Quot Bool AllTrue\n\n\
         theorem boom: (Quot.mk False: Q) = Quot.mk True → Void\n  | ()"
            .to_string(),
    ));
    out.push(attempt(
        "quotient",
        "def Never (x: Bool) (y: Bool): Prop := Void\ndef Q: Type := Quot Bool Never\n\n\
         theorem boom: (Quot.mk False: Q) = Quot.mk True := Quot.sound Trivial"
            .to_string(),
    ));

    // Opaque definitions seen through.
    for proof in ["rfl", "omega", "byDecision", "cases"] {
        out.push(attempt(
            "opaque",
            format!("opaque def k: Nat := 3\n\ntheorem boom: k = 4 := {proof}"),
        ));
        out.push(attempt(
            "opaque",
            format!("opaque def k: Nat := 3\n\ntheorem boom: k = 4\n    unfolding k\n:= {proof}"),
        ));
    }

    // Instances that lie.
    out.push(attempt(
        "instance",
        "type Two: Type =\n  | A\n  | B\n\n\
         instance badFin: Finite Two := { all = [A], complete = (x => cases) }\n\n\
         theorem boom: Void := boom"
            .to_string(),
    ));
    out.push(attempt(
        "instance",
        "type Two: Type =\n  | A\n  | B\n\n\
         instance Two.instDecEq: DecEq Two := { decide = (x y => Decidable.yes rfl) }\n\n\
         theorem boom: A = B := byDecision"
            .to_string(),
    ));

    // Records: a proof field that doesn't hold.
    out.push(attempt(
        "record",
        "type Dial: Type = { position: Nat, inRange: position ≤ 9 }\n\n\
         def bad: Dial := { position = 12, inRange = rfl }\n\n\
         theorem boom: Void := omega [bad.inRange]"
            .to_string(),
    ));
    out.push(attempt(
        "record",
        "type Dial: Type = { position: Nat, inRange: position ≤ 9 }\n\n\
         def good: Dial := { position = 3, inRange = omega }\n\n\
         def bad: Dial := { good | position = 12 }\n\n\
         theorem boom: Void := omega [bad.inRange]"
            .to_string(),
    ));

    // A shared-field update, and its generated lemmas, on a type with a
    // proof field that mentions the field.
    out.push(attempt(
        "record",
        "type Shape: Type =\n  | Dot (ref: Nat) (ok: ref ≤ 3)\n  | Circle (ref: Nat) (ok: ref ≤ 3) (r: Nat)\n\n\
         def big (s: Shape): Shape := { s | ref = 9 }\n\n\
         theorem boom: Void := boom"
            .to_string(),
    ));
    out.push(attempt(
        "record",
        "type Shape: Type =\n  | Dot (ref: Nat) (id: Nat)\n  | Circle (ref: Nat) (id: Nat) (r: Nat)\n\n\
         theorem boom (s: Shape): ({ s | ref = 1 }).id = 1 := Shape.ref.update.id s 1"
            .to_string(),
    ));
    out.push(attempt(
        "record",
        "type Shape: Type =\n  | Dot (ref: Nat) (id: Nat)\n  | Circle (ref: Nat) (id: Nat) (r: Nat)\n\n\
         theorem boom (s: Shape): ({ s | ref = 1 }).ref = s.ref := Shape.ref.update.ref s 1"
            .to_string(),
    ));

    // `Char` without its proof.
    for code in ["55296", "1114112", "57343"] {
        out.push(attempt(
            "char",
            format!("def bad: Char := MkChar {code} rfl\n\ntheorem boom: Void := boom"),
        ));
    }
    out
}

/// Whether `id`'s type is an empty type with no parameters: a closed proof
/// of `Void` (or of another empty type).
fn closed_empty(g: &stitchwort_core::Ev, id: DefId) -> bool {
    use stitchwort_core::Value;
    use stitchwort_core::value::force;
    matches!(force(g, g.def(id).ty_value().clone()), Ok(Value::Data(d, _)) if g.data(d).ctors().is_empty())
}

/// What a program's check found.
struct VoidReport {
    accepted: bool,
    /// The codes of its errors.
    codes: Vec<&'static str>,
    findings: Vec<String>,
}

/// Checks `text`, then looks for an accepted `boom`, an accepted closed
/// proof of an empty type, and an accepted theorem the search refutes.
///
/// Accepted means finished, as `audit` reads it (`Elaborator::is_unfinished`):
/// final and relying on no assumption. A declaration with an error stands
/// in as an assumption of its statement under its own name (D3527), final
/// and unmarked, so `boom: Void` with a bad body is one, and what uses it
/// relies on it; neither is accepted.
fn check_attempt(text: &str, cache: &Path) -> VoidReport {
    let mut session = session();
    session.use_check_cache(cache);
    let first = session.elab.kernel.env.defs().len();
    let result = session.load("attempt.sw", text);
    let (accepted, codes) = match &result {
        Ok(_) => (true, Vec::new()),
        Err(ds) => (
            false,
            ds.iter()
                .filter(|d| d.severity == stitchwort_syntax::Severity::Error)
                .map(|d| d.code)
                .collect(),
        ),
    };
    let g = &session.elab.ev();
    let mut findings = Vec::new();
    let mut theorems = Vec::new();
    for id in (first..g.env.defs().len()).map(DefId) {
        let def = g.def(id);
        let path = def.path().to_string();
        if path.starts_with("Std.") || path.contains('%') || session.elab.is_unfinished(id) {
            continue;
        }
        let name = def.name().to_string();
        if name == "boom" {
            findings.push("`boom` was accepted".to_string());
        } else if closed_empty(g, id) {
            findings.push(format!("`{name}` proves an empty type"));
        }
        if def.theorem() {
            theorems.push((id, path));
        }
    }
    let options = Options {
        allowed: ["Quot.sound".to_string()].into_iter().collect(),
        search: Some(SEARCH),
    };
    for audit in session.audit(&theorems, &options) {
        if let Some(search) = &audit.search
            && search.verdict == Verdict::False
        {
            findings.push(format!(
                "`{}` checked but has a counterexample: {}",
                audit.name, search.line
            ));
        }
    }
    VoidReport {
        accepted,
        codes,
        findings,
    }
}

/// The token-level edits of the elaborator fuzzer, simplified: a name
/// replaced by another of the file, a numeral changed, a line deleted or
/// duplicated, a token deleted.
fn mutate_program(rng: &mut Rng, text: &str) -> String {
    let mut tokens = tokenize(text);
    for _ in 0..=rng.below(2) {
        let names: Vec<usize> = (0..tokens.len())
            .filter(|&i| tokens[i].0 == Kind::Ident)
            .collect();
        match rng.below(6) {
            0 | 1 if names.len() > 1 => {
                let at = names[rng.below(names.len())];
                let from = names[rng.below(names.len())];
                tokens[at].1 = tokens[from].1.clone();
            }
            2 => {
                let numbers: Vec<usize> = (0..tokens.len())
                    .filter(|&i| tokens[i].0 == Kind::Number)
                    .collect();
                if !numbers.is_empty() {
                    let at = numbers[rng.below(numbers.len())];
                    let n: u128 = tokens[at].1.replace('_', "").parse().unwrap_or(0);
                    tokens[at].1 = (n + 1).to_string();
                }
            }
            3 | 4 => {
                let lines: Vec<usize> = (0..tokens.len())
                    .filter(|&i| tokens[i].1.contains('\n'))
                    .collect();
                if lines.len() > 2 {
                    let k = rng.below(lines.len() - 1);
                    let range = lines[k] + 1..lines[k + 1] + 1;
                    if rng.below(2) == 0 {
                        tokens.drain(range);
                    } else {
                        let copy: Vec<Tok> = tokens[range.clone()].to_vec();
                        tokens.splice(range.end..range.end, copy);
                    }
                }
            }
            _ => {
                let solid: Vec<usize> = (0..tokens.len())
                    .filter(|&i| !matches!(tokens[i].0, Kind::Space | Kind::Comment))
                    .collect();
                if !solid.is_empty() {
                    tokens.remove(solid[rng.below(solid.len())]);
                }
            }
        }
    }
    join(&tokens)
}

#[test]
fn void_attempts_are_rejected() {
    let started = Instant::now();
    let seed = env_number("SOUND_SEED").unwrap_or(SEED);
    let default = if tier() == Tier::All {
        4 * VOIDS
    } else {
        VOIDS
    };
    let mutants = env_number("SOUND_VOID").map_or(default, |n| n as usize);
    let mut attempts = if env_text("SOUND_VOID").is_some() {
        void_attempts()
    } else {
        tier_sample(void_attempts(), 2)
    };
    let generated = attempts.len();
    // The soundness examples, mutated.
    let soundness: Vec<String> = read_dir_sorted(&root().join("examples/soundness"))
        .into_iter()
        .map(|p| std::fs::read_to_string(&p).unwrap())
        .collect();
    let mut rng = Rng(seed ^ 0x766f_6964);
    for _ in 0..mutants {
        let text = &soundness[rng.below(soundness.len())];
        attempts.push(Attempt {
            family: "mutated soundness example",
            text: mutate_program(&mut rng, text),
        });
    }
    let reports: Vec<Result<VoidReport, String>> = run_parallel(&attempts, |a, cache| {
        on_thread(|| check_attempt(&a.text, cache))
    });

    let mut failures = Vec::new();
    let mut tally: BTreeMap<&str, [usize; 2]> = BTreeMap::new();
    let mut codes: BTreeMap<&str, usize> = BTreeMap::new();
    let verbose = env_text("SOUND_VERBOSE").is_some();
    for (i, (a, r)) in attempts.iter().zip(&reports).enumerate() {
        let row = tally.entry(a.family).or_default();
        row[0] += 1;
        match r {
            Err(panic) => failures.push(format!(
                "{} attempt {i} panicked: {panic}\n{}",
                a.family, a.text
            )),
            Ok(r) => {
                if !r.accepted {
                    row[1] += 1;
                    if i < generated
                        && let Some(c) = r.codes.first()
                    {
                        *codes.entry(c).or_default() += 1;
                    }
                }
                if !r.findings.is_empty() {
                    let saved = save_finding(&format!("void-{seed:x}-{i}"), &a.text);
                    failures.push(format!(
                        "SOUNDNESS: {} attempt {i}: {}\n  saved to {}:\n{}",
                        a.family,
                        r.findings.join("; "),
                        saved.display(),
                        a.text
                    ));
                }
                if verbose && i < generated {
                    println!("--- {} attempt {i}: {:?}\n{}", a.family, r.codes, a.text);
                }
            }
        }
    }
    let total = attempts.len();
    let rejected: usize = tally.values().map(|r| r[1]).sum();
    println!(
        "soundness_fuzz void: seed {seed:#x}, {:.1}s, {total} attempts ({generated} generated, \
         {} mutated soundness examples): {rejected} rejected, {} accepted, {} findings",
        started.elapsed().as_secs_f64(),
        total - generated,
        total - rejected,
        failures.len()
    );
    for (family, r) in &tally {
        println!("  {family:26} {:4} attempts, {:4} rejected", r[0], r[1]);
    }
    println!("  first error of each generated attempt: {codes:?}");
    assert!(
        failures.is_empty(),
        "{} finding(s):\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}
