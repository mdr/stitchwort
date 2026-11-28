//! Elaborator fuzzing, stage 1 (SW-685): mutated example programs, run through
//! a full check (`Session::load`: parse, elaborate, kernel, export checks).
//!
//! This lives in the driver crate because it is the lowest crate that can run
//! a whole check, with the check cache and the elaborator's limits; the
//! syntax, formatter and kernel fuzzers sit in their own crates.
//!
//! The generator is the syntax fuzzer's (`crates/syntax/tests/it/fuzz.rs`: the
//! xorshift `Rng`, `TOKENS`, and the character-level edits `swap_ranges` and
//! range delete or duplicate), copied rather than shared, because a test
//! file can't be depended on and a new crate for 60 lines isn't worth it.
//! On top of it are token-level edits that keep most programs parsing:
//! replace or swap identifiers drawn from the same file, change a numeral,
//! swap a constructor or type name for another, delete, duplicate or swap
//! lines, swap two arguments, drop an annotation.
//!
//! Oracles, for every case:
//!
//! 1. no panic;
//! 2. no `E-INTERNAL` (or `E-ALGEBRA-INTERNAL`, `E-ARITHMETIC-INTERNAL`) diagnostic;
//! 3. the kernel never rejects a term the elaborator built. The kernel's
//!    refusals come back as ordinary diagnostics, so the elaborator records
//!    each one as it passes (`stitchwort_elab::take_kernel_rejections`), and a
//!    refusal with a code that says "ill-typed term" (`BAD_KERNEL_CODES`) whose
//!    code, message and location the check then reports as a diagnostic of its
//!    own fails the case. The location is the kernel's primary span, or the
//!    declaration being checked when the kernel gave none. (The kernel
//!    is also the checker for some user mistakes: termination, positivity,
//!    `E-PROP-ELIM`, `E-NOT-A-PROP`; and the elaborator may rewrite a
//!    refusal into a better diagnostic, as `E-MUTUAL-SIGNATURE`.);
//! 4. the case finishes: the session's work limit is `WORK` (a hit is
//!    `E-RESOURCE`, an acceptable outcome), and a wall-clock watchdog of
//!    `WATCHDOG` reports a hang, naming the case;
//!    (The main check shares one cache of the library's files across the
//!    run, so the standard library is checked once, not in every case:
//!    SW-3707.)
//! 5. on every `CACHE_EVERY`th case, a cold and then a warm check cache give
//!    the same verdict and the same diagnostic codes;
//! 6. no check holds more than `MEM_CAP` bytes of heap (`FUZZ_MEM_CAP_MB`
//!    sets another): a check that does is cancelled and the case reported
//!    with its input saved, and the run goes on (SW-2582). The test's
//!    allocator counts each thread's live bytes, and the budget's cancel hook
//!    reads the count every few thousand evaluation steps.
//!
//! The seed is fixed. A failure prints the oracle, the case number, the seed
//! and the generator's state, and writes the input to
//! `target/fuzz-elab/<seed>-<case>.sw`. `FUZZ_CASES` and `FUZZ_SEED` (decimal or
//! `0x…`) control a longer or different run; `FUZZ_CORPUS=1` skips the
//! mutation and checks the unmutated examples (a calibration of the oracles).
//!
//! Every case is generated, so case `n` is the same program whatever the
//! count (for the same examples: a new one changes every case), but only cases `FUZZ_FROM..FUZZ_TO` are checked (default: all), and
//! `FUZZ_ONLY=n` checks case `n` alone; with `FUZZ_DUMP=1` the checked cases'
//! inputs are also written to `target/fuzz-elab/<seed>-<case>.sw`. A case
//! whose check runs longer than `SLOW` is named on standard error, so one
//! that runs away in memory, which the watchdog is too slow for, can be
//! found from the log.

use std::ops::Range;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::mpsc;
use std::sync::{Arc, Mutex, OnceLock};
use std::time::{Duration, Instant};

use stitchwort_core::budget::{Budget, Limits};
use stitchwort_driver::check_cache::CheckCache;
use stitchwort_driver::driver::{Session, Tier, test_threads, tier};
use stitchwort_elab::cache::{Key, Store};
use stitchwort_elab::{Rejection, RejectionLocation};
use stitchwort_syntax::{FileId, SourceMap, Span, parse_module_recovering};

#[path = "support/heap_cap.rs"]
mod heap_cap;

/// The default number of cases, about 20 s in the broad tier (four times as
/// many in the all tier); `FUZZ_CASES` sets another count.
const CASES: usize = 400;
const SEED: u64 = 0x5eed_e1ab_0000_0685;
const MAX_LEN: usize = 64 * 1024;
const STACK: usize = 16 * 1024 * 1024;
/// Evaluation steps a case may spend (the default, 10^10, takes minutes).
const WORK: u64 = 300_000_000;
/// Nodes a value may grow to when read back (the default is 2 million;
/// several of the runaway cases reached it, for a verdict, `E-RESOURCE`,
/// that comes the same at half).
const SIZE: u64 = 1_000_000;
/// A case still running after this long is a hang. The work limit bounds a
/// genuine runaway well inside this.
const WATCHDOG: Duration = Duration::from_secs(60);
/// A check of a case running this long is named as it runs. Short, because
/// a case that runs away in memory can fill 16 GB in under ten seconds.
const SLOW: Duration = Duration::from_secs(5);
/// The most heap one check may hold. A normal case takes under 200 MB; the
/// cases that ran away took 6 to 16 GB each. Four checks run at once.
const MEM_CAP: i64 = 2 << 30;
/// Every this many cases also check the cold and warm cache agree.
const CACHE_EVERY: usize = 10;

/// Kernel error codes that mean the term the elaborator gave was ill-typed or
/// ill-formed, which the elaborator is supposed to prevent. The others the
/// kernel can give (`E-TERMINATION`, `E-POSITIVITY`, `E-UNIVERSE`,
/// `E-NONEXHAUSTIVE`, `E-RESOURCE`, `E-BUILTIN`, `E-UNFOLDING-*`,
/// `E-NOT-OPAQUE`, `E-FAILED-DEPENDENCY`) are verdicts on the program that
/// the user can cause.
const BAD_KERNEL_CODES: &[&str] = &[
    "E-MALFORMED",
    "E-TYPE-MISMATCH",
    "E-NOT-A-FUNCTION",
    "E-NOT-A-TYPE",
    "E-CANNOT-INFER",
    "E-REFL",
    "E-INDEX-STUCK",
];

const TOKENS: &[&str] = &[
    "(",
    ")",
    "[",
    "]",
    "{",
    "}",
    "${",
    "\"",
    "'",
    "\\",
    "|",
    "|>",
    "=>",
    "->",
    ":=",
    ":",
    ",",
    "..",
    "--",
    "let",
    "match",
    "def",
    "type",
    "theorem",
    "test",
    "namespace",
    "calc",
    "rewrite",
    "arithmetic",
    "cases",
    "algebra",
    "opaque",
    "unfolding",
    "interface",
    "instance",
    "import",
    "if",
    "then",
    "else",
    "\n",
    " ",
];

/// Names a swapped type or constructor may become, besides those in the file.
const KNOWN_UPPER: &[&str] = &[
    "Nat", "Bool", "List", "Option", "True", "False", "Some", "None", "Int", "Text", "Char",
    "Unit", "Type", "Prop", "Eq", "Refl", "Cons", "Nil", "Pair", "Either", "Left", "Right",
];

/// xorshift64*, as in the syntax fuzzer.
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

    fn range(&mut self, len: usize) -> Range<usize> {
        if len == 0 {
            return 0..0;
        }
        let a = self.below(len + 1);
        let b = self.below(len + 1);
        a.min(b)..a.max(b)
    }
}

// --- the corpus --------------------------------------------------------

struct Example {
    name: String,
    text: String,
}

fn read_corpus() -> Vec<Example> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut out = Vec::new();
    for group in ["accept", "reject"] {
        let dir = root.join(group);
        let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("can't read {}: {e}", dir.display()))
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "sw"))
            .collect();
        files.sort();
        for file in files {
            out.push(Example {
                name: format!("{group}/{}", file.file_name().unwrap().to_string_lossy()),
                text: std::fs::read_to_string(&file).expect("readable example"),
            });
        }
    }
    assert!(!out.is_empty(), "no examples under {}", root.display());
    out
}

// --- token-level mutation ----------------------------------------------

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Ident,
    Number,
    Space,
    Comment,
    Str,
    Punct,
}

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

/// Splits `text` into tokens that concatenate back to it exactly.
fn tokenize(text: &str) -> Vec<(Kind, String)> {
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
                i += 1;
            }
            if i < chars.len() && chars[i] == '"' {
                i += 1;
            }
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
            i += 1;
            Kind::Punct
        };
        out.push((kind, chars[start..i].iter().collect()));
    }
    out
}

fn is_upper(s: &str) -> bool {
    s.chars().next().is_some_and(char::is_uppercase)
}

const KEYWORDS: &[&str] = &[
    "let",
    "match",
    "def",
    "type",
    "theorem",
    "test",
    "namespace",
    "calc",
    "rewrite",
    "arithmetic",
    "cases",
    "algebra",
    "opaque",
    "unfolding",
    "interface",
    "instance",
    "import",
    "if",
    "then",
    "else",
    "with",
    "where",
    "in",
    "fn",
    "forall",
    "export",
    "from",
    "decreasing",
    "by",
];

fn is_name(tok: &(Kind, String)) -> bool {
    tok.0 == Kind::Ident && !KEYWORDS.contains(&tok.1.as_str())
}

fn indices(tokens: &[(Kind, String)], pred: impl Fn(&(Kind, String)) -> bool) -> Vec<usize> {
    (0..tokens.len()).filter(|&i| pred(&tokens[i])).collect()
}

/// Start and end token index of each line (the end includes its newline).
fn lines(tokens: &[(Kind, String)]) -> Vec<Range<usize>> {
    let mut out = Vec::new();
    let mut start = 0;
    for (i, (_, s)) in tokens.iter().enumerate() {
        if s.contains('\n') {
            out.push(start..i + 1);
            start = i + 1;
        }
    }
    if start < tokens.len() {
        out.push(start..tokens.len());
    }
    out
}

fn mutate_tokens(rng: &mut Rng, tokens: &mut Vec<(Kind, String)>) {
    let names = indices(tokens, is_name);
    match rng.below(14) {
        // Replace an identifier by another from the same file.
        0..=2 => {
            if names.is_empty() {
                return;
            }
            let at = names[rng.below(names.len())];
            let upper = is_upper(&tokens[at].1);
            let same: Vec<usize> = names
                .iter()
                .copied()
                .filter(|&j| is_upper(&tokens[j].1) == upper)
                .collect();
            let from = same[rng.below(same.len())];
            tokens[at].1 = tokens[from].1.clone();
        }
        // Swap two identifiers.
        3 | 4 => {
            if names.len() < 2 {
                return;
            }
            let a = names[rng.below(names.len())];
            let b = names[rng.below(names.len())];
            let (x, y) = (tokens[a].1.clone(), tokens[b].1.clone());
            tokens[a].1 = y;
            tokens[b].1 = x;
        }
        // Change a numeral.
        5 | 6 => {
            let numbers = indices(tokens, |t| t.0 == Kind::Number);
            if numbers.is_empty() {
                return;
            }
            let at = numbers[rng.below(numbers.len())];
            let old: u64 = tokens[at].1.replace('_', "").parse().unwrap_or(0);
            tokens[at].1 = match rng.below(6) {
                0 => "0".into(),
                1 => (old + 1).to_string(),
                2 => old.saturating_sub(1).to_string(),
                3 => (old * 2).to_string(),
                4 => "340282366920938463463374607431768211456".into(),
                _ => rng.below(100).to_string(),
            };
        }
        // Swap a constructor or type name for another.
        7 => {
            let uppers = indices(tokens, |t| is_name(t) && is_upper(&t.1));
            if uppers.is_empty() {
                return;
            }
            let at = uppers[rng.below(uppers.len())];
            tokens[at].1 = if rng.below(2) == 0 {
                KNOWN_UPPER[rng.below(KNOWN_UPPER.len())].to_string()
            } else {
                tokens[uppers[rng.below(uppers.len())]].1.clone()
            };
        }
        // Delete, duplicate or swap lines.
        8..=10 => {
            let ls = lines(tokens);
            if ls.is_empty() {
                return;
            }
            let i = rng.below(ls.len());
            let line = ls[i].clone();
            match rng.below(3) {
                0 => {
                    tokens.drain(line);
                }
                1 => {
                    let copy: Vec<_> = tokens[line.clone()].to_vec();
                    tokens.splice(line.end..line.end, copy);
                }
                _ => {
                    if i + 1 < ls.len() {
                        let next = ls[i + 1].clone();
                        let a: Vec<_> = tokens[line.clone()].to_vec();
                        let b: Vec<_> = tokens[next.clone()].to_vec();
                        let mut swapped = b;
                        swapped.extend(a);
                        tokens.splice(line.start..next.end, swapped);
                    }
                }
            }
        }
        // Swap two adjacent arguments (names, numbers, or bracketed atoms).
        11 => {
            let atoms = indices(tokens, |t| is_name(t) || t.0 == Kind::Number);
            let pairs: Vec<usize> = atoms
                .windows(2)
                .filter(|w| w[1] == w[0] + 2 && tokens[w[0] + 1].1 == " ")
                .map(|w| w[0])
                .collect();
            if pairs.is_empty() {
                return;
            }
            let a = pairs[rng.below(pairs.len())];
            tokens.swap(a, a + 2);
        }
        // Drop an annotation: from a `:` to the end of its group or line.
        12 => {
            let colons = indices(tokens, |t| t.1 == ":");
            if colons.is_empty() {
                return;
            }
            let at = colons[rng.below(colons.len())];
            let mut depth = 0i32;
            let mut end = at + 1;
            while end < tokens.len() {
                let s = tokens[end].1.as_str();
                if s.contains('\n') {
                    break;
                }
                if s == "(" || s == "[" || s == "{" {
                    depth += 1;
                } else if s == ")" || s == "]" || s == "}" {
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                } else if depth == 0 && (s == "=" || s == ":=" || s == "|") {
                    break;
                }
                end += 1;
            }
            tokens.drain(at..end);
        }
        // Delete a token, or insert one from the syntax fuzzer's list.
        _ => {
            if tokens.is_empty() {
                return;
            }
            if rng.below(2) == 0 {
                let at = rng.below(tokens.len());
                tokens.remove(at);
            } else {
                let at = rng.below(tokens.len() + 1);
                tokens.insert(
                    at,
                    (Kind::Punct, TOKENS[rng.below(TOKENS.len())].to_string()),
                );
            }
        }
    }
}

fn swap_ranges(chars: &mut Vec<char>, rng: &mut Rng) {
    let n = chars.len();
    if n < 2 {
        return;
    }
    let mut bounds = [0; 4];
    for bound in &mut bounds {
        *bound = rng.below(n + 1);
    }
    bounds.sort_unstable();
    let [a, b, c, d] = bounds;
    let first: Vec<char> = chars[a..b].to_vec();
    let second: Vec<char> = chars[c..d].to_vec();
    let mut swapped = Vec::with_capacity(n);
    swapped.extend_from_slice(&chars[..a]);
    swapped.extend_from_slice(&second);
    swapped.extend_from_slice(&chars[b..c]);
    swapped.extend_from_slice(&first);
    swapped.extend_from_slice(&chars[d..]);
    *chars = swapped;
}

/// A mutation of `base`: one to three edits, token-level mostly, and now and
/// then one of the syntax fuzzer's character-level ones.
fn mutate(rng: &mut Rng, base: &str) -> String {
    let mut tokens = tokenize(base);
    for _ in 0..=rng.below(3) {
        if rng.below(8) == 0 {
            let mut chars: Vec<char> = tokens.iter().flat_map(|t| t.1.chars()).collect();
            match rng.below(3) {
                0 => {
                    chars.drain(rng.range(chars.len()));
                }
                1 => {
                    let copy: Vec<char> = chars[rng.range(chars.len())].to_vec();
                    let at = rng.below(chars.len() + 1);
                    chars.splice(at..at, copy);
                }
                _ => swap_ranges(&mut chars, rng),
            }
            let text: String = chars.into_iter().collect();
            tokens = tokenize(&text);
        } else {
            mutate_tokens(rng, &mut tokens);
        }
    }
    let mut text: String = tokens.into_iter().map(|t| t.1).collect();
    if text.len() > MAX_LEN {
        let mut cut = MAX_LEN;
        while !text.is_char_boundary(cut) {
            cut -= 1;
        }
        text.truncate(cut);
    }
    text
}

// --- running a case ----------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
struct Verdict {
    accepted: bool,
    /// The codes of every error and warning, in order.
    codes: Vec<&'static str>,
}

#[global_allocator]
static ALLOCATOR: heap_cap::Counting = heap_cap::Counting;

/// The cap in bytes: `FUZZ_MEM_CAP_MB` or [`MEM_CAP`].
fn mem_cap() -> i64 {
    env_number("FUZZ_MEM_CAP_MB").map_or(MEM_CAP, |mb| (mb as i64) << 20)
}

struct Report {
    verdict: Verdict,
    /// The text parsed with no error.
    parsed: bool,
    /// The elaborator saw at least one declaration (or the file parsed).
    /// A recovered partial parse counts, so this can be higher than
    /// [`Report::parsed`].
    reached: bool,
    rejections: Vec<Rejection>,
    /// Every diagnostic's code, message and primary source location.
    messages: Vec<ReportMessage>,
    /// A message of each diagnostic with an INTERNAL code.
    internal: Vec<String>,
    /// The most heap the check held at once, in bytes.
    peak: i64,
}

/// What a diagnostic says, and where, for oracle 3 to compare with a kernel
/// rejection.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ReportMessage {
    code: &'static str,
    message: String,
    span: Option<Span>,
}

/// Which check cache a check uses.
#[derive(Clone)]
enum CacheUse {
    /// The library files' entries, kept in one directory for the whole run
    /// (SW-3707): a library file's entry is keyed by its own text, so a
    /// case's declarations cannot reach another case through it, and the
    /// cases skip re-checking the standard library (about 20 s of CPU in a
    /// debug build for the parser library).
    SharedLibrary,
    /// A directory of the case's own, for the cold and warm comparison.
    Own(PathBuf),
}

/// A check cache that keeps only library files' entries (unit names
/// `std.…`), not the case's own namespaces.
struct LibraryOnly(CheckCache);

impl Store for LibraryOnly {
    fn compiler(&self) -> &str {
        self.0.compiler()
    }
    fn salt(&self) -> [u8; 16] {
        self.0.salt()
    }
    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        unit.starts_with("std.").then(|| self.0.read(unit, key))?
    }
    fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
        if unit.starts_with("std.") {
            self.0.write(unit, key, entry);
        }
    }
}

/// The directory of the shared library cache, made on first use.
fn shared_library_dir() -> &'static Path {
    static DIR: OnceLock<PathBuf> = OnceLock::new();
    DIR.get_or_init(|| {
        let dir =
            std::env::temp_dir().join(format!("stitchwort-fuzz-elab-std-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        // Makes the salt before any two checks race to.
        let _ = CheckCache::at(&dir);
        dir
    })
}

/// `None` if the check held more heap than the cap and was cancelled.
fn check(text: &str, cache: &CacheUse) -> Option<Report> {
    Budget::set_cancel_hook(heap_cap::over_cap);
    let before = heap_cap::start(mem_cap(), None);
    let mut sources = SourceMap::new();
    let file = sources.add("fuzz.sw", text);
    let (module, errors) = parse_module_recovering(file, text, STACK);
    let parsed = errors.is_empty();
    let reached = parsed || module.namespace.is_some() || !module.decls.is_empty();

    let mut session = Session::for_stack(STACK);
    session.elab.options.limits = Limits {
        work: WORK,
        size: SIZE,
        ..Limits::for_stack(STACK)
    };
    // A timed counterexample search can differ between two runs.
    session.elab.options.untimed_counterexamples = true;
    match cache {
        CacheUse::SharedLibrary => session
            .elab
            .set_check_cache(Rc::new(LibraryOnly(CheckCache::at(shared_library_dir())))),
        CacheUse::Own(dir) => session.use_check_cache(dir),
    }
    stitchwort_elab::record_kernel_rejections(true);
    stitchwort_elab::take_kernel_rejections();
    let budget = &session.elab.kernel.machine.budget;
    budget.set_cancel_flag(Default::default());
    budget.watch_cancel(true);
    let result = session.load("fuzz.sw", text);
    session.elab.kernel.machine.budget.watch_cancel(false);
    if session.elab.kernel.machine.budget.cancelled() {
        stitchwort_elab::take_kernel_rejections();
        return None;
    }
    let rejections = stitchwort_elab::take_kernel_rejections();
    let (accepted, diagnostics) = match result {
        Ok(_) => (true, std::mem::take(&mut session.warnings)),
        Err(ds) => (false, ds),
    };
    let internal = diagnostics
        .iter()
        .filter(|d| d.code.contains("INTERNAL") && d.code != "E-STD-INTERNAL")
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect();
    let codes = diagnostics.iter().map(|d| d.code).collect();
    let messages = diagnostics
        .iter()
        .map(|d| ReportMessage {
            code: d.code,
            message: d.message.clone(),
            span: d
                .labels
                .first()
                .map(|label| label.span)
                .filter(|span| *span != Span::NOWHERE),
        })
        .collect();
    let peak = heap_cap::peak_since(before);
    Some(Report {
        verdict: Verdict { accepted, codes },
        parsed,
        reached,
        rejections,
        messages,
        internal,
        peak,
    })
}

/// Whether `rejection` and `message` describe the same kernel error: same
/// code, same message, and the same source location. A rejection the kernel
/// gave no span for is matched by the declaration it happened in.
fn same_kernel_error(rejection: &Rejection, message: &ReportMessage) -> bool {
    if rejection.code != message.code || rejection.message != message.message {
        return false;
    }
    match rejection.location {
        RejectionLocation::Span(span) => message.span == Some(span),
        RejectionLocation::Declaration(declaration) => message.span.is_some_and(|span| {
            declaration.file == span.file
                && declaration.start <= span.start
                && span.end <= declaration.end
        }),
    }
}

/// Oracle 3: the kernel rejections that the check then reports as a
/// diagnostic of their own, formatted for the failure message.
fn bad_kernel_rejections(report: &Report) -> Vec<String> {
    report
        .rejections
        .iter()
        .filter(|rejection| BAD_KERNEL_CODES.contains(&rejection.code))
        .filter(|rejection| {
            report
                .messages
                .iter()
                .any(|message| same_kernel_error(rejection, message))
        })
        .map(|rejection| format!("{}: {}", rejection.code, rejection.message))
        .collect()
}

enum Ran {
    Done(Box<Report>),
    /// Cancelled for holding more heap than the cap.
    OverMemory,
    Panicked(String),
    Hung,
}

/// Runs `check` on a thread of its own, with the watchdog.
fn run_watched(text: &str, cache: &CacheUse) -> Ran {
    let (tx, rx) = mpsc::channel();
    let text = text.to_string();
    let cache = cache.clone();
    let spawned = std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let outcome = catch_unwind(AssertUnwindSafe(|| check(&text, &cache)));
            let _ = tx.send(match outcome {
                Ok(Some(report)) => Ran::Done(Box::new(report)),
                Ok(None) => Ran::OverMemory,
                Err(payload) => Ran::Panicked(
                    payload
                        .downcast_ref::<String>()
                        .cloned()
                        .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                        .unwrap_or_else(|| "<non-string panic>".into()),
                ),
            });
        })
        .expect("spawn a case thread");
    match rx.recv_timeout(WATCHDOG) {
        Ok(ran) => {
            let _ = spawned.join();
            ran
        }
        // The thread is left running; the test fails and the process ends.
        Err(_) => Ran::Hung,
    }
}

fn temp_dir(case: usize) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-fuzz-elab-{}-{case}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

struct Case {
    number: usize,
    state: u64,
    base: String,
    text: String,
}

#[derive(Default)]
struct Tally {
    parsed: usize,
    reached: usize,
    accepted: usize,
    cache_checked: usize,
    failures: Vec<(usize, String)>,
}

/// Names a check that held over a quarter of the cap, on standard error, so
/// a case heading for the cap can be found in the log.
fn note_heavy(case: &Case, run: &str, report: &Report) {
    if report.peak > mem_cap() / 4 {
        eprintln!(
            "fuzz_elab: case {} ({run}) held {} MB of heap",
            case.number,
            report.peak >> 20
        );
    }
}

/// Checks `case`, calling `starting` before each check of it (the slow-case
/// report times each one).
fn run_case(case: &Case, seed: u64, out_dir: &Path, tally: &mut Tally, starting: &dyn Fn()) {
    let fail = |tally: &mut Tally, oracle: &str, detail: String| {
        let path = out_dir.join(format!("{seed:x}-{}.sw", case.number));
        let _ = std::fs::create_dir_all(out_dir);
        let _ = std::fs::write(&path, &case.text);
        tally.failures.push((
            case.number,
            format!(
                "oracle {oracle}: case {} (seed {seed:#x}, rng state {:#x}, from {}): {detail}\n  input saved to {}",
                case.number,
                case.state,
                case.base,
                path.display()
            ),
        ));
    };
    let over_memory = |tally: &mut Tally, run: &str| {
        fail(
            tally,
            "6 (memory)",
            format!(
                "a check ({run}) held over {} MB of heap and was cancelled",
                mem_cap() >> 20
            ),
        )
    };
    starting();
    let report = match run_watched(&case.text, &CacheUse::SharedLibrary) {
        Ran::Done(report) => *report,
        Ran::Panicked(message) => {
            return fail(tally, "1 (no panic)", format!("panicked: {message}"));
        }
        Ran::OverMemory => return over_memory(tally, "shared library cache"),
        Ran::Hung => {
            return fail(
                tally,
                "4 (budget)",
                format!("still running after {}s", WATCHDOG.as_secs()),
            );
        }
    };
    note_heavy(case, "shared library cache", &report);
    tally.parsed += usize::from(report.parsed);
    tally.reached += usize::from(report.reached);
    tally.accepted += usize::from(report.verdict.accepted);
    if !report.internal.is_empty() {
        fail(tally, "2 (no E-INTERNAL)", report.internal.join("; "));
    }
    let bad = bad_kernel_rejections(&report);
    if !bad.is_empty() {
        fail(
            tally,
            "3 (kernel rejected an elaborated term)",
            bad.join("; "),
        );
    }
    if case.number.is_multiple_of(CACHE_EVERY) && report.reached {
        tally.cache_checked += 1;
        let dir = temp_dir(case.number);
        starting();
        let cold = run_watched(&case.text, &CacheUse::Own(dir.clone()));
        starting();
        let warm = run_watched(&case.text, &CacheUse::Own(dir.clone()));
        let _ = std::fs::remove_dir_all(&dir);
        match (cold, warm) {
            (Ran::Done(cold), Ran::Done(warm)) => {
                note_heavy(case, "cold cache", &cold);
                note_heavy(case, "warm cache", &warm);
                if cold.verdict != warm.verdict {
                    fail(
                        tally,
                        "5 (cold and warm cache agree)",
                        format!("cold {:?}, warm {:?}", cold.verdict, warm.verdict),
                    );
                }
                if cold.verdict != report.verdict {
                    fail(
                        tally,
                        "5 (cache changes nothing)",
                        format!(
                            "shared library cache {:?}, cold {:?}",
                            report.verdict, cold.verdict
                        ),
                    );
                }
            }
            (Ran::Panicked(m), _) | (_, Ran::Panicked(m)) => {
                fail(tally, "1 (no panic, with the cache)", m);
            }
            (Ran::OverMemory, _) | (_, Ran::OverMemory) => over_memory(tally, "with the cache"),
            _ => fail(tally, "4 (budget, with the cache)", "hung".into()),
        }
    }
}

/// A case being checked: its number, and when it started.
type Started = (usize, Instant);

fn env_number(name: &str) -> Option<u64> {
    let value = std::env::var(name).ok()?;
    match value.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16).ok(),
        None => value.parse().ok(),
    }
}

#[test]
fn mutated_examples_check_without_internal_errors() {
    // The all tier runs four times as many.
    let default = if tier() == Tier::All {
        4 * CASES
    } else {
        CASES
    };
    let cases = env_number("FUZZ_CASES").map_or(default, |n| n as usize);
    let seed = env_number("FUZZ_SEED").unwrap_or(SEED);
    let corpus_only = std::env::var("FUZZ_CORPUS").is_ok_and(|v| v == "1");
    let corpus = read_corpus();
    let out_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/fuzz-elab");
    let started = Instant::now();

    // The cases are made first, in order, from the one generator, so a case
    // doesn't depend on how the checks are spread over threads.
    let mut rng = Rng(seed);
    let all: Vec<Case> = if corpus_only {
        corpus
            .iter()
            .enumerate()
            .map(|(number, e)| Case {
                number,
                state: 0,
                base: e.name.clone(),
                text: e.text.clone(),
            })
            .collect()
    } else {
        (0..cases)
            .map(|number| {
                let state = rng.0;
                let base = &corpus[rng.below(corpus.len())];
                Case {
                    number,
                    state,
                    base: base.name.clone(),
                    text: mutate(&mut rng, &base.text),
                }
            })
            .collect()
    };

    let only = env_number("FUZZ_ONLY").map(|n| n as usize);
    let from = only
        .or(env_number("FUZZ_FROM").map(|n| n as usize))
        .unwrap_or(0);
    let to = only
        .map(|n| n + 1)
        .or(env_number("FUZZ_TO").map(|n| n as usize))
        .unwrap_or(all.len())
        .min(all.len());
    let mut all = all;
    all.truncate(to);
    all.drain(..from.min(to));
    if std::env::var("FUZZ_DUMP").is_ok_and(|v| v == "1") {
        std::fs::create_dir_all(&out_dir).unwrap();
        for case in &all {
            let path = out_dir.join(format!("{seed:x}-{}.sw", case.number));
            std::fs::write(path, &case.text).unwrap();
        }
    }

    let next = Arc::new(Mutex::new(0usize));
    let all = Arc::new(all);
    // What each worker is checking, and since when, for the slow-case report.
    let running: Arc<Mutex<Vec<Option<Started>>>> =
        Arc::new(Mutex::new(vec![None; test_threads().min(4)]));
    let finished = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let tallies: Vec<Tally> = std::thread::scope(|scope| {
        {
            let running = Arc::clone(&running);
            let finished = Arc::clone(&finished);
            scope.spawn(move || {
                let mut reported = std::collections::BTreeSet::new();
                while !finished.load(std::sync::atomic::Ordering::Relaxed) {
                    std::thread::sleep(Duration::from_millis(500));
                    for (number, since) in running.lock().unwrap().iter().flatten() {
                        if since.elapsed() >= SLOW && reported.insert(*number) {
                            eprintln!(
                                "fuzz_elab: case {number} (seed {seed:#x}) still running after {}s",
                                SLOW.as_secs()
                            );
                        }
                    }
                }
            });
        }
        let handles: Vec<_> = (0..test_threads().min(4))
            .map(|worker| {
                let next = Arc::clone(&next);
                let all = Arc::clone(&all);
                let running = Arc::clone(&running);
                let out_dir = out_dir.clone();
                scope.spawn(move || {
                    let mut tally = Tally::default();
                    loop {
                        let i = {
                            let mut n = next.lock().unwrap();
                            let i = *n;
                            *n += 1;
                            i
                        };
                        let Some(case) = all.get(i) else { break };
                        let starting = || {
                            running.lock().unwrap()[worker] = Some((case.number, Instant::now()))
                        };
                        run_case(case, seed, &out_dir, &mut tally, &starting);
                        running.lock().unwrap()[worker] = None;
                    }
                    tally
                })
            })
            .collect();
        // Stops the reporter even if a worker panicked.
        struct Finish(Arc<std::sync::atomic::AtomicBool>);
        impl Drop for Finish {
            fn drop(&mut self) {
                self.0.store(true, std::sync::atomic::Ordering::Relaxed);
            }
        }
        let _finish = Finish(Arc::clone(&finished));
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });

    let _ = std::fs::remove_dir_all(shared_library_dir());
    let total = all.len();
    let sum = |f: fn(&Tally) -> usize| tallies.iter().map(f).sum::<usize>();
    let pct = |n: usize| 100.0 * n as f64 / total.max(1) as f64;
    println!(
        "fuzz_elab: {total} cases, seed {seed:#x}, {:.1}s: {:.1}% parsed, {:.1}% reached the \
         elaborator, {:.1}% accepted, {} cache comparisons",
        started.elapsed().as_secs_f64(),
        pct(sum(|t| t.parsed)),
        pct(sum(|t| t.reached)),
        pct(sum(|t| t.accepted)),
        sum(|t| t.cache_checked),
    );
    let reached = sum(|t| t.reached);
    let mut failures: Vec<(usize, String)> = tallies.into_iter().flat_map(|t| t.failures).collect();
    failures.sort();
    if !failures.is_empty() {
        let shown: Vec<&str> = failures.iter().take(10).map(|(_, m)| m.as_str()).collect();
        panic!(
            "{} failure(s) in {total} cases; the first {}:\n\n{}",
            failures.len(),
            shown.len(),
            shown.join("\n\n")
        );
    }
    if !corpus_only {
        // The generator must keep producing programs the elaborator sees.
        assert!(
            total < 100 || reached * 4 > total,
            "under a quarter of the cases reached the elaborator"
        );
    }
}

/// A report with only what oracle 3 reads, for the tests that make one by
/// hand.
fn report_with(rejections: Vec<Rejection>, messages: Vec<ReportMessage>) -> Report {
    Report {
        verdict: Verdict {
            accepted: false,
            codes: Vec::new(),
        },
        parsed: true,
        reached: true,
        rejections,
        messages,
        internal: Vec::new(),
        peak: 0,
    }
}

/// SW-4888: a trial arm's kernel rejection and an unrelated elaborator error
/// in a later declaration both say "type mismatch"; oracle 3 must not pair
/// them.
#[test]
fn oracle_3_ignores_unrelated_messages() {
    let text = r#"import Std (Bool, Decidable, Eq, Vec)
type Colour = | Red | Green
def anyColour (x y: Colour): Decidable (x = y) := match x, y with
  | Red, Red => Decidable.yes byComputing
  | Green, Green => Decidable.yes byComputing
  | Red, Green => Decidable.no (e => Bool.falseNotTrue (Eq.cong isGreen e))
  | Green, x => Decidable.no (e => Bool.falseNotTrue (Eq.cong isRed e))
def isGreen: Colour → Bool
  | Green => True
  | Red => False
def isRed: Colour → Bool
  | Red => True
  | Green => False
def three: Vec Nat 2 := VCons 1 (VCons 2 True)
"#;
    let report = match run_watched(text, &CacheUse::SharedLibrary) {
        Ran::Done(report) => report,
        Ran::Panicked(message) => panic!("check panicked: {message}"),
        Ran::OverMemory => panic!("check held too much memory"),
        Ran::Hung => panic!("check hung"),
    };
    assert!(
        report
            .rejections
            .iter()
            .any(|rejection| rejection.code == "E-TYPE-MISMATCH"),
        "the trial arm's kernel rejection is missing: {:?}",
        report.rejections
    );
    assert!(
        report
            .messages
            .iter()
            .any(|message| message.code == "E-TYPE-MISMATCH"),
        "the unrelated diagnostic is missing: {:?}",
        report.messages
    );
    assert!(
        bad_kernel_rejections(&report).is_empty(),
        "oracle 3 paired unrelated errors: {:?}",
        bad_kernel_rejections(&report)
    );
}

/// SW-4888: oracle 3 still fires when the kernel's own refusal is what the
/// check reports, both at the same span and, when the kernel gave no span, in
/// the declaration it happened in.
#[test]
fn oracle_3_pairs_a_rejection_with_its_own_diagnostic() {
    let span = Span::new(FileId::SCRATCH, 10, 20);
    let report = report_with(
        vec![Rejection {
            code: "E-TYPE-MISMATCH",
            message: "type mismatch".into(),
            location: RejectionLocation::Span(span),
        }],
        vec![ReportMessage {
            code: "E-TYPE-MISMATCH",
            message: "type mismatch".into(),
            span: Some(span),
        }],
    );
    assert_eq!(
        bad_kernel_rejections(&report),
        vec!["E-TYPE-MISMATCH: type mismatch".to_string()]
    );

    let declaration = Span::new(FileId::SCRATCH, 100, 200);
    let inside = Span::new(FileId::SCRATCH, 120, 130);
    let report = report_with(
        vec![Rejection {
            code: "E-MALFORMED",
            message: "malformed core term".into(),
            location: RejectionLocation::Declaration(declaration),
        }],
        vec![ReportMessage {
            code: "E-MALFORMED",
            message: "malformed core term".into(),
            span: Some(inside),
        }],
    );
    assert_eq!(
        bad_kernel_rejections(&report),
        vec!["E-MALFORMED: malformed core term".to_string()]
    );

    let outside = Span::new(FileId::SCRATCH, 300, 310);
    let report = report_with(
        vec![Rejection {
            code: "E-MALFORMED",
            message: "malformed core term".into(),
            location: RejectionLocation::Declaration(declaration),
        }],
        vec![ReportMessage {
            code: "E-MALFORMED",
            message: "malformed core term".into(),
            span: Some(outside),
        }],
    );
    assert!(
        bad_kernel_rejections(&report).is_empty(),
        "a diagnostic outside the declaration was paired"
    );
}

/// SW-4910: a `byComputing` in the arms of a `match` proving an equation over
/// a let-bound value must be refused by the elaborator, not left to the
/// kernel (oracle 3).
#[test]
fn oracle_3_let_bound_value_in_match_arms() {
    let text = include_str!("../../../docs/reviews/repros/fuzz-elab-26112611-1834.sw");
    let report = match run_watched(text, &CacheUse::SharedLibrary) {
        Ran::Done(report) => report,
        Ran::Panicked(message) => panic!("check panicked: {message}"),
        Ran::OverMemory => panic!("check held too much memory"),
        Ran::Hung => panic!("check hung"),
    };
    assert!(
        report
            .messages
            .iter()
            .any(|message| message.code == "E-REFL"),
        "the elaborator's E-REFL is missing: {:?}",
        report.messages
    );
    assert!(
        bad_kernel_rejections(&report).is_empty(),
        "the kernel rejected what the elaborator passed: {:?} {:?}",
        report.rejections,
        bad_kernel_rejections(&report)
    );
}

/// The report of checking `text`, which must finish.
fn report_of(text: &str) -> Report {
    match run_watched(text, &CacheUse::SharedLibrary) {
        Ran::Done(report) => *report,
        Ran::Panicked(message) => panic!("check panicked: {message}"),
        Ran::OverMemory => panic!("check held too much memory"),
        Ran::Hung => panic!("check hung"),
    }
}

/// That the elaborator refused `text` with `E-REFL` and the kernel saw
/// nothing it refused (oracle 3).
fn assert_elaborator_refl(text: &str) {
    let report = report_of(text);
    assert!(
        report
            .messages
            .iter()
            .any(|message| message.code == "E-REFL"),
        "the elaborator's E-REFL is missing: {:?}",
        report.messages
    );
    assert!(
        report.rejections.is_empty(),
        "the kernel refused something first: {:?}",
        report.rejections
    );
}

/// SW-4913: a `match` that calls the local definition it is in is one group
/// with it, and an equation about the `match` later in the definition is
/// checked in that group's bodies: the elaborator refuses a false
/// `byComputing` there before the group goes to the kernel. So it does a
/// true one that needs the `match` unfolded, which the kernel, checking
/// the group with its members pending, can't do either.
#[test]
fn oracle_3_comparison_in_a_recursive_helpers_group() {
    let text = include_str!("../../../docs/reviews/repros/sw-4913-recursive-helper.sw");
    assert_elaborator_refl(text);
    assert_elaborator_refl(&text.replace("pick = 0", "pick = go k"));
}

/// SW-4913: a comparison in a `match` admitted with its owner (it calls the
/// owner) is made when the owner's body is finished, before the kernel sees
/// either: the elaborator refuses it.
#[test]
fn oracle_3_comparison_in_a_joined_group() {
    assert_elaborator_refl(include_str!(
        "../../../docs/reviews/repros/sw-4913-joined-group.sw"
    ));
}

/// SW-4913: an equation about a local definition written after it, in the
/// owner, waits for the definition to be final, and holds.
#[test]
fn comparison_after_a_recursive_local_waits_for_it() {
    let report = report_of(include_str!(
        "../../../docs/reviews/repros/sw-4913-lemma-after-local.sw"
    ));
    assert!(report.verdict.accepted, "refused: {:?}", report.messages);
}
