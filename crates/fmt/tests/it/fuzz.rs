//! The formatter must never panic, whatever text it is given: it formats the
//! text or refuses it, and an `Internal` error (the output failed the §4.1
//! checks) is a formatter bug. Every output must also be stable: formatting it
//! again changes nothing. This feeds it thousands of mutated example programs
//! and random token soup, from the same generator and seed as
//! `crates/syntax/tests/it/fuzz.rs`, so failures are reproducible. The seed
//! defaults to a fixed one; `FUZZ_CASES` and `FUZZ_SEED` (decimal or `0x...`)
//! change the count and the seed.
//!
//! `FUZZ_ONLY` (a substring of a file name) mutates only matching example
//! programs, which digs deeper into one file than the whole corpus does.
//! `FUZZ_CASE=<index>` runs only the case with that 0-based index, generating
//! the cases before it so that its input is the same as in a full run, and
//! prints that input on standard output. `FUZZ_DUMP=<path>` writes each case's
//! input to that file (overwriting it) before the case is formatted, so a run
//! killed for memory or time leaves the case it was on behind.
//!
//! `FUZZ_COMMENTS=<rate>` (a number from 0 to 1) also inserts a `-- c` comment
//! at each line break with that chance (where a comment can go without moving
//! a token to another line), half trailing (ending at a line end, which is
//! added if needed) and half on a line of their own. Without it, the generator
//! is unchanged.
//!
//! The run ends with the counts of cases skipped because they didn't parse,
//! refused although they parsed, and formatted (and checked for idempotence).

use std::io::Write;
use std::ops::Range;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};

use stitchwort_fmt::{Error, format};
use stitchwort_syntax::{SourceMap, parse_module};

/// Each case is one format and one re-format. 50,000 keeps the release run
/// well under ten seconds; set `FUZZ_CASES` for a longer run, and `FUZZ_ONLY`
/// (a substring of a file name) to mutate only matching example programs,
/// which digs deeper into one file than the whole corpus does.
const CASES: u64 = 50_000;
const SEED: u64 = 0x9e37_79b9_7f4a_7c15;
/// A mutated example can grow a lot when ranges are duplicated; the parser
/// doesn't need more than this to be exercised.
const MAX_LEN: usize = 64 * 1024;

/// The punctuation, keywords and whitespace an edit may insert.
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
    "-",
    " -",
    "- ",
    " -1",
    ".abs",
    "let",
    "match",
    "def",
    "type",
    "theorem",
    "test",
    "namespace",
    "calc",
    "rewrite",
    "omega",
    "cases",
    "ring",
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
    "\t",
    "                                ",
];

const IDENTS: &[&str] = &["x", "y", "foo", "Nat", "List", "map", "_", "x'", "ℕ"];
const NUMBERS: &[&str] = &["0", "1", "42", "999999999999999999999999"];
const LITERALS: &[&str] = &[
    "\"\"",
    "\"hello\"",
    "\"a${x}b\"",
    "\"unterminated",
    "'a'",
    "'\\n'",
    "''",
    "'ab'",
];

/// xorshift64*: tiny, deterministic, good enough for generating test cases.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    /// A possibly empty range within `len`, with both ends chosen uniformly.
    fn range(&mut self, len: usize) -> Range<usize> {
        if len == 0 {
            return 0..0;
        }
        let a = self.below(len + 1);
        let b = self.below(len + 1);
        a.min(b)..a.max(b)
    }
}

fn read_corpus() -> Vec<String> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut texts = Vec::new();
    for group in ["accept", "reject"] {
        let dir = root.join(group);
        let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("can't read {}: {e}", dir.display()))
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "sw"))
            .collect();
        // `read_dir` order is unspecified; sort so the fixed seed always
        // produces the same cases.
        files.sort();
        for file in files {
            if let Ok(only) = std::env::var("FUZZ_ONLY")
                && !file.to_string_lossy().contains(&only)
            {
                continue;
            }
            texts.push(
                std::fs::read_to_string(&file)
                    .unwrap_or_else(|e| panic!("can't read {}: {e}", file.display())),
            );
        }
    }
    assert!(
        !texts.is_empty(),
        "no example programs found under {}",
        root.display()
    );
    texts
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
    if a == b && c == d {
        return;
    }
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

fn mutate(rng: &mut Rng, base: &str) -> String {
    // Working on chars keeps every intermediate string valid UTF-8, even when
    // an edit lands in the middle of a multi-byte character.
    let mut chars: Vec<char> = base.chars().collect();
    for _ in 0..=rng.below(4) {
        match rng.below(5) {
            0 => {
                chars.drain(rng.range(chars.len()));
            }
            1 => {
                let copy: Vec<char> = chars[rng.range(chars.len())].to_vec();
                let at = rng.below(chars.len() + 1);
                chars.splice(at..at, copy);
            }
            2 => swap_ranges(&mut chars, rng),
            3 => {
                let token = TOKENS[rng.below(TOKENS.len())];
                let at = rng.below(chars.len() + 1);
                chars.splice(at..at, token.chars());
            }
            _ => {
                let keep = rng.below(chars.len() + 1);
                chars.truncate(keep);
            }
        }
        if chars.len() > MAX_LEN {
            chars.truncate(MAX_LEN);
        }
    }
    chars.into_iter().collect()
}

fn soup(rng: &mut Rng) -> String {
    let mut text = String::new();
    for _ in 0..=rng.below(200) {
        let atom = match rng.below(4) {
            0 => TOKENS[rng.below(TOKENS.len())],
            1 => IDENTS[rng.below(IDENTS.len())],
            2 => NUMBERS[rng.below(NUMBERS.len())],
            _ => LITERALS[rng.below(LITERALS.len())],
        };
        text.push_str(atom);
        match rng.below(6) {
            0 | 1 => {}
            2 => text.push(' '),
            3 => text.push_str("  "),
            4 => text.push('\n'),
            _ => text.push('\t'),
        }
        if text.len() > MAX_LEN {
            break;
        }
    }
    text
}

/// Whether `ch` can be part of an identifier, keyword or number. A boundary
/// between two such characters would split a token, so it is not a token
/// boundary.
fn is_word(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '\''
}

/// The positions in `chars` where a comment can go without moving a token to
/// another line: at a line break (or the ends), and not inside a string,
/// character literal, text block or `--` comment. A `--` comment runs to the
/// end of its line, so one inserted anywhere else would split the line and can
/// turn layout-sensitive syntax (a continuation line starting with `.map`, say)
/// into a parse error.
fn token_boundaries(chars: &[char]) -> Vec<bool> {
    let mut boundaries = vec![false; chars.len() + 1];
    // `"""` text blocks span lines and may hold `"` and `--`, so the scanner
    // has to know them apart from strings and comments.
    let mut in_string = false;
    let mut in_text = false;
    let mut in_char = false;
    let mut in_comment = false;
    let mut escaped = false;
    let mut i = 0;
    while i <= chars.len() {
        let at_line_break =
            i == 0 || i == chars.len() || chars[i] == '\n' || (i > 0 && chars[i - 1] == '\n');
        if !in_string && !in_text && !in_char && !in_comment {
            boundaries[i] = at_line_break;
        }
        let Some(&ch) = chars.get(i) else {
            break;
        };
        if in_comment {
            if ch == '\n' {
                in_comment = false;
            }
            i += 1;
        } else if escaped {
            escaped = false;
            i += 1;
        } else if in_string {
            if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            i += 1;
        } else if in_text {
            if ch == '\\' {
                escaped = true;
                i += 1;
            } else if chars[i..].starts_with(&['"', '"', '"']) {
                in_text = false;
                i += 3;
            } else {
                i += 1;
            }
        } else if in_char {
            if ch == '\\' {
                escaped = true;
            } else if ch == '\'' {
                in_char = false;
            }
            i += 1;
        } else if chars[i..].starts_with(&['"', '"', '"']) {
            in_text = true;
            i += 3;
        } else if ch == '"' {
            in_string = true;
            i += 1;
        } else if ch == '\'' && !(i > 0 && is_word(chars[i - 1])) {
            // `x'` is an identifier, not the start of a character literal.
            in_char = true;
            i += 1;
        } else if ch == '-' && chars.get(i + 1) == Some(&'-') {
            in_comment = true;
            i += 1;
        } else {
            i += 1;
        }
    }
    boundaries
}

/// True with probability `rate`, consuming one draw from `rng`.
fn chance(rng: &mut Rng, rate: f64) -> bool {
    rate > 0.0 && (rng.below(10_000) as f64) < rate * 10_000.0
}

/// Insert `-- c` comments at random line breaks, each with probability
/// `rate`. Half are trailing comments, followed by a line break when the text
/// does not already have one there; the other half sit on a line of their own,
/// with a line break on either side. (A comment can't share a line with code
/// after it, so these are the positions that don't move a token to another
/// line and change the layout.)
fn add_comments(rng: &mut Rng, text: &str, rate: f64) -> String {
    let chars: Vec<char> = text.chars().collect();
    let boundaries = token_boundaries(&chars);
    let mut out = Vec::with_capacity(chars.len());
    for (i, &boundary) in boundaries.iter().enumerate() {
        if boundary && chance(rng, rate) {
            if rng.below(2) == 0 {
                out.extend("-- c".chars());
                if chars.get(i) != Some(&'\n') {
                    out.push('\n');
                }
            } else {
                out.extend("\n-- c\n".chars());
            }
        }
        if let Some(&ch) = chars.get(i) {
            out.push(ch);
        }
    }
    if out.len() > MAX_LEN {
        out.truncate(MAX_LEN);
    }
    out.into_iter().collect()
}

/// An environment number, decimal or `0x...`; unset or empty is `None`, and an
/// unparsable one fails the run rather than silently using the default.
fn env_number(name: &str) -> Option<u64> {
    let value = std::env::var(name).ok().filter(|v| !v.is_empty())?;
    let parsed = match value.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16),
        None => value.parse(),
    };
    Some(parsed.unwrap_or_else(|_| panic!("{name}={value:?} is not a number")))
}

/// `FUZZ_DUMP`: a path to write each formatted case's input to, before it is
/// formatted.
fn dump_path() -> Option<PathBuf> {
    let path = std::env::var_os("FUZZ_DUMP").filter(|path| !path.is_empty())?;
    Some(PathBuf::from(path))
}

/// `FUZZ_COMMENTS`: the chance of a comment at each token boundary, a number
/// from 0 to 1.
fn comment_rate() -> Option<f64> {
    let value = std::env::var("FUZZ_COMMENTS")
        .ok()
        .filter(|value| !value.is_empty())?;
    let rate: f64 = value
        .parse()
        .unwrap_or_else(|_| panic!("FUZZ_COMMENTS={value:?} is not a number"));
    assert!(
        (0.0..=1.0).contains(&rate),
        "FUZZ_COMMENTS={value:?} is not between 0 and 1"
    );
    Some(rate)
}

/// Whether `text` lexes and parses, as the formatter's refusal check does
/// (D1021). A case the formatter refuses is skipped unless this says it
/// parsed: then the formatter refused a parseable file, counted apart.
fn parses(text: &str) -> bool {
    let file = SourceMap::new().add("input.sw", text);
    parse_module(file, text).is_ok()
}

#[test]
fn comments_keep_a_valid_file_parseable() {
    // A leading operator can't start a continuation line (docs/syntax.md,
    // "Layout"), so a comment inserted mid-line would move `+` to the start of
    // a line and make this a parse error.
    let program = "def f (x: Nat): Nat :=\n  x +\n    x\n";
    // A text block holds its own lines (and `"` and `--`), so a comment in it
    // would change the text, and one inside `"""` would break the delimiter.
    let block = "def text: Text := \"\"\"\n  a -- not a comment\n  b\n  \"\"\"\n";
    for text in [program, block] {
        let mut rng = Rng(SEED);
        let commented = add_comments(&mut rng, text, 1.0);
        let once = format(&commented)
            .unwrap_or_else(|e| panic!("{e} on input:\n{}", commented.escape_debug()));
        let twice = format(&once).expect("its own output parses");
        assert_eq!(
            twice,
            once,
            "not idempotent on input:\n{}",
            commented.escape_debug()
        );
    }
}

#[test]
fn the_formatter_never_panics_and_is_idempotent() {
    let cases = env_number("FUZZ_CASES").unwrap_or(CASES);
    let seed = env_number("FUZZ_SEED").unwrap_or(SEED);
    let only = env_number("FUZZ_CASE");
    let comments = comment_rate();
    match only {
        Some(only) => eprintln!("fuzz fmt: case {only} (0-based), seed {seed:#x}"),
        None => eprintln!("fuzz fmt: {cases} cases, seed {seed:#x}"),
    }
    let dump = dump_path();
    let corpus = read_corpus();
    let mut rng = Rng(seed);
    let mut skipped = 0;
    let mut refused = 0;
    let mut formatted = 0;
    // Reaching case n from the fixed seed means generating every case before
    // it; only the selected one is formatted.
    let last = only.map_or(cases, |only| only.saturating_add(1));
    for case in 0..last {
        let state = rng.0;
        let mut text = if rng.below(2) == 0 {
            let base = rng.below(corpus.len());
            mutate(&mut rng, &corpus[base])
        } else {
            soup(&mut rng)
        };
        if let Some(rate) = comments {
            text = add_comments(&mut rng, &text, rate);
        }
        if only.is_some_and(|only| case != only) {
            continue;
        }
        if let Some(path) = &dump {
            std::fs::write(path, &text).unwrap_or_else(|e| {
                panic!(
                    "can't write FUZZ_DUMP={} for case {case}: {e}",
                    path.display()
                )
            });
        }
        if only.is_some() {
            print!("{text}");
            std::io::stdout()
                .flush()
                .unwrap_or_else(|e| panic!("can't print case {case}: {e}"));
        }
        let context = |what: &str| {
            format!(
                "case {case} (seed {seed:#x}, rng state {state:#x}): {what} on input:\n  {}",
                text.escape_debug()
            )
        };
        let Ok(outcome) = catch_unwind(AssertUnwindSafe(|| format(&text))) else {
            panic!("{}", context("the formatter panicked"));
        };
        match outcome {
            Err(Error::Refused(_)) if parses(&text) => refused += 1,
            Err(Error::Refused(_)) => skipped += 1,
            Err(Error::Internal(message)) => {
                panic!("{}", context(&format!("internal error ({message})")))
            }
            Ok(once) => {
                formatted += 1;
                let Ok(again) = catch_unwind(AssertUnwindSafe(|| format(&once))) else {
                    panic!("{}", context("the formatter panicked on its own output"));
                };
                match again {
                    Ok(twice) if twice == once => {}
                    Ok(twice) => panic!(
                        "{}\nonce:  {}\ntwice: {}",
                        context("not idempotent"),
                        once.escape_debug(),
                        twice.escape_debug()
                    ),
                    Err(e) => panic!(
                        "{}\nonce: {}",
                        context(&format!("its own output fails to format ({e})")),
                        once.escape_debug()
                    ),
                }
            }
        }
    }
    eprintln!(
        "fuzz fmt: {cases} cases, seed {seed:#x}: {skipped} skipped (failed to parse), \
         {refused} refused (parsed, formatter refused), {formatted} formatted (idempotence checked)"
    );
    // Sanity check that the generator isn't only producing nonsense. A single
    // selected case may legitimately be one the formatter refuses.
    if only.is_none() {
        assert!(formatted > 0, "no random input was formatted");
    }
}
