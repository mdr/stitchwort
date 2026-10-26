//! The formatter must never panic, whatever text it is given: it formats the
//! text or refuses it, and an `Internal` error (the output failed the §4.1
//! checks) is a formatter bug. Every output must also be stable: formatting it
//! again changes nothing. This feeds it thousands of mutated example programs
//! and random token soup, from the same generator and seed as
//! `crates/syntax/tests/fuzz.rs`, so failures are reproducible.

use std::ops::Range;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};

use stitchwort_fmt::{Error, format};

/// Each case is one format and one re-format. 50,000 keeps the release run
/// well under ten seconds; set `FUZZ_CASES` for a longer run.
const CASES: usize = 50_000;
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

#[test]
fn the_formatter_never_panics_and_is_idempotent() {
    let cases: usize = std::env::var("FUZZ_CASES")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(CASES);
    let corpus = read_corpus();
    let mut rng = Rng(SEED);
    let mut accepted = 0;
    for case in 0..cases {
        let state = rng.0;
        let text = if rng.below(2) == 0 {
            let base = rng.below(corpus.len());
            mutate(&mut rng, &corpus[base])
        } else {
            soup(&mut rng)
        };
        let context = |what: &str| {
            format!(
                "case {case} (seed {SEED:#x}, rng state {state:#x}): {what} on input:\n  {}",
                text.escape_debug()
            )
        };
        let Ok(outcome) = catch_unwind(AssertUnwindSafe(|| format(&text))) else {
            panic!("{}", context("the formatter panicked"));
        };
        match outcome {
            Err(Error::Refused(_)) => {}
            Err(Error::Internal(message)) => {
                panic!("{}", context(&format!("internal error ({message})")))
            }
            Ok(once) => {
                accepted += 1;
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
    // Sanity check that the generator isn't only producing nonsense.
    assert!(accepted > 0, "no random input was formatted");
}
