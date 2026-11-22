//! The formatter must never panic, whatever text it is given: it formats the
//! text or refuses it, and an `Internal` error (the output failed the §4.1
//! checks) is a formatter bug. Every output must also be stable: formatting it
//! again changes nothing. This feeds it thousands of mutated example programs
//! and random token soup, in the style of `crates/syntax/tests/it/fuzz.rs`
//! but retrying a mutation that doesn't parse with fewer edits (see
//! `generate`), so most cases are formatted. The seed
//! defaults to a fixed one; `FUZZ_CASES` and `FUZZ_SEED` (decimal or `0x...`)
//! change the count and the seed.
//!
//! `FUZZ_ONLY` (a substring of a file name) mutates only matching example
//! programs, which digs deeper into one file than the whole corpus does.
//! `FUZZ_CASE=<index>` runs only the case with that 0-based index, generating
//! the cases before it so that its input is the same as in a full run, and
//! prints that input on standard output. `FUZZ_DUMP=<path>` writes each
//! candidate input to that file (overwriting it) just before it is parsed
//! during generation or formatted, so a run killed for memory or time leaves
//! the case it was on behind, and a panic in the parser leaves the input that
//! panicked there for reproduction.
//!
//! `FUZZ_WRITE_DIR=<dir>` writes every case that parses to `<dir>/case-N.sw`
//! (N the 0-based index, zero-padded), for `task fmt:twin`'s fuzzer inputs.
//!
//! `FUZZ_COMMENTS=<rate>` (a number from 0 to 1) also inserts a `-- c` comment
//! at each token boundary with that chance, half trailing (ending at a line
//! end, which is added if needed) and half on a line of their own. Boundaries
//! where the next line would start with a method section or an infix-only
//! operator are left out (a comment there would put that token at the start of
//! a line, which the parser rejects), as are the insides of text blocks.
//! Without `FUZZ_COMMENTS`, the generator is unchanged.
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

/// `edits` is how many mutations to apply.
fn mutate(rng: &mut Rng, base: &str, edits: usize) -> String {
    // Working on chars keeps every intermediate string valid UTF-8, even when
    // an edit lands in the middle of a multi-byte character.
    let mut chars: Vec<char> = base.chars().collect();
    for _ in 0..edits {
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

/// The positions in `chars` where one token can end and another begin: not
/// inside a string, character literal, text block or `--` comment, and not
/// inside a word. The scanner is only a heuristic, but it keeps inserted
/// comments from cutting literals and existing comments apart.
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
        if !in_string && !in_text && !in_char && !in_comment {
            let left_word = i > 0 && is_word(chars[i - 1]);
            let right_word = i < chars.len() && is_word(chars[i]);
            let splits_comment = i > 0 && i < chars.len() && chars[i - 1] == '-' && chars[i] == '-';
            boundaries[i] =
                !(left_word && right_word) && !splits_comment && !starts_with_infix_only(chars, i);
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

/// Whether a line starting at `i` would start with a token that can't start a
/// line: a method section (`.name`), a comma, or an infix-only operator
/// (`crates/syntax/src/parser.rs`'s `is_infix_only`). The scanner skips spaces
/// and tabs first, since the line starts with those when the boundary is in the
/// indentation. A `|>` may start a line, and a prefix `-` or `!` may start one
/// indented further than its block, so those stay.
fn starts_with_infix_only(chars: &[char], i: usize) -> bool {
    let mut j = i;
    while matches!(chars.get(j), Some(' ' | '\t')) {
        j += 1;
    }
    let Some(&first) = chars.get(j) else {
        return false;
    };
    if first == '.' || first == ',' {
        return true;
    }
    if first == '!' && chars.get(j + 1) == Some(&'=') {
        return true;
    }
    if first == '-' && chars.get(j + 1) == Some(&'>') {
        return true;
    }
    matches!(
        first,
        '+' | '*'
            | '/'
            | '%'
            | '<'
            | '>'
            | '='
            | ':'
            | '&'
            | '≠'
            | '≤'
            | '≥'
            | '∧'
            | '∨'
            | '↔'
            | '→'
    )
}

/// True with probability `rate`, consuming one draw from `rng`.
fn chance(rng: &mut Rng, rate: f64) -> bool {
    rate > 0.0 && (rng.below(10_000) as f64) < rate * 10_000.0
}

/// Insert `-- c` comments at random token boundaries, each with probability
/// `rate`. Half are trailing comments, followed by a line break when the text
/// does not already have one there; the other half sit on a line of their own,
/// with a line break on either side. A boundary after which a line would start
/// with a method section or an infix-only operator is left out: the comment
/// would move that token to the start of a line, which doesn't parse.
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

/// `FUZZ_DUMP`: a path to write each candidate input to, before it is parsed
/// or formatted.
fn dump_path() -> Option<PathBuf> {
    let path = std::env::var_os("FUZZ_DUMP").filter(|path| !path.is_empty())?;
    Some(PathBuf::from(path))
}

/// Write `text` to the dump at `path`. A dump needed to reproduce a failure
/// must not be missing, so failing to write one fails the run.
fn write_dump(path: &Path, text: &str) {
    std::fs::write(path, text)
        .unwrap_or_else(|e| panic!("can't write FUZZ_DUMP={}: {e}", path.display()));
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

/// How many times a case is regenerated, with fewer edits each time, when the
/// text doesn't parse. Most mutations of a program break it; a case that
/// does parse exercises the formatter, which is the point.
const ATTEMPTS: usize = 8;

/// One case: usually a mutated example, sometimes token soup (which seldom
/// parses, but reaches odd corners of the lexer). A mutated example that
/// doesn't parse is retried from the same stream with fewer edits (4, 4, 3,
/// 3, 2, 2, 1, 1 at most, and the comment rate halved each time), and the last try is kept if none parses. The
/// retries come from the one seeded stream, so a case is a function of the
/// seed and its index alone.
fn generate(rng: &mut Rng, corpus: &[String], comments: Option<f64>) -> String {
    if rng.below(8) == 0 {
        let text = soup(rng);
        return match comments {
            Some(rate) => add_comments(rng, &text, rate),
            None => text,
        };
    }
    let base = &corpus[rng.below(corpus.len())];
    let mut text = String::new();
    for attempt in 0..ATTEMPTS {
        let edits = 1 + rng.below(4 - attempt / 2);
        text = mutate(rng, base, edits);
        if let Some(rate) = comments {
            text = add_comments(rng, &text, rate / f64::from(1u32 << attempt));
        }
        if parses(&text) {
            break;
        }
    }
    text
}

/// Whether `text` parses, as the formatter's refusal check does (D1021). A case
/// the formatter refuses is skipped unless this says it parsed: then the
/// formatter refused a parseable file, counted apart.
///
/// The input is written to the dump first, so if the parser panics, the dump
/// holds the input that panicked rather than the previous case's.
fn parses(text: &str) -> bool {
    parses_with(text, dump_path().as_deref(), |text| {
        let file = SourceMap::new().add("input.sw", text);
        parse_module(file, text).is_ok()
    })
}

/// `parses` with the dump and parser left to the caller, so the dump-before-
/// parse behaviour can be tested without the real parser.
fn parses_with(text: &str, dump: Option<&Path>, parse: impl FnOnce(&str) -> bool) -> bool {
    if let Some(path) = dump {
        write_dump(path, text);
    }
    parse(text)
}

#[test]
fn a_parser_panic_leaves_the_input_in_the_dump() {
    let dir = std::env::temp_dir().join(format!("stitchwort-fmt-fuzz-dump-{}", std::process::id()));
    let path = dir.join("dump.sw");
    std::fs::create_dir_all(&dir).expect("can't create the dump directory");
    let input = "theorem e:(()):=byWalking";
    let panicked = catch_unwind(|| {
        parses_with(input, Some(&path), |text| {
            assert_eq!(text, input);
            panic!("the stand-in parser panicked");
        })
    });
    assert!(
        panicked.is_err(),
        "the stand-in parser should have panicked"
    );
    assert_eq!(
        std::fs::read_to_string(&path).expect("can't read the dump"),
        input,
        "the dump should hold the input that panicked"
    );
    std::fs::remove_dir_all(&dir).expect("can't remove the dump directory");
}

/// How a refused case is counted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Refusal {
    /// The input didn't parse, so the case was skipped.
    Skipped,
    /// The input parsed, but the formatter refused it.
    Refused,
}

fn classify_refusal(text: &str) -> Refusal {
    if parses(text) {
        Refusal::Refused
    } else {
        Refusal::Skipped
    }
}

#[test]
fn a_refusal_is_counted_as_skipped_or_refused() {
    assert_eq!(classify_refusal("def x: Nat := )"), Refusal::Skipped);
    assert_eq!(classify_refusal("def x: Nat := 1\n"), Refusal::Refused);
}

#[test]
fn comments_go_mid_line_but_not_before_an_infix_operator() {
    let text = "def f (x: Nat): Nat := x + x\n";
    let chars: Vec<char> = text.chars().collect();
    let boundaries = token_boundaries(&chars);
    let plus = text.find('+').expect("a plus");
    assert!(
        !boundaries[plus],
        "a comment before `+` would start a line with it"
    );
    assert!(
        boundaries[plus + 2],
        "a comment after `+ x` is still in the middle of the line"
    );

    // A method section can't start a line either.
    let text = "def g (p: Point): Nat := p.x\n";
    let chars: Vec<char> = text.chars().collect();
    let boundaries = token_boundaries(&chars);
    let dot = text.find('.').expect("a dot");
    assert!(
        !boundaries[dot],
        "a comment before `.x` would start a method section"
    );

    // Nothing goes inside a text block or between its `"""` delimiters.
    let text = "def text: Text := \"\"\"\n  a -- not a comment\n  b\n  \"\"\"\n";
    let chars: Vec<char> = text.chars().collect();
    let boundaries = token_boundaries(&chars);
    let open = text.find("\"\"\"").expect("an opening `\"\"\"`");
    let close = text.rfind("\"\"\"").expect("a closing `\"\"\"`");
    assert!(
        boundaries[open + 1..close + 3]
            .iter()
            .all(|boundary| !boundary),
        "a comment in a text block changes its text or breaks `\"\"\"`"
    );
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
    let write_dir = std::env::var_os("FUZZ_WRITE_DIR").filter(|dir| !dir.is_empty());
    if let Some(dir) = &write_dir {
        std::fs::create_dir_all(dir).unwrap_or_else(|e| panic!("can't create FUZZ_WRITE_DIR: {e}"));
    }
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
        let text = generate(&mut rng, &corpus, comments);
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
        if let Some(dir) = &write_dir
            && parses(&text)
        {
            let path = Path::new(dir).join(format!("case-{case:06}.sw"));
            std::fs::write(&path, &text)
                .unwrap_or_else(|e| panic!("can't write {}: {e}", path.display()));
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
            Err(Error::Refused(_)) => match classify_refusal(&text) {
                Refusal::Skipped => skipped += 1,
                Refusal::Refused => refused += 1,
            },
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
