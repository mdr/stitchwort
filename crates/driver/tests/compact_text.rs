//! Compact text in the evaluator (docs/proposals/compact-text.md, option B1):
//! a text literal's characters are one `Term::Chars`, standing for
//! `Cons (MkChar c rfl) … Nil`, and nothing the kernel or the elaborator does
//! may tell the two apart.
//!
//! The tests are in three tiers, as the proposal plans them:
//!
//! - **small, comprehensive**: every short text over awkward alphabets, and
//!   random ones, through the prelude's text operations, with the literal
//!   compact and with it written out as constructors (compact text switched
//!   off). The results are compared as complete core terms (proofs and the
//!   functions inside a `No` included), after expanding every compact list
//!   in the compact run's result with the reference evaluator's own
//!   expansion. Conversion is compared too, across the two representations;
//! - **medium**: texts of thousands of characters, on the stack-safe machine,
//!   compact against a copy made of ordinary cons cells;
//! - **large**: million-character literals, against expectations computed
//!   here, and laws.
//!
//! Then the representation's own cases: ranges of a buffer, the kernel's
//! treatment of proofs that aren't `rfl`, unification through the
//! elaborator, termination, hashing, printing, memory retention and the
//! binding to the prelude.

use std::rc::Rc;

use stitchwort_core::chars::{self, Chars};
use stitchwort_core::check::{declare_def, define_def, infer_closed};
use stitchwort_core::hash::def_hash;
use stitchwort_core::reference;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{self, Value};
use stitchwort_core::{BigUint, DataId, DefId, Globals, Icit, Limits, Term};
use stitchwort_driver::driver::{Cache, Outcome, Session, with_stack};
use stitchwort_syntax::{SourceMap, Span};

fn span() -> Span {
    Span::point(SourceMap::new().add("kernel", ""), 0)
}

fn data(g: &Globals, name: &str) -> DataId {
    g.find_data(name)
        .unwrap_or_else(|| panic!("the prelude defines `{name}`"))
}

fn def(g: &Globals, name: &str) -> DefId {
    DefId(
        g.defs
            .iter()
            .position(|d| &*d.name == name)
            .unwrap_or_else(|| panic!("`{name}` is defined")),
    )
}

/// Source syntax for a text literal, with everything but printable ASCII
/// escaped.
fn literal(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '"' | '\\' => {
                out.push('\\');
                out.push(c);
            }
            ' '..='~' => out.push(c),
            c => out.push_str(&format!("\\u{{{:X}}}", u32::from(c))),
        }
    }
    out.push('"');
    out
}

fn load(session: &mut Session, source: &str) {
    if let Err(errors) = session.load("test.sw", source) {
        let shown: Vec<String> = errors
            .iter()
            .map(|d| {
                let labels: Vec<String> = d
                    .labels
                    .iter()
                    .map(|l| l.message.chars().take(300).collect())
                    .collect();
                format!("{}: {} {labels:?}", d.code, d.message)
            })
            .collect();
        panic!("{shown:#?}");
    }
}

fn codes(session: &mut Session, source: &str) -> Vec<&'static str> {
    match session.load("test.sw", source) {
        Ok(_) => Vec::new(),
        Err(ds) => ds.iter().map(|d| d.code).collect(),
    }
}

/// Elaborates `expr` with text literals compact or not, and evaluates it.
fn value_of(session: &mut Session, expr: &str, compact: bool) -> (Term, Value) {
    session.elab.globals.builtins.disable_compact_text = !compact;
    let parsed = session.parse_expression("<test>", expr).unwrap();
    let result = session.elab.infer_expr(&parsed);
    session.elab.globals.builtins.disable_compact_text = false;
    let (term, _) = result.unwrap_or_else(|e| panic!("{expr}: {e:?}"));
    let g = &session.elab.globals;
    let _op = g.budget.operation(session.elab.limits);
    let value = value::eval(g, &[], &term).unwrap();
    (term, value)
}

/// The normal form of `value`, as a complete core term with every compact
/// list expanded (by the reference evaluator, not `chars`).
fn normal(session: &Session, value: &Value) -> String {
    let g = &session.elab.globals;
    let _op = g.budget.operation(session.elab.limits);
    let term = value::quote(g, 0, value).unwrap();
    format!("{:?}", reference::expand_term(g, &term))
}

fn has_chars(term: &Term) -> bool {
    term.subterms().any(|(t, _)| matches!(t, Term::Chars(_)))
}

/// `expr` gives the same complete result with its literals compact as with
/// them written out as constructors.
fn same_both_ways(session: &mut Session, expr: &str) {
    let (compact_term, compact) = value_of(session, expr, true);
    let (cons_term, cons) = value_of(session, expr, false);
    assert!(!has_chars(&cons_term), "{expr}: compact text was off");
    if !expr.contains("\"\"") {
        assert!(has_chars(&compact_term), "{expr}: compact text was on");
    }
    assert_eq!(normal(session, &compact), normal(session, &cons), "{expr}");
}

/// Programs over texts, for the comparisons: a user's own match on `MkText`
/// (with nested patterns), a fold, and a copy of a text made of ordinary cons
/// cells.
const HELPERS: &str = r#"
def swapFirst : Text -> List Char
  | MkText (Cons a (Cons b rest)) => Cons b (Cons a rest)
  | t => Text.toList t

def countChars (t : Text) : Nat := Text.fold (c n => Succ n) 0 t

def copy : List Char -> List Char
  | Nil => Nil
  | Cons c cs => Cons c (copy cs)

def copyText : Text -> Text
  | MkText cs => MkText (copy cs)

-- Counts with an accumulator, so a long list needs no frames.
def countFrom (k : Nat) (c : Char) : List Char -> Nat
  | Nil => k
  | Cons d ds => countFrom (if Char.toNat c == Char.toNat d then Succ k else k) c ds

def lengthFrom (k : Nat) : List Char -> Nat
  | Nil => k
  | Cons c cs => lengthFrom (Succ k) cs

def dropChars : Nat -> List Char -> List Char
  | Zero, cs => cs
  | Succ n, Nil => Nil
  | Succ n, Cons c cs => dropChars n cs
"#;

fn session_with_helpers() -> Session {
    let mut session = Session::new();
    load(&mut session, HELPERS);
    session
}

/// Every operation on one text, compared both ways.
fn one_text(session: &mut Session, t: &str) {
    let t = literal(t);
    for expr in [
        t.clone(),
        format!("Text.toList {t}"),
        format!("Text.length {t}"),
        format!("Text.isEmpty {t}"),
        format!("Text.uncons {t}"),
        format!("Text.trim {t}"),
        format!("Text.split ',' {t}"),
        format!("Text.join ',' (Text.split ',' {t})"),
        format!("Text.toNat {t}"),
        format!("Text.fromList (Text.toList {t})"),
        format!("Text.decEq {t} {t}"),
        format!("swapFirst {t}"),
        format!("countChars {t}"),
        format!("copyText {t}"),
    ] {
        same_both_ways(session, &expr);
    }
}

/// Every operation on two texts, compared both ways, and conversion between
/// them, each in either representation.
fn two_texts(session: &mut Session, a: &str, b: &str) {
    let (la, lb) = (literal(a), literal(b));
    for expr in [
        format!("Text.decEq {la} {lb}"),
        format!("Text.compare {la} {lb}"),
        format!("Text.less {la} {lb}"),
        format!("{la} ++ {lb}"),
        format!("Text.join ',' [{la}, {lb}]"),
    ] {
        same_both_ways(session, &expr);
    }
    let (_, ca) = value_of(session, &la, true);
    let (_, cb) = value_of(session, &lb, true);
    let (_, xa) = value_of(session, &la, false);
    let (_, xb) = value_of(session, &lb, false);
    let g = &session.elab.globals;
    let _op = g.budget.operation(session.elab.limits);
    let conv = |x: &Value, y: &Value| value::conv(g, 0, x, y).unwrap();
    let equal = a == b;
    assert_eq!(conv(&ca, &cb), equal, "{la} ~ {lb}, both compact");
    assert_eq!(conv(&ca, &xb), equal, "{la} ~ {lb}, compact ~ constructors");
    assert_eq!(conv(&xa, &cb), equal, "{la} ~ {lb}, constructors ~ compact");
    assert_eq!(conv(&xa, &xb), equal, "{la} ~ {lb}, both constructors");
}

/// Every text of at most `n` characters from `alphabet`.
fn texts(alphabet: &[char], n: usize) -> Vec<String> {
    let mut all = vec![String::new()];
    let mut last = vec![String::new()];
    for _ in 0..n {
        last = last
            .iter()
            .flat_map(|t| {
                alphabet.iter().map(move |c| {
                    let mut t = t.clone();
                    t.push(*c);
                    t
                })
            })
            .collect();
        all.extend(last.iter().cloned());
    }
    all
}

/// A small deterministic generator, so failures can be reproduced.
struct Random(u64);

impl Random {
    fn next(&mut self, below: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) % below as u64) as usize
    }

    fn text(&mut self, alphabet: &[char], max: usize) -> String {
        let n = self.next(max + 1);
        (0..n)
            .map(|_| alphabet[self.next(alphabet.len())])
            .collect()
    }
}

/// Small code points only, so that with the number natives off too (each
/// comparison of two codes counts down), everything is the definitions.
const SMALL: [char; 6] = ['\0', ' ', ',', '0', '9', 'a'];

/// The awkward characters: NUL, the edges of the surrogate gap, U+FFFF,
/// U+10000, U+10FFFF, a combining accent, an emoji, look-alike spaces, a
/// separator and a digit.
const AWKWARD: [char; 13] = [
    '\0',
    '\u{D7FF}',
    '\u{E000}',
    '\u{FFFF}',
    '\u{10000}',
    '\u{10FFFF}',
    '\u{301}',
    '\u{1F600}',
    '\u{A0}',
    '\u{2028}',
    ',',
    '1',
    ' ',
];

/// Tier 1, with every native off: the definitions alone.
#[test]
fn small_texts_mean_the_same_compact_with_natives_off() {
    with_stack(64 * 1024 * 1024, || {
        let mut session = session_with_helpers();
        session.elab.globals.builtins.disable_natives = true;
        for t in texts(&SMALL, 3) {
            one_text(&mut session, &t);
        }
        let short = texts(&SMALL, 2);
        for a in &short {
            for b in &short {
                two_texts(&mut session, a, b);
            }
        }
    });
}

/// Tier 1, on awkward characters (with the number natives on: they compare
/// code points above a million, which counting down would take too long for).
#[test]
fn small_texts_mean_the_same_compact_on_awkward_characters() {
    with_stack(64 * 1024 * 1024, || {
        let mut session = session_with_helpers();
        for t in texts(&AWKWARD, 2) {
            one_text(&mut session, &t);
        }
        let short = texts(&AWKWARD, 1);
        for a in &short {
            for b in &short {
                two_texts(&mut session, a, b);
            }
        }
        let mut random = Random(7);
        for _ in 0..150 {
            let t = random.text(&AWKWARD, 24);
            one_text(&mut session, &t);
        }
        for _ in 0..150 {
            // Mostly a pair that shares a prefix and differs by one edit.
            let a = random.text(&AWKWARD, 24);
            let mut b: Vec<char> = a.chars().collect();
            match random.next(4) {
                0 => b = random.text(&AWKWARD, 24).chars().collect(),
                1 if !b.is_empty() => {
                    let i = random.next(b.len());
                    b[i] = AWKWARD[random.next(AWKWARD.len())];
                }
                2 => b.push(AWKWARD[random.next(AWKWARD.len())]),
                _ => {
                    b.pop();
                }
            }
            two_texts(&mut session, &a, &b.into_iter().collect::<String>());
        }
    });
}

/// Tier 2: texts of thousands of characters, compact against a copy of
/// ordinary cons cells, on the stack-safe machine. Evaluation has the limits
/// of a 2 MiB thread (the default), which stop it if it uses the stack; the
/// thread is larger only for comparing the results (`normal` formats deep
/// terms recursively).
#[test]
fn medium_texts_mean_the_same_compact_as_a_copy() {
    with_stack(256 * 1024 * 1024, medium_texts);
}

fn medium_texts() {
    let mut session = session_with_helpers();
    assert_eq!(session.elab.limits.stack, Limits::default().stack);
    let mut random = Random(11);
    for n in [5_000, 20_000] {
        let text: String = (0..n)
            .map(|i| match random.next(10) {
                0 => ',',
                1 => ' ',
                2 => '\u{1F600}',
                _ => char::from(b'a' + (i % 26) as u8),
            })
            .collect();
        let differs_at_end = {
            let mut t: Vec<char> = text.chars().collect();
            *t.last_mut().unwrap() = '!';
            literal(&t.into_iter().collect::<String>())
        };
        let digits: String = (0..n / 10)
            .map(|i| char::from(b'0' + (i % 10) as u8))
            .collect();
        let t = literal(&text);
        let d = literal(&digits);
        // Each text, compact and copied into cons cells by `copyText`.
        let (_, t_compact) = value_of(&mut session, &t, true);
        let (_, t_copy) = value_of(&mut session, &format!("copyText {t}"), true);
        let (_, d_compact) = value_of(&mut session, &d, true);
        let (_, d_copy) = value_of(&mut session, &format!("copyText {d}"), true);
        let (_, other) = value_of(&mut session, &differs_at_end, true);
        let (_, comma) = value_of(&mut session, "','", true);
        // A prelude function applied to values, so that no long value ends
        // up in a type for the elaborator to finish.
        let call = |session: &Session, f: &str, args: &[&Value]| {
            let g = &session.elab.globals;
            let _op = g.budget.operation(session.elab.limits);
            let mut v = value::eval(g, &[], &Term::Def(def(g, f))).unwrap();
            for arg in args {
                v = value::apply(g, v, (*arg).clone()).unwrap();
            }
            v
        };
        for (f, compact, copied) in [
            ("Text.length", vec![&t_compact], vec![&t_copy]),
            (
                "Text.split",
                vec![&comma, &t_compact],
                vec![&comma, &t_copy],
            ),
            (
                "Text.compare",
                vec![&t_compact, &other],
                vec![&t_copy, &other],
            ),
            ("Text.trim", vec![&t_compact], vec![&t_copy]),
            ("Text.toNat", vec![&d_compact], vec![&d_copy]),
            ("countChars", vec![&t_compact], vec![&t_copy]),
        ] {
            let compact = call(&session, f, &compact);
            let cons = call(&session, f, &copied);
            assert_eq!(
                normal(&session, &compact),
                normal(&session, &cons),
                "{f}, {n}"
            );
        }
        // Equality, by its answer: its complete proof grows with the square of
        // the length (tier 1 compares complete proofs).
        let answer = |session: &Session, a: &Value, b: &Value| {
            let decision = call(session, "Text.decEq", &[a, b]);
            let g = &session.elab.globals;
            let _op = g.budget.operation(session.elab.limits);
            let to_bool = value::eval(g, &[], &Term::Def(def(g, "Decidable.toBool"))).unwrap();
            let to_bool = value::apply_icit(g, to_bool, value::unused(), Icit::Implicit).unwrap();
            normal(session, &value::apply(g, to_bool, decision).unwrap())
        };
        assert_eq!(
            answer(&session, &t_compact, &t_compact),
            answer(&session, &t_copy, &t_compact)
        );
        assert_eq!(
            answer(&session, &t_compact, &t_copy),
            answer(&session, &t_copy, &t_copy)
        );
        assert_eq!(
            answer(&session, &t_compact, &other),
            answer(&session, &t_copy, &other)
        );
        assert!(answer(&session, &t_copy, &t_compact).contains("Ctor(DataId"));
        assert_ne!(
            answer(&session, &t_compact, &t_compact),
            answer(&session, &t_compact, &other)
        );
        let split = call(&session, "Text.split", &[&comma, &t_compact]);
        let split_copy = call(&session, "Text.split", &[&comma, &t_copy]);
        let joined = call(&session, "Text.join", &[&comma, &split]);
        let joined_copy = call(&session, "Text.join", &[&comma, &split_copy]);
        assert_eq!(normal(&session, &joined), normal(&session, &joined_copy));
        assert_eq!(normal(&session, &joined), normal(&session, &t_copy));
    }
}

/// Tier 3: a million characters, in a 2 MiB thread (this one), against
/// expectations computed here. A literal that long used to stop at about
/// 1,800 characters here, and 59,000 in the CLI.
#[test]
fn a_million_character_literal_checks_and_runs() {
    let n = 1_000_000;
    let text: String = (0..n)
        .map(|i| match i % 7 {
            3 => ',',
            5 => '\u{1F600}',
            _ => char::from(b'a' + (i % 26) as u8),
        })
        .collect();
    let commas = text.chars().filter(|c| *c == ',').count();
    let mut session = session_with_helpers();
    let t = literal(&text);
    let source = format!(
        "def big : Text := {t}\n\n\
         test \"commas\" := countFrom 0 ',' (Text.toList big) == {commas}\n\
         test \"length\" := lengthFrom 0 (Text.toList big) == {n}\n\
         test \"last\" := Text.fromList (dropChars {} (Text.toList big)) == \"{}\"\n\
         theorem bigIsBig : countFrom 0 ',' (Text.toList big) = {commas} := rfl\n",
        n - 1,
        text.chars().last().unwrap()
    );
    load(&mut session, &source);
    let results = session.run_tests(&Cache::disabled());
    assert!(
        results.iter().all(|r| r.outcome == Outcome::Passed),
        "{:?}",
        results.iter().map(|r| r.outcome).collect::<Vec<_>>()
    );
}

/// Tier 3: laws on long texts, and a comparison that fails at the very end is
/// a type error, not a resource error. The laws are functions, so that the
/// texts are only computed with when the tests run: in a test written as
/// `textJoin ',' (textSplit ',' t) == t`, the decision's type would have the
/// computed text in it, which the elaborator walks recursively.
#[test]
fn laws_hold_on_long_texts() {
    let n = 50_000;
    let text: String = (0..n).map(|i| if i % 9 == 4 { ',' } else { 'x' }).collect();
    let other: String = text[..n - 1].to_string() + "y";
    let mut session = session_with_helpers();
    let (t, o) = (literal(&text), literal(&other));
    load(
        &mut session,
        &format!(
            "def splitJoin (t : Text) : Bool := Text.join ',' (Text.split ',' t) == t\n\n\
             def lengthsAdd (a : Text) (b : Text) : Bool := Text.length (a ++ b) == Text.length a + Text.length b\n\n\
             def differ (a : Text) (b : Text) : Bool := not (a == b)\n\n\
             test \"split then join\" := splitJoin {t}\n\
             test \"lengths add\" := lengthsAdd {t} {o}\n\
             test \"differ\" := differ {t} {o}\n"
        ),
    );
    let results = session.run_tests(&Cache::disabled());
    assert!(results.iter().all(|r| r.outcome == Outcome::Passed));
    // Two million-character literals that differ in their last character.
    let long: String = "ab".repeat(500_000);
    let differs = long[..999_999].to_string() + "c";
    let (t, o) = (literal(&long), literal(&differs));
    assert_eq!(
        codes(&mut session, &format!("theorem same : {t} = {o} := rfl\n")),
        ["E-REFL"]
    );
    assert_eq!(
        codes(&mut session, &format!("theorem same2 : {t} = {t} := rfl\n")),
        Vec::<&str>::new()
    );
}

/// The kernel checks `Term::Chars` as a `List Char`, and it means its
/// expansion: for a range that starts after its buffer does and ends before
/// it, and for an empty one.
#[test]
fn a_range_means_the_list_of_its_characters() {
    let session = Session::new();
    let g = &session.elab.globals;
    let _op = g.budget.operation(Limits::default());
    let (list, char) = (data(g, "List"), data(g, "Char"));
    let buffer: Rc<[char]> = "xabcdy".chars().collect();
    let expansion = |text: &str| {
        let mut term = Term::Ctor(list, 0, Vec::new());
        for c in text.chars().rev() {
            let c = Term::ctor(
                char,
                0,
                vec![Term::Nat(Rc::new(u32::from(c).into())), Term::Refl],
            );
            term = Term::ctor(list, 1, vec![c, term]);
        }
        term
    };
    let range = |start, end| Term::Chars(Chars::new(buffer.clone(), start, end).unwrap());
    for (start, end, text) in [(1, 5, "abcd"), (0, 6, "xabcdy"), (5, 6, "y"), (3, 3, "")] {
        let (_, ty) = infer_closed(g, &range(start, end), span()).expect("a `List Char`");
        assert_eq!(stitchwort_core::pretty::value(g, &[], &ty), "List Char");
        let compact = value::eval(g, &[], &range(start, end)).unwrap();
        let cons = value::eval(g, &[], &expansion(text)).unwrap();
        assert!(value::conv(g, 0, &compact, &cons).unwrap(), "{text:?}");
        assert!(value::conv(g, 0, &cons, &compact).unwrap(), "{text:?}");
        let shorter = value::eval(g, &[], &expansion(&text[..text.len().saturating_sub(1)]));
        if !text.is_empty() {
            assert!(!value::conv(g, 0, &compact, &shorter.unwrap()).unwrap());
        }
        // `rfl` proves them equal: the kernel's conversion, from a type.
        let proof = Term::Ann(
            Rc::new(Term::Refl),
            Rc::new(Term::Eq(
                None,
                Rc::new(range(start, end)),
                Rc::new(expansion(text)),
            )),
        );
        infer_closed(g, &proof, span()).expect("`rfl` proves it");
    }
    // An empty range is `Nil`, holding no buffer.
    let empty = value::eval(g, &[], &range(3, 3)).unwrap();
    assert!(matches!(empty, Value::Ctor(d, 0, _) if d == list));
    // Ranges are made within their buffers, or not at all.
    assert!(Chars::new(buffer.clone(), 2, 1).is_none());
    assert!(Chars::new(buffer.clone(), 0, 7).is_none());
    assert!(Chars::new(buffer.clone(), 6, 6).is_some());
}

/// Quoting a range keeps its offsets, sharing the buffer, unless the range is
/// short, when it's copied so it doesn't keep a long buffer alive; an empty
/// range is `Nil`.
#[test]
fn quoting_a_suffix_shares_or_copies_it() {
    let mut session = session_with_helpers();
    let text = "abcdefghij";
    let quoted = |session: &mut Session, drop: usize| {
        let (_, v) = value_of(
            session,
            &format!("dropChars {drop} (Text.toList {})", literal(text)),
            true,
        );
        let g = &session.elab.globals;
        let _op = g.budget.operation(Limits::default());
        value::quote(g, 0, &v).unwrap()
    };
    // Six of ten characters: shared, from offset 4.
    let Term::Chars(suffix) = &quoted(&mut session, 4) else {
        panic!("a suffix of a compact list is compact")
    };
    assert_eq!(suffix.as_slice(), ['e', 'f', 'g', 'h', 'i', 'j']);
    assert_eq!(suffix.buffer().len(), 10);
    // Two of ten: copied into a buffer of two.
    let Term::Chars(suffix) = &quoted(&mut session, 8) else {
        panic!("a suffix of a compact list is compact")
    };
    let suffix = suffix.clone();
    assert_eq!(suffix.as_slice(), ['i', 'j']);
    assert_eq!(suffix.buffer().len(), 2);
    // None left: `Nil`.
    let g_list = data(&session.elab.globals, "List");
    assert!(matches!(quoted(&mut session, 10), Term::Ctor(d, 0, _) if d == g_list));
    // The quoted suffixes check, and mean what they say.
    let g = &session.elab.globals;
    let _op = g.budget.operation(Limits::default());
    let suffix = quoted_check(g, &Term::Chars(suffix));
    assert_eq!(suffix, "['i', 'j']");
}

fn quoted_check(g: &Globals, term: &Term) -> String {
    infer_closed(g, term, span()).expect("checks");
    stitchwort_core::pretty::term(g, &[], term)
}

/// Keeping only the last character of a million-character literal doesn't
/// keep the literal's buffer alive once it's quoted.
#[test]
fn a_short_suffix_of_a_long_literal_is_copied() {
    let mut session = session_with_helpers();
    let text = "ab".repeat(500_000);
    let (_, v) = value_of(
        &mut session,
        &format!("dropChars 999999 (Text.toList {})", literal(&text)),
        true,
    );
    let g = &session.elab.globals;
    let _op = g.budget.operation(Limits::default());
    let Value::Chars(range) = &v else {
        panic!("dropping from a compact list leaves a compact list")
    };
    assert_eq!(range.buffer().len(), 1_000_000, "evaluation shares");
    let Term::Chars(quoted) = &value::quote(g, 0, &v).unwrap() else {
        panic!("a compact list quotes to one")
    };
    assert_eq!(quoted.as_slice(), ['b']);
    assert_eq!(quoted.buffer().len(), 1, "quotation copies a short range");
}

/// `Cons (MkChar 97 h) Nil`, with `h` a proof variable, isn't `"a"`'s list:
/// without definitional proof irrelevance, `h` isn't `rfl`. The kernel
/// refuses it as it would refuse the expansion; with `rfl` for `h`, it
/// accepts.
#[test]
fn a_proof_variable_is_not_rfl() {
    let session = Session::new();
    let g = &session.elab.globals;
    let _op = g.budget.operation(Limits::default());
    let (list, char, bool) = (data(g, "List"), data(g, "Char"), data(g, "Bool"));
    let is_scalar = def(g, "Char.isScalar");
    let a = Term::Chars(Chars::whole(Rc::from(['a'])));
    let a_expanded = |proof: Term| {
        Term::ctor(
            list,
            1,
            vec![
                Term::ctor(
                    char,
                    0,
                    vec![Term::Nat(Rc::new(BigUint::from(97u32))), proof],
                ),
                Term::Ctor(list, 0, Vec::new()),
            ],
        )
    };
    // (h : isScalar 97 = True) -> chars = Cons (MkChar 97 proof) Nil
    let claim = |chars: Term, proof: Term| {
        let h_ty = Term::Eq(
            Some(Rc::new(Term::Data(bool, Vec::new()))),
            Rc::new(Term::app(
                Term::Def(is_scalar),
                Term::Nat(Rc::new(BigUint::from(97u32))),
            )),
            Rc::new(Term::Ctor(bool, 1, Vec::new())),
        );
        let eq = Term::Eq(
            Some(Rc::new(Term::data(
                list,
                vec![Term::Data(char, Vec::new())],
            ))),
            Rc::new(chars),
            Rc::new(a_expanded(proof)),
        );
        Term::Ann(
            Rc::new(Term::Lam("h".into(), Icit::Explicit, Rc::new(Term::Refl))),
            Rc::new(Term::Pi(
                "h".into(),
                Icit::Explicit,
                Rc::new(h_ty),
                Rc::new(eq),
            )),
        )
    };
    let code = |t: Term| infer_closed(g, &t, span()).map(|_| ()).map_err(|d| d.code);
    assert_eq!(code(claim(a.clone(), Term::Var(0))), Err("E-REFL"));
    assert_eq!(
        code(claim(a_expanded(Term::Refl), Term::Var(0))),
        Err("E-REFL")
    );
    assert_eq!(code(claim(a.clone(), Term::Refl)), Ok(()));
}

/// The same, written in the language: the elaborator's unifier tells the two
/// apart as the kernel does.
#[test]
fn proofs_in_characters_are_compared() {
    let mut session = Session::new();
    assert_eq!(
        codes(
            &mut session,
            "theorem bad (h : Char.isScalar 97 = True) : Text.toList \"a\" = Cons (MkChar 97 h) Nil := rfl\n"
        ),
        ["E-REFL"]
    );
    assert_eq!(
        codes(
            &mut session,
            "theorem good : Text.toList \"a\" = Cons (MkChar 97 rfl) Nil := rfl\n"
        ),
        Vec::<&str>::new()
    );
}

/// Unification against a literal solves metavariables as it would against
/// the literal's constructors: `Cons ?c ?tail ~ "ab"` solves both,
/// consistently, and a character metavariable solved before or after its
/// proof's gives the same result.
#[test]
fn unification_solves_through_a_compact_list() {
    for compact in [true, false] {
        unification_solves(compact);
    }
}

/// [`unification_solves_through_a_compact_list`], with literals compact or
/// as constructors: the same programs check, and fail, either way.
fn unification_solves(compact: bool) {
    let mut session = Session::new();
    session.elab.globals.builtins.disable_compact_text = !compact;
    load(
        &mut session,
        r#"
def headOf [c : Char] [t : List Char] (p : Cons c t = Text.toList "ab") : Char := c

def restOf [c : Char] [t : List Char] (p : Cons c t = Text.toList "ab") : List Char := t

theorem heads : headOf rfl = 'a' := rfl

theorem tails : restOf rfl = ['b'] := rfl

theorem tailsCompact : restOf rfl = Text.toList "b" := rfl

def codeOf [n : Nat] [p : Char.isScalar n = True] (e : Cons (MkChar n p) Nil = Text.toList "a") : Nat := n

theorem codes : codeOf rfl = 97 := rfl

def codeAt (n : Nat) [p : Char.isScalar n = True] (e : Cons (MkChar n p) Nil = Text.toList "a") : Nat := n

theorem codesKnown : codeAt 97 rfl = 97 := rfl
"#,
    );
    // The solution for `?t` is the range after `a`.
    let expr = session.parse_expression("<t>", "restOf rfl").unwrap();
    let (term, _) = session.elab.infer_expr(&expr).unwrap();
    assert_eq!(
        term.subterms()
            .any(|(t, _)| matches!(t, Term::Chars(c) if c.as_slice() == ['b'])),
        compact,
        "{term:?}"
    );
    // With a different code known first, there's no solution.
    assert_eq!(
        codes(&mut session, "theorem no : codeAt 98 rfl = 98 := rfl\n"),
        ["E-REFL"]
    );
    assert_eq!(
        codes(&mut session, "theorem no2 : headOf rfl = 'b' := rfl\n"),
        ["E-REFL"]
    );
}

/// A recursive call is only structurally smaller when its argument came out
/// of a match: a compact list, however it was made, is never smaller than a
/// parameter.
#[test]
fn a_compact_list_is_never_a_smaller_argument() {
    let mut session = Session::new();
    let g = &mut session.elab.globals;
    let (list, char, nat) = (data(g, "List"), data(g, "Char"), data(g, "Nat"));
    let list_char = Term::data(list, vec![Term::Data(char, Vec::new())]);
    let ty = Term::Pi(
        "cs".into(),
        Icit::Explicit,
        Rc::new(list_char),
        Rc::new(Term::Data(nat, Vec::new())),
    );
    // Kernel declarations outside an operation have no limits.
    let define = |g: &mut Globals, name: &str, recurse: Term| {
        let id = declare_def(g, &name.into(), &ty, false, false, span()).unwrap();
        // cs => case cs of Nil -> 0 | Cons c rest -> self <recurse>
        let body = Term::Lam(
            "cs".into(),
            Icit::Explicit,
            Rc::new(Term::Case(
                0,
                list,
                vec![
                    Branch {
                        names: vec![],
                        body: Some(Rc::new(Term::Nat(Rc::new(BigUint::from(0u32))))),
                    },
                    Branch {
                        names: vec!["c".into(), "rest".into()],
                        body: Some(Rc::new(Term::app(Term::Def(id), recurse))),
                    },
                ]
                .into(),
            )),
        );
        define_def(g, id, &body).map_err(|d| d.code)
    };
    assert_eq!(define(g, "byTail", Term::Var(0)), Ok(()));
    let abc = Term::Chars(Chars::whole("abc".chars().collect()));
    assert_eq!(define(g, "byLiteral", abc), Err("E-TERMINATION"));
    // A suffix of a buffer, too.
    let suffix = Term::Chars(Chars::new("abc".chars().collect(), 1, 3).unwrap());
    assert_eq!(define(g, "bySuffix", suffix), Err("E-TERMINATION"));
}

/// A compact list hashes by its characters (and `List` and `Char`), not its
/// buffer or offsets: the same characters from another buffer hash the same.
/// It differs from the same characters as constructors, as `3` and
/// `Succ 2` do, which only costs a cache miss.
#[test]
fn hashes_cover_the_characters_not_the_buffer() {
    let mut session = Session::new();
    load(&mut session, "def plain : Text := \"abc\"\n");
    let g = &mut session.elab.globals;
    let text = data(g, "Text");
    let declare = |g: &mut Globals, name: &str, chars: Term| {
        let ty = Term::Data(text, Vec::new());
        let id = declare_def(g, &name.into(), &ty, false, false, span()).unwrap();
        define_def(g, id, &Term::ctor(text, 0, vec![chars])).unwrap();
        def_hash(g, id).unwrap().unwrap()
    };
    let in_middle = declare(
        g,
        "inMiddle",
        Term::Chars(Chars::new("zzabczz".chars().collect(), 2, 5).unwrap()),
    );
    let other = declare(
        g,
        "other",
        Term::Chars(Chars::whole("abd".chars().collect())),
    );
    let _op = g.budget.operation(Limits::default());
    let plain = def_hash(g, def(g, "plain")).unwrap().unwrap();
    assert_eq!(plain, in_middle);
    assert_ne!(plain, other);
    let mut cons = Session::new();
    cons.elab.globals.builtins.disable_compact_text = true;
    load(&mut cons, "def plain : Text := \"abc\"\n");
    let g = &cons.elab.globals;
    let _op = g.budget.operation(Limits::default());
    assert_ne!(plain, def_hash(g, def(g, "plain")).unwrap().unwrap());
}

/// Printing shows a compact list as the literal it is.
#[test]
fn compact_lists_print_as_literals() {
    let mut session = Session::new();
    let show = |session: &mut Session, expr: &str| {
        let expr = session.parse_expression("<t>", expr).unwrap();
        session.elab.eval_expr(&expr).unwrap().0
    };
    assert_eq!(
        show(&mut session, "\"a\\u{1F600}\\n\""),
        "\"a\\u{1F600}\\n\""
    );
    assert_eq!(show(&mut session, "Text.toList \"ab\""), "['a', 'b']");
    assert_eq!(
        show(&mut session, "Cons 'x' (Text.toList \"ab\")"),
        "['x', 'a', 'b']"
    );
    assert_eq!(show(&mut session, "\"x\" ++ \"ab\""), "\"xab\"");
    assert_eq!(show(&mut session, "\"\""), "\"\"");
}

/// DESIGN.md §13's must-reject examples next to compact literals, each with
/// an accepted neighbour.
#[test]
fn must_reject_examples_still_are() {
    for (source, expected) in [
        ("theorem t : \"a\" = \"b\" := rfl\n", vec!["E-REFL"]),
        ("theorem t : \"ab\" = \"a\" ++ \"b\" := rfl\n", vec![]),
        (
            "theorem t : Text.less \"\\u{10000}\" \"\\u{E000}\" = True := rfl\n",
            vec!["E-REFL"],
        ),
        (
            "theorem t : Text.less \"\\u{10000}\" \"\\u{E000}\" = False := rfl\n",
            vec![],
        ),
        (
            "def bad : List Char := Cons (MkChar 55296 rfl) (Text.toList \"ab\")\n",
            vec!["E-REFL"],
        ),
        (
            "def bad : List Char := Cons (MkChar 57343 rfl) (Text.toList \"ab\")\n",
            vec!["E-REFL"],
        ),
        (
            "def bad : List Char := Cons (MkChar 1114112 rfl) (Text.toList \"ab\")\n",
            vec!["E-REFL"],
        ),
        (
            "def bad : List Char := Cons (MkChar 4294967393 rfl) (Text.toList \"ab\")\n",
            vec!["E-REFL"],
        ),
        (
            "def bad : List Char := Cons (MkChar 18446744073709551713 rfl) (Text.toList \"ab\")\n",
            vec!["E-REFL"],
        ),
        (
            "def good : List Char := Cons (MkChar 1114111 rfl) (Text.toList \"ab\")\n",
            vec![],
        ),
    ] {
        assert_eq!(codes(&mut Session::new(), source), expected, "{source}");
    }
}

/// `isScalar` is true of exactly the code points a Rust `char` can hold, up
/// to U+10FFFF and a little beyond: the forward property the expansion's
/// `rfl` relies on. (The hash binding is what fixes it on every number.)
#[test]
fn is_scalar_agrees_with_rust_on_every_code_point() {
    let session = Session::new();
    let g = &session.elab.globals;
    let is_scalar = def(g, "Char.isScalar");
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    for code in 0..0x11_0100u32 {
        let term = Term::app(Term::Def(is_scalar), Term::Nat(Rc::new(code.into())));
        let Value::Ctor(_, c, _) = value::eval(g, &[], &term).unwrap() else {
            panic!("`Char.isScalar {code}` is a `Bool`")
        };
        assert_eq!(c == 1, char::from_u32(code).is_some(), "U+{code:X}");
    }
}

/// The compact representation is bound to the prelude's `List` and `Char` by
/// content hash. If this fails, the prelude changed one of them (or
/// `isScalar`, or something it uses): check that every rule in
/// `stitchwort_core::chars` still holds for the new declarations, then update
/// `LIST_HASH` and `CHAR_HASH` there to the hashes printed.
#[test]
fn compact_text_is_bound_to_the_prelude() {
    let session = Session::new();
    let g = &session.elab.globals;
    let binding = chars::binding(g, data(g, "List"), data(g, "Char"));
    assert!(
        binding.bound,
        "`List` or `Char` changed: their hashes are now {:?} and {:?}",
        binding.list_hash, binding.char_hash
    );
    assert!(g.builtins.text.is_some());
}

/// A prelude whose `isScalar` is changed, keeping its type, isn't the one the
/// compact representation was written for. Then literals are constructors,
/// as before compact text, and the kernel refuses a compact list.
#[test]
fn a_changed_builtin_isnt_bound() {
    let original = "def Char.isScalar (n : Nat) : Bool := if Nat.leq 55296 n then (if Nat.leq n 57343 then False else Nat.leq n 1114111) else True";
    assert!(stitchwort_elab::PRELUDE.contains(original));
    let changed = stitchwort_elab::PRELUDE.replace(
        original,
        "def Char.isScalar (n : Nat) : Bool := if Nat.leq 55296 n then (if Nat.leq n 57343 then False else Nat.leq n 1114112) else True",
    );
    let mut session = Session {
        sources: SourceMap::new(),
        elab: stitchwort_elab::Elaborator::new(),
        warnings: Vec::new(),
    };
    session.elab.loading_prelude = true;
    load(&mut session, &changed);
    session.elab.loading_prelude = false;
    let g = &session.elab.globals;
    assert!(g.builtins.text.is_none());
    assert!(!chars::binding(g, data(g, "List"), data(g, "Char")).bound);
    // Literals still work, as constructors.
    load(
        &mut session,
        "test \"length\" := Text.length \"abc\" == 3\ntheorem t : Text.toList \"ab\" = ['a', 'b'] := rfl\n",
    );
    let expr = session.parse_expression("<t>", "\"abc\"").unwrap();
    let (term, _) = session.elab.infer_expr(&expr).unwrap();
    assert!(!has_chars(&term));
    let results = session.run_tests(&Cache::disabled());
    assert_eq!(results[0].outcome, Outcome::Passed);
    // And the kernel refuses a compact list.
    let g = &session.elab.globals;
    let _op = g.budget.operation(Limits::default());
    let abc = Term::Chars(Chars::whole("abc".chars().collect()));
    assert_eq!(
        infer_closed(g, &abc, span())
            .map(|_| ())
            .map_err(|d| d.code),
        Err("E-MALFORMED")
    );
}
