//! Checking past a syntax error (docs/proposals/syntax-error-recovery.md,
//! stage S1): a definition the parser recovered in is checked for the errors
//! of its other lines, reports nothing about the gaps the error left, and is
//! never admitted with a body.

use stitchwort_driver::driver::Session;
use stitchwort_syntax::ast::Decl;
use stitchwort_syntax::{DEFAULT_STACK, SourceMap, lex, parse_module_recovering};

/// The codes of the errors checking `source` reports, in order.
fn codes(source: &str) -> Vec<&'static str> {
    let mut session = Session::new();
    match session.load("test.sw", source) {
        Ok(_) => Vec::new(),
        Err(errors) => errors.iter().map(|d| d.code).collect(),
    }
}

#[test]
fn a_type_error_after_a_line_that_ran_out_is_reported() {
    let source = "\
def f (n: Nat): Nat :=
  let a := n +
  let bad: Nat := \"text\"
  a + bad

def usesF: Nat := f 1 + 1
";
    assert_eq!(codes(source), ["E-PARSE", "E-TYPE-MISMATCH"]);
}

/// The crash probe (§7): gaps whose types are unknown, or that leave a
/// type unknown, then arithmetic on the names they bind. Nothing ill typed
/// reaches the evaluator, so no panic, and nothing but the syntax error is
/// reported.
#[test]
fn arithmetic_on_what_a_gap_binds_reports_nothing_more() {
    for source in [
        // A gap whose type nothing says, applied to a list.
        "def m (xs: List Nat): Nat :=\n  let a := xs |>\n  let b := a + 1\n  b * 2\n",
        // A gap that is a type, then a value of that type in arithmetic.
        "def m (n: Nat): Nat :=\n  let t: Type :=\n  let a: t := n\n  let b := a + 1\n  b * 2\n",
        // An expression `let` on the line after a line-final `:=` is the
        // value, not the next statement: no error at all.
        "def m (n: Nat): Nat :=\n  let t :=\n  let x := n; x + 1\n  t * 2\n",
        // A gap in a list, whose sum is then taken.
        "def m (n: Nat): Nat :=\n  let ys := [n] ++\n  ys.length + ys.sum * n\n",
        // A gap compared in a proof's statement position.
        "theorem t (n: Nat): n + 0 = n :=\n  let k := n *\n  rfl\n",
    ] {
        let expected: &[&str] = if source.contains(';') {
            &[]
        } else {
            &["E-PARSE"]
        };
        assert_eq!(codes(source), expected, "{source}");
    }
}

/// Correct programs to break, one line at a time.
const CORPUS: &[&str] = &[
    "\
def double (n: Nat): Nat := n + n

def sumTo: Nat -> Nat
  | 0 => 0
  | n + 1 => n + 1 + sumTo n

theorem doubleTwo: double 2 = 4 := rfl

def usesBoth (n: Nat): Nat :=
  let a := double n
  let b := sumTo (a + 1)
  a * b + n

theorem addZero (n: Nat): n + 0 = n := rfl
",
    "\
type Shape =
  | Circle (r: Nat)
  | Square (side: Nat)

def area (s: Shape): Nat :=
  match s with
    | Circle r => 3 * r * r
    | Square side => side * side

def total (shapes: List Shape): Nat :=
  shapes.map area |> .sum

def biggest (shapes: List Shape): Nat :=
  let areas := shapes.map area
  areas.foldl (best a => if a > best then a else best) 0

test \"areas\" := total [Circle 1, Square 2] == 7
",
];

/// The invariant of §4.1, fuzzed: breaks of the corpus's lines (a line's
/// last token dropped, a stray `)` put before its middle token, its middle
/// token dropped) that are syntax errors fail the check, and leave the
/// declaration each is in without a kernel term, whatever the recovery
/// made of it. Its statement may stand in for it, as for any declaration
/// with an error: a constant with no body, so what hash it has is never
/// one of a body.
#[test]
fn a_declaration_with_a_syntax_error_has_no_kernel_term_or_hash() {
    let mut broken = 0;
    for text in CORPUS {
        // Every fifth break: each check takes a second or so, and `dev
        // breaks` runs them all.
        for edited in breaks(text).into_iter().step_by(5) {
            let file = SourceMap::new().add("test.sw", edited.as_str());
            let (module, errors) = parse_module_recovering(file, &edited, DEFAULT_STACK);
            if errors.is_empty() {
                continue;
            }
            broken += 1;
            let mut names: Vec<String> = module
                .decls
                .iter()
                .filter_map(|d| match d {
                    Decl::Signature {
                        name,
                        syntax_error: Some(_),
                        ..
                    } => Some(name.text.clone()),
                    _ => None,
                })
                .collect();
            names.extend(module.failed.iter().map(|f| f.name.text.clone()));
            let mut session = Session::new();
            let loaded = session.load("test.sw", &edited);
            assert!(loaded.is_err(), "a syntax error passed:\n{edited}");
            let g = session.elab.ev();
            for def in g.env.defs() {
                let path = def.path().to_string();
                let own = path
                    .rsplit_once('.')
                    .map_or(path.as_str(), |(_, last)| last);
                let made = names
                    .iter()
                    .any(|n| own == n || path.contains(&format!("{n}.")));
                assert!(
                    !(made && path.starts_with("Main.") && def.body().is_some()),
                    "`{path}` has a syntax error but has a kernel term:\n{edited}"
                );
            }
        }
    }
    assert!(broken > 10, "only {broken} breaks were syntax errors");
}

/// Each line of `text` broken three ways, each on its own.
fn breaks(text: &str) -> Vec<String> {
    let tokens = lex(SourceMap::new().add("test.sw", text), text).expect("the corpus lexes");
    let mut lines: Vec<Vec<(usize, usize)>> = Vec::new();
    let mut last_line = None;
    for token in &tokens {
        let (start, end) = (token.span.start as usize, token.span.end as usize);
        let line = text[..start].matches('\n').count();
        if last_line != Some(line) {
            lines.push(Vec::new());
            last_line = Some(line);
        }
        lines.last_mut().expect("pushed").push((start, end));
    }
    let mut out = Vec::new();
    for line in lines {
        let (start, end) = *line.last().expect("a line has a token");
        out.push(format!("{}{}", &text[..start], &text[end..]));
        let (middle, middle_end) = line[line.len() / 2];
        out.push(format!("{}) {}", &text[..middle], &text[middle..]));
        out.push(format!("{}{}", &text[..middle], &text[middle_end..]));
    }
    out
}
