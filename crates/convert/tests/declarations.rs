//! The declaration syntax (docs/proposals/declaration-syntax.md): each form
//! must parse to the tree its old-syntax equivalent parsed to (read by the
//! converter's copy of the old parser), the layout rules of section 2.10
//! must hold, and mistakes must be reported as the spec says. (Here rather
//! than in `crates/syntax`, because only the converter still reads the old
//! syntax.)

use stitchwort_convert::assert_equivalent;
use stitchwort_syntax::equivalence::parse_shape;
use stitchwort_syntax::{SourceMap, parse_module};

/// The error text of `src` in the new syntax; panics if it parses.
#[track_caller]
fn new_err(src: &str) -> String {
    match parse_shape(src) {
        Ok(_) => panic!("expected a parse error, but this parsed:\n{src}"),
        Err(e) => e,
    }
}

/// Asserts `src` fails in the new syntax with `code` and a message containing `part`.
#[track_caller]
fn assert_err(src: &str, code: &str, part: &str) {
    let e = new_err(src);
    assert!(
        e.contains(code) && e.contains(part),
        "expected {code} and {part:?}, got:\n{e}\nfor:\n{src}"
    );
}

// ---------------------------------------------------------------------
// a. Equivalence with the old syntax

// A one-line definition with named parameters.
#[test]
fn one_line_def() {
    assert_equivalent(
        "def add (x : Nat) (y : Nat) : Nat := x + y\n",
        "add : (x : Nat) -> (y : Nat) -> Nat\nadd x y = x + y\n",
    );
}

// A value with no parameters.
#[test]
fn value() {
    assert_equivalent(
        "def example : List Text := [\"987654321111111\", \"811111111111119\"]\n",
        "example : List Text\nexample = [\"987654321111111\", \"811111111111119\"]\n",
    );
}

// Arms over the argument after the colon.
#[test]
fn arms_length() {
    assert_equivalent(
        "def length : List a -> Nat\n  | Nil       => 0\n  | Cons x xs => Succ (length xs)\n",
        "length : List a -> Nat\nlength Nil = 0\nlength (Cons x xs) = Succ (length xs)\n",
    );
}

// A named parameter plus arms (section 0's `total`).
#[test]
fn named_param_and_arms() {
    assert_equivalent(
        "def total (k : Nat) : List Text -> Nat\n  | Nil       => 0\n  | Cons l ls => joltage k l + total k ls\n",
        "total : (k : Nat) -> List Text -> Nat\ntotal k Nil = 0\ntotal k (Cons l ls) = joltage k l + total k ls\n",
    );
}

// A theorem proved by arms, with a lambda.
#[test]
fn theorem_with_arms() {
    assert_equivalent(
        "theorem appendNil : (xs : List a) -> List.append xs Nil = xs\n  | Nil       => rfl\n  | Cons x xs => Eq.cong (\\ys => Cons x ys) (appendNil xs)\n",
        "theorem appendNil : (xs : List a) -> List.append xs Nil = xs\nappendNil Nil = rfl\nappendNil (Cons x xs) = Eq.cong (\\ys -> Cons x ys) (appendNil xs)\n",
    );
}

// The `()` header lowers to a dependent `() ->` and the pattern `_`.
#[test]
fn unit_header() {
    assert_equivalent(
        "def main () : {IO, Partial} () := report (solve (IO.readAllLines ()))\n",
        "main : () -> {IO, Partial} ()\nmain _ = report (solve (IO.readAllLines ()))\n",
    );
}

// `export def` is `export` before the signature.
#[test]
fn export_def() {
    assert_equivalent(
        "export def identityNat (n : Nat) : Nat := n\n",
        "export identityNat : (n : Nat) -> Nat\nidentityNat n = n\n",
    );
}

// `export theorem`.
#[test]
fn export_theorem() {
    assert_equivalent(
        "export theorem triv (n : Nat) : n = n := rfl\n",
        "export theorem triv : (n : Nat) -> n = n\ntriv n = rfl\n",
    );
}

// `test "n" := e`.
#[test]
fn test_decl() {
    assert_equivalent(
        "test \"parse\" := parseBank \"102\" == [1, 0, 2]\n",
        "test \"parse\" = parseBank \"102\" == [1, 0, 2]\n",
    );
}

// Implicit and auto binders in the header take no pattern.
#[test]
fn implicit_and_auto_binders() {
    assert_equivalent(
        "def cong (f : a -> b) [x y : a] (p : x = y) : f x = f y := q f p\n",
        "cong : (f : a -> b) -> [x y : a] -> (p : x = y) -> f x = f y\ncong f p = q f p\n",
    );
    assert_equivalent(
        "def g (x : a) [auto h : P a] : Nat := 0\n",
        "g : (x : a) -> [auto h : P a] -> Nat\ng x = 0\n",
    );
}

// `(x y : A)` is one binder with two names.
#[test]
fn two_names_one_binder() {
    assert_equivalent(
        "def plus (x y : Nat) : Nat := x + y\n",
        "plus : (x y : Nat) -> Nat\nplus x y = x + y\n",
    );
}

// A qualified definition name.
#[test]
fn qualified_name() {
    assert_equivalent(
        "def List.sum (xs : List Nat) : Nat := List.foldr (\\a b => a + b) 0 xs\n",
        "List.sum : (xs : List Nat) -> Nat\nList.sum xs = List.foldr (\\a b -> a + b) 0 xs\n",
    );
}

// `let x := e`, `let (q, r) := e` and `let x : T := e` in a block body.
#[test]
fn let_forms() {
    assert_equivalent(
        "def f (n : Nat) : Nat :=\n  let x := n + 1\n  let (q, r) := (n / 7, n % 7)\n  let y : Nat := x + q\n  y + r\n",
        "f : (n : Nat) -> Nat\nf n =\n  let x = n + 1\n  let (q, r) = (n / 7, n % 7)\n  let y : Nat = x + q\n  y + r\n",
    );
}

// Pattern lambdas.
#[test]
fn pattern_lambda() {
    assert_equivalent(
        "def f : (Nat, Nat) -> Nat := \\(a, b) => a + b\n",
        "f : (Nat, Nat) -> Nat\nf = \\(a, b) -> a + b\n",
    );
}

// `match` with `=>` and several scrutinees.
#[test]
fn match_arrows() {
    assert_equivalent(
        "def f (xs : List Nat) (ys : List Nat) : Nat :=\n  match xs, ys with\n    | Nil, _ => 0\n    | Cons x _, Nil => x\n    | Cons x _, Cons y _ => x + y\n",
        "f : (xs : List Nat) -> (ys : List Nat) -> Nat\nf xs ys =\n  match xs, ys with\n    | Nil, _ -> 0\n    | Cons x _, Nil -> x\n    | Cons x _, Cons y _ -> x + y\n",
    );
}

// `handle` with a return clause and operation clauses.
#[test]
fn handle_clauses() {
    assert_equivalent(
        "def allResults (prog : () -> {Choose | e} a) : {e} List a :=\n  handle prog () with\n    | return x => [x]\n    | choose u, k => List.append (k True) (k False)\n",
        "allResults : (prog : () -> {Choose | e} a) -> {e} List a\nallResults prog =\n  handle prog () with\n    | return x -> [x]\n    | choose u => k -> List.append (k True) (k False)\n",
    );
}

// An absurd arm has no body.
#[test]
fn absurd_arm() {
    assert_equivalent(
        "def absurd : Void -> a\n  | ()\n",
        "absurd : Void -> a\nabsurd ()\n",
    );
}

// A multi-pattern arm table (section 2.4's `pick`).
#[test]
fn pick_table() {
    assert_equivalent(
        "def pick : Nat -> List Nat -> Nat -> List Nat -> (Nat, List Nat)\n  | Zero,   ds,          d, after => (d, after)\n  | Succ w, Nil,         d, after => (d, after)\n  | Succ w, Cons x rest, d, after =>\n    if Nat.leq (d + 1) x then pick w rest x rest else pick w rest d after\n",
        "pick : Nat -> List Nat -> Nat -> List Nat -> (Nat, List Nat)\npick Zero ds d after = (d, after)\npick (Succ w) Nil d after = (d, after)\npick (Succ w) (Cons x rest) d after =\n  if Nat.leq (d + 1) x then pick w rest x rest else pick w rest d after\n",
    );
}

// Section 2.3's auto-binding table: each header lowers to the old complete type.
#[test]
fn auto_binding_table() {
    // the first parameter's type
    assert_equivalent(
        "def f (x : a) (xs : List a) : Nat := 0\n",
        "f : (x : a) -> (xs : List a) -> Nat\nf x xs = 0\n",
    );
    // only a later parameter's type
    assert_equivalent(
        "def f (n : Nat) (xs : List a) : Nat := 0\n",
        "f : (n : Nat) -> (xs : List a) -> Nat\nf n xs = 0\n",
    );
    // only the result type
    assert_equivalent(
        "def f (n : Nat) : List a := Nil\n",
        "f : (n : Nat) -> List a\nf n = Nil\n",
    );
    // an auto binder
    assert_equivalent(
        "def f (x : a) [auto h : P a] : Nat := 0\n",
        "f : (x : a) -> [auto h : P a] -> Nat\nf x = 0\n",
    );
    // under another dependent binder
    assert_equivalent(
        "def f (x : a) (p : P a x) : R a x p := w\n",
        "f : (x : a) -> (p : P a x) -> R a x p\nf x p = w\n",
    );
    // after the colon, with arms
    assert_equivalent(
        "def f (k : Nat) : List a -> Nat\n  | Nil => k\n  | Cons x xs => k\n",
        "f : (k : Nat) -> List a -> Nat\nf k Nil = k\nf k (Cons x xs) = k\n",
    );
}

// ---------------------------------------------------------------------
// b. Layout goldens (section 2.10)

// A header over several lines, then arms.
#[test]
fn header_over_several_lines() {
    assert_equivalent(
        "def f :\n  A ->\n  B\n  | p => q\n  | r => s\n",
        "f : A -> B\nf p = q\nf r = s\n",
    );
}

// A type ending in an open row, then arms (the `|` inside braces belongs to the row).
#[test]
fn open_row_then_arms() {
    assert_equivalent(
        "def f : A -> {State s | e} B\n  | p => q\n  | r => s2\n",
        "f : A -> {State s | e} B\nf p = q\nf r = s2\n",
    );
}

// An arm whose body is a `match` with further-indented `|`s, then another arm.
#[test]
fn match_inside_arm() {
    assert_equivalent(
        "def f : A -> B -> C\n  | p, q =>\n    match q with\n      | x => 1\n      | y => 2\n  | r, s => 3\n",
        "f : A -> B -> C\nf p q =\n  match q with\n    | x -> 1\n    | y -> 2\nf r s = 3\n",
    );
}

// The same with `handle`.
#[test]
fn handle_inside_arm() {
    assert_equivalent(
        "def f : A -> B\n  | p =>\n    handle p () with\n      | return x => x\n      | op y, k => k y\n  | r => s\n",
        "f : A -> B\nf p =\n  handle p () with\n    | return x -> x\n    | op y => k -> k y\nf r = s\n",
    );
}

// A `match` inside a handler clause inside an arm: three levels of `|`.
#[test]
fn three_levels_of_bars() {
    assert_equivalent(
        "def f : A -> B\n  | p =>\n    handle p () with\n      | return x => x\n      | op y, k =>\n        match y with\n          | a => k a\n          | b => k b\n  | r => s\n",
        "f : A -> B\nf p =\n  handle p () with\n    | return x -> x\n    | op y => k ->\n      match y with\n        | a -> k a\n        | b -> k b\nf r = s\n",
    );
}

// A nested `match` whose `|`s are at the arms' column: they read as the
// definition's arms, so the nested `match` has no alternatives.
#[test]
fn nested_match_at_arm_column() {
    let e = new_err("def f : A -> B -> C\n  | p, q =>\n    match q with\n  | x => 1\n  | y => 2\n");
    insta::assert_snapshot!("nested_match_at_arm_column", e);
}

// A `|` between column 0 and the arms' column.
#[test]
fn bar_between_d_and_a() {
    assert_err(
        "def f : A -> B\n    | p => q\n  | r => s\n",
        "E-PARSE",
        "doesn't line up",
    );
}

// The first arm on the header's line.
#[test]
fn first_arm_on_header_line() {
    assert_err(
        "def f : A -> B | p => q\n",
        "E-PARSE",
        "arms start on their own lines",
    );
}

// A token at the arms' column that isn't `|`.
#[test]
fn token_at_arm_column_not_bar() {
    let e = new_err("def f : A -> B\n  | p => q\n  r => s\n");
    assert!(e.contains("expected `|`"), "{e}");
}

// Comments and blank lines are invisible to layout.
#[test]
fn comments_and_blank_lines() {
    assert_equivalent(
        "def f : A -> B\n-- a comment at column 0\n  | p => q\n  -- a comment at column A\n\n  | r => -- at end of line\n    s\n\n    t\n-- another\n  | u => v\n",
        "f : A -> B\nf p = q\nf r =\n  s\n  t\nf u = v\n",
    );
}

// An arm body that is a multi-line block of `print` lines (section 2.7).
#[test]
fn multi_line_block_arm() {
    assert_equivalent(
        "def report : (Nat, Nat) -> {IO} ()\n  | (a, b) =>\n    print (\"Part 1: \" ++ Nat.toText a)\n    print (\"Part 2: \" ++ Nat.toText b)\n",
        "report : (Nat, Nat) -> {IO} ()\nreport (a, b) =\n  print (\"Part 1: \" ++ Nat.toText a)\n  print (\"Part 2: \" ++ Nat.toText b)\n",
    );
}

// ---------------------------------------------------------------------
// c. `where` is not implemented

const AFTER_BODY: &str = "`where` after a definition isn't supported yet";

// `where` after a `:=` body on the same line.
#[test]
fn where_same_line_after_body() {
    assert_err(
        "def f (x : Nat) : Nat := g x where\n  def g (y : Nat) : Nat := y\n",
        "E-PARSE",
        AFTER_BODY,
    );
}

// `where` after a `:=` body on the next line.
#[test]
fn where_next_line_after_body() {
    assert_err(
        "def f (x : Nat) : Nat := g x\n  where\n    def g (y : Nat) : Nat := y\n",
        "E-PARSE",
        AFTER_BODY,
    );
}

// `where` after the last arm.
#[test]
fn where_after_last_arm() {
    assert_err(
        "def f : Nat -> Nat\n  | Zero => 0\n  | Succ n => g n\n  where\n    def g (y : Nat) : Nat := y\n",
        "E-PARSE",
        AFTER_BODY,
    );
}

// `where` between arms.
#[test]
fn where_between_arms() {
    let e = new_err(
        "def f : Nat -> Nat\n  | Zero => 0\n  where\n    def g (y : Nat) : Nat := y\n  | Succ n => 1\n",
    );
    assert!(e.contains("E-PARSE"), "{e}");
}

// `where` inside an arm body.
#[test]
fn where_inside_arm() {
    let e = new_err("def f : Nat -> Nat\n  | Zero => g\n      where\n        def g : Nat := 0\n");
    assert!(e.contains("E-PARSE"), "{e}");
}

// `where` at column 0.
#[test]
fn where_at_column_zero() {
    let e = new_err("def f : Nat := 0\nwhere\n  def g : Nat := 0\n");
    assert!(e.contains("E-PARSE"), "{e}");
}

// ---------------------------------------------------------------------
// d. Errors

// `=` instead of `:=` after a header.
#[test]
fn equals_after_header() {
    assert_err("def f (x : Nat) : Nat = x\n", "E-DEF-EQUALS", "`:=`");
}

// `=` in `test`.
#[test]
fn equals_in_test() {
    assert_err("test \"n\" = True\n", "E-DEF-EQUALS", "`:=`");
}

// `=` in `let`.
#[test]
fn equals_in_let() {
    assert_err(
        "def f (n : Nat) : Nat :=\n  let x = n\n  x\n",
        "E-DEF-EQUALS",
        "`:=`",
    );
}

// A type that is an equation with nothing after it: the note mentions `:=`.
#[test]
fn equation_type_with_no_body() {
    let text = "def p : a = b\n";
    let mut sources = SourceMap::new();
    let file = sources.add("t.sw", text);
    let errors = parse_module(file, text).unwrap_err();
    let shown = format!("{errors:?}");
    assert!(shown.contains("`:=`"), "{shown}");
}

// A `:=` body followed by arms.
#[test]
fn body_then_arms() {
    assert_err(
        "def f (x : Nat) : Nat := x\n  | y => y\n",
        "E-PARSE",
        "`:=` body or arms, not both",
    );
}

// An unclosed parameter.
#[test]
fn unclosed_paren_binder() {
    assert_err(
        "def f (x : Nat : Nat := 0\n",
        "E-PARSE",
        "`)` to close the parameter",
    );
}

// A parameter without a type.
#[test]
fn binder_without_type() {
    assert_err(
        "def f (x) : Nat := 0\n",
        "E-PARSE",
        "a parameter needs a type",
    );
}

// An unclosed implicit parameter.
#[test]
fn unclosed_bracket_binder() {
    assert_err(
        "def f [x : A : Nat := 0\n",
        "E-PARSE",
        "`]` to close the parameter",
    );
}

// Two header binders with one name, in separate binders and in one.
#[test]
fn duplicate_header_binders() {
    assert_err(
        "def f (x : Nat) (x : Nat) : Nat := x\n",
        "E-DUPLICATE-PARAMETER",
        "`x` is already a parameter of `f`",
    );
    assert_err(
        "def f (x x : Nat) : Nat := x\n",
        "E-DUPLICATE-PARAMETER",
        "`x`",
    );
}

// A header name repeated by an implicit binder after the colon.
#[test]
fn duplicate_with_implicit_after_colon() {
    assert_err(
        "def f (x : Nat) : [x : Bool] -> Nat\n  | y => 0\n",
        "E-DUPLICATE-PARAMETER",
        "`x`",
    );
}

// A header name repeated by an auto binder after the colon.
#[test]
fn duplicate_with_auto_after_colon() {
    assert_err(
        "def f (x : Nat) : [auto x : P] -> Nat\n  | y => 0\n",
        "E-DUPLICATE-PARAMETER",
        "`x`",
    );
}

// An explicit binder after the colon may repeat a header name (section 2.5).
#[test]
fn explicit_after_colon_may_repeat() {
    parse_shape("def f (x : Nat) : (x : Nat) -> P x\n  | y => w\n").unwrap();
}

// An old-style signature line is an error.
#[test]
fn old_signature_is_error() {
    assert_err(
        "f : Nat -> Nat\n",
        "E-OLD-DECLARATION",
        "definitions start with `def`",
    );
}

// So is an old-style equation.
#[test]
fn old_equation_is_error() {
    assert_err(
        "f x = x\n",
        "E-OLD-DECLARATION",
        "definitions start with `def`",
    );
}

// An old-style lambda gets a hint.
#[test]
fn old_lambda_arrow_is_explained() {
    let e = new_err("def f : Nat -> Nat := \\x -> x\n");
    assert!(e.contains("expected `=>`"), "{e}");
}

// A header without a body parses as a signature alone (the elaborator
// admits it only for the prelude's primitives).
#[test]
fn bodiless_header_is_a_signature() {
    let text = "def Delay : Type -> Type\n";
    let mut sources = SourceMap::new();
    let file = sources.add("t.sw", text);
    let module = parse_module(file, text).unwrap();
    assert_eq!(module.decls.len(), 1);
    assert!(matches!(
        module.decls[0],
        stitchwort_syntax::ast::Decl::Signature { .. }
    ));
}

// `export f : …` is an error in the new syntax.
#[test]
fn old_export_is_error() {
    assert_err(
        "export f : Nat -> Nat\n",
        "E-PARSE",
        "`def` or `theorem` after `export`",
    );
}

// ---------------------------------------------------------------------
// e. Handler clauses (section 2.11)

// A handler with a return clause and the given operation clause, in both syntaxes.
#[track_caller]
fn handler(new_clause: &str, old_clause: &str) {
    assert_equivalent(
        &format!(
            "def h (p : () -> {{E | e}} a) : {{e}} a :=\n  handle p () with\n    | return x => x\n    {new_clause}\n"
        ),
        &format!(
            "h : (p : () -> {{E | e}} a) -> {{e}} a\nh p =\n  handle p () with\n    | return x -> x\n    {old_clause}\n"
        ),
    );
}

// A tuple argument.
#[test]
fn clause_tuple() {
    handler("| op (a, b), k => k a", "| op (a, b) => k -> k a");
}

// A unit argument.
#[test]
fn clause_unit() {
    handler("| op (), k => k ()", "| op () => k -> k ()");
}

// A record pattern with a rest.
#[test]
fn clause_record() {
    handler("| op { x, .. }, k => k x", "| op { x, .. } => k -> k x");
}

// A nested tuple.
#[test]
fn clause_nested_tuple() {
    handler("| op ((a, b), c), k => k a", "| op ((a, b), c) => k -> k a");
}

// A list pattern.
#[test]
fn clause_list() {
    handler("| op [a, b], k => k a", "| op [a, b] => k -> k a");
}

// A constructor pattern in brackets.
#[test]
fn clause_constructor() {
    handler("| op (Just x), k => k x", "| op (Just x) => k -> k x");
}

// Two arguments are refused.
#[test]
fn clause_two_arguments() {
    assert_err(
        "def h (p : () -> {E | e} a) : {e} a :=\n  handle p () with\n    | return x => x\n    | op a, b, k => k a\n",
        "E-PARSE",
        "an operation takes one argument",
    );
}

// A missing continuation is refused.
#[test]
fn clause_no_continuation() {
    assert_err(
        "def h (p : () -> {E | e} a) : {e} a :=\n  handle p () with\n    | return x => x\n    | op x => x\n",
        "E-PARSE",
        "name the continuation",
    );
}
