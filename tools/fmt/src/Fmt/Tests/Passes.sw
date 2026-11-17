--| The tidy passes on small cases, ported from `crates/fmt/src/passes.rs`,
--| `parens.rs` and `merge.rs`. The harness (`dev/fmt-twin passes`) compares
--| whole files with the Rust side; these pin each pass's rule, and the
--| parked comma. A case is the tree's dump before and after a pass, as
--| the tree's `Def` lines.

namespace Fmt.Tests
import Fmt (..)
import Std (Bool, List, Option, Result, Text)
import Syntax (SourceFile, lex, parseFile)

def parsed (source: Text): Result SourceFile Text := match lex source with
  | Ok lexed => parseFile lexed.settled
  | Err message => Err message

--| The dump after a pass is the dump of the written-out result: each case
--| names the source that has the same tree as the pass's result.
def sameTree (before: Text) (pass: SourceFile → SourceFile) (after: Text): Bool :=
  match parsed before, parsed after with
    | Ok tree, Ok tidy => (pass tree).dump == tidy.dump
    | _, _ => False

def unchanged (source: Text) (pass: SourceFile → SourceFile): Bool := sameTree source pass source

test "P1: a theorem with explicit parameters gets a ∀" :=
  sameTree "theorem t (a: Nat): a = a := byComputing" SourceFile.withForall "theorem t ∀ (a: Nat): a = a := byComputing"

test "P1: a theorem that is tidy for ∀ is left alone" :=
  unchanged "theorem t ∀ (a: Nat): a = a := byComputing" SourceFile.withForall
    && unchanged "theorem t: 1 = 1 := byComputing" SourceFile.withForall
    && unchanged "theorem t [a: Nat]: a = a := byComputing" SourceFile.withForall
    && unchanged "def f (a: Nat): Nat := a" SourceFile.withForall

test "P1: a local theorem gets its ∀ too" :=
  sameTree "def f: Nat :=\n  theorem t (a: Nat): a = a := byComputing\n  1" SourceFile.withForall
      "def f: Nat :=\n  theorem t ∀ (a: Nat): a = a := byComputing\n  1"

test "P2: the last comma of a comma bracket goes" :=
  sameTree "def x: T := [1, 2,]" SourceFile.withoutTrailingCommas "def x: T := [1, 2]"
    && sameTree "def x: T := { a = 1, b = 2, }" SourceFile.withoutTrailingCommas "def x: T := { a = 1, b = 2 }"
    && sameTree "type R = { x: Nat, }" SourceFile.withoutTrailingCommas "type R = { x: Nat }"
    && sameTree "@[inline,] def x: T := 1" SourceFile.withoutTrailingCommas "@[inline] def x: T := 1"
    && sameTree "def f: Nat := match x with | [a,] => a | { a, } => a" SourceFile.withoutTrailingCommas
        "def f: Nat := match x with | [a] => a | { a } => a"

test "P2: a tuple keeps its two items" :=
  sameTree "def x: T := (1, 2,)" SourceFile.withoutTrailingCommas "def x: T := (1, 2)"
    && sameTree "def f: Nat := match x with | (p, q,) => 1" SourceFile.withoutTrailingCommas
        "def f: Nat := match x with | (p, q) => 1"

test "P2: a comma before a tail isn't a last one" :=
  unchanged "def f: Nat := match x with | [a, ..r] => a" SourceFile.withoutTrailingCommas

test "P3: brackets after a row and around a binder's type are dropped" :=
  sameTree "def a: {Fail} (List Nat) := []" SourceFile.withoutSpareBrackets "def a: {Fail} List Nat := []"
    && sameTree "theorem c ∀ (h: (∀ (i: Nat) => i = i)): True := h" SourceFile.withoutSpareBrackets
        "theorem c ∀ (h: ∀ (i: Nat) => i = i): True := h"
    && sameTree "def a (x: (T)) (y: ((U))): {Fail} ((List Nat)) := x" SourceFile.withoutSpareBrackets
        "def a (x: T) (y: U): {Fail} List Nat := x"

test "P3: a bracket that holds the grammar together stays" :=
  unchanged "def a: {Fail} (List Nat) Nat := x" SourceFile.withoutSpareBrackets
    && unchanged "def a: {Fail} (a + b) * c := x" SourceFile.withoutSpareBrackets
    && unchanged "def a: {Fail} (A → B) := x" SourceFile.withoutSpareBrackets
    && unchanged "def a: {Fail} (-1) := x" SourceFile.withoutSpareBrackets
    && unchanged "def a (x: (T) U): T := x" SourceFile.withoutSpareBrackets
    && unchanged "def a (x: (T) := 1): T := x" SourceFile.withoutSpareBrackets
    && unchanged "def a: {Fail} ( -- c\n  List Nat) := x" SourceFile.withoutSpareBrackets

test "P3: an operator's left side stands bare as the grammar's levels allow" :=
  sameTree "def a: {Fail} (a + b) + c := x" SourceFile.withoutSpareBrackets "def a: {Fail} a + b + c := x"
    && sameTree "def a: {Fail} (List Nat) → B := x" SourceFile.withoutSpareBrackets "def a: {Fail} List Nat → B := x"
    && unchanged "def a: {Fail} (a ++ b) ++ c := x" SourceFile.withoutSpareBrackets
    && unchanged "def a: {Fail} (a ∧ b) ∧ c := x" SourceFile.withoutSpareBrackets

test "P4: adjacent parameters of one type merge" :=
  sameTree "def f (a: Nat) (b: Nat) [t: Type] [u: Type] (x: t): Nat := a" SourceFile.withMergedParameters
      "def f (a b: Nat) [t u: Type] (x: t): Nat := a"
    && sameTree "theorem g ∀ (xs: List Nat) (ys: List Nat): xs = ys := h" SourceFile.withMergedParameters
        "theorem g ∀ (xs ys: List Nat): xs = ys := h"
    && sameTree "def h: Nat := forall (x: Nat) (y: Nat) => (p: Nat) (q: Nat) => x" SourceFile.withMergedParameters
        "def h: Nat := forall (x y: Nat) => (p q: Nat) => x"

test "P4: dependent types, defaults, comments and other brackets keep parameters apart" :=
  unchanged "def f (x: P x) (y: P x): Nat := a" SourceFile.withMergedParameters
    && unchanged "def g (a: Nat) -- a\n  (b: Nat): Nat := a" SourceFile.withMergedParameters
    && unchanged "def g (a: Nat)\n  -- b\n  (b: Nat): Nat := a" SourceFile.withMergedParameters
    && unchanged "def h (a: Nat := 1) (b: Nat): Nat := a" SourceFile.withMergedParameters
    && unchanged "def i [auto e: Eq a] [auto f: Eq a]: Nat := 1" SourceFile.withMergedParameters
    && unchanged "def j (a: Nat) [b: Nat]: Nat := a" SourceFile.withMergedParameters
    && unchanged "instance i (a: Nat) (b: Nat): Foo := x" SourceFile.withMergedParameters
    && unchanged "type T = | C (a: Nat) (b: Nat)" SourceFile.withMergedParameters

test "P3 before P4: dropping a parameter's brackets lets the group merge" :=
  match parsed "def f (a: (Nat)) (b: Nat): Nat := a", parsed "def f (a b: Nat): Nat := a" with
    | Ok tree, Ok tidy => tree.withoutSpareBrackets.withMergedParameters.dump == tidy.dump
    | _, _ => False

test "the parked comma: a comma that starts the closer's line leaves its comments where Rust puts them" :=
  -- The comma's own-line comment and the closer's trailing comment, with the
  -- comma written out as a space (the Rust pass deletes it from the text).
  let withComma := "def x: T := g ([\n  1\n  -- above\n  , ] -- b\n) -- c\n"
  let withoutComma := "def x: T := g ([\n  1\n  -- above\n    ] -- b\n) -- c\n"
  match lex withComma, lex withoutComma with
    | Ok a, Ok b => a.settledBare.dump == b.settled.dump
    | _, _ => False
