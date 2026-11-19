--| `loweringDeaf` computed on parsed declarations with comments: the lowering's error of each, and of its blanked tree.

namespace Fmt.Tests
import Fmt (..)
import Fmt.Walk (..)
import Fmt.Proofs (blankPure)
import Std (Bool, List, Option, Parse, Result, Text)
import Syntax (Decl, Seen, declaration, groupsOf, items, lex)

--| The lowering's errors of each declaration in `source` that parses, on its own tree and on the tree blanked.
def loweringPairs (source: Text): List (Option Text, Option Text) := match lex source with
  | Err _ => []
  | Ok lexed => (groupsOf lexed.settledOnce.leaves).filterMap (group =>
    match Parse.run (items group) (() => declaration Seen.start) with
      | Err _ => None
      | Ok decl => Some (decl.loweringError, (decl.walk blankPure).loweringError))

def loweringAgrees (source: Text): Bool := (loweringPairs source).all (match | (first, second) => first == second)

def loweringSources: List Text := ["-- a\ndef f (x: Nat) -- b\n    (x: Nat): Nat := -- c\n  x -- d\n",
  "def orZero (o: Option Nat): Nat := -- a\n  match o with -- b\n    | Some x | None => 0 -- c\n",
  "def g (n: Nat): Nat :=\n  -- a\n  def h (y: Nat) (y: Nat): Nat := y -- b\n  h n n -- c\n",
  "def k (n: Empty): Nat := match n with -- a\n  | () if True -- b\n",
  "def k2 (n: Empty): Nat := (match n with | () if True) -- a\n",
  "def k3 (n: Nat): Nat := n.map (matches | Zero if True) -- a\n",
  "def k4 (n: Nat): Nat := n.map (match | () if True) -- a\n", "def m (n: Nat): Nat := -- a\n  n + 1 -- b\n"]

test "lowering ignores comments" := loweringSources.all loweringAgrees

--| The sources reach the lowering's three checks: six of the eight declarations have an error.
test "lowering sources have errors" :=
  (loweringSources.flatMap loweringPairs).filter (match | (first, _) => first != None) |> .length == 6

--| The lowering's error of each declaration in `source` that parses.
def loweringErrors (source: Text): List (Option Text) := loweringPairs source |> .map (match | (first, _) => first)

test "or-patterns whose alternatives bind the same names are accepted" :=
  loweringErrors
      "def size (shape: Shape): Nat := match shape with\n  | Circle size | Square size => size\n  | Dot => 0\n"
    ++ loweringErrors
        "def f (x: Option Shape): Nat := match x with\n  | Some (Circle size | Square size) => size\n  | _ => 0\n"
    ++ loweringErrors
        "def f (x: Option (Pair Nat Nat)): Nat := match x with\n  | Some ((n, 0) | (0, n)) => n\n  | _ => 0\n"
    ++ loweringErrors
        "def f (x: Option R): Nat := match x with\n  | Some { a, .. } | Some { b = a, .. } => a\n  | None => 0\n"
    == [None, None, None, None]

--| The messages are the Rust lowering's, which quote the alternatives from the (formatted) source.
test "an or-pattern with a name missing from an alternative is refused" :=
  loweringErrors "def g (x: Option Nat): Nat := match x with\n  | Some n | None => 0\n"
    ++ loweringErrors "def g (x: List Nat): Nat := match x with\n  | [n, ..rest] | [] => 0\n"
    ++ loweringErrors "def g (x: Option R): Nat := match x with\n  | Some { a, b = (n, _) } | None => 0\n"
    ++ loweringErrors "def g (x: Option (Pair Nat Nat)): Nat := match x with\n  | Some (0, n) | Some (m, 1) => 0\n"
    ++ loweringErrors "def g (x: Text): Nat := match x with\n  | \"a\" ++ rest | \"b\" ++ (other) => 0\n"
    == [
      Some "`n` is bound in `Some n` but not in `None`",
      Some "`n` is bound in `[n, ..rest]` but not in `[]`",
      Some "`a` is bound in `Some { a, b = (n, _) }` but not in `None`",
      Some "`n` is bound in `Some (0, n)` but not in `Some (m, 1)`",
      Some "`rest` is bound in `\"a\" ++ rest` but not in `\"b\" ++ (other)`"
    ]
