--| `meaning` on small trees, each case proved by computing: what it
--| forgets, and what it must not.

namespace Fmt.Sketch.Examples
import Fmt.Sketch (..)
import Std (Bool, Eq, List, Option, Text)

def name (text: Text): Expr := Token { text, comments = Comments.none }

def word (text: Text): Word := { text, comments = Comments.none }

def bare (inner: Expr): Expr := Pair Comments.none inner Comments.none

def row: Expr := Commas Row Comments.none None [name "IO"] False Comments.none

def listNat: Expr := Form App [Sub (name "List"), Sub (name "Nat")]

def group (names: List Word) (annotation: Expr): Parameter :=
  Group Param False Comments.none None names Comments.none annotation None Comments.none

--| `{IO} ((List Nat))` means `{IO} List Nat`.
theorem pairAfterRowForgotten: (WithRow row (bare (bare listNat))).traverse plainSteps Elsewhere
      = (WithRow row listNat).traverse plainSteps Elsewhere :=
  byComputing

--| `(f) x` keeps its pair: the compiler reads the pair around an
--| application's head.
theorem pairAtHeadKept: (Form App [Sub (bare (name "f")), Sub (name "x")]).traverse plainSteps Elsewhere
      = Form App [Sub (bare (name "f")), Sub (name "x")] :=
  byComputing

--| A pair that holds a comment stays where one without would go.
theorem pairWithCommentKept: (WithRow row (Pair { above = [], after = Some "-- why" } listNat Comments.none)).traverse
        plainSteps Elsewhere
      = WithRow row (Pair { above = [], after = Some "-- why" } listNat Comments.none) :=
  byComputing

--| `(a b: Nat)` means `(a: Nat) (b: Nat)`, and `(h: (Nat))` means
--| `(h: Nat)`.
theorem groupSplit: splitGroups (traverseParameters plainSteps [group [word "a", word "b"] (bare (name "Nat"))])
      = splitGroups (traverseParameters plainSteps [group [word "a"] (name "Nat"), group [word "b"] (name "Nat")]) :=
  byComputing

--| `(x y: P x)` is kept whole: split, its second type would mean the
--| first `x`.
theorem dependentGroupKept: splitGroups [group [word "x", word "y"] (Form App [Sub (name "P"), Sub (name "x")])]
      = [group [word "x", word "y"] (Form App [Sub (name "P"), Sub (name "x")])] :=
  byComputing

--| `[1, 2,]` means `[1, 2]`.
theorem commaForgotten: (Commas ListOf Comments.none None [name "1", name "2"] True Comments.none).traverse plainSteps
        Elsewhere
      = Commas ListOf Comments.none None [name "1", name "2"] False Comments.none :=
  byComputing

--| A theorem with a parameter in round brackets and a result type means
--| the same with `∀` or without.
theorem forallForgotten: plainDeclaration
      (Headed Theorem [] [word "theorem"] (word "t") None [group [word "a"] (name "Nat")] [
        Sub (Form ResultType [Piece (word ":"), Sub (name "P")])
      ])
      = plainDeclaration
        (Headed Theorem [] [word "theorem"] (word "t") (Some Comments.none) [group [word "a"] (name "Nat")] [
          Sub (Form ResultType [Piece (word ":"), Sub (name "P")])
        ]) :=
  byComputing
