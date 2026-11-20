-- A `rewrite` whose left side is inside a call the goal shows folded: only
-- the calls on the path to it are unfolded, so the next goal keeps the rest
-- as written. Here `size items` is inside `line items`, and the goal is
-- `Parse.Follows` around `line items` and `line others`. The search as
-- written can't see it, and the search over the computed goal unfolds
-- everything, so `Parse.followsThen` found no continuation to solve. Now
-- only the left `line` is opened: `Parse.Follows` mentions `items` only
-- inside it, and the right `line others` doesn't mention `items` at all. The
-- next goal is `Parse.Follows SameNat SameNat (() => here() + size others)
-- (() => line others)`. (docs/syntax.md, "rewrite";
-- docs/proposals/partial-unfold.md; the shape of the formatter's
-- `followsBlockLine`.)
import Std (List, Parse)

def SameNat (x y: Nat): Prop := x = y

def here (): {Parse Nat} Nat := Parse.mark().offset

theorem followsHere: Parse.Follows SameNat SameNat (() => here()) (() => here()) :=
  Parse.followsMap [alike := SameNat] (m => m.offset) (m => m.offset) Parse.followsMark (m n alike => alike.right.left)

def size (items: List Nat): Nat := items.length

def line (items: List Nat): {Parse Nat} Nat := here() + size items

theorem followsLine ∀ (items others: List Nat)
    (same: size items = size others):
    Parse.Follows SameNat SameNat (() => line items) (() => line others) :=
  rewrite same then Parse.followsThen followsHere (x y alike => Parse.followsDone (rewrite alike))
