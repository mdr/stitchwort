-- A `match` whose expression is inside a call the goal shows folded: only
-- the calls on the path to it are unfolded, so the arms keep the rest of the
-- goal as written. Here `lower && n == 0` is `start`'s `if` condition, and
-- the goal is `Parse.Follows` around two `start` calls. The search as written
-- can't see it, and the search over the computed goal unfolds everything,
-- `Parse.Follows` and both parsers' runs included, so in the `False` arm
-- `Parse.followsThen` found no continuation to solve. Now `start` is opened
-- (its arguments mention `lower` and `n`) and `Parse.Follows` is not (its
-- arguments then mention them only inside the condition), so the `False`
-- arm's goal is `Parse.Follows SameNat SameNat (() => here() + 1) (() =>
-- here() + 1)`. (docs/syntax.md, "Generalised `match`";
-- docs/proposals/partial-unfold.md; the shape of the formatter's
-- `followsRowStart`.)
import Std (Parse)

def SameNat (x y: Nat): Prop := x = y

def here (): {Parse Nat} Nat := Parse.mark().offset

theorem followsHere: Parse.Follows SameNat SameNat (() => here()) (() => here()) :=
  Parse.followsMap [alike := SameNat] (m => m.offset) (m => m.offset) Parse.followsMark (m n alike => alike.right.left)

def start (lower: Bool) (n: Nat): {Parse Nat} Nat := if lower && n == 0 then 0 else here() + 1

theorem followsStart ∀ (lower: Bool) (n: Nat):
    Parse.Follows SameNat SameNat (() => start lower n) (() => start lower n) :=
  match lower && n == 0 with
    | True => Parse.followsDone byComputing
    | False => Parse.followsThen followsHere (x y same => Parse.followsDone (rewrite same))
