-- The arm's goal after a `match` whose expression is inside a call: only
-- that call is opened. `Parse.Follows` stays folded, since its arguments
-- mention `lower` and `n` only inside the condition, and the `False` arm's
-- goal is about `here() + 1` on both sides. (examples/accept/
-- match-partial-unfold.sw; docs/proposals/partial-unfold.md.)
import Std (Parse)

def SameNat (x y: Nat): Prop := x = y

def here (): {Parse Nat} Nat := Parse.mark().offset

def start (lower: Bool) (n: Nat): {Parse Nat} Nat := if lower && n == 0 then 0 else here() + 1

theorem followsStart ∀ (lower: Bool) (n: Nat):
    Parse.Follows SameNat SameNat (() => start lower n) (() => start lower n) :=
  match lower && n == 0 with
    | True => Parse.followsDone byComputing
    | False => ?
