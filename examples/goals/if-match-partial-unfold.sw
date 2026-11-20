-- A `match` at the end of an `if`'s branch keeps the goal as written: the
-- arm's goal shows `Parse.Follows` folded, as it would with no `if`
-- (examples/goals/match-partial-unfold.sw; docs/proposals/partial-unfold.md
-- §2.2).
import Std (Parse)

def SameNat (x y: Nat): Prop := x = y

def here (): {Parse Nat} Nat := Parse.mark().offset

def start (lower: Bool) (n: Nat): {Parse Nat} Nat := if lower && n == 0 then 0 else here() + 1

theorem followsStart ∀ (lower: Bool) (n: Nat):
    Parse.Follows SameNat SameNat (() => start lower n) (() => start lower n) :=
  if n == 0 then
    match lower && n == 0 with
      | True => Parse.followsDone byComputing
      | False => ?
  else
    match lower && n == 0 with
      | True => Parse.followsDone byComputing
      | False => ?

theorem followsStartH ∀ (lower: Bool) (n: Nat):
    Parse.Follows SameNat SameNat (() => start lower n) (() => start lower n) :=
  if h: n = 0 then ?
  else
    match lower && n == 0 with
      | True => Parse.followsDone byComputing
      | False => ?
