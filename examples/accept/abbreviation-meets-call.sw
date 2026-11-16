-- A lemma over any invariant, used where the goal is a definition that
-- fills the invariant in: `Within ?rule n` against `Anywhere n`, where
-- `Anywhere n` is `Within Rule.any n`. The goal is compared as written
-- first, so its arguments give `?rule := Rule.any`. Unfolded, the two
-- would meet `?rule.holds m` against `Unit`, which says nothing about
-- `?rule` (SW-3534; std's `Parse.Reads`, defined as `Parse.ReadsIn any`).
import Std (Nat)

type Rule = { holds: Nat → Prop }

def Rule.any: Rule := { holds = n => Unit }

def Within (rule: Rule) (n: Nat): Prop := ∀ (m: Nat) => rule.holds m → m = n → n = m

def Anywhere (n: Nat): Prop := Within Rule.any n

theorem withinAll ∀ [rule: Rule] (n: Nat): Within rule n := m h same => Std.Eq.sym same

theorem anywhereAll ∀ (n: Nat): Anywhere n := withinAll n

theorem withinKeep ∀ [rule: Rule] [n: Nat] (h: Within rule n): Within rule n := h

theorem anywhereKeep ∀ (n: Nat) (h: Anywhere n): Anywhere n := withinKeep h
