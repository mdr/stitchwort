-- expect-error: E-WALK-LEMMA
-- Two `@[walk]` lemmas for a pair of runs must not both fit one pair of
-- calls. A run a lemma leaves open (`second`, any parser) fits every
-- function, so `(fail, any)` and `(fail, bump)` overlap; the error is at
-- the second lemma, naming both, not at a walk that meets the pair.

import Std (Parse, Nat, Result, Empty)

def SameNat (x y: Nat): Prop := x = y

def fail(): {Parse Nat} Nat := Empty.absurd (Parse.fatal "no")

def bump(): {Parse Nat} Nat := Parse.mark().offset

theorem neverFail ∀ (state: Parse.State Nat) (value: Nat) (after: Parse.Mark Nat):
    ¬(Parse.runFrom state (() => (fail(), Parse.mark())) = Ok (value, after)) :=
  ran => (Result.errNotOk ran).impossible

@[walk]
theorem followsFailAny ∀ (second: () → {Parse Nat} Nat): Parse.Follows SameNat SameNat (() => fail()) second :=
  Parse.followsNever (() => fail()) second neverFail

@[walk]
theorem followsFailBump: Parse.Follows SameNat SameNat (() => fail()) (() => bump()) :=
  Parse.followsNever (() => fail()) (() => bump()) neverFail
