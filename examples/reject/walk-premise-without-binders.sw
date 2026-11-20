-- expect-error: E-UNSOLVED
-- A then-lemma whose last premise is no `∀` binds nothing, so the walk
-- writes no lambda for it; it once wrote one with no parameters and
-- (It still fails, with an ordinary error: `E-UNSOLVED`.)

import Std (Parse, Nat, Option)

def Mine (p: () → {Parse Nat} a) (post: a → Prop): Prop := True

@[walk.done]
theorem mineDone ∀ [x: a] [holds: a → Prop]: Mine (() => x) holds := byComputing

@[walk.weaken]
theorem mineWeaken ∀ [p: () → {Parse Nat} a] [holds weaker: a → Prop] (m: Mine p holds): Mine p weaker := byComputing

@[walk.bind]
theorem mineThen ∀ [p: () → {Parse Nat} a] [j: a → {Parse Nat} Nat] [first: a → Prop] [holds: Nat → Prop]
    (firstMine: Mine p first)
    (rest: Mine (() => 0) holds):
    Mine (() => j (p())) holds :=
  byComputing

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

@[walk]
theorem mineLook: Mine (() => look()) ((v: Option Nat) => True) := byComputing

def twice(): {Parse Nat} Nat :=
  let first := look()
  0

theorem mineTwice: Mine (() => twice()) (n => True) := byWalking []
