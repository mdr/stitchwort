-- expect-error: E-WALK
-- A family's relation must mention its thunk and its post. `Mine`'s body is
-- `True`, so `Mine p post` computes to `True` whatever `p` and `post` are:
-- the walk can't read the family, the code or the post back from the goal.
-- The error says so; `walk-minimal-family.sw` is the same family with a
-- relation that uses both arguments.

import Std (Parse, Nat, Option)

def Mine (p: () → {Parse Nat} a) (post: a → Prop): Prop := True

@[walk.done]
theorem mineDone ∀ [x: a] [holds: a → Prop]: Mine (() => x) holds := byComputing

@[walk.weaken]
theorem mineWeaken ∀ [p: () → {Parse Nat} a] [holds weaker: a → Prop] (m: Mine p holds): Mine p weaker := byComputing

@[walk.bind]
theorem mineThen ∀ [p: () → {Parse Nat} a] [j: a → {Parse Nat} Nat] [first: a → Prop] [holds: Nat → Prop]
    (firstMine: Mine p first)
    (rest: ∀ (v: a) => first v → Mine (() => j v) holds):
    Mine (() => j (p())) holds :=
  byComputing

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

@[walk]
theorem mineLook: Mine (() => look()) ((v: Option Nat) => True) := byComputing

def twice(): {Parse Nat} Nat :=
  let first := look()
  0

theorem mineTwice: Mine (() => twice()) (n => True) := byWalking []
