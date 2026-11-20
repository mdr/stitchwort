-- The smallest walk family: a relation over one thunk, with a done, a
-- weaken and a bind lemma. The bind lemma's last premise is a `∀` over the
-- first premise's result (`walk-premise-without-binders.sw` is the refusal
-- of one without). The relation must mention both its arguments: a
-- relation that is `True` computes to `True`, and the walk can no longer
-- read the family, the code or the post back from the goal.

import Std (Parse, Nat, Option)

def Mine (p: () → {Parse Nat} a) (post: a → Prop): Prop := (p, post) = (p, post)

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
