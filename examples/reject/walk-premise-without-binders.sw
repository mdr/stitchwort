-- expect-error: E-WALK-LEMMA
-- A then-lemma's last premise must be a `∀` over the first premise's
-- results: `j` is called on a value, and a premise that binds nothing gives
-- the walk none to hand it. `mineThen`'s `rest` is no `∀`, so registering it
-- as `@[walk.bind]` is refused (`walk-minimal-family.sw` has the lemma with
-- the `∀`).

import Std (Parse, Nat, Option)

def Mine (p: () → {Parse Nat} a) (post: a → Prop): Prop := True

@[walk.bind]
theorem mineThen ∀ [p: () → {Parse Nat} a] [j: a → {Parse Nat} Nat] [first: a → Prop] [holds: Nat → Prop]
    (firstMine: Mine p first)
    (rest: Mine (() => 0) holds):
    Mine (() => j (p())) holds :=
  byComputing
