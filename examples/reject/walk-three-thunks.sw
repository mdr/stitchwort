-- expect-error: E-WALK-LEMMA
-- A walk follows one run of code or two in lockstep, so a family relating
-- three thunks is refused where its lemma is registered, rather than walked
-- silently as one run on its first thunk.

import Std (Parse, Nat)

def Three (first second third: () → {Parse Nat} Nat): Prop := True

@[walk.done]
theorem threeDone (x: Nat): Three (() => x) (() => x) (() => x) := byComputing
