-- expect-error: E-WALK-LEMMA
-- At most one lemma per function and family is registered with
-- `@[walk]`, so which one a walk uses never depends on the order they
-- were loaded in.

import Std (Parse, Option, Nat, Bool, List)

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

@[walk]
theorem givesLook: Parse.Gives Parse.Invariant.any (() => look()) ((v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)

@[walk]
theorem givesLookAgain: Parse.Gives Parse.Invariant.any (() => look()) ((v: Option Nat) => True) :=
  givesLook
