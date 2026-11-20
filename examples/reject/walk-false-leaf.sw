-- expect-error: E-WALK
-- The walk reaches a value the statement is false of: no closer proves
-- the leaf, and the message shows it.

import Std (Parse, Option, Nat, Bool, List)

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

@[walk]
theorem givesLook: Parse.Gives Parse.Invariant.any (() => look()) ((v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)

def lookThenZero(): {Parse Nat} Nat :=
  let seen := look()
  0

theorem givesOne: Parse.Gives Parse.Invariant.any (() => lookThenZero()) (n => n = 1) :=
  byWalking []
