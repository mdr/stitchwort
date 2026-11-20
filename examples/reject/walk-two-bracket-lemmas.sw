-- expect-error: E-WALK
-- Two lemmas in the brackets fit the call: the walk never chooses between
-- them.

import Std (Parse, Option, Nat)

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

theorem givesLook: Parse.Gives Parse.Invariant.any (() => look()) ((v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)

theorem givesLookAgain: Parse.Gives Parse.Invariant.any (() => look()) ((v: Option Nat) => True) := givesLook

def lookTwice(): {Parse Nat} Nat :=
  let first := look()
  let second := look()
  0

theorem givesLookTwice: Parse.Gives Parse.Invariant.any (() => lookTwice()) (n => n = 0) :=
  byWalking [givesLook, givesLookAgain]
