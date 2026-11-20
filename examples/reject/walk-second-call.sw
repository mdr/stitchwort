-- expect-error: E-WALK
-- The same function is called twice, and the walk stops at the second call:
-- the message says which call it is, not just the function.

import Std (Parse, Option, Nat)

def lookAt (n: Nat): {Parse Nat} Option Nat := Parse.next (k => k == n)

theorem givesLookAtOne: Parse.Gives Parse.Invariant.any (() => lookAt 1) ((v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (k => k == 1)) (read value proved => byComputing)

def twice(): {Parse Nat} Nat :=
  let first := lookAt 1
  let second := lookAt 2
  0

theorem givesTwice: Parse.Gives Parse.Invariant.any (() => twice()) (n => n = 0) := byWalking [givesLookAtOne]
