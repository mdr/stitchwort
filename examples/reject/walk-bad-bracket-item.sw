-- expect-error: E-UNKNOWN-NAME
-- A bracket item that doesn't elaborate is reported as it stands, not
-- taken for a lemma that fits nothing.

import Std (Parse, Option, Nat)

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

@[walk]
theorem givesLook: Parse.Gives Parse.Invariant.any (() => look()) ((v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)

def lookTwice(): {Parse Nat} Nat :=
  let first := look()
  let second := look()
  0

theorem givesLookTwice: Parse.Gives Parse.Invariant.any (() => lookTwice()) (n => n = 0) := byWalking [givesLookk]
