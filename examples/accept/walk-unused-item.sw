-- expect-warning: W-WALK-UNUSED-ITEM
-- A bracket lemma that fits no call in the walk is unused, and warned about
-- at the item, rather than silently ignored.

import Std (Parse, Option, Nat)

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

@[walk]
theorem givesLook: Parse.Gives Parse.Invariant.any (() => look()) ((v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)

theorem oneEqOne: 1 = 1 := byComputing

def once(): {Parse Nat} Option Nat := look()

theorem givesOnce: Parse.Gives Parse.Invariant.any (() => once()) ((v: Option Nat) => True) :=
  byWalking [givesLook, oneEqOne]
