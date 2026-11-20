-- expect-error: E-WALK
-- A call with no lemma: none in the brackets, none registered, and the
-- function isn't unfolded unless asked. The message names the call and
-- shows the goal there.

import Std (Parse, Option, Nat, Bool, List)

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

def lookTwice(): {Parse Nat} (Option Nat, Option Nat) :=
  let first := look()
  let second := look()
  (first, second)

theorem givesLookTwice: Parse.Gives Parse.Invariant.any (() => lookTwice()) (pair => True) :=
  byWalking []
