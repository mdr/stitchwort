-- One registered lemma for `look` in sight: its own.
namespace User

import Std (Parse, Option, Nat)
import Look (look)

@[walk]
theorem givesLook: Parse.Gives Parse.Invariant.any (() => look()) ((v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)

def lookTwice(): {Parse Nat} Nat :=
  let first := look()
  let second := look()
  0

theorem givesLookTwice: Parse.Gives Parse.Invariant.any (() => lookTwice()) (n => n = 0) := byWalking []
