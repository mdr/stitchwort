-- `byWalking` inside a `match` written in the proof, nested in another:
-- the goal's code there is already stepped (`look()` shows as the
-- operation it performs), so the registered lemma about `look` fits it
-- by unification, and the theorem's own recursive call is found from its
-- statement.

import Std (Parse, Option, Nat)

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

@[walk]
theorem givesLook: Parse.Gives Parse.Invariant.any (() => look()) ((v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)

def down (fuel: Nat): {Parse Nat} Nat := match fuel with
  | Zero => 0
  | Succ more =>
    let x := look()
    down more

theorem givesDown ∀ (fuel: Nat): Parse.Gives Parse.Invariant.any (() => down fuel) (n => True) := match fuel with
  | Zero => byWalking []
  | Succ more =>
    match more with
      | Zero => byWalking []
      | Succ m => byWalking []
