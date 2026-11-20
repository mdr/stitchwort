-- Checked before `User`, which doesn't import it.
namespace Aside

import Std (Parse, Option, Nat)
import Look (look)

@[walk]
theorem givesLook: Parse.Gives Parse.Invariant.any (() => look()) ((v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)
