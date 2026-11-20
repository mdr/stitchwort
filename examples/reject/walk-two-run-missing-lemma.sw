-- expect-error: E-WALK
-- A two-run walk needs a lemma for each pair of calls, here about `here`
-- and `here`; none is registered or named. The message shows both runs'
-- calls and the goal there.

import Std (Parse, Nat)

def SameNat (x y: Nat): Prop := x = y

def here(): {Parse Nat} Nat := Parse.mark().offset

theorem followsHere: Parse.Follows SameNat SameNat (() => here()) (() => here()) :=
  Parse.followsMap [alike := SameNat] (m => m.offset) (m => m.offset) Parse.followsMark (m n alike => alike.right.left)

def hereTwice(): {Parse Nat} Nat :=
  let first := here()
  let second := here()
  first + second

theorem followsHereTwice: Parse.Follows SameNat SameNat (() => hereTwice()) (() => hereTwice()) := byWalking []
