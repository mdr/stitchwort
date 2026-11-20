-- expect-error: E-WALK
-- Two lemmas in the brackets fit one pair of calls: the walk never
-- chooses between them, for two runs as for one.

import Std (Parse, Nat)

def SameNat (x y: Nat): Prop := x = y

def here(): {Parse Nat} Nat := Parse.mark().offset

theorem followsHere: Parse.Follows SameNat SameNat (() => here()) (() => here()) :=
  Parse.followsMap [alike := SameNat] (m => m.offset) (m => m.offset) Parse.followsMark (m n alike => alike.right.left)

theorem followsHereAgain: Parse.Follows SameNat SameNat (() => here()) (() => here()) := followsHere

def hereTwice(): {Parse Nat} Nat :=
  let first := here()
  let second := here()
  first + second

theorem followsHereTwice: Parse.Follows SameNat SameNat (() => hereTwice()) (() => hereTwice()) :=
  byWalking [followsHere, followsHereAgain]
