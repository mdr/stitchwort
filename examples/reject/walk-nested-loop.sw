-- expect-error: E-WALK
-- Two lemmas whose premises are about each other's functions: walking
-- one's premise needs the other's, whose premise needs the first's again.
-- The walk stops there rather than going round for ever.

import Std (Parse, Nat)

def SameNat (x y: Nat): Prop := x = y

def f (n: Nat): {Parse Nat} Nat := Parse.mark().offset

def g (n: Nat): {Parse Nat} Nat := Parse.mark().offset

def h(): {Parse Nat} Nat := f 0

@[walk]
theorem followsF ∀ (n: Nat) (gs: ∀ (m: Nat) => Parse.Follows SameNat SameNat (() => g m) (() => g m)):
    Parse.Follows SameNat SameNat (() => f n) (() => f n) :=
  Parse.followsMap [alike := SameNat] (m => m.offset) (m => m.offset) Parse.followsMark (m k alike => alike.right.left)

@[walk]
theorem followsG ∀ (n: Nat) (fs: ∀ (m: Nat) => Parse.Follows SameNat SameNat (() => f m) (() => f m)):
    Parse.Follows SameNat SameNat (() => g n) (() => g n) :=
  Parse.followsMap [alike := SameNat] (m => m.offset) (m => m.offset) Parse.followsMark (m k alike => alike.right.left)

theorem followsH: Parse.Follows SameNat SameNat (() => h()) (() => h()) := byWalking []
