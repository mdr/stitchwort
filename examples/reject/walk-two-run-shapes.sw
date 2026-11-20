-- expect-error: E-WALK
-- A two-run walk follows both runs only where their code has the same
-- shape. Here the first run reads a number and the second gives one
-- without reading: the walk stops there, showing both runs, and doesn't
-- guess how they line up.

import Std (Parse, Nat)

def SameNat (x y: Nat): Prop := x = y

def here(): {Parse Nat} Nat := Parse.mark().offset

@[walk]
theorem followsHere: Parse.Follows SameNat SameNat (() => here()) (() => here()) :=
  Parse.followsMap [alike := SameNat] (m => m.offset) (m => m.offset) Parse.followsMark (m n alike => alike.right.left)

def reading(): {Parse Nat} Nat :=
  let at := here()
  at + 1

def fixed(): {Parse Nat} Nat := 1

theorem followsReading: Parse.Follows SameNat (x y => True) (() => reading()) (() => fixed()) := byWalking []
