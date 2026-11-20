-- expect-error: E-WALK
-- Each split doubles the paths a walk follows; past 64 it stops and says
-- to give the splitting function a lemma of its own.

import Std (Parse, Option, Nat, Bool, List)

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

def s1 (a: Bool): {Parse Nat} Nat := if a then 1 else 0
def s2 (a b: Bool): {Parse Nat} Nat := if a then s1 b else s1 b
def s3 (a b c: Bool): {Parse Nat} Nat := if a then s2 b c else s2 b c
def s4 (a b c d: Bool): {Parse Nat} Nat := if a then s3 b c d else s3 b c d
def s5 (a b c d e: Bool): {Parse Nat} Nat := if a then s4 b c d e else s4 b c d e
def s6 (a b c d e f: Bool): {Parse Nat} Nat := if a then s5 b c d e f else s5 b c d e f
def s7 (a b c d e f g: Bool): {Parse Nat} Nat := if a then s6 b c d e f g else s6 b c d e f g

theorem givesS7 ∀ (a b c d e f g: Bool): Parse.Gives Parse.Invariant.any (() => s7 a b c d e f g) (n => n <= 1) :=
  byWalking [unfold s1, unfold s2, unfold s3, unfold s4, unfold s5, unfold s6]
