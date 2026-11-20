-- expect-error: E-WALK
-- A premise is a family statement, so the leaf walks it; that walk fails at
-- a call with no lemma (`lookOnce`), and the walk's `then` doesn't prove the
-- premise either. The leaf shows both errors, not only the nested walk's.

import Std (Parse, Option, Nat, Bool, List)

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

def lookOnce(): {Parse Nat} Option Nat := look()

def both (next: () → {Parse Nat} a): {Parse Nat} List a :=
  let first := next()
  let second := next()
  [first, second]

theorem givesBoth ∀ (next: () → {Parse Nat} a) (holds: a → Prop)
    (nextGives: Parse.Gives Parse.Invariant.any next holds):
    Parse.Gives Parse.Invariant.any (() => both next) (List.All holds) :=
  byWalking [] then (firstFacts, secondFacts, ())

def bothOnce(): {Parse Nat} List (Option Nat) := both (() => lookOnce())

theorem givesBothOnce: Parse.Gives Parse.Invariant.any (() => bothOnce()) (List.All ((v: Option Nat) => True)) :=
  byWalking [givesBoth] then byComputing
