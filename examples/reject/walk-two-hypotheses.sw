-- expect-error: E-WALK
-- Two hypotheses fit the parameter's call: the walk never chooses between
-- them, and says to name the one wanted in the brackets.

import Std (Parse, Nat, List)

def twice (next: () → {Parse Nat} a): {Parse Nat} List a :=
  let first := next()
  let second := next()
  [first, second]

theorem givesTwice ∀ (next: () → {Parse Nat} a) (holds: a → Prop)
    (nextGives nextGivesAgain: Parse.Gives Parse.Invariant.any next holds):
    Parse.Gives Parse.Invariant.any (() => twice next) (List.All holds) :=
  byWalking [] then (firstFacts, secondFacts, ())
