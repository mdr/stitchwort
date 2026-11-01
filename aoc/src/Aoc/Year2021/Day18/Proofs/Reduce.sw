-- Reducing: when `reduce` finishes within its budget, its steps are the
-- spec's steps on the leaves, and what it gives is reduced.

namespace Aoc.Year2021.Day18.Proofs
import Aoc.Year2021.Day18 (..)
import Aoc.Year2021.Day18.Spec (ReducesTo, leaves, reduceStep)
import Std (Nat, Option, Void)

-- Starting from a number with nothing inside more than five pairs, as the
-- pair of two reduced numbers is: if `reduce` finishes within its budget,
-- the spec's reduction of the number's leaves ends at the leaves of what it
-- gives, which has nothing inside more than four pairs and nothing to
-- split.
theorem reduceSound: (budget: Nat) → (number: Number) → (final: Number) → reduce budget number = Some final → height number ≤ 5 →
    ReducesTo (leaves 0 number) (leaves 0 final) ∧ height final ≤ 4 ∧ split final = None
  | 0, number, final, none, _ => Void.exfalso (Option.noneNotSome final none)
  | Succ budget, number, final, done, fits =>
    match ex: explode 0 number with
      | Some exploded =>
        let rest := reduceSound budget exploded.number final done (omega [explodeHeight 0 number exploded ex])
        let step: reduceStep (leaves 0 number) = Some (leaves 0 exploded.number) := rewrite explodeSome number exploded ex fits in rfl
        Both (Steps step (And.left rest)) (And.right rest)
      | None =>
        let shallow := explodeNone number ex fits
        match sp: split number with
          | Some split2 =>
            let rest := reduceSound budget split2 final done (omega [splitHeight number split2 sp, And.left shallow])
            let step: reduceStep (leaves 0 number) = Some (leaves 0 split2) := rewrite And.right shallow, splitSome number split2 sp in rfl
            Both (Steps step (And.left rest)) (And.right rest)
          | None =>
            let step: reduceStep (leaves 0 number) = None := rewrite And.right shallow, splitNone number sp in rfl
            rewrite <- Option.someInjective _ final done in Both (Reduced step) (Both (And.left shallow) sp)
