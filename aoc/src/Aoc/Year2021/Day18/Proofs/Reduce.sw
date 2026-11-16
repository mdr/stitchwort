--| Reducing: when `reduce` finishes within its budget, its steps are the
--| spec's steps on the leaves, and what it gives is reduced.

namespace Aoc.Year2021.Day18.Proofs
import Aoc.Year2021.Day18 (..)
import Aoc.Year2021.Day18.Spec (Leaf, ReducesTo, leaves, reduceStep)
import Std (Eq, Exists, Nat, Option, Void)

--| Starting from a number with nothing inside more than five pairs, as the
--| pair of two reduced numbers is: if `reduce` finishes within its budget,
--| the spec's reduction of the number's leaves ends at the leaves of what it
--| gives, which has nothing inside more than four pairs and nothing to
--| split.
theorem reduceSound ∀ (budget: Nat) (number final: Number)
    (none: reduce budget number = Some final)
    (fits: height number ≤ 5):
    ReducesTo (leaves 0 number) (leaves 0 final) ∧ height final ≤ 4 ∧ split final = None :=
  match budget, none with
    | 0, none => (Option.noneNotSome final none).impossible
    | Succ budget, done =>
      match ex: explode 0 number with
        | Some exploded =>
          let rest := reduceSound budget exploded.number final done (arithmetic [explodeHeight 0 number exploded ex])
          let step: reduceStep (leaves 0 number) = Some (leaves 0 exploded.number) :=
            rewrite explodeSome number exploded ex fits
          Both (Steps step rest.left) rest.right
        | None =>
          let shallow := explodeNone number ex fits
          match sp: split number with
            | Some split2 =>
              let rest := reduceSound budget split2 final done (arithmetic [splitHeight number split2 sp, shallow.left])
              let step: reduceStep (leaves 0 number) = Some (leaves 0 split2) :=
                rewrite And.right shallow, splitSome number split2 sp
              Both (Steps step rest.left) rest.right
            | None =>
              let step: reduceStep (leaves 0 number) = None := rewrite And.right shallow, splitNone number sp
              rewrite <- Option.someInjective done then Both (Reduced step) (Both shallow.left sp)

--| One step of `reduce`, by what it found.
theorem reduceExplodes ∀ (budget: Nat) (number: Number) (exploded: Explosion)
    (ex: explode 0 number = Some exploded):
    reduce (Succ budget) number = reduce budget exploded.number :=
  rewrite ex

theorem reduceSplits ∀ (budget: Nat) (number split2: Number)
    (ex: explode 0 number = None)
    (sp: split number = Some split2):
    reduce (Succ budget) number = reduce budget split2 :=
  rewrite ex, sp

theorem reduceStops ∀ (budget: Nat) (number: Number)
    (ex: explode 0 number = None)
    (sp: split number = None):
    reduce (Succ budget) number = Some number :=
  rewrite ex, sp

--| The budget is the only gap: whenever the spec's reduction of a number's
--| leaves ends (the number nested at most five pairs deep), a large enough
--| budget lets `reduce` finish, and it finishes there.
theorem reduceComplete ∀ (final: List Leaf):
    ∀ (start: List Leaf) => ReducesTo start final
      → ∀ (number: Number) => leaves 0 number = start
        → height number ≤ 5
        → ∃ (budget: Nat) => ∃ (result: Number) => reduce budget number = Some result ∧ leaves 0 result = final
  | start, Reduced done, number, is, fits =>
    match ex: explode 0 number with
      | Some exploded =>
        let step: reduceStep (leaves 0 number) = Some (leaves 0 exploded.number) :=
          rewrite explodeSome number exploded ex fits
        Void.impossible (Option.someNotNone _ (Eq.trans step.flipped (rewrite is then done)))
      | None =>
        let shallow := explodeNone number ex fits
        match sp: split number with
          | Some split2 =>
            let step: reduceStep (leaves 0 number) = Some (leaves 0 split2) :=
              rewrite And.right shallow, splitSome number split2 sp
            Void.impossible (Option.someNotNone _ (Eq.trans step.flipped (rewrite is then done)))
          | None => Witness 1 (Witness number (Both (reduceStops 0 number ex sp) is))
  | start, Steps [next := next] step rest, number, is, fits =>
    match ex: explode 0 number with
      | Some exploded =>
        let mine: reduceStep (leaves 0 number) = Some (leaves 0 exploded.number) :=
          rewrite explodeSome number exploded ex fits
        let same := Option.someInjective (Eq.trans mine.flipped (rewrite is then step))
        match reduceComplete final next rest exploded.number same (arithmetic [explodeHeight 0 number exploded ex]) with
          | Witness budget (Witness result (Both ran ends)) =>
            Witness
              (Succ budget)
              (Witness result (Both (rewrite reduceExplodes budget number exploded ex then ran) ends))
      | None =>
        let shallow := explodeNone number ex fits
        match sp: split number with
          | Some split2 =>
            let mine: reduceStep (leaves 0 number) = Some (leaves 0 split2) :=
              rewrite And.right shallow, splitSome number split2 sp
            let same := Option.someInjective (Eq.trans mine.flipped (rewrite is then step))
            match reduceComplete final next rest split2 same
              (arithmetic [splitHeight number split2 sp, shallow.left]) with
              | Witness budget (Witness result (Both ran ends)) =>
                Witness
                  (Succ budget)
                  (Witness result (Both (rewrite reduceSplits budget number split2 ex sp then ran) ends))
          | None =>
            let mine: reduceStep (leaves 0 number) = None := rewrite And.right shallow, splitNone number sp
            Void.impossible (Option.noneNotSome _ (Eq.trans mine.flipped (rewrite is then step)))
