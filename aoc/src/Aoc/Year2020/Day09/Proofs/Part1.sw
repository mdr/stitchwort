--| Part 1: the number the walk stops at is the first after the preamble
--| that isn't the sum of two different numbers before it.

namespace Aoc.Year2020.Day09.Proofs
import Aoc.Year2020.Day09 (..)
import Aoc.Year2020.Day09.Spec (Part1, SumOfTwo, previous)
import Std (Bool, Eq, List, Nat, Option, Void)

--| Each number the walk has passed was valid.
def ValidBefore (numbers: List Nat) (preamble position: Nat): Prop :=
  ∀ (earlier: Nat) => preamble ≤ earlier < position
    → ∀ (number: Nat) => numbers.get earlier = Some number → SumOfTwo (previous numbers preamble earlier) number

--| The walk is at `front`, the numbers from `start` on: the number it
--| checks is at `start + preamble`, after the numbers it checks it against.
theorem walkAt ∀ (numbers: List Nat) (preamble start: Nat) (front: List Nat)
    (at: front = numbers.drop start)
    (number: Nat) (later: List Nat)
    (ahead: front.drop preamble = [number, ..later]):
    numbers.get (start + preamble) = Some number ∧ previous numbers preamble (start + preamble) = front.take preamble :=
  let here: front.get preamble = Some number := rewrite <- Nat.addZero preamble, <- List.getDrop front preamble 0, ahead
  Both
    (rewrite <- List.getDrop numbers start preamble, <- at then here)
    (rewrite (arithmetic: start + preamble - preamble = start), <- at)

theorem walkSound ∀ (numbers: List Nat) (preamble answer: Nat) (front: List Nat) (start: Nat)
    (at: front = numbers.drop start)
    (valid: ValidBefore numbers preamble (start + preamble))
    (found: firstInvalidFrom preamble front = Some answer):
    Part1 numbers preamble answer :=
  match d: front.drop preamble with
    | [number, ..later] =>
      let (Both atPosition window) := walkAt numbers preamble start front at number later d
      match c: ({ numbers = front.take preamble }: Window).sumsTo number with
        | False =>
          let isAnswer: number = answer := Option.someInjective found
          Witness
            (start + preamble)
            (Both
              (arithmetic)
              (Both
                (rewrite <- isAnswer then atPosition)
                (Both
                  (rewrite window, <- isAnswer then
                    (sum =>
                      Bool.falseNotTrue
                        (Eq.trans c.flipped (sumsToComplete { numbers = front.take preamble } number sum))))
                  (earlier bounds => valid earlier (arithmetic)))))
        | True =>
          match front with
            | [first, ..rest] =>
              let moved: rest = numbers.drop (start + 1) := rewrite List.dropAdd start 1 numbers, <- at
              walkSound numbers preamble answer rest
                (start + 1)
                moved
                (earlier bounds n listed =>
                  if h: earlier < start + preamble then valid earlier (arithmetic) n listed
                  else
                    let same: earlier = start + preamble := arithmetic
                    let isNumber: n = number :=
                      Option.someInjective (rewrite same at listed then Eq.trans listed.flipped atPosition)
                    rewrite same, isNumber, window then
                      sumsToSound { numbers = [first, ..rest].take preamble } number c)
                found

theorem part1Rules ∀ (data: XmasData) (preamble answer: Nat)
    (found: data.firstInvalid preamble = Some answer):
    Part1 data.numbers preamble answer :=
  walkSound data.numbers preamble answer data.numbers 0 byComputing (earlier bounds => Void.impossible arithmetic) found

theorem walkComplete ∀ (numbers: List Nat) (preamble answer position: Nat)
    (listed: numbers.get position = Some answer)
    (notSum: ¬SumOfTwo (previous numbers preamble position) answer)
    (valid: ValidBefore numbers preamble position)
    (front: List Nat) (start: Nat)
    (at: front = numbers.drop start)
    (ahead: start + preamble ≤ position):
    firstInvalidFrom preamble front = Some answer
    decreasing position - start
:=
  match d: front.drop preamble with
    | [] =>
      let index: start + (preamble + (position - start - preamble)) = position := arithmetic
      let gone: numbers.get position = None :=
        rewrite <- index,
            <- List.getDrop numbers start (preamble + (position - start - preamble)),
            <- at,
            <- List.getDrop front preamble (position - start - preamble),
            d
      Void.impossible (Option.noneNotSome answer (Eq.trans gone.flipped listed))
    | [number, ..later] =>
      let (Both atPosition window) := walkAt numbers preamble start front at number later d
      if h: start + preamble = position then
        let isAnswer: number = answer := Option.someInjective (Eq.trans atPosition.flipped (rewrite h then listed))
        match c: ({ numbers = front.take preamble }: Window).sumsTo number with
          | True =>
            Void.impossible
              (notSum (rewrite <- h, window, <- isAnswer then sumsToSound { numbers = front.take preamble } number c))
          | False => rewrite isAnswer
      else
        let sums: SumOfTwo (front.take preamble) number :=
          rewrite <- window then valid (start + preamble) (arithmetic) number atPosition
        match c: ({ numbers = front.take preamble }: Window).sumsTo number with
          | False =>
            Void.impossible
              (Bool.falseNotTrue (Eq.trans c.flipped (sumsToComplete { numbers = front.take preamble } number sums)))
          | True =>
            match front with
              | [] =>
                Void.impossible (List.consNotNil number later (Eq.flipped (rewrite List.dropNil preamble at d then d)))
              | [first, ..rest] =>
                walkComplete numbers preamble answer position listed notSum valid rest
                  (start + 1)
                  (rewrite List.dropAdd start 1 numbers, <- at)
                  (arithmetic)

--| Whenever there is a first invalid number, part 1 finds it.
theorem part1Complete ∀ (data: XmasData) (preamble answer: Nat)
    (first: Part1 data.numbers preamble answer):
    data.firstInvalid preamble = Some answer :=
  let (Witness position (Both after (Both listed (Both notSum valid)))) := first
  walkComplete data.numbers preamble answer position listed notSum valid data.numbers 0 byComputing (arithmetic)

--| "The first number" is one number.
theorem part1Unique ∀ (numbers: List Nat) (preamble a b: Nat)
    (isA: Part1 numbers preamble a)
    (isB: Part1 numbers preamble b):
    a = b :=
  Option.someInjective
    (Eq.trans (Eq.flipped (part1Complete { numbers } preamble a isA)) (part1Complete { numbers } preamble b isB))
