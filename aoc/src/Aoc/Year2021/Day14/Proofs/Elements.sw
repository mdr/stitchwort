--| Element counts from pair counts. A step keeps the first element
--| (`stepsKeepFirst`); every other element is the second of the pair it
--| ends, so an element's count is whether the first element is it plus the
--| pairs that end with it (`countByPairs`), which the program's counts
--| give (`elementCountQuantity`).

namespace Aoc.Year2021.Day14.Proofs
import Aoc.Year2021.Day14 (..)
import Aoc.Year2021.Day14.Spec (..)
import Std (Bool, Eq, Exists, List, Map, Nat, Void)

--| A step keeps the first element...
theorem stepKeepsFirst ∀ (rules: List Rule) (a: Char) (rest: List Char): ∃ (tail: List Char) => step rules [a, ..rest] = [a, ..tail] :=
  match rest with
    | [] => Witness [] rfl
    | [b, ..more] => Witness (List.append (between rules a b) (step rules [b, ..more])) rfl

--| ...and so do any number of steps.
theorem stepsKeepFirst ∀ (rules: List Rule) (steps: Nat) (a: Char) (rest: List Char):
    ∃ (tail: List Char) => Nat.iterate steps (step rules) [a, ..rest] = [a, ..tail] := match steps with
      | Zero => Witness rest rfl
      | Succ steps =>
        match stepKeepsFirst rules a rest with
          | Witness tail e => rewrite e in stepsKeepFirst rules steps a tail

--| Steps leave an empty polymer empty.
theorem stepsEmpty ∀ (rules: List Rule) (steps: Nat): Nat.iterate steps (step rules) [] = [] := match steps with
  | Zero => rfl
  | Succ steps => stepsEmpty rules steps

--| An element's count: the first element, if it is that one, and the
--| pairs that end with it.
theorem countByPairs ∀ (c: Char) (a: Char) (rest: List Char):
    List.count [a, ..rest] (== c) = Bool.toNat (a == c) + List.sumBy (pairsOf [a, ..rest]) (pair => Bool.toNat (pair.second == c)) :=
  match rest with
    | [] => omega [List.countCons [] a (== c)]
    | [b, ..more] =>
      omega [
        List.countCons [b, ..more] a (== c),
        List.sumByCons (pairsOf [b, ..more]) { first = a, second = b } (pair => Bool.toNat (pair.second == c)),
        countByPairs c b more
      ]

--| The program's element count is a weighted sum of the counts...
theorem elementCountWeight ∀ (first: Char) (counts: PairCounts) (c: Char):
    elementCount first counts c = Bool.toNat (first == c) + weight counts (pair => Bool.toNat (pair.second == c)) :=
  let each :=
    List.sumByCong (Map.toList counts) (entry => if entry.fst.second == c then entry.snd else 0) (entry => entry.snd * Bool.toNat (entry.fst.second == c))
      (entry => cases)
  omega [each]

--| ...so it is the element's count in the polymer the counts stand for.
theorem elementCountQuantity ∀ (first: Char) (tail: List Char) (counts: PairCounts) (represents: Represents counts [first, ..tail]) (c: Char):
    elementCount first counts c = quantity [first, ..tail] c :=
  omega [elementCountWeight first counts c, represents (pair => Bool.toNat (pair.second == c)), countByPairs c first tail]
