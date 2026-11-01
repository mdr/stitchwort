-- Element counts from pair counts. A step keeps the first element
-- (`stepsKeepFirst`); every other element is the second of the pair it
-- ends, so an element's count is whether the first element is it plus the
-- pairs that end with it (`countByPairs`), which the program's counts
-- give (`elementCountQuantity`).

namespace Aoc.Year2021.Day14.Proofs
import Aoc.Year2021.Day14 (..)
import Aoc.Year2021.Day14.Spec (..)
import Std (Bool, Eq, Exists, List, Map, Nat, Void)

-- A step keeps the first element...
theorem stepKeepsFirst (rules: List Rule) (a: Char) (rest: List Char): ∃ (tail: List Char) => step rules (Cons a rest) = Cons a tail :=
  match rest with
    | Nil => Witness Nil rfl
    | Cons b more => Witness (List.append (between rules a b) (step rules (Cons b more))) rfl

-- ...and so do any number of steps.
theorem stepsKeepFirst (rules: List Rule): (steps: Nat) → (a: Char) → (rest: List Char) →
    ∃ (tail: List Char) => Nat.iterate steps (step rules) (Cons a rest) = Cons a tail
  | Zero, a, rest => Witness rest rfl
  | Succ steps, a, rest =>
    match stepKeepsFirst rules a rest with
      | Witness tail e => rewrite e in stepsKeepFirst rules steps a tail

-- Steps leave an empty polymer empty.
theorem stepsEmpty (rules: List Rule): (steps: Nat) → Nat.iterate steps (step rules) Nil = Nil
  | Zero => rfl
  | Succ steps => stepsEmpty rules steps

-- An element's count: the first element, if it is that one, and the
-- pairs that end with it.
theorem countByPairs (c: Char) (a: Char): (rest: List Char) →
    List.count (Cons a rest) (== c) = Bool.toNat (a == c) + List.sumBy (List.zipWithNext (Cons a rest)) (pair => Bool.toNat (pair.snd == c))
  | Nil => omega [List.countCons Nil a (== c)]
  | Cons b more =>
    omega [
      List.countCons (Cons b more) a (== c),
      List.sumByCons (List.zipWithNext (Cons b more)) (a, b) (pair => Bool.toNat (pair.snd == c)),
      countByPairs c b more
    ]

-- The program's element count is a weighted sum of the counts...
theorem elementCountWeight (first: Char) (counts: PairCounts) (c: Char):
    elementCount first counts c = Bool.toNat (first == c) + weight counts (pair => Bool.toNat (pair.snd == c)) :=
  let each :=
    List.sumByCong (Map.toList counts) (entry => if entry.fst.snd == c then entry.snd else 0) (entry => entry.snd * Bool.toNat (entry.fst.snd == c))
      (entry => cases)
  omega [each]

-- ...so it is the element's count in the polymer the counts stand for.
theorem elementCountQuantity (first: Char) (tail: List Char) (counts: PairCounts) (represents: Represents counts (Cons first tail)) (c: Char):
    elementCount first counts c = quantity (Cons first tail) c :=
  omega [elementCountWeight first counts c, represents (pair => Bool.toNat (pair.snd == c)), countByPairs c first tail]
