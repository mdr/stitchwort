--| The answers: a sum `add` finishes is the spec's sum, so part 1's total
--| and part 2's largest magnitude are the spec's.

namespace Aoc.Year2021.Day18.Proofs
import Aoc.Year2021.Day18 (..)
import Aoc.Year2021.Day18.Spec (AddsUpTo, IsReduced, IsSum, Part1, Part2, leaves)
import Std (DecEq, Eq, Exists, List, Nat, Option, Void)

--| The program's magnitude is the puzzle's.
theorem magnitudeSame ∀ (number: Number): Aoc.Year2021.Day18.Spec.magnitude number = magnitude number :=
  match number with
    | Regular _ => rfl
    | Pair left right => rewrite magnitudeSame left, magnitudeSame right in rfl

--| A sum of two reduced numbers that `add` finishes is their sum, and is
--| reduced.
theorem addSound ∀ (x: Number) (y: Number) (sum: Number) (reducedX: IsReduced x) (reducedY: IsReduced y) (added: add x y = Some sum):
    IsSum x y sum ∧ IsReduced sum :=
  let reduced := reduceSound steps (Pair x y) sum added (omega [reducedHeight x reducedX, reducedHeight y reducedY])
  Both (And.left reduced) (leavesSmall 0 sum (And.left (And.right reduced)) (And.right (And.right reduced)))

theorem addAllSound ∀ (total: Number) (numbers: List Number) (final: Number) (reducedTotal: IsReduced total) (h: List.All IsReduced numbers) (done: addAll total numbers = Some final):
    AddsUpTo total numbers final := match numbers, h with
      | [], _ => rewrite <- Option.someInjective done in NothingAdded total
      | [next, ..rest], Both reducedNext reducedRest =>
        match a: add total next with
          | Some sum =>
            let added := addSound total next sum reducedTotal reducedNext a
            AddNext (And.left added) (addAllSound sum rest final (And.right added) reducedRest done)

--| Part 1: for reduced numbers, if the program's sums finish, its answer
--| is the spec's.
theorem part1Correct ∀ (numbers: List Number) (reduced: List.All IsReduced numbers) (answer: Nat) (solved: solvePart1 numbers = Some answer): Part1 numbers answer :=
  match numbers with
    | [first, ..rest] =>
      match a: addAll first rest with
        | Some final =>
          Witness first
            (Witness rest
              (Witness final
                (Both rfl
                  (Both (addAllSound first rest final (And.left reduced) (And.right reduced) a)
                    (rewrite magnitudeSame final in Option.someInjective solved)))))

--| Adding up is one number, so part 1's answer is one number.
theorem addsUpToUnique ∀ (final2: Number) (total: Number) (numbers: List Number) (final1: Number) (h: AddsUpTo total numbers final1) (h1: AddsUpTo total numbers final2): final1 = final2 :=
  match numbers, h, h1 with
    | [], NothingAdded _, NothingAdded _ => rfl
    | [next, ..rest], AddNext [total2 := sum1] first1 rest1, AddNext [total2 := sum2] first2 rest2 =>
      let same := sumUnique total next sum1 sum2 first1 first2
      addsUpToUnique final2 sum2 rest final1 (rewrite same at rest1 in rest1) rest2

theorem part1Unique ∀ (numbers: List Number) (answer1: Nat) (answer2: Nat) (first: Part1 numbers answer1) (second: Part1 numbers answer2): answer1 = answer2 :=
  match first, second with
    | Witness first1 (Witness rest1 (Witness final1 (Both split1 (Both adds1 magnitude1)))), Witness first2 (Witness rest2 (Witness final2 (Both split2 (Both adds2 magnitude2)))) =>
      let same := Eq.trans (Eq.sym split1) split2
      let firsts := Option.someInjective (Eq.cong (xs => List.get xs 0) same)
      let rests: rest1 = rest2 := Eq.cong (xs => List.drop xs 1) same
      let finals := addsUpToUnique final2 first2 rest2 final1 (rewrite firsts, rests at adds1 in adds1) adds2
      rewrite <- magnitude1, <- magnitude2, finals in rfl

--| Two numbers on different lines are a pair `orderedPairs` lists.
theorem memberPairs ∀ (numbers: List Number) (i: Nat) (j: Nat) (x: Number) (y: Number) (different: i ≠ j) (atI: numbers.get i = Some x) (atJ: numbers.get j = Some y):
    (x, y) ∈ orderedPairs numbers :=
  List.memFlatMapIntro _ (i, x) (x, y) numbers.withIndex ((List.memWithIndex numbers i x).backward atI)
    (List.memFilterMapIntro _ (j, y) (x, y) numbers.withIndex ((List.memWithIndex numbers j y).backward atJ) cases)

--| And every pair it lists is two numbers on different lines.
theorem pairsMember ∀ (numbers: List Number) (x: Number) (y: Number) (member: (x, y) ∈ orderedPairs numbers):
    ∃ (i: Nat) => ∃ (j: Nat) => i ≠ j ∧ numbers.get i = Some x ∧ numbers.get j = Some y :=
  match List.anyMember _ numbers.withIndex (List.memFlatMapElim _ (x, y) numbers.withIndex member) with
    | Witness (i, a) (Both atI inner) =>
      match List.anyMember _ numbers.withIndex (List.memFilterMapElim _ (x, y) numbers.withIndex inner) with
        | Witness (j, b) (Both atJ made) =>
          match e: i != j with
            | True =>
              let pairs := Option.someInjective made
              Witness i
                (Witness j
                  (Both (DecEq.neTrue e)
                    (Both (rewrite <- Eq.cong Std.Pair.fst pairs in (List.memWithIndex numbers i a).forward atI)
                      (rewrite <- Eq.cong Std.Pair.snd pairs in (List.memWithIndex numbers j b).forward atJ))))

--| What `sumMagnitudes` gives: each magnitude is that of a listed pair's sum,
--| and each listed pair's sum finished, its magnitude among them.
theorem sumMagnitudesSound ∀ (pairs: List (Number, Number)) (magnitudes: List Nat) (done: sumMagnitudes pairs = Some magnitudes): (∀ (k: Nat) => k ∈ magnitudes → ∃ (x: Number) => ∃ (y: Number) => ∃ (sum: Number) => (x, y) ∈ pairs ∧ add x y = Some sum ∧ magnitude sum = k)
    ∧ (∀ (x y: Number) => (x, y) ∈ pairs → ∃ (sum: Number) => add x y = Some sum ∧ magnitude sum ∈ magnitudes) :=
  match pairs with
    | [] => rewrite <- Option.someInjective done in Both (k member => Void.exfalso member) (x y member => Void.exfalso member)
    | [(x, y), ..rest] =>
      match a: add x y with
        | Some sum =>
          match m: sumMagnitudes rest with
            | Some others =>
              let later := sumMagnitudesSound rest others m
              rewrite <- Option.someInjective done in
                Both
                  (k member =>
                    match member with
                      | Inl here => Witness x (Witness y (Witness sum (Both (Inl rfl) (Both a here))))
                      | Inr there =>
                        match And.left later k there with
                          | Witness x2 (Witness y2 (Witness sum2 (Both inRest found))) => Witness x2 (Witness y2 (Witness sum2 (Both (Inr inRest) found))))
                  (x2 y2 member =>
                    match member with
                      | Inl here => rewrite <- Eq.cong Std.Pair.fst here, <- Eq.cong Std.Pair.snd here in Witness sum (Both a (Inl rfl))
                      | Inr there =>
                        match And.right later x2 y2 there with
                          | Witness sum2 (Both added inOthers) => Witness sum2 (Both added (Inr inOthers)))

--| Part 2: for reduced numbers, if the program's sums finish, its answer
--| is the spec's.
theorem part2Correct ∀ (numbers: List Number) (reduced: List.All IsReduced numbers) (answer: Nat) (solved: solvePart2 numbers = Some answer): Part2 numbers answer :=
  match s: sumMagnitudes (orderedPairs numbers) with
    | Some magnitudes =>
      let sound := sumMagnitudesSound (orderedPairs numbers) magnitudes s
      let most := List.maximumSome magnitudes answer solved
      Both
        (match And.left sound answer (And.left most) with
          | Witness x (Witness y (Witness sum (Both member (Both added size)))) =>
            match pairsMember numbers x y member with
              | Witness i (Witness j (Both different (Both atI atJ))) =>
                let reducedX := List.allMem IsReduced x numbers reduced (List.memOfGet numbers i x atI)
                let reducedY := List.allMem IsReduced y numbers reduced (List.memOfGet numbers j y atJ)
                Witness i
                  (Witness j
                    (Witness x
                      (Witness y
                        (Witness sum
                          (Both different (Both atI (Both atJ (Both (And.left (addSound x y sum reducedX reducedY added)) (rewrite magnitudeSame sum in size))))))))))
        (i j x y sum different atI atJ isSum =>
          let reducedX := List.allMem IsReduced x numbers reduced (List.memOfGet numbers i x atI)
          let reducedY := List.allMem IsReduced y numbers reduced (List.memOfGet numbers j y atJ)
          match And.right sound x y (memberPairs numbers i j x y different atI atJ) with
            | Witness made (Both added inList) =>
              let same := sumUnique x y made sum (And.left (addSound x y made reducedX reducedY added)) isSum
              rewrite magnitudeSame sum, <- same in And.right most (magnitude made) inList)
