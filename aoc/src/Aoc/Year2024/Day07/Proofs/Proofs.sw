-- Day 7 proved, for every list of equations: the program's backwards search
-- decides the puzzle's "some combination of operators, evaluated left to
-- right, gives the test value", so both parts are the total calibration
-- result, and part 2 is at least part 1. The forwards search the proofs go
-- through is in Search.sw, undoing each operator in Undo.sw.

namespace Aoc.Year2024.Day07.Proofs
import Aoc.Year2024.Day07 (..)
import Aoc.Year2024.Day07.Spec (..)
import Std (And, Bool, DecEq, Eq, List, Nat, Void)

-- Reversing onto `acc`, then back, is `acc` reversed onto the list.
theorem reverseOntoTwice: (xs: List a) → (acc: List a) → List.reverseOnto (List.reverseOnto xs acc) Nil = List.reverseOnto acc xs
  | Nil, acc => rfl
  | Cons x rest, acc => reverseOntoTwice rest (Cons x acc)

theorem reverseReverse (xs: List a): xs.reverse.reverse = xs := reverseOntoTwice xs Nil

-- Reversing onto `acc` is reversing, then appending `acc`.
theorem reverseOntoAppend: (xs: List a) → (acc: List a) → List.reverseOnto xs acc = (List.reverseOnto xs Nil).append acc
  | Nil, acc => rfl
  | Cons x rest, acc =>
    rewrite reverseOntoAppend rest (Cons x acc), reverseOntoAppend rest [x]
      in Eq.sym (List.appendAssoc (List.reverseOnto rest Nil) [x] acc)

-- Reversing a list puts its first element last.
theorem reverseCons (x: a) (xs: List a): (Cons x xs).reverse = xs.reverse.append [x] := reverseOntoAppend xs [x]

-- `left || right` is `left`, shifted left by the digits of `right`, plus
-- `right`.
theorem concatenateArithmetic (left: Nat) (right: Nat): concatenate left right = left * placeValue right + right :=
  rewrite Nat.fromDigitsAppend (Nat.digits left) (Nat.digits right), Nat.fromDigitsDigits left, Nat.fromDigitsDigits right in rfl

-- `right` is less than its place value.
theorem belowPlaceValue (right: Nat): right < placeValue right := Nat.ltPowTenDigits right

-- Concatenating never makes a smaller number, on either side.
theorem concatenateAtLeast (left: Nat) (right: Nat): And (left ≤ concatenate left right) (right ≤ concatenate left right) :=
  let shifted := Nat.leMulPos left (placeValue right) (Nat.powSuccPos 9 (Nat.digits right).length)
  rewrite concatenateArithmetic left right in Both (omega) (omega)

-- `v + last` is `target` when `last ≤ target` and `v` is `target - last`.
theorem undoAdd (last: Nat) (target: Nat) (v: Nat): (v + last == target) = (last <= target && v == target - last) :=
  Bool.eqOf (v + last == target) (last <= target && v == target - last)
    (matches =>
      let same := DecEq.sound (v + last) target matches
      Bool.andIntro (last <= target) (v == target - last) (omega) (rewrite (omega: v = target - last) in DecEq.refl (target - last)))
    (both =>
      let fits: last ≤ target := Bool.andLeft (last <= target) (v == target - last) both
      let same := DecEq.sound v (target - last) (Bool.andRight (last <= target) (v == target - last) both)
      rewrite (omega: v + last = target) in DecEq.refl target)

-- The backwards search over the numbers after `first`, last one first, is
-- the forwards search over them in order.
theorem canMakeReaches (operators: List Operator) (first: Nat): (reversed: List Nat) → (target: Nat) →
    canMake operators first target reversed = reaches operators first (== target) reversed.reverse
  | Nil, target => DecEq.eqComm target first
  | Cons last earlier, target =>
    let before := canMakeReaches operators first earlier
    rewrite reverseCons last earlier, reachesAppend operators (== target) last earlier.reverse first,
      reachesAny operators operators (operator value => combine operator value last == target) earlier.reverse first
      in List.anyCongMem operators _ _ (operator has =>
        let rest := earlier.reverse
        match operator with
          | Add =>
            rewrite before (target - last) in
              Eq.sym (Eq.trans (reachesCong operators _ (value => last <= target && value == target - last) (undoAdd last target) rest first)
                (reachesAnd operators (last <= target) (== target - last) rest first))
          | Multiply =>
            match last with
              | Zero =>
                Eq.sym (Eq.trans (reachesCong operators _ (value => (target == 0) && True)
                    (value => rewrite Nat.mulZero value, DecEq.eqComm 0 target in Eq.sym (Bool.andTrue (target == 0))) rest first)
                  (rewrite reachesAnd operators (target == 0) (value => True) rest first, reachesAnything operators Multiply has rest first
                    in Bool.andTrue (target == 0)))
              | Succ less =>
                rewrite before (target / Succ less) in
                  Eq.sym (Eq.trans (reachesCong operators _ (value => target % Succ less == 0 && value == target / Succ less)
                      (value => Eq.trans (Eq.cong (product => product == target) (Eq.sym (Nat.addZero (value * Succ less))))
                        (divModMatch (Succ less) 0 rfl value target)) rest first)
                    (reachesAnd operators (target % Succ less == 0) (== target / Succ less) rest first))
          | Concatenate =>
            let nonzero := placeValueNonzero last
            rewrite before (target / placeValue last) in
              Eq.sym (Eq.trans (reachesCong operators _ (value => target % placeValue last == last && value == target / placeValue last)
                  (value => rewrite concatenateArithmetic value last in divModMatch (placeValue last) last (belowPlaceValue last) value target) rest first)
                (reachesAnd operators (target % placeValue last == last) (== target / placeValue last) rest first)))

-- The program's check is the puzzle's "could possibly be true", for any
-- operators.
theorem couldBeTrueCorrect (operators: List Operator) (equation: Equation): couldBeTrue operators equation = couldPossiblyBeTrue operators equation :=
  match numbers: equation.numbers with
    | Nil => rfl
    | Cons first rest =>
      rewrite canMakeReaches operators first rest.reverse equation.testValue, reverseReverse rest
        in Eq.sym (combinationsReach operators (== equation.testValue) rest first)

-- So the program's total is the total calibration result.
theorem calibrationResultCorrect (operators: List Operator) (equations: List Equation):
    calibrationResult operators equations = totalCalibrationResult operators equations :=
  rewrite List.filterCongMem equations (couldBeTrue operators) (couldPossiblyBeTrue operators) (equation listed => couldBeTrueCorrect operators equation)
    in rfl

theorem part1Correct (equations: List Equation): solvePart1 equations = part1 equations := calibrationResultCorrect [Add, Multiply] equations

theorem part2Correct (equations: List Equation): solvePart2 equations = part2 equations :=
  calibrationResultCorrect [Add, Multiply, Concatenate] equations

-- More operators reach at least as much.
theorem reachesMore (fewer: List Operator) (more: List Operator) (included: (operator: Operator) → operator ∈ fewer → operator ∈ more)
    (wanted: Nat → Bool): (numbers: List Nat) → (start: Nat) → reaches fewer start wanted numbers = True → reaches more start wanted numbers = True
  | Nil, start, found => found
  | Cons number rest, start, found =>
    List.anyTrueElim fewer _ (reaches more start wanted (Cons number rest) = True) found (operator has reached =>
      List.anyOfMem more _ operator (reachesMore fewer more included wanted rest (combine operator start number) reached) (included operator has))

-- An equation that could be true with fewer operators could be with more.
theorem couldBeTrueMore (fewer: List Operator) (more: List Operator) (included: (operator: Operator) → operator ∈ fewer → operator ∈ more)
    (equation: Equation): couldBeTrue fewer equation = True → couldBeTrue more equation = True :=
  match numbers: equation.numbers with
    | Nil => holds => holds
    | Cons first rest =>
      rewrite canMakeReaches fewer first rest.reverse equation.testValue, canMakeReaches more first rest.reverse equation.testValue
        in reachesMore fewer more included (== equation.testValue) rest.reverse.reverse first

-- Keeping more of a list keeps at least as large a sum.
theorem sumFilterMore (keep1: a → Bool) (keep2: a → Bool) (value: a → Nat) (xs: List a) (included: (x: a) → keep1 x = True → keep2 x = True):
    (xs.filter keep1).sumBy value ≤ (xs.filter keep2).sumBy value :=
  rewrite List.sumByFilter xs value keep1, List.sumByFilter xs value keep2 in
    List.sumByLe xs (x => if keep2 x then value x else 0) (x => if keep1 x then value x else 0) (x =>
      match kept: keep1 x with
        | True => rewrite included x kept in Nat.leRefl (value x)
        | False => Nat.zeroLe (if keep2 x then value x else 0))

-- Part 2 adds an operator, so its total is at least part 1's.
theorem part2AtLeastPart1 (equations: List Equation): solvePart1 equations ≤ solvePart2 equations :=
  sumFilterMore (couldBeTrue [Add, Multiply]) (couldBeTrue [Add, Multiply, Concatenate]) (equation => equation.testValue) equations
    (couldBeTrueMore [Add, Multiply] [Add, Multiply, Concatenate] (operator has =>
      match has with
        | Inl same => Inl same
        | Inr later =>
          match later with
            | Inl same => Inr (Inl same)
            | Inr nothing => Void.exfalso nothing))
