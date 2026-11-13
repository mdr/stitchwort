--| Day 7 proved, for every input: both answers are the least total fuel
--| over every position (Spec/). No hypotheses.

namespace Aoc.Year2021.Day07.Proofs
import Aoc.Year2021.Day07 (..)
import Aoc.Year2021.Day07.Spec (..)
import Std (And, Eq, Exists, List, Nat, Option, Void)

--| The answers.

theorem part1Correct (crabs: List Nat): Part1Answer crabs (solvePart1 crabs) :=
  leastFuelMeetsSpec stepFuel part1Fuel (n => rfl) (a b le => le) crabs

theorem part2Correct (crabs: List Nat): Part2Answer crabs (solvePart2 crabs) :=
  leastFuelMeetsSpec growingFuel part2Fuel (n => Eq.sym (Nat.sumBetweenCorrect 1 n)) growingFuelMonotone crabs

--| The spec's least fuel is one number.
theorem leastFuelUnique (fuel: Nat → Nat) (crabs: List Nat) (a: Nat) (b: Nat) (first: LeastFuel fuel crabs a) (second: LeastFuel fuel crabs b): a = b :=
  match first, second with
    | Both (Witness p costsA) lowA, Both (Witness q costsB) lowB => omega [lowA q, lowB p]

--| For any fuel that never falls as the crab goes further, and the spec's
--| fuel giving the same, the program's least is the spec's.
theorem leastFuelMeetsSpec (fuel: Nat → Nat) (specFuel: Nat → Nat) (same: ∀ (n: Nat) => specFuel n = fuel n)
    (monotone: ∀ (a b: Nat) => a ≤ b → fuel a ≤ fuel b) (crabs: List Nat): LeastFuel specFuel crabs (leastFuel fuel crabs) :=
  match programLeast fuel monotone crabs with
    | Both (Witness p costs) lowest =>
      Both (Witness p (rewrite totalFuelIs fuel specFuel same crabs p in costs))
        (position => rewrite totalFuelIs fuel specFuel same crabs position in lowest position)

--| The program's least: some position costs it, and every position costs at
--| least it.
theorem programLeast (fuel: Nat → Nat) (monotone: ∀ (a b: Nat) => a ≤ b → fuel a ≤ fuel b) (crabs: List Nat):
    (exists (position: Nat) => fuelAt fuel crabs position = leastFuel fuel crabs) ∧ (∀ (position: Nat) => leastFuel fuel crabs ≤ fuelAt fuel crabs position) :=
  let scan := List.range (leftmost crabs) (rightmost crabs + 1)
  let totals := scan.map (fuelAt fuel crabs)
  let first := ((List.memRange (leftmost crabs) (leftmost crabs) (rightmost crabs + 1)).backward (Both (Nat.leRefl (leftmost crabs)) (Nat.leLessSucc (leftmost crabs) (rightmost crabs) (leftmostLeRightmost crabs))))
  match List.minimumExists totals (fuelAt fuel crabs (leftmost crabs)) (List.memMap scan (leftmost crabs) first (fuelAt fuel crabs)) with
    | Witness least found =>
      rewrite leastFuelIs fuel crabs least found in
        match List.minimumSome totals least found with
          | Both member lowest =>
            Both
              (match List.memMapElim (fuelAt fuel crabs) least scan member with
                | Witness p (Both _ costs) => Witness p costs)
              (position =>
                match scannedNoWorse fuel monotone crabs position with
                  | Witness s (Both scanned noWorse) =>
                    Nat.leTrans least (fuelAt fuel crabs s) (fuelAt fuel crabs position)
                      (lowest (fuelAt fuel crabs s) (List.memMap scan s scanned (fuelAt fuel crabs))) noWorse)

--| The program's answer is the least of the scan's totals.
theorem leastFuelIs (fuel: Nat → Nat) (crabs: List Nat) (least: Nat)
    (found: (List.range (leftmost crabs) (rightmost crabs + 1) |> .map (fuelAt fuel crabs) |> .minimum) = Some least): leastFuel fuel crabs = least :=
  rewrite found in rfl

--| The spec's total fuel is the program's, for the same fuel.
theorem totalFuelIs (fuel: Nat → Nat) (specFuel: Nat → Nat) (same: ∀ (n: Nat) => specFuel n = fuel n) (crabs: List Nat) (position: Nat):
    totalFuel specFuel crabs position = fuelAt fuel crabs position := match crabs with
      | [] => rfl
      | [crab, ..rest] =>
        calc totalFuel specFuel [crab, ..rest] position
          _ = specFuel (distance crab position) + totalFuel specFuel rest position := List.sumCons (specFuel (distance crab position)) (rest.map (c => specFuel (distance c position)))
          _ = fuel (Nat.absDiff crab position) + fuelAt fuel rest position := rewrite same (distance crab position), distanceIs crab position, totalFuelIs fuel specFuel same rest position in rfl
          _ = fuelAt fuel [crab, ..rest] position := Eq.sym (List.sumByCons rest crab (c => fuel (Nat.absDiff c position)))

--| The spec's distance is `Nat.absDiff`.
theorem distanceIs (crab: Nat) (position: Nat): distance crab position = crab.absDiff position := cases

--| Part 2's fuel never falls as the crab goes further.
theorem growingFuelMonotone (a: Nat) (b: Nat) (le: a ≤ b): growingFuel a ≤ growingFuel b :=
  Nat.leDivOfMulLe ((a + (a * a)) / 2) (b + (b * b)) 2
    (omega [Nat.divMulLe (a + (a * a)) 2, Nat.leMulRight a b a le, Nat.leMulRight a b b le, Nat.mulComm b a])

--| Folding `Nat.min` gives at most the start and each element.
theorem foldMinLe (xs: List Nat) (start: Nat): xs.foldLeft start Nat.min ≤ start := match xs with
  | [] => Nat.leRefl start
  | [x, ..rest] =>
    Nat.leTrans (rest.foldLeft (Nat.min start x) Nat.min) (Nat.min start x) start (foldMinLe rest (Nat.min start x)) (Nat.minLeLeft start x)

theorem foldMinLeMember (xs: List Nat) (start x: Nat) (h: x ∈ xs): xs.foldLeft start Nat.min ≤ x := match xs, h with
  | [], member => Void.exfalso member
  | [y, ..rest], Inl same =>
    rewrite <- same in Nat.leTrans (rest.foldLeft (Nat.min start y) Nat.min) (Nat.min start y) y (foldMinLe rest (Nat.min start y)) (Nat.minLeRight start y)
  | [y, ..rest], Inr member => foldMinLeMember rest (Nat.min start y) x member

--| The scan's ends hold every crab between them.
theorem rightmostGe (crabs: List Nat) (crab: Nat) (member: crab ∈ crabs): crab ≤ rightmost crabs := List.leFoldMax crabs crab 0 member

theorem leftmostLe (crabs: List Nat) (crab: Nat) (member: crab ∈ crabs): leftmost crabs ≤ crab :=
  foldMinLeMember crabs (rightmost crabs) crab member

theorem leftmostLeRightmost (crabs: List Nat): leftmost crabs ≤ rightmost crabs := foldMinLe crabs (rightmost crabs)

--| A sum over a list is at most another when each term is.
theorem sumByLeMember (f: Nat → Nat) (g: Nat → Nat) (xs: List Nat) (each: ∀ (x: Nat) => x ∈ xs → g x ≤ f x): xs.sumBy g ≤ xs.sumBy f :=
  match xs with
    | [] => Nat.leRefl 0
    | [x, ..rest] =>
      rewrite List.sumByCons rest x g, List.sumByCons rest x f in
        omega [each x (Inl rfl), sumByLeMember f g rest (y member => each y (Inr member))]

--| Moving further from every crab costs at least as much fuel.
theorem fuelAtLe (fuel: Nat → Nat) (monotone: ∀ (a b: Nat) => a ≤ b → fuel a ≤ fuel b) (crabs: List Nat) (near: Nat) (far: Nat)
    (further: ∀ (crab: Nat) => crab ∈ crabs → crab.absDiff near ≤ crab.absDiff far): fuelAt fuel crabs near ≤ fuelAt fuel crabs far :=
  sumByLeMember (crab => fuel (Nat.absDiff crab far)) (crab => fuel (Nat.absDiff crab near)) crabs
    (crab member => monotone (Nat.absDiff crab near) (Nat.absDiff crab far) (further crab member))

--| Every position costs at least as much as the nearest one between the
--| leftmost crab and the rightmost.
theorem scannedNoWorse (fuel: Nat → Nat) (monotone: ∀ (a b: Nat) => a ≤ b → fuel a ≤ fuel b) (crabs: List Nat) (position: Nat):
    exists (scanned: Nat) => (scanned ∈ List.range (leftmost crabs) (rightmost crabs + 1)) ∧ fuelAt fuel crabs scanned ≤ fuelAt fuel crabs position :=
  let lo := leftmost crabs
  let hi := rightmost crabs
  let nearest := Nat.min (Nat.max position lo) hi
  let ordered := leftmostLeRightmost crabs
  Witness nearest
    (Both (((List.memRange nearest lo (hi + 1)).backward (Both omega (Nat.leLessSucc nearest hi omega))))
      (fuelAtLe fuel monotone crabs nearest position (crab member =>
        let above := leftmostLe crabs crab member
        let below := rightmostGe crabs crab member
        omega [(rfl: Nat.absDiff crab nearest = (crab - nearest) + (nearest - crab)), (rfl: Nat.absDiff crab position = (crab - position) + (position - crab))])))
