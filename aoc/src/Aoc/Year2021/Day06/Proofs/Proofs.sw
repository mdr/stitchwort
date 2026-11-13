--| Day 6 proved, for every list of timers of at most 8 and every number of
--| days: counting the fish at each timer and moving the counts along a day at
--| a time (`fishAfter`) gives the length of the puzzle's list of every fish
--| (`fishCount`). The counts the program keeps are the counts of the puzzle's
--| list on every day (`iterateCounts`), and they add up to its length
--| (`totalCounts`). Timers above 8 would fall outside the counts; no fish
--| starts above 8, and the parser rejects one.

namespace Aoc.Year2021.Day06.Proofs
import Aoc.Year2021.Day06 (..)
import Aoc.Year2021.Day06.Spec (..)
import Std (Bool, List, Nat)

--| Every timer is at most 8.
def Bounded (fish: List Nat): Prop := List.All (t => t ≤ 8) fish

--| Copies of one element: all or none of them count.
theorem countReplicate (x: Nat) (p: Nat → Bool) (n: Nat): List.count (List.replicate n x) p = n * Bool.toNat (p x) :=
  match n with
    | Zero => rfl
    | Succ n => omega [List.countCons (List.replicate n x) x p, countReplicate x p n]

--| Counting with a predicate that, at each element, counts as two others
--| together.
theorem countSum [p: Nat → Bool] [q: Nat → Bool] [r: Nat → Bool] (each: ∀ (t: Nat) => Bool.toNat (p t) = Bool.toNat (q t) + Bool.toNat (r t))
    (fish: List Nat): fish.count p = fish.count q + fish.count r := match fish with
      | [] => rfl
      | [x, ..xs] => omega [List.countCons xs x p, List.countCons xs x q, List.countCons xs x r, each x, countSum each xs]

--| A day keeps every timer at most 8.
theorem nextTimerBounded (t: Nat) (bounded: t ≤ 8): nextTimer t ≤ 8 := cases

theorem replicateBounded (n: Nat): Bounded (List.replicate n 8) := match n with
  | Zero => Trivial
  | Succ n => Both rfl (replicateBounded n)

theorem nextDayBounded (fish: List Nat) (bounded: Bounded fish): Bounded (nextDay fish) :=
  List.allAppend (t => t ≤ 8) (List.map fish nextTimer) (List.replicate (List.count fish (== 0)) 8)
    (List.allMap fish (t => t ≤ 8) nextTimer (List.allImplies (t => t ≤ 8) (t => nextTimer t ≤ 8) nextTimerBounded fish bounded))
    (replicateBounded (List.count fish (== 0)))

--| The fish at `v` the next day: those whose timer goes to `v`, and the new
--| fish if `v` is 8.
theorem countNextDay (fish: List Nat) (v: Nat):
    (nextDay fish).count (== v) = fish.count (t => nextTimer t == v) + fish.count (== 0) * Bool.toNat (8 == v) :=
  omega [
    List.countAppend (List.map fish nextTimer) (List.replicate (List.count fish (== 0)) 8) (== v),
    List.countMap fish (== v) nextTimer,
    countReplicate 8 (== v) (List.count fish (== 0))
  ]

--| Away from 6, the fish at `v` the next day are those at `v + 1` today.
theorem nextTimerEq (v: Nat) (t: Nat) (not6: v ≠ 6): (nextTimer t == v) = (t == v + 1) := cases

theorem agedCount (v: Nat) (not6: v ≠ 6) (fish: List Nat): fish.count (t => nextTimer t == v) = fish.count (== v + 1) :=
  List.countCongMem _ _ _ (t _ => nextTimerEq v t not6)

--| The fish at 6 the next day are those at 7 and those at 0 today.
theorem agedSix (fish: List Nat): fish.count (t => nextTimer t == 6) = fish.count (== 7) + fish.count (== 0) :=
  countSum (t => cases) fish

--| No fish is at 9.
theorem noneAtNine (fish: List Nat) (bounded: Bounded fish): fish.count (== 9) = 0 :=
  List.countNone fish (== 9) (t member =>
    let small := List.allMem (t => t ≤ 8) t fish bounded member
    cases)

--| The counts of the puzzle's list the next day are the program's next day
--| of today's counts, timer by timer.
theorem countsNextDay (fish: List Nat) (bounded: Bounded fish):
    Counts.ofTimers (nextDay fish) = Counts.nextDay (Counts.ofTimers fish) :=
  Counts.ext (Counts.ofTimers (nextDay fish)) (Counts.nextDay (Counts.ofTimers fish))
    (omega [countNextDay fish 0, agedCount 0 omega fish])
    (omega [countNextDay fish 1, agedCount 1 omega fish])
    (omega [countNextDay fish 2, agedCount 2 omega fish])
    (omega [countNextDay fish 3, agedCount 3 omega fish])
    (omega [countNextDay fish 4, agedCount 4 omega fish])
    (omega [countNextDay fish 5, agedCount 5 omega fish])
    (omega [countNextDay fish 6, agedSix fish])
    (omega [countNextDay fish 7, agedCount 7 omega fish])
    (omega [countNextDay fish 8, agedCount 8 omega fish, noneAtNine fish bounded])

--| A timer of at most 8 is one of 0 to 8.
theorem oneTimer (x: Nat) (bounded: x ≤ 8):
    Bool.toNat (x == 0) + Bool.toNat (x == 1) + Bool.toNat (x == 2) + Bool.toNat (x == 3) + Bool.toNat (x == 4)
    + Bool.toNat (x == 5) + Bool.toNat (x == 6) + Bool.toNat (x == 7) + Bool.toNat (x == 8) = 1 := match x with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | 3 => rfl
      | 4 => rfl
      | 5 => rfl
      | 6 => rfl
      | 7 => rfl
      | 8 => rfl
      | Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ above)))))))) => omega

--| The counts add up to the number of fish.
theorem totalCounts (fish: List Nat) (bounded: Bounded fish): Counts.total (Counts.ofTimers fish) = fish.length :=
  match fish with
    | [] => rfl
    | [x, ..xs] =>
      omega [
        List.countCons xs x (== 0),
        List.countCons xs x (== 1),
        List.countCons xs x (== 2),
        List.countCons xs x (== 3),
        List.countCons xs x (== 4),
        List.countCons xs x (== 5),
        List.countCons xs x (== 6),
        List.countCons xs x (== 7),
        List.countCons xs x (== 8),
        oneTimer x bounded.left,
        totalCounts xs bounded.right
      ]

--| After any number of days, the program's counts are those of the
--| puzzle's list.
theorem iterateCounts (days: Nat) (fish: List Nat) (bounded: Bounded fish):
    Nat.iterate days Counts.nextDay (Counts.ofTimers fish) = Counts.ofTimers (afterDays days fish) := match days with
      | Zero => rfl
      | Succ days =>
        rewrite <- countsNextDay fish bounded in iterateCounts days (nextDay fish) (nextDayBounded fish bounded)

theorem afterDaysBounded (days: Nat) (fish: List Nat) (bounded: Bounded fish): Bounded (afterDays days fish) :=
  match days with
    | Zero => bounded
    | Succ days => afterDaysBounded days (nextDay fish) (nextDayBounded fish bounded)

--| The program's count is the puzzle's, for every number of days.
theorem fishAfterCorrect (days: Nat) (fish: List Nat) (bounded: fish.all (t => t ≤ 8) = True): fishAfter days fish = fishCount days fish :=
  let start := List.allToAll (t => t ≤ 8) fish bounded
  calc fishAfter days fish
    _ = Counts.total (Nat.iterate days Counts.nextDay (Counts.ofTimers fish))
    _ = Counts.total (Counts.ofTimers (afterDays days fish)) := rewrite iterateCounts days fish start
    _ = fishCount days fish := totalCounts (afterDays days fish) (afterDaysBounded days fish start)

--| Part 1 is the number of fish the puzzle's list has after 80 days, for
--| every list of timers of at most 8.
theorem part1Correct (fish: List Nat) (bounded: fish.all (t => t ≤ 8) = True): solvePart1 fish = fishCount 80 fish :=
  fishAfterCorrect 80 fish bounded

--| Part 2, after 256 days.
theorem part2Correct (fish: List Nat) (bounded: fish.all (t => t ≤ 8) = True): solvePart2 fish = fishCount 256 fish :=
  fishAfterCorrect 256 fish bounded
