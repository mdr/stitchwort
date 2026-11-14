--| Day 6 as the puzzle states it: every fish is listed by its timer, and a
--| day changes each fish on the list and adds the new ones at the end. The
--| proofs (Proofs/) show the program counts the fish this list has, for
--| every input and every number of days.

namespace Aoc.Year2021.Day06.Spec
import Std (List, Nat)

--| One fish's timer the next day: down by one, or back to 6 from 0.
def nextTimer (timer: Nat): Nat := if timer == 0 then 6 else timer - 1

--| A day: each fish's timer changes, and each fish that was at 0 adds a new
--| fish at 8 to the end of the list.
def nextDay (fish: List Nat): List Nat := fish.map nextTimer ++ List.replicate (fish.count (== 0)) 8

--| The list of every fish after `days` days.
def afterDays (days: Nat) (fish: List Nat): List Nat := Nat.iterate days nextDay fish

--| The answer: how many fish there are after `days` days (80 for part 1,
--| 256 for part 2).
def fishCount (days: Nat) (fish: List Nat): Nat := (afterDays days fish).length
