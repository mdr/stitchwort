--| Part 2: the run the sliding window finds is a contiguous run of at
--| least two numbers summing to the target, and the weakness is its
--| smallest plus its largest.

namespace Aoc.Year2020.Day09.Proofs
import Aoc.Year2020.Day09 (..)
import Aoc.Year2020.Day09.Spec (Contiguous, Weakness)
import Std (Bool, DecEq, Eq, List, Nat, NonEmptyList, Option, Void)

--| The window is `count` numbers from `start` on, summing to `sum`, and
--| `rest` is what follows it.
theorem runFromSound ∀ (numbers: List Nat) (target: Nat) (run front: List Nat) (count sum: Nat)
    (rest: List Nat) (start: Nat)
    (at: front = numbers.drop start)
    (fits: count ≤ front.length)
    (after: rest = front.drop count)
    (total: sum = (front.take count).sum)
    (found: runFrom target front count sum rest = Some run):
    Contiguous numbers run ∧ 2 ≤ run.length ∧ run.sum = target
    decreasing front.length + rest.length
:=
  rewrite runFrom.unfold target front count sum rest at found then
    match c: target < sum with
      | True =>
        match front with
          | [first, ..later] =>
            match count with
              | Zero =>
                let empty: sum = 0 := total
                Void.impossible (arithmetic)
              | Succ k =>
                runFromSound numbers target run later k
                  (sum - first)
                  rest
                  (start + 1)
                  (rewrite List.dropAdd start 1 numbers, <- at then byComputing)
                  (arithmetic)
                  after
                  (arithmetic [List.sumCons first (later.take k)])
                  found
      | False =>
        match e: sum == target && 2 <= count with
          | True =>
            let runIs: front.take count = run := Option.someInjective found
            Both
              (Witness start (Witness count (rewrite <- runIs, at then byComputing)))
              (Both
                (rewrite <- runIs, List.lengthTake front count fits then arithmetic)
                (rewrite <- runIs then arithmetic))
          | False =>
            match rest with
              | [next, ..more] =>
                let (Both taken below) := List.takeOfDropCons front count next more after.flipped
                runFromSound numbers target run front
                  (count + 1)
                  (sum + next)
                  more
                  start
                  at
                  (arithmetic)
                  (rewrite List.dropAdd count 1 front, <- after then byComputing)
                  (rewrite taken, List.sumAppend (front.take count) [next] then arithmetic)
                  found

theorem weaknessRules ∀ (data: XmasData) (invalid answer: Nat)
    (found: data.weakness invalid = Some answer):
    Weakness data.numbers invalid answer :=
  match r: data.runSumming invalid with
    | Some run =>
      match n: run.nonEmpty with
        | Some ordered =>
          let same := List.toListOfNonEmpty run ordered n
          let (Both contiguous (Both long total)) :=
            runFromSound data.numbers invalid run data.numbers 0 0 data.numbers 0 byComputing
              (arithmetic)
              byComputing
              byComputing
              r
          Witness run
            (Both contiguous
              (Both long
                (Both total
                  (Witness ordered.minimum
                    (Witness ordered.maximum
                      (Both
                        (rewrite <- same then NonEmptyList.minimumMem ordered)
                        (Both
                          (rewrite <- same then NonEmptyList.maximumMem ordered)
                          (Both
                            (x member =>
                              let listed: NonEmptyList.Mem x ordered := rewrite <- same at member then member
                              Both (NonEmptyList.minimumLe ordered x listed) (NonEmptyList.maximumLe ordered x listed))
                            (Option.someInjective found).flipped))))))))
