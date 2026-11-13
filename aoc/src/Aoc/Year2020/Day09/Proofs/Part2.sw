--| Part 2: the run the sliding window finds is a contiguous run of at
--| least two numbers summing to the target, and the weakness is its
--| smallest plus its largest.

namespace Aoc.Year2020.Day09.Proofs
import Aoc.Year2020.Day09 (..)
import Aoc.Year2020.Day09.Spec (Contiguous, Weakness)
import Std (Bool, DecEq, Eq, List, Nat, NonEmptyList, Option, Void)

--| The window is `count` numbers from `start` on, summing to `sum`, and
--| `rest` is what follows it.
theorem runFromSound ∀ (numbers: List Nat) (target: Nat) (run: List Nat) (front: List Nat) (count: Nat) (sum: Nat) (rest: List Nat) (start: Nat)
    (at: front = numbers.drop start) (fits: count ≤ front.length) (after: rest = front.drop count) (total: sum = (front.take count).sum)
    (found: runFrom target front count sum rest = Some run):
    Contiguous numbers run ∧ 2 ≤ run.length ∧ run.sum = target
    decreasing front.length + rest.length
:=
  rewrite runFrom.unfold target front count sum rest at found in
    match c: target < sum with
      | True =>
        match front with
          | [first, ..later] =>
            match count with
              | Zero =>
                let empty: sum = 0 := total
                Void.exfalso (omega)
              | Succ k =>
                runFromSound numbers target run later k (sum - first) rest (start + 1)
                  (rewrite List.dropAdd start 1 numbers, <- at in rfl) (omega) after
                  (omega [List.sumCons first (later.take k)]) found
      | False =>
        match e: sum == target && 2 <= count with
          | True =>
            let runIs: front.take count = run := Option.someInjective found
            Both (Witness start (Witness count (rewrite <- runIs, at in rfl)))
              (Both (rewrite <- runIs, List.lengthTake front count fits in omega)
                (rewrite <- runIs in omega))
          | False =>
            match rest with
              | [next, ..more] =>
                let (Both taken below) := List.takeOfDropCons front count next more (Eq.sym after)
                runFromSound numbers target run front (count + 1) (sum + next) more start at (omega)
                  (rewrite List.dropAdd count 1 front, <- after in rfl)
                  (rewrite taken, List.sumAppend (front.take count) [next] in omega)
                  found

theorem weaknessRules ∀ (data: XmasData) (invalid: Nat) (answer: Nat) (found: data.weakness invalid = Some answer): Weakness data.numbers invalid answer :=
  match r: data.runSumming invalid with
    | Some run =>
      match n: run.nonEmpty with
        | Some ordered =>
          let same := List.toListOfNonEmpty run ordered n
          let (Both contiguous (Both long total)) :=
            runFromSound data.numbers invalid run data.numbers 0 0 data.numbers 0 rfl (omega) rfl rfl r
          Witness run (Both contiguous (Both long (Both total
            (Witness ordered.minimum (Witness ordered.maximum
              (Both (rewrite <- same in NonEmptyList.minimumMem ordered)
                (Both (rewrite <- same in NonEmptyList.maximumMem ordered)
                  (Both
                    (x member =>
                      let listed: NonEmptyList.Mem x ordered := rewrite <- same at member in member
                      Both (NonEmptyList.minimumLe ordered x listed) (NonEmptyList.maximumLe ordered x listed))
                    (Eq.sym (Option.someInjective found))))))))))
