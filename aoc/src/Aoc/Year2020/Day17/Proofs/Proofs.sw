--| Day 17 proved, about the input text: for every input the parser reads,
--| each line is its row of the slice (Parse.sw), and in any number of
--| dimensions the program's count is the spec's answer, and the only one
--| (a cycle cube by cube in Neighbours.sw and Cycle.sw, the start and the
--| six cycles in Boot.sw). Part 1 is 3 dimensions and part 2 is 4.

namespace Aoc.Year2020.Day17.Proofs
import Aoc.Year2020.Day17 (..)
import Aoc.Year2020.Day17 (Spec)
import Std (Eq, Exists, Fail, List, Nat, Result, Set, Text)

theorem startsUnique ∀ (slice: Slice) (dimensions: Nat) (one: Set Cube) (other: Set Cube)
    (starts: Spec.Starts slice dimensions one) (alsoStarts: Spec.Starts slice dimensions other): one = other :=
  Set.extIff one other (cube => {
    forward = there => (alsoStarts cube).backward ((starts cube).forward there),
    backward = there => (starts cube).backward ((alsoStarts cube).forward there)
  })

theorem cyclesUnique ∀ (count: Nat) (start one other: Set Cube)
    (same: Spec.Cycles count start one) (alsoSame: Spec.Cycles count start other): one = other :=
  match count, same, alsoSame with
    | Zero, same, alsoSame => Eq.trans same (Eq.sym alsoSame)
    | Succ more, Witness next (Both cycle rest), Witness alsoNext (Both alsoCycle alsoRest) =>
      let nextSame: next = alsoNext := Set.ext next alsoNext (cube => Eq.trans (cycle cube) (Eq.sym (alsoCycle cube)))
      cyclesUnique more next one other rest (rewrite nextSame in alsoRest)

--| The spec's answer is the program's and no other.
theorem answerExactly ∀ (slice: Slice) (dimensions: Nat) (answer: Nat):
    Spec.Answer slice dimensions answer ↔ answer = (slice.pocket dimensions |> .boot |> .activeCount) := {
  forward = (Witness start (Witness final (Both starts (Both cycled counted)))) =>
    let startSame := startsUnique slice dimensions start (slice.pocket dimensions).active starts (startsPocket slice dimensions)
    let finalSame := cyclesUnique 6 (slice.pocket dimensions).active final (slice.pocket dimensions).boot.active
      (rewrite <- startSame in cycled) (cycles 6 (slice.pocket dimensions))
    Eq.trans counted (Eq.cong Set.size finalSame),
  backward = same =>
    Witness (slice.pocket dimensions).active (Witness (slice.pocket dimensions).boot.active
      (Both (startsPocket slice dimensions) (Both (cycles 6 (slice.pocket dimensions)) same)))
}

theorem correct ∀ (input: Text) (slice: Slice) (parsed: Fail.toResult (() => parseSlice input) = Ok slice) (dimensions: Nat) (answer: Nat):
    (List.All2 Spec.RowWritten (input.lines.map Text.toList) slice.grid.rows ∧ slice.grid.Rectangle)
      ∧ (Spec.Answer slice dimensions answer ↔ answer = (slice.pocket dimensions |> .boot |> .activeCount)) :=
  Both (parseWritten input slice parsed) (answerExactly slice dimensions answer)
