--| Day 16 proved, about the input text: for every input the parser reads,
--| it is the notes written out (Parse.sw); part 1's answer is the spec's
--| scanning error rate (Part1.sw); and when the program gives a part 2
--| answer, it is the departure product under an order of the fields the
--| puzzle allows, and under every such order (Part2.sw, with the
--| candidates in Candidates.sw, the elimination in `Aoc.Common.Proofs`, and in
--| Unique.sw that no other order fits). Whether part 2 gives an answer
--| depends on the notes: the elimination can get stuck where more than one
--| order fits (the tests have one); on the puzzle's input it doesn't.

namespace Aoc.Year2020.Day16.Proofs
import Aoc.Year2020.Day16 (..)
import Aoc.Year2020.Day16 (Spec)
import Std (Eq, Fail, List, Option, Result, Text, Void)

theorem part1Correct (input: Text) (notes: Notes) (parsed: Fail.toResult (() => parseNotes input) = Ok notes):
    (∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ Spec.NotesWritten read notes ∧ ending.all (char => char == '\n' ∨ char == '\r') = True)
      ∧ Spec.Part1 notes notes.errorRate :=
  Both (parseWritten input notes parsed) (errorRateSpec notes)

--| Part 2's answer, when there is one, is the departure product under an
--| order of the fields the puzzle allows, and no other number is.
theorem part2Exactly (notes: Notes) (answer: Nat) (found: notes.departureProduct = Some answer) (other: Nat):
    Spec.Part2 notes other ↔ other = answer :=
  let valid := departureProductValid notes answer found
  match ordered: notes.fieldOrder with
    | Some order =>
      let product: answer = Spec.departureProduct order notes.yours.values :=
        Eq.trans (Eq.sym (Option.someInjective found)) (departureProductSpec order notes.yours.values)
      {
        forward = (Witness fitting (Both fits same)) => rewrite same, fieldOrderOnly notes order ordered fitting fits, <- product in rfl,
        backward = same => rewrite same in valid
      }

theorem part2Correct (input: Text) (notes: Notes) (parsed: Fail.toResult (() => parseNotes input) = Ok notes) (answer: Nat)
    (found: notes.departureProduct = Some answer):
    (∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ Spec.NotesWritten read notes ∧ ending.all (char => char == '\n' ∨ char == '\r') = True)
      ∧ Spec.Part2 notes answer ∧ (∀ (other: Nat) => Spec.Part2 notes other → other = answer) :=
  Both (parseWritten input notes parsed) (Both (departureProductValid notes answer found) (other => (part2Exactly notes answer found other).forward))
