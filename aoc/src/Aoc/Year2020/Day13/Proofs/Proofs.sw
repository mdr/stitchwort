--| Day 13 proved, about the input text: for every input the parser reads,
--| the input is the notes written out (Parse.sw); part 1's answer, when
--| there is one, is the spec's, and there is one whenever a bus is in
--| service (Part1.sw); part 2's answer is the spec's earliest time, and
--| there is none exactly when no time lines up (Part2.sw, with the sieve
--| in Sieve.sw). No ID needs to be coprime with the others.

namespace Aoc.Year2020.Day13.Proofs
import Aoc.Year2020.Day13 (..)
import Aoc.Year2020.Day13 (Spec)
import Std (Eq, Fail, Iff, List, Option, Result, Text, Void)

def Written (input: Text) (notes: Notes): Prop :=
  ∃ (read: List Char) => ∃ (ending: List Char) =>
    input.toList = read ++ ending ∧ Spec.NotesWritten read notes ∧ ending.all (char => char == '\n' ∨ char == '\r') = True

theorem parsedPositive ∀ (input: Text) (notes: Notes) (parsed: Fail.toResult (() => parseNotes input) = Ok notes): IdsPositive notes :=
  match parseWritten input notes parsed with
    | Witness read (Witness ending (Both split (Both written ended))) => writtenPositive read notes written

theorem part1Correct ∀ (input: Text) (notes: Notes) (parsed: Fail.toResult (() => parseNotes input) = Ok notes) (answer: Nat)
    (found: notes.earliestBus = Some answer): Written input notes ∧ Spec.Part1 notes answer :=
  Both (parseWritten input notes parsed) (part1Rules notes answer (parsedPositive input notes parsed) found)

--| Part 1 answers exactly when some bus is in service. (Part 1 names the
--| program's answer; if two buses left at the same first minute, the spec
--| would name the other's answer too.)
theorem part1AnswersIff ∀ (input: Text) (notes: Notes) (parsed: Fail.toResult (() => parseNotes input) = Ok notes):
    notes.earliestBus ≠ None ↔ ∃ (id: Nat) => Listed id ∈ notes.schedule := {
  forward = answers =>
    match e: notes.earliestBus with
      | None => Void.exfalso (answers rfl)
      | Some answer =>
        match part1Rules notes answer (parsedPositive input notes parsed) e with
          | Witness id (Witness departure (Both listed rest)) => Witness id listed,
  backward = (Witness id listed) => none => part1Answers notes id listed none
}

theorem part2Correct ∀ (input: Text) (notes: Notes) (parsed: Fail.toResult (() => parseNotes input) = Ok notes) (answer: Nat)
    (found: notes.earliestLineUp = Some answer): Written input notes ∧ Spec.Part2 notes answer :=
  Both (parseWritten input notes parsed) (part2Rules notes answer (parsedPositive input notes parsed) found)

--| Part 2's answer is the spec's earliest time, and no other number is.
theorem part2Exactly ∀ (input: Text) (notes: Notes) (parsed: Fail.toResult (() => parseNotes input) = Ok notes) (answer: Nat):
    notes.earliestLineUp = Some answer ↔ Spec.Part2 notes answer :=
  let positive := parsedPositive input notes parsed
  {
    forward = found => part2Rules notes answer positive found,
    backward = (Both lined earliest) =>
      match e: notes.earliestLineUp with
        | None => Void.exfalso (part2Never notes positive e answer lined)
        | Some other =>
          match part2Rules notes other positive e with
            | Both otherLined otherEarliest =>
              Eq.cong Some (omega [earliest other otherLined, otherEarliest answer lined])
  }

--| Part 2 finds no time exactly when no time lines up.
theorem part2NoneIff ∀ (input: Text) (notes: Notes) (parsed: Fail.toResult (() => parseNotes input) = Ok notes):
    notes.earliestLineUp = None ↔ (∀ (time: Nat) => ¬Spec.LinedUp notes.schedule time) :=
  let positive := parsedPositive input notes parsed
  {
    forward = none time lined => part2Never notes positive none time lined,
    backward = never =>
      match e: notes.earliestLineUp with
        | None => rfl
        | Some answer => Void.exfalso (never answer (And.left (part2Rules notes answer positive e)))
  }
