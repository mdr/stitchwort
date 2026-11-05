--| Part 2: the accumulator the program reports is that of the boot code
--| with one `jmp` or `nop` repaired, run until it terminates.

namespace Aoc.Year2020.Day08.Proofs
import Aoc.Year2020.Day08 (..)
import Aoc.Year2020.Day08 (Spec)
import Std (Bool, DecEq, Eq, Fail, Int, List, Map, Nat, Option, Result, Void)

theorem findMapFound (f: a → Option b): (xs: List a) → (y: b) → xs.findMap f = Some y → ∃ (x: a) => x ∈ xs ∧ f x = Some y
  | [], y, found => Void.exfalso (Option.noneNotSome y found)
  | [x, ..xs], y, found =>
    match c: f x with
      | Some z => Witness x (Both (Inl rfl) (rewrite c in found))
      | None =>
        match findMapFound f xs y found with
          | Witness later (Both member made) => Witness later (Both (Inr member) made)

--| `xs` with the element at `index` replaced by `x` (Scala's `updated`).
def replaceAt: (xs: List a) → (index: Nat) → (x: a) → List a
  | [], index, x => []
  | [y, ..ys], Zero, x => [x, ..ys]
  | [y, ..ys], Succ index, x => [y, ..replaceAt ys index x]

theorem lengthReplaceAt: (xs: List a) → (index: Nat) → (x: a) → (replaceAt xs index x).length = xs.length
  | [], index, x => rfl
  | [y, ..ys], Zero, x => rfl
  | [y, ..ys], Succ index, x => Eq.cong Succ (lengthReplaceAt ys index x)

theorem getReplaceAt: (xs: List a) → (index: Nat) → (x: a) → index < xs.length → (replaceAt xs index x).get index = Some x
  | [], index, x, below => Void.exfalso (Bool.falseNotTrue below)
  | [y, ..ys], Zero, x, below => rfl
  | [y, ..ys], Succ index, x, below => getReplaceAt ys index x (omega)

theorem getReplaceAtOther: (xs: List a) → (index: Nat) → (x: a) → (other: Nat) → other ≠ index → (replaceAt xs index x).get other = xs.get other
  | [], index, x, other, differ => rfl
  | [y, ..ys], Zero, x, Zero, differ => Void.exfalso (differ rfl)
  | [y, ..ys], Zero, x, Succ other, differ => rfl
  | [y, ..ys], Succ index, x, Zero, differ => rfl
  | [y, ..ys], Succ index, x, Succ other, differ => getReplaceAtOther ys index x other (same => differ (Eq.cong Succ same))

def Program.replaceAt (program: Program) (index: Nat) (instruction: Instruction): Program :=
  { instructions = replaceAt program.instructions index instruction }

theorem repairedHolds (program: Program) (index: Nat) (instruction: Instruction) (below: index < program.instructions.length):
    Holds ({ program.code | byPosition = program.code.byPosition.insert index instruction }) (program.replaceAt index instruction) :=
  Both (Eq.sym (lengthReplaceAt program.instructions index instruction))
    (position =>
      match d: position == index with
        | True =>
          rewrite DecEq.sound d, Map.getInsert index instruction program.code.byPosition in
            Eq.sym (getReplaceAt program.instructions index instruction below)
        | False =>
          let differ: position ≠ index := same => DecEq.soundFalse position index d same
          rewrite Map.getInsertOther index instruction position differ program.code.byPosition, getReplaceAtOther program.instructions index instruction position differ in
            getByPosition program.instructions position)

theorem repairIs (program: Program) (index: Nat) (instruction: Instruction) (repaired: Instruction) (listed: program.instructions.get index = Some instruction)
    (swapped: instruction.repaired = Some repaired):
    Spec.Repair program index (program.replaceAt index repaired) :=
  let below := getLength program.instructions index instruction listed
  let placed: (program.replaceAt index repaired).instructions.get index = Some repaired := getReplaceAt program.instructions index repaired below
  Both (lengthReplaceAt program.instructions index repaired)
    (Both (other differ => getReplaceAtOther program.instructions index repaired other differ)
      (match instruction with
        | { operation = Acc, argument } => Void.exfalso (Option.noneNotSome repaired swapped)
        | { operation = Jmp, argument } =>
          Witness argument (Inl (Both listed (rewrite Option.someInjective swapped in placed)))
        | { operation = Nop, argument } =>
          Witness argument (Inr (Both listed (rewrite Option.someInjective swapped in placed)))))

--| Repairing `instruction` at `position` makes the program terminate with
--| `answer`, as the spec says.
theorem repairTerminates (program: Program) (position: Nat) (instruction: Instruction) (answer: Int)
    (listed: program.instructions.get position = Some instruction) (made: program.code.terminatesRepaired position instruction = Some answer):
    ∃ (repaired: Program) => Spec.Repair program position repaired ∧ Spec.Terminates repaired answer :=
  match r: instruction.repaired with
    | None => Void.exfalso (Option.noneNotSome answer made)
    | Some repaired =>
      let fixed := program.replaceAt position repaired
      let holds := repairedHolds program position repaired (getLength program.instructions position instruction listed)
      match runRuns fixed ({ program.code | byPosition = program.code.byPosition.insert position repaired }) holds with
        | Witness positions (Witness last (Both runs (Both distinct ended))) =>
          match o: ({ program.code | byPosition = program.code.byPosition.insert position repaired }).run with
            | Terminates accumulator =>
              let (Both atEnd same) := ended
              let found: accumulator = answer := Option.someInjective made
              Witness fixed (Both (repairIs program position instruction repaired listed r)
                (Witness positions (Witness last (Both runs (Both atEnd (rewrite <- found in same))))))
            | Loops accumulator => Void.exfalso (Option.noneNotSome answer made)
            | JumpsAway accumulator => Void.exfalso (Option.noneNotSome answer made)

theorem part2Rules (program: Program) (answer: Int) (solved: Fail.toResult (() => solvePart2 program) = Ok answer): Spec.Part2 program answer :=
  let ran: Fail.toResult (() => (program.instructions.withIndex.findMap (((position, instruction)) => program.code.terminatesRepaired position instruction)).orFail "no repair of one jmp or nop makes the boot code terminate") = Ok answer :=
    solved
  match f: program.instructions.withIndex.findMap (((position, instruction)) => program.code.terminatesRepaired position instruction) with
    | None => Void.exfalso (Result.errNotOk ran)
    | Some found =>
      match findMapFound (((position, instruction)) => program.code.terminatesRepaired position instruction) program.instructions.withIndex found f with
        | Witness (position, instruction) (Both member made) =>
          let listed := (List.memWithIndex program.instructions position instruction).forward member
          Witness position (rewrite <- Result.okInjective ran in repairTerminates program position instruction found listed made)
