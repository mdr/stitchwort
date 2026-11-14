--| The converse of `Parse.sw`: every line written out as an instruction is
--| read as that instruction, and so is a whole input of such lines.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day08.Proofs
import Aoc.Year2020.Day08 (..)
import Aoc.Year2020.Day08.Spec (ArgumentWritten, InstructionWritten, OperationWritten)
import Std (Eq, Fail, List, Parse, Result, Text)

theorem runsAsValue ∀ (p: () → {Parse} a) (read rest: List Char) (v w: a)
    (same: v = w)
    (runs: Parse.Runs p read rest v):
    Parse.Runs p read rest w :=
  rewrite same at runs in runs

theorem instructionEta ∀ (item: Instruction): { operation = item.operation, argument = item.argument } = item :=
  match item with | { operation, argument } => rfl

theorem programEta ∀ (program: Program): ({ instructions = program.instructions }: Program) = program :=
  match program with | { instructions } => rfl

theorem runsOperation ∀ (op: Operation) (read: List Char)
    (written: OperationWritten read op) (rest: List Char):
    Parse.Runs operation read rest op :=
  match op with
    | Acc => rewrite written in Parse.runsPick [] "acc" Acc [("jmp", Jmp), ("nop", Nop)] rest rfl
    | Jmp => rewrite written in Parse.runsPick [("acc", Acc)] "jmp" Jmp [("nop", Nop)] rest (Both rfl rfl)
    | Nop => rewrite written in Parse.runsPick [("acc", Acc), ("jmp", Jmp)] "nop" Nop [] rest (Both rfl (Both rfl rfl))

theorem runsInstruction ∀ (read: List Char) (item: Instruction)
    (written: InstructionWritten read item):
    Parse.Runs instruction read [] item :=
  match written with
    | Witness operationRead (Witness argumentRead (Both split (Both operationWritten argumentWritten))) =>
      rewrite split in
        runsAsValue instruction _ [] _ item
          (instructionEta item)
          (Parse.runsBind operation _ operationRead
            ([' ', ..argumentRead]) _
            []
            item.operation _
            rfl
            (runsOperation item.operation operationRead operationWritten _)
            (Parse.runsBind
              (() => Parse.char ' ') _
              [' ']
              argumentRead _
              []
              () _
              rfl
              (Parse.runsChar ' ' _)
              (Parse.runsBind argument _ argumentRead [] _ [] item.argument _
                (Eq.sym (List.appendNil _))
                (Parse.runsIntRead argumentRead item.argument argumentWritten [] rfl)
                (Parse.runsPure _ []))))

--| Input whose lines are instructions written out is read as that program.
theorem parseComplete ∀ (input: Text) (program: Program)
    (written: List.All2 InstructionWritten (input.lines.map Text.toList) program.instructions):
    Fail.toResult (() => parseProgram input) = Ok program :=
  let lines: Fail.toResult (() => Parse.eachLine input instruction) = Ok program.instructions :=
    Parse.runsEachLine input instruction program.instructions (List.all2Weaken runsInstruction _ _ written)
  rewrite Fail.toResultThen (() => Parse.eachLine input instruction) (instructions => ({ instructions }: Program)),
      lines,
      programEta program in
    rfl

--| A line is written as at most one instruction, because the parser reads it as one.
theorem writtenUnique ∀ (chars: List Char) (a b: Instruction)
    (writtenA: InstructionWritten chars a)
    (writtenB: InstructionWritten chars b):
    a = b :=
  Result.okInjective
    (Eq.trans
      (Eq.sym (Parse.runsRun instruction chars a (runsInstruction chars a writtenA)))
      (Parse.runsRun instruction chars b (runsInstruction chars b writtenB)))

--| ... and an input is written as at most one program.
theorem inputUnique ∀ (input: Text) (a b: Program)
    (writtenA: List.All2 InstructionWritten (input.lines.map Text.toList) a.instructions)
    (writtenB: List.All2 InstructionWritten (input.lines.map Text.toList) b.instructions):
    a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
