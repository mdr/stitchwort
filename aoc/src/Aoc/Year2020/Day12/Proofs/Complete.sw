--| The converse of `Parse.sw`: every line written out as `F10` is read as
--| its instruction, and so is a whole input of such lines.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day12.Proofs
import Aoc.Common (Heading)
import Aoc.Year2020.Day12 (..)
import Aoc.Year2020.Day12.Spec (ActionWritten, InstructionWritten)
import Std (Bool, Char, Eq, Exists, Fail, List, Parse, Result, Text, Void)

theorem runsAs ∀ (read: List Char) (a b: Instruction)
    (same: a = b)
    (runs: Parse.Runs instruction read [] a):
    Parse.Runs instruction read [] b :=
  rewrite same at runs in runs

--| `action` on the letter of an action, whatever follows.
theorem runsAction ∀ (letter: Char) (chosen: Action)
    (written: ActionWritten letter chosen) (rest: List Char):
    Parse.Runs action [letter] rest chosen :=
  match chosen with
    | Move North =>
      rewrite written in
        Parse.runsPick [] "N"
          (Move North)
          [
            (("S", Move South)),
            (("E", Move East)),
            (("W", Move West)),
            (("L", Turn Left)),
            (("R", Turn Right)),
            (("F", Forward))
          ]
          rest
          rfl
    | Move South =>
      rewrite written in
        Parse.runsPick
          [(("N", Move North))]
          "S"
          (Move South)
          [(("E", Move East)), (("W", Move West)), (("L", Turn Left)), (("R", Turn Right)), (("F", Forward))]
          rest
          (Both rfl rfl)
    | Move East =>
      rewrite written in
        Parse.runsPick
          [(("N", Move North)), (("S", Move South))]
          "E"
          (Move East)
          [(("W", Move West)), (("L", Turn Left)), (("R", Turn Right)), (("F", Forward))]
          rest
          (Both rfl (Both rfl rfl))
    | Move West =>
      rewrite written in
        Parse.runsPick
          [(("N", Move North)), (("S", Move South)), (("E", Move East))]
          "W"
          (Move West)
          [(("L", Turn Left)), (("R", Turn Right)), (("F", Forward))]
          rest
          (Both rfl (Both rfl (Both rfl rfl)))
    | Turn Left =>
      rewrite written in
        Parse.runsPick
          [(("N", Move North)), (("S", Move South)), (("E", Move East)), (("W", Move West))]
          "L"
          (Turn Left)
          [(("R", Turn Right)), (("F", Forward))]
          rest
          (Both rfl (Both rfl (Both rfl (Both rfl rfl))))
    | Turn Right =>
      rewrite written in
        Parse.runsPick
          [(("N", Move North)), (("S", Move South)), (("E", Move East)), (("W", Move West)), (("L", Turn Left))]
          "R"
          (Turn Right)
          [(("F", Forward))]
          rest
          (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl rfl)))))
    | Forward =>
      rewrite written in
        Parse.runsPick
          [
            (("N", Move North)),
            (("S", Move South)),
            (("E", Move East)),
            (("W", Move West)),
            (("L", Turn Left)),
            (("R", Turn Right))
          ]
          "F"
          Forward
          []
          rest
          (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl rfl))))))

theorem turnFails ∀ (item: Instruction) (digits: List Char)
    (turn: item.action.isTurn = True → item.value % 90 = 0)
    (decimal: item.value = Parse.digitsValue digits)
    (fails: (item.action.isTurn && Parse.digitsValue digits % 90 != 0) = True):
    Void :=
  let Both isTurn bad := fails
  let zero: Parse.digitsValue digits % 90 = 0 := rewrite decimal at turn in turn isTurn
  rewrite zero at bad in cases

theorem instructionEta ∀ (item: Instruction): { action = item.action, value = item.value } = item := match item with
  | { action, value } => rfl

--| `instruction` on a line as `InstructionWritten` has it.
theorem runsInstruction ∀ (read: List Char) (item: Instruction)
    (written: InstructionWritten read item):
    Parse.Runs instruction read [] item :=
  match written with
    | Witness letter
        (Witness digits (Both split (Both actionWritten (Both nonEmpty (Both allDigits (Both decimal turn)))))) =>
      let sameItem: { action = item.action, value = Parse.digitsValue digits } = item :=
        rewrite <- decimal in instructionEta item
      rewrite split in
        runsAs _ _ item sameItem
          (Parse.runsBind action _
            [letter]
            digits _
            []
            item.action _
            rfl
            (runsAction letter item.action actionWritten (digits ++ []))
            (Parse.runsBind Parse.nat _ digits [] _ []
              (Parse.digitsValue digits) _
              (Eq.sym (List.appendNil digits))
              (Parse.runsNat digits [] nonEmpty allDigits rfl)
              (Parse.runsIf
                (item.action.isTurn && Parse.digitsValue digits % 90 != 0) _ _
                []
                [] _
                (fails => Void.exfalso (turnFails item digits turn decimal fails))
                (ok => Parse.runsPure _ []))))

--| Input whose lines are instructions written out is read as the route of them.
theorem parseComplete ∀ (input: Text) (route: Route)
    (written: List.All2 InstructionWritten (input.lines.map Text.toList) route.instructions):
    Fail.toResult (() => parseRoute input) = Ok route :=
  rewrite Fail.toResultThen (() => Parse.eachLine input instruction) (instructions => ({ instructions }: Route)) in
    rewrite Parse.runsEachLine input instruction route.instructions (List.all2Weaken runsInstruction _ _ written) in
      match route with | { instructions } => rfl

--| A route is written by an input in at most one way, since the parser reads it as one.
theorem writtenUnique ∀ (input: Text) (a b: Route)
    (writtenA: List.All2 InstructionWritten (input.lines.map Text.toList) a.instructions)
    (writtenB: List.All2 InstructionWritten (input.lines.map Text.toList) b.instructions):
    a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
