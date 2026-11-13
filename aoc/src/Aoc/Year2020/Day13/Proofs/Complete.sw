--| The converse of `Parse.sw`: notes written out as the puzzle has them
--| (a time, a line break, comma-separated bus IDs and `x`s), then any line
--| breaks, are read as those notes.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day13.Proofs
import Aoc.Year2020.Day13 (..)
import Aoc.Year2020.Day13.Spec (NotesWritten, SlotWritten)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Text, Void)

theorem runsAsValue (p: () → {Parse} a) (read: List Char) (rest: List Char) (v: a) (w: a) (same: v = w) (runs: Parse.Runs p read rest v): Parse.Runs p read rest w :=
  rewrite same at runs in runs

theorem digitNotX (char: Char) (isDigit: Parse.isDigit char = True): (char == 'x') = False :=
  match e: char == 'x' with
    | False => rfl
    | True => cases

theorem declinesX (read: List Char) (after: List Char) (some: read ≠ []) (all: read.all Parse.isDigit = True):
    Parse.Declines (() => Parse.char 'x') (read ++ after) :=
  match read with
    | [] => Void.exfalso (some rfl)
    | [char, ..more] => Parse.declinesChar 'x' char (more ++ after) (digitNotX char (Bool.andLeft all))

--| `slot` on a bus ID or an `x`, before something that doesn't continue the digits.
theorem runsSlot (read: List Char) (slot2: Slot) (written: SlotWritten read slot2) (after: List Char) (stops: Parse.CannotStart Parse.isDigit after):
    Parse.Runs slot read after slot2 :=
  match slot2 with
    | OutOfService =>
      rewrite written in
        Parse.runsBind (() => Parse.optional (() => Parse.char 'x')) _ ['x'] [] ['x'] after (Some ()) OutOfService (Eq.sym (List.appendNil ['x']))
          (Parse.runsOptional (() => Parse.char 'x') ['x'] ([] ++ after) () (Parse.runsChar 'x' ([] ++ after)))
          (Parse.runsPure OutOfService after)
    | Listed id =>
      match written with
        | Both nonEmpty (Both allDigits (Both decimal notZero)) =>
          Parse.runsBind (() => Parse.optional (() => Parse.char 'x')) _ [] read read after None (Listed id) rfl
            (Parse.declinesRuns (() => Parse.char 'x') (read ++ after) (declinesX read after nonEmpty allDigits))
            (Parse.runsBind Parse.nat _ read [] read after (Parse.digitsValue read) (Listed id) (Eq.sym (List.appendNil read))
              (Parse.runsNatBefore read ([] ++ after) nonEmpty allDigits stops)
              (Parse.runsIf (Parse.digitsValue read == 0) _ _ [] after (Listed id)
                (zero => Void.exfalso (notZero (Eq.trans decimal zero.read)))
                (nonZero => runsAsValue (() => Listed (Parse.digitsValue read)) [] after _ _ (rewrite decimal in rfl) (Parse.runsPure (Listed (Parse.digitsValue read)) after))))

theorem notesEta (notes2: Notes): { earliest = notes2.earliest, schedule = notes2.schedule } = notes2 :=
  match notes2 with
    | { earliest, schedule } => rfl

--| `notes` on notes written out, before nothing but line breaks.
theorem runsNotes (read: List Char) (notes2: Notes) (written: NotesWritten read notes2) (ending: List Char) (breaks: Parse.OnlyBreaks ending):
    Parse.Runs notes read ending notes2 :=
  match written with
    | Witness digits (Witness lineBreak (Witness entries (Witness slots (Both split (Both nonEmpty (Both allDigits (Both decimal (Both isBreak (Both listed same))))))))) =>
      match slots, listed, same with
        | { head, tail }, listed2, same2 =>
          let sameNotes: { earliest = Parse.digitsValue digits, schedule = (NonEmptyList.cons head tail).toList } = notes2 :=
            rewrite <- decimal, <- same2 in notesEta notes2
          rewrite split in
            runsAsValue notes _ ending _ notes2 sameNotes
              (Parse.runsBind Parse.nat _ digits (lineBreak ++ entries) _ ending (Parse.digitsValue digits) _ rfl
                (Parse.runsNatBefore digits ((lineBreak ++ entries) ++ ending) nonEmpty allDigits
                  (rewrite List.appendAssoc lineBreak entries ending in Parse.cannotStartAfterBreak Parse.isDigit rfl rfl lineBreak (entries ++ ending) isBreak))
                (Parse.runsBind Parse.newline _ lineBreak entries _ ending () _ rfl
                  (Parse.runsNewline lineBreak (entries ++ ending) isBreak)
                  (Parse.runsBind (() => Parse.sepBy1 slot (() => Parse.char ',')) _ entries [] _ ending (NonEmptyList.cons head tail) _ (Eq.sym (List.appendNil entries))
                    (Parse.runsSepBy1Of slot (() => Parse.char ',') SlotWritten (read2 u => read2 = [',']) (Parse.CannotStart Parse.isDigit) ending
                      (read2 v after ok stops => runsSlot read2 v ok after stops)
                      (read2 after u same3 => rewrite same3 in Parse.runsChar ',' after)
                      (read2 u same3 => rewrite same3 in List.consNotNil ',' [])
                      (read2 after u same3 => rewrite same3 in (char more found => rewrite <- List.consInjectiveHead _ _ _ _ found in rfl))
                      (Parse.cannotStartAtBreaks Parse.isDigit rfl rfl ending breaks)
                      (Parse.declinesSepStep slot (() => Parse.char ',') ending (Parse.declinesCharCannotStart ',' (char => char == ',') rfl ending (Parse.cannotStartAtBreaks (char => char == ',') rfl rfl ending breaks)))
                      entries head tail listed2)
                    (Parse.runsPure { earliest = Parse.digitsValue digits, schedule = (NonEmptyList.cons head tail).toList } ending))))

--| The soundness theorem's conclusion: the input is the notes written out,
--| then any line breaks.
def InputWritten (input: Text) (notes2: Notes): Prop :=
  ∃ (read: List Char) => ∃ (ending: List Char) =>
    input.toList = read ++ ending ∧ NotesWritten read notes2 ∧ ending.all (char => char == '\n' ∨ char == '\r') = True

--| Input that is notes written out is read as those notes.
theorem parseComplete (input: Text) (notes2: Notes) (written: InputWritten input notes2): Fail.toResult (() => parseNotes input) = Ok notes2 :=
  match written with
    | Witness read (Witness ending (Both split (Both notesWritten breaks))) =>
      Parse.runsAll input notes read ending notes2 split breaks (runsNotes read notes2 notesWritten ending breaks)

--| Soundness (`parseWritten`) is the converse: the input is written as at most one set of notes.
theorem writtenUnique (input: Text) (a: Notes) (b: Notes) (writtenA: InputWritten input a) (writtenB: InputWritten input b): a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
