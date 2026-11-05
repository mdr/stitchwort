--| The parser reads exactly the puzzle's format: "Each passport is
--| represented as a sequence of key:value pairs separated by spaces or
--| newlines. Passports are separated by blank lines." If `parsePassports`
--| reads `input` as `passports`, the input is the passports written out, in
--| order, each field as its key's three letters, a colon and its value,
--| nothing dropped, added or changed, then any line breaks.

namespace Aoc.Year2020.Day04.Proofs
import Aoc.Year2020.Day04 (..)
import Std (Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Text)

def FieldWritten (read: List Char) (field: Field): Prop :=
  read = field.key.code.toList ++ [':'] ++ field.value.toList ∧ field.value.toList ≠ [] ∧ field.value.toList.all isValueChar = True

--| "Separated by spaces or newlines."
def FieldBreak (read: List Char) (u: ()): Prop := read = [' '] ∨ Parse.LineBreak read

-- The `∃ fields` goes when stage 4 makes `Passport.fields` a `NonEmptyList` (SW-1346).
def PassportWritten (read: List Char) (passport: Passport): Prop :=
  ∃ (fields: NonEmptyList Field) => Parse.SepBy FieldWritten FieldBreak read fields ∧ passport.fields = fields.toList

theorem readsField: Parse.Reads field FieldWritten :=
  Parse.readsThen _ _ _ _ (Parse.readsPickBy keys Key.code) (keyRead key (Both member keyIs) =>
    Parse.readsThen _ _ _ _ (Parse.readsChar ':') (colonRead u colon =>
      Parse.readsThen _ _ _ _ (Parse.readsTakeWhile1 "a value" isValueChar) (valueRead value (Both nonEmpty (Both chars made)) =>
        Parse.readsDone { key, value } _
          (rewrite made in Both (rewrite keyIs, colon, List.appendNil valueRead in rfl) (Both nonEmpty chars)))))

theorem readsFieldBreak: Parse.Reads fieldBreak FieldBreak :=
  Parse.readsOneOf FieldBreak [() => Parse.char ' ', Parse.newline]
    (Both (Parse.readsWeaken _ _ _ (Parse.readsChar ' ') (read u same => Inl same))
      (Both (Parse.readsWeaken _ _ _ Parse.readsNewline (read u breaks => Inr breaks)) ()))

theorem readsPassport: Parse.Reads passport PassportWritten :=
  Parse.readsThen _ _ _ _ (Parse.readsSepBy1 field fieldBreak _ _ readsField readsFieldBreak) (fieldsRead fields written =>
    Parse.readsDone { fields = fields.toList } _ (rewrite List.appendNil fieldsRead in Witness fields (Both written rfl)))

theorem parseWritten (input: Text) (passports: List Passport) (parsed: Fail.toResult (() => parsePassports input) = Ok passports):
    ∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending
        ∧ (∃ (listed: NonEmptyList Passport) => Parse.SepBy PassportWritten (read u => Parse.BlankLine read) read listed ∧ passports = listed.toList)
        ∧ ending.all (char => char == '\n' ∨ char == '\r') = True :=
  Parse.allReads input (() => Parse.sections passport |> .toList) _ passports parsed
    (Parse.readsMap (() => Parse.sections passport) NonEmptyList.toList _ (Parse.readsSections passport _ readsPassport))

--| The first passport is written too: the input starts with it, field by
--| field as in `PassportWritten`.
theorem firstPassportWritten (input: Text) (first: Passport) (rest: List Passport) (parsed: Fail.toResult (() => parsePassports input) = Ok [first, ..rest]):
    ∃ (read: List Char) => ∃ (after: List Char) => input.toList = read ++ after ∧ PassportWritten read first :=
  match parseWritten input [first, ..rest] parsed with
    | Witness read (Witness ending (Both text (Both (Witness listed (Both (Witness firstRead (Witness restRead (Witness value (Both split (Both written (Both isHead each))))))
        same)) done))) =>
      let firstIs: first = listed.head := List.consInjectiveHead first listed.head rest listed.tail same
      Witness firstRead (Witness (restRead ++ ending)
        (Both (rewrite text, split, List.appendAssoc firstRead restRead ending in rfl) (rewrite firstIs, <- isHead in written)))
