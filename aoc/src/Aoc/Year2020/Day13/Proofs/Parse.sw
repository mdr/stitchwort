--| The parser reads exactly the puzzle's format: if `parseNotes` reads
--| `input`, the input is the notes written out as `Spec.NotesWritten` says,
--| then any line breaks; so every bus ID it read is at least 1.

namespace Aoc.Year2020.Day13.Proofs
import Aoc.Year2020.Day13 (..)
import Aoc.Year2020.Day13.Spec (NotesWritten, SlotWritten)
import Std (Bool, Fail, List, NonEmptyList, Parse, Text, Void)

theorem readsSlot: Parse.Reads slot SlotWritten :=
  Parse.readsThen (Parse.readsOptional (Parse.readsChar 'x')) (optionRead found maybe =>
    match found with
      | Some u => Parse.readsDone OutOfService _ (rewrite List.appendNil optionRead in maybe)
      | None => Parse.readsThen Parse.readsNat (digits id (Both nonEmpty (Both allDigits decimal)) =>
        match zero: id == 0 with
          | True => Parse.readsFail "a bus ID is at least 1" _
          | False =>
            Parse.readsDone
              (Listed id) _
              (rewrite maybe, List.appendNil digits in
                Both nonEmpty
                  (Both allDigits (Both decimal (isZero => Bool.trueNotFalse (rewrite isZero at zero in zero)))))))

theorem readsNotes: Parse.Reads notes NotesWritten := Parse.readsThen Parse.readsNat (digits earliest (Both nonEmpty
  (Both allDigits decimal)) =>
  Parse.readsThen Parse.readsNewline (lineBreak u breaks =>
    Parse.readsThen
      (Parse.readsSepBy1 slot (() => Parse.char ',') SlotWritten _ readsSlot (Parse.readsChar ','))
      (entries slots listed =>
        Parse.readsDone
          { earliest, schedule = slots.toList } _
          (Witness digits
            (Witness lineBreak
              (Witness entries
                (Witness slots
                  (Both
                    (rewrite List.appendNil entries in rfl)
                    (Both nonEmpty (Both allDigits (Both decimal (Both breaks (Both listed rfl)))))))))))))

theorem parseWritten ∀ (input: Text) (notes: Notes)
    (parsed: Fail.toResult (() => parseNotes input) = Ok notes):
    ∃ (read: List Char) => ∃ (ending: List Char) => input.toList = read ++ ending
      ∧ NotesWritten read notes
      ∧ ending.all (char => char == '\n' ∨ char == '\r') = True :=
  Parse.allReads input Aoc.Year2020.Day13.notes NotesWritten notes parsed readsNotes

theorem eachSlotPositive ∀ (read: List Char) (slots: List Slot)
    (each: Parse.Each (Parse.Then (read (u: ()) => read = [',']) (u => SlotWritten)) read slots) (id: Nat)
    (member: Listed id ∈ slots):
    id ≠ 0 :=
  match slots with
    | [slot, ..rest] =>
      match each with
        | Witness first
            (Witness later
              (Both split
                (Both (Witness comma (Witness slotRead (Witness u (Both parts (Both isComma written))))) each))) =>
          match member with
            | Inl same => rewrite same at written in And.right (And.right (And.right written))
            | Inr inRest => eachSlotPositive later rest each id inRest

theorem writtenPositive ∀ (read: List Char) (notes: Notes) (written: NotesWritten read notes): IdsPositive notes :=
  match written with
    | Witness digits
        (Witness lineBreak
          (Witness entries
            (Witness slots
              (Both split (Both nonEmpty (Both allDigits (Both decimal (Both breaks (Both listed same))))))))) =>
      match listed with
        | Witness firstRead (Witness restRead (Witness head (Both parts (Both headWritten (Both isHead each))))) =>
          rewrite same in
            (id member =>
              match member with
                | Inl isFirst => rewrite isHead, isFirst at headWritten in And.right (And.right (And.right headWritten))
                | Inr inRest => eachSlotPositive restRead slots.tail each id inRest)
