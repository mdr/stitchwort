--| The parser reads exactly the puzzle's format: if `parseNotes` reads
--| `input`, the input is the notes written out, as `Spec.NotesWritten`
--| says, then any line breaks.

namespace Aoc.Year2020.Day16.Proofs
import Aoc.Year2020.Day16 (..)
import Aoc.Year2020.Day16.Spec (LineBreakWritten, NotesWritten, NumberWritten, RangeWritten, RuleWritten, TicketWritten)
import Std (Char, Fail, List, NonEmptyList, Parse, Text)

theorem readsRange: Parse.Reads range RangeWritten := Parse.readsThen Parse.readsNat (lowRead low lowNumber =>
  Parse.readsThen (Parse.readsChar '-') (dashRead u dash =>
    Parse.readsThen Parse.readsNat (highRead high highNumber =>
      Parse.readsDone
        { low, high } _
        (Witness lowRead
          (Witness highRead (Both (rewrite dash, List.appendNil highRead in rfl) (Both lowNumber highNumber)))))))

theorem readsRule: Parse.Reads rule RuleWritten := Parse.readsThen Parse.readsTakeWhile1 (nameRead field (Both named
  (Both chars made)) =>
  Parse.readsThen (Parse.readsText ": ") (colonRead u colon =>
    Parse.readsThen readsRange (firstRead first firstWritten =>
      Parse.readsThen (Parse.readsText " or ") (orRead u2 or =>
        Parse.readsThen readsRange (secondRead second secondWritten =>
          Parse.readsDone
            { field, first, second } _
            (rewrite made in
              Witness firstRead
                (Witness secondRead
                  (Both
                    (rewrite colon, or, List.appendNil secondRead in rfl)
                    (Both named (Both chars (Both firstWritten secondWritten)))))))))))

theorem readsTicket: Parse.Reads ticket TicketWritten :=
  Parse.readsThen
    (Parse.readsSepBy1 Parse.nat (() => Parse.char ',') NumberWritten _ Parse.readsNat (Parse.readsChar ','))
    (valuesRead values written =>
      Parse.readsDone
        { values = values.toList } _
        (Witness values (Both (rewrite List.appendNil valuesRead in written) rfl)))

theorem readsNotes: Parse.Reads notes NotesWritten :=
  Parse.readsThen (Parse.readsLines rule RuleWritten readsRule) (rulesRead rules rulesWritten =>
    Parse.readsThen Parse.readsBlankLine (blank1 u1 blankFirst =>
      Parse.readsThen (Parse.readsText "your ticket:") (yourRead u2 yourHeading =>
        Parse.readsThen Parse.readsNewline (break1 u3 breakFirst =>
          Parse.readsThen readsTicket (yoursRead yours yoursWritten =>
            Parse.readsThen Parse.readsBlankLine (blank2 u4 blankSecond =>
              Parse.readsThen (Parse.readsText "nearby tickets:") (nearbyHeadingRead u5 nearbyHeading =>
                Parse.readsThen Parse.readsNewline (break2 u6 breakSecond =>
                  Parse.readsThen
                    (Parse.readsLines ticket TicketWritten readsTicket)
                    (nearbyRead nearby nearbyWritten =>
                      Parse.readsDone
                        { rules = rules.toList, yours, nearby = nearby.toList } _
                        (Witness rulesRead
                          (Witness yoursRead
                            (Witness nearbyRead
                              (Witness blank1
                                (Witness break1
                                  (Witness blank2
                                    (Witness break2
                                      (Both
                                        (rewrite yourHeading, nearbyHeading, List.appendNil nearbyRead in rfl)
                                        (Both
                                          (Witness rules (Both rulesWritten rfl))
                                          (Both blankFirst
                                            (Both breakFirst
                                              (Both yoursWritten
                                                (Both blankSecond
                                                  (Both breakSecond
                                                    (Witness nearby (Both nearbyWritten rfl)))))))))))))))))))))))))

theorem parseWritten ∀ (input: Text) (notes: Notes)
    (parsed: Fail.toResult (() => parseNotes input) = Ok notes):
    ∃ (read: List Char) => ∃ (ending: List Char) => input.toList = read ++ ending
      ∧ NotesWritten read notes
      ∧ ending.all (char => char == '\n' ∨ char == '\r') = True :=
  Parse.allReads input Aoc.Year2020.Day16.notes NotesWritten notes parsed readsNotes
