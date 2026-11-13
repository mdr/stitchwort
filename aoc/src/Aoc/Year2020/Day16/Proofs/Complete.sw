--| The converse of `Parse.sw`: notes written out as the puzzle has them (the
--| rules, your ticket, the nearby tickets), then any line breaks, are read as
--| those notes.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day16.Proofs
import Aoc.Year2020.Day16 (..)
import Aoc.Year2020.Day16.Spec (LineBreakWritten, NotesWritten, NumberWritten, RangeWritten, RuleWritten, TicketWritten)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Text, Void)

theorem runsAsValue ∀ (p: () → {Parse} a) (read: List Char) (rest: List Char) (v: a) (w: a) (same: v = w) (runs: Parse.Runs p read rest v): Parse.Runs p read rest w :=
  rewrite same at runs in runs

--| What can follow a number in the notes' lists: not another digit, and not a comma.
def continues (char: Char): Bool := Parse.isDigit char ∨ char == ','

theorem spaceStops ∀ (char: Char) (isSpace: Parse.isSpace char = True): continues char = False := match isSpace with
  | Inl space => rewrite space.read in rfl
  | Inr tab => rewrite tab.read in rfl

theorem spaceNotDigit ∀ (char: Char) (isSpace: Parse.isSpace char = True): Parse.isDigit char = False :=
  match isSpace with
    | Inl space => rewrite space.read in rfl
    | Inr tab => rewrite tab.read in rfl

theorem continuesNotDigit ∀ (rest: List Char) (stops: Parse.CannotStart continues rest): Parse.CannotStart Parse.isDigit rest :=
  char more found => Bool.orFalseLeft _ _ (stops char more found)

theorem runsNumber ∀ (read: List Char) (number: Nat) (after: List Char) (written: NumberWritten read number) (stops: Parse.CannotStart Parse.isDigit after):
    Parse.Runs Parse.nat read after number := match written with
      | Both nonEmpty (Both allDigits decimal) => rewrite decimal in Parse.runsNatBefore read after nonEmpty allDigits stops

theorem runsRange ∀ (read: List Char) (range2: Range) (written: RangeWritten read range2) (after: List Char) (stops: Parse.CannotStart Parse.isDigit after):
    Parse.Runs range read after range2 := match range2, written with
      | { low, high }, Witness lowRead (Witness highRead (Both split (Both (Both lowSome (Both lowAll lowValue)) (Both highSome (Both highAll highValue))))) =>
        rewrite split, lowValue, highValue in
          Parse.runsBind Parse.nat _ lowRead (['-'] ++ highRead) _ after (Parse.digitsValue lowRead) _ rfl
            (Parse.runsNat lowRead _ lowSome lowAll rfl)
            (Parse.runsBind (() => Parse.char '-') _ ['-'] highRead _ after () _ rfl
              (Parse.runsChar '-' _)
              (Parse.runsBind Parse.nat _ highRead [] _ after (Parse.digitsValue highRead) _ (Eq.sym (List.appendNil highRead))
                (Parse.runsNatBefore highRead _ highSome highAll stops)
                (Parse.runsPure _ after)))

theorem runsRule ∀ (read: List Char) (rule2: Rule) (written: RuleWritten read rule2) (after: List Char) (stops: Parse.CannotStart Parse.isDigit after):
    Parse.Runs rule read after rule2 := match rule2, written with
      | { field, first, second }, Witness firstRead (Witness secondRead (Both split (Both nonEmpty (Both names (Both firstWritten secondWritten))))) =>
        runsAsValue rule read after { field = Text.fromList field.toList, first, second } { field, first, second } (rewrite Text.fromToList field in rfl)
          (rewrite split in
            Parse.runsBind (() => Parse.takeWhile1 "a field name" isNameChar) _ field.toList (": ".toList ++ firstRead ++ " or ".toList ++ secondRead) _ after
              (Text.fromList field.toList) _ rfl
              (Parse.runsTakeWhile1 "a field name" isNameChar field.toList _ nonEmpty names rfl)
              (Parse.runsBind (() => Parse.text ": ") _ ": ".toList (firstRead ++ " or ".toList ++ secondRead) _ after () _ rfl
                (Parse.runsText ": " _)
                (Parse.runsBind range _ firstRead (" or ".toList ++ secondRead) _ after first _ rfl
                  (runsRange firstRead first firstWritten _ (char more found => rewrite <- List.consInjectiveHead _ _ _ _ found in rfl))
                  (Parse.runsBind (() => Parse.text " or ") _ " or ".toList secondRead _ after () _ rfl
                    (Parse.runsText " or " _)
                    (Parse.runsBind range _ secondRead [] _ after second _ (Eq.sym (List.appendNil secondRead))
                      (runsRange secondRead second secondWritten _ stops)
                      (Parse.runsPure _ after))))))

theorem runsTicket ∀ (read: List Char) (ticket2: Ticket) (written: TicketWritten read ticket2) (after: List Char) (stops: Parse.CannotStart continues after):
    Parse.Runs ticket read after ticket2 := match ticket2, written with
      | { values = vs }, Witness values (Both listed same) =>
        match values, listed with
          | { head, tail }, listed2 =>
            runsAsValue ticket read after { values = (NonEmptyList.cons head tail).toList } { values = vs } (rewrite same in rfl)
              (Parse.runsMap (() => Parse.sepBy1 Parse.nat (() => Parse.char ',')) (values2 => { values = values2.toList }) read after (NonEmptyList.cons head tail)
                (Parse.runsSepBy1Of Parse.nat (() => Parse.char ',') NumberWritten (read2 u => read2 = [',']) (Parse.CannotStart Parse.isDigit) after
                  (read2 v after2 ok stops2 => runsNumber read2 v after2 ok stops2)
                  (read2 after2 u same2 => rewrite same2 in Parse.runsChar ',' after2)
                  (read2 u same2 => rewrite same2 in List.consNotNil ',' [])
                  (read2 after2 u same2 => rewrite same2 in (char more found => rewrite <- List.consInjectiveHead _ _ _ _ found in rfl))
                  (continuesNotDigit after stops)
                  (Parse.declinesSepStep Parse.nat (() => Parse.char ',') after (Parse.declinesCharCannotStart ',' continues rfl after stops))
                  read head tail listed2))

theorem declinesTicket ∀ (input: List Char) (stops: Parse.CannotStart continues input): Parse.Declines ticket input :=
  Parse.declinesBind (() => Parse.sepBy1 Parse.nat (() => Parse.char ',')) _ input
    (Parse.declinesSepBy1 Parse.nat (() => Parse.char ',') input (Parse.declinesNat input (Parse.takeWhileOfCannotStart Parse.isDigit input (continuesNotDigit input stops))))

-- The rules end at a blank line, and a rule's name could run over spaces and a
-- carriage return before the line feed that stops it, so `rule` declines
-- there because the name isn't followed by a colon, not because of its first
-- character.

theorem spaceIsName ∀ (char: Char) (isSpace: Parse.isSpace char = True): isNameChar char = True := match isSpace with
  | Inl space => rewrite space.read in rfl
  | Inr tab => rewrite tab.read in rfl

--| `rule` declines on a run of name characters and then a line feed.
theorem declinesRuleBeforeBreak ∀ (run: List Char) (more: List Char) (names: run.all isNameChar = True): Parse.Declines rule (run ++ ['\n', ..more]) :=
  match run with
    | [] => Parse.declinesBind (() => Parse.takeWhile1 "a field name" isNameChar) _ ['\n', ..more] (Parse.declinesTakeWhile1 "a field name" isNameChar ['\n', ..more] rfl)
    | [char, ..others] =>
      Parse.declinesAfter (() => Parse.takeWhile1 "a field name" isNameChar) _ [char, ..others] ['\n', ..more] (Text.fromList [char, ..others])
        (Parse.runsTakeWhile1 "a field name" isNameChar [char, ..others] ['\n', ..more] (List.consNotNil char others) names rfl)
        (Parse.declinesBind (() => Parse.text ": ") _ ['\n', ..more] (Parse.declinesText ": " _ rfl))

--| A round of `lines rule` declines at a blank line.
theorem declinesRulesAtBlank ∀ (blank: List Char) (more: List Char) (isBlank: Parse.BlankLine blank): Parse.Declines (() => Parse.sepStep rule Parse.newline) (blank ++ more) :=
  match isBlank with
    | Witness first (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
      rewrite split, List.appendAssoc first (middle ++ last) more, List.appendAssoc middle last more in
        Parse.declinesAfter Parse.newline (u => rule()) first (middle ++ (last ++ more)) () (Parse.runsNewline first _ firstBreak)
          (Parse.declinesAfterSpacesBreak rule isNameChar spaceIsName rfl declinesRuleBeforeBreak middle last more spaced lastBreak)

--| The notes, as `NotesWritten` has them, before nothing but line breaks.
theorem runsNotes ∀ (read: List Char) (notes2: Notes) (written: NotesWritten read notes2) (ending: List Char) (breaks: Parse.OnlyBreaks ending):
    Parse.Runs notes read ending notes2 := match notes2, written with
      | { rules, yours, nearby }, Witness rulesRead (Witness yoursRead (Witness nearbyRead (Witness blank1 (Witness break1 (Witness blank2 (Witness break2 parts)))))) =>
        match parts with
          | Both split (Both (Witness rulesList (Both rulesWritten rulesSame)) (Both blank1Ok (Both break1Ok (Both yoursWritten (Both blank2Ok (Both break2Ok (Witness nearbyList (Both nearbyWritten nearbySame)))))))) =>
        match rulesList, rulesWritten, nearbyList, nearbyWritten with
          | { head = firstRule, tail = otherRules }, rulesWritten2, { head = firstNearby, tail = otherNearby }, nearbyWritten2 =>
            let sameNotes: ({ rules = (NonEmptyList.cons firstRule otherRules).toList, yours, nearby = (NonEmptyList.cons firstNearby otherNearby).toList }: Notes) =
              { rules, yours, nearby } := rewrite <- rulesSame, <- nearbySame in rfl
            let afterTickets := "your ticket:".toList ++ break1 ++ yoursRead ++ blank2 ++ "nearby tickets:".toList ++ break2 ++ nearbyRead
            let afterNearby := "nearby tickets:".toList ++ break2 ++ nearbyRead
            let afterRules := blank1 ++ afterTickets
            rewrite split in
              runsAsValue notes _ ending _ { rules, yours, nearby } sameNotes
                (Parse.runsBind (() => Parse.lines rule) _ rulesRead afterRules _ ending
                  (NonEmptyList.cons firstRule otherRules) _ rfl
                  (Parse.runsLinesOf rule RuleWritten (Parse.CannotStart Parse.isDigit) (afterRules ++ ending)
                    (read2 v after ok stops => runsRule read2 v ok after stops)
                    (read2 after isBreak => Parse.cannotStartAfterBreak Parse.isDigit rfl rfl read2 after isBreak)
                    (rewrite List.appendAssoc blank1 afterTickets ending in Parse.cannotStartAtBlank Parse.isDigit rfl rfl spaceNotDigit blank1 (afterTickets ++ ending) blank1Ok)
                    (rewrite List.appendAssoc blank1 afterTickets ending in declinesRulesAtBlank blank1 (afterTickets ++ ending) blank1Ok)
                    rulesRead firstRule otherRules rulesWritten2)
                  (Parse.runsBind Parse.blankLine _ blank1 afterTickets _ ending () _ rfl
                    (Parse.runsBlankLineOf blank1 _ blank1Ok)
                    (Parse.runsBind (() => Parse.text "your ticket:") _ "your ticket:".toList (break1 ++ yoursRead ++ blank2 ++ "nearby tickets:".toList ++ break2 ++ nearbyRead) _ ending () _ rfl
                      (Parse.runsText "your ticket:" _)
                      (Parse.runsBind Parse.newline _ break1 (yoursRead ++ blank2 ++ "nearby tickets:".toList ++ break2 ++ nearbyRead) _ ending () _ rfl
                        (Parse.runsNewline break1 _ break1Ok)
                        (Parse.runsBind ticket _ yoursRead (blank2 ++ "nearby tickets:".toList ++ break2 ++ nearbyRead) _ ending yours _ rfl
                          (runsTicket yoursRead yours yoursWritten ((blank2 ++ afterNearby) ++ ending)
                            (rewrite List.appendAssoc blank2 afterNearby ending in Parse.cannotStartAtBlank continues rfl rfl spaceStops blank2 (afterNearby ++ ending) blank2Ok))
                          (Parse.runsBind Parse.blankLine _ blank2 ("nearby tickets:".toList ++ break2 ++ nearbyRead) _ ending () _ rfl
                            (Parse.runsBlankLineOf blank2 _ blank2Ok)
                            (Parse.runsBind (() => Parse.text "nearby tickets:") _ "nearby tickets:".toList (break2 ++ nearbyRead) _ ending () _ rfl
                              (Parse.runsText "nearby tickets:" _)
                              (Parse.runsBind Parse.newline _ break2 nearbyRead _ ending () _ rfl
                                (Parse.runsNewline break2 _ break2Ok)
                                (Parse.runsBind (() => Parse.lines ticket) _ nearbyRead [] _ ending (NonEmptyList.cons firstNearby otherNearby) _ (Eq.sym (List.appendNil nearbyRead))
                                  (Parse.runsLinesOf ticket TicketWritten (Parse.CannotStart continues) ending
                                    (read2 v after ok stops => runsTicket read2 v ok after stops)
                                    (read2 after isBreak => Parse.cannotStartAfterBreak continues rfl rfl read2 after isBreak)
                                    (Parse.cannotStartAtBreaks continues rfl rfl ending breaks)
                                    (Parse.declinesLinesAtBreaks ticket continues declinesTicket rfl rfl ending breaks)
                                    nearbyRead firstNearby otherNearby nearbyWritten2)
                                  (Parse.runsPure _ ending))))))))))

--| The soundness theorem's conclusion: the input is the notes written out,
--| then any line breaks.
def InputWritten (input: Text) (notes2: Notes): Prop :=
  ∃ (read: List Char) => ∃ (ending: List Char) =>
    input.toList = read ++ ending ∧ NotesWritten read notes2 ∧ ending.all (char => char == '\n' ∨ char == '\r') = True

--| Input that is notes written out is read as those notes.
theorem parseComplete ∀ (input: Text) (notes2: Notes) (written: InputWritten input notes2): Fail.toResult (() => parseNotes input) = Ok notes2 :=
  match written with
    | Witness read (Witness ending (Both split (Both notesWritten breaks))) =>
      Parse.runsAll input notes read ending notes2 split breaks (runsNotes read notes2 notesWritten ending breaks)

--| Soundness (`parseWritten`) is the converse: the input is written as at most one set of notes.
theorem writtenUnique ∀ (input: Text) (a: Notes) (b: Notes) (writtenA: InputWritten input a) (writtenB: InputWritten input b): a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
