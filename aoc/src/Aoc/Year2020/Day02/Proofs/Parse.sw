--| The parser reads exactly the puzzle's format: if `parseEntries` reads
--| `input` as `entries`, each line of the input is its entry written as
--| `1-3 a: abcde`, nothing dropped, added or changed. Numbers may have
--| leading zeros (`01-3 a: abc`): the line has digits whose value is the
--| entry's number.
--
-- From std's lemmas on what parsers read (Std/Parse/Reads.sw).

namespace Aoc.Year2020.Day02.Proofs
import Aoc.Year2020.Day02 (..)
import Std (Char, Eq, Exists, Fail, List, Parse, Text)

--| Decimal digits, at least one, with the value `n`.
def Digits (read: List Char) (n: Nat): Prop :=
  Not (read = []) ∧ read.all Parse.isDigit = True ∧ n = Parse.digitsValue read

--| `line` is `entry` written out: its low number, a dash, its high number, a
--| space, its lowercase letter, a colon and a space, and its password, of at
--| least one lowercase letter.
def Written (line: List Char) (entry: Entry): Prop :=
  ∃ (low: List Char) => ∃ (high: List Char) =>
    line = low ++ ['-'] ++ high ++ [' ', entry.letter, ':', ' '] ++ entry.password.toList
      ∧ Digits low entry.low ∧ Digits high entry.high ∧ entry.letter.isAsciiLowercase = True
      ∧ Not (entry.password.toList = []) ∧ entry.password.toList.all Char.isAsciiLowercase = True

theorem readsLine: Parse.Reads line Written :=
  Parse.readsThen Parse.nat _ _ _ Parse.readsNat (lowRead low lowDigits =>
    Parse.readsThen (() => Parse.char '-') _ _ _ (Parse.readsChar '-') (dashRead u1 dash =>
      Parse.readsThen Parse.nat _ _ _ Parse.readsNat (highRead high highDigits =>
        Parse.readsThen (() => Parse.char ' ') _ _ _ (Parse.readsChar ' ') (spaceRead u2 space =>
          Parse.readsThen (() => Parse.satisfy "a lowercase letter" Char.isAsciiLowercase) _ _ _ (Parse.readsSatisfy "a lowercase letter" Char.isAsciiLowercase) (letterRead letter (Both letterIs lower) =>
            Parse.readsThen (() => Parse.text ": ") _ _ _ (Parse.readsText ": ") (colonRead u3 colon =>
              Parse.readsThen (() => Parse.takeWhile1 "a password" Char.isAsciiLowercase) _ _ _ (Parse.readsTakeWhile1 "a password" Char.isAsciiLowercase) (passwordRead password (Both nonEmpty (Both lowers made)) =>
                Parse.readsDone { low, high, letter, password } _
                  (rewrite made in
                    Witness lowRead (Witness highRead
                      (Both (rewrite dash, space, letterIs, colon, List.appendNil passwordRead in rfl)
                        (Both lowDigits (Both highDigits (Both lower (Both nonEmpty lowers))))))))))))))

--| Every line of the input is its entry written out, and there is one entry
--| per line.
theorem parseWritten (input: Text) (entries: List Entry) (parsed: Fail.toResult (() => parseEntries input) = Ok entries):
    List.All2 Written (input.lines.map Text.toList) entries :=
  Parse.eachLineReads input line Written entries parsed readsLine
