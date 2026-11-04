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
  Parse.readsWeaken line _ _
    (Parse.readsBind Parse.nat
      (low =>
        Parse.char '-'
        let high := Parse.nat()
        Parse.char ' '
        let letter := Parse.satisfy "a lowercase letter" Char.isAsciiLowercase
        Parse.text ": "
        let password := Parse.takeWhile1 "a password" Char.isAsciiLowercase
        { low, high, letter, password })
      _ _ Parse.readsNat (low =>
      Parse.readsBind _ _ _ _ (Parse.readsChar '-') (u1 =>
        Parse.readsBind _ _ _ _ Parse.readsNat (high =>
          Parse.readsBind _ _ _ _ (Parse.readsChar ' ') (u2 =>
            Parse.readsBind _ _ _ _ (Parse.readsSatisfy "a lowercase letter" Char.isAsciiLowercase) (letter =>
              Parse.readsBind _ _ _ _ (Parse.readsText ": ") (u3 =>
                Parse.readsBind _ _ _ _ (Parse.readsTakeWhile1 "a password" Char.isAsciiLowercase) (password =>
                  Parse.readsPure { low, high, letter, password }))))))))
    (read entry h =>
      match h with
        | Witness lowRead (Witness rest1 (Witness low (Both split1 (Both lowDigits more1)))) =>
          match more1 with
            | Witness dashRead (Witness rest2 (Witness u1 (Both split2 (Both dash more2)))) =>
              match more2 with
                | Witness highRead (Witness rest3 (Witness high (Both split3 (Both highDigits more3)))) =>
                  match more3 with
                    | Witness spaceRead (Witness rest4 (Witness u2 (Both split4 (Both space more4)))) =>
                      match more4 with
                        | Witness letterRead (Witness rest5 (Witness letter (Both split5 (Both (Both letterIs lower) more5)))) =>
                          match more5 with
                            | Witness colonRead (Witness rest6 (Witness u3 (Both split6 (Both colon more6)))) =>
                              match more6 with
                                | Witness passwordRead (Witness rest7 (Witness password (Both split7 (Both (Both nonEmpty (Both lowers made)) (Both none built))))) =>
                                  rewrite built, made in
                                    Witness lowRead (Witness highRead
                                      (Both
                                        (rewrite split1, split2, dash, split3, split4, space, split5, letterIs, split6, colon, split7, none, List.appendNil passwordRead in rfl)
                                        (Both lowDigits (Both highDigits (Both lower (Both nonEmpty lowers)))))))

--| Every line of the input is its entry written out, and there is one entry
--| per line.
theorem parseWritten (input: Text) (entries: List Entry) (parsed: Fail.toResult (() => parseEntries input) = Ok entries):
    List.All2 Written (input.lines.map Text.toList) entries :=
  Parse.eachLineReads input line Written entries parsed readsLine
