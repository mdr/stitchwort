-- The experiment behind §2.3 of proofs-about-definitions.md: the same
-- `line`, built from opaque copies of std's reading steps. `line()` then
-- computes only as far as `Effect.bind (nat ()) (low => …)`, the shape
-- `Parse.readsBind`'s conclusion has, so every `_` is solved and nothing of
-- the parser is restated. Not a proposal: opacity here is a probe
-- (4 Nov 2026; `stitchwort check opaque-steps.sw`).
import Std (Char, Exists, List, Parse, Text)

opaque def nat(): {Parse} Nat := Parse.nat()
opaque def char (c: Char): {Parse} () := Parse.char c
opaque def satisfy (what: Text) (passes: Char → Bool): {Parse} Char := Parse.satisfy what passes
opaque def text (t: Text): {Parse} () := Parse.text t
opaque def takeWhile1 (what: Text) (passes: Char → Bool): {Parse} Text := Parse.takeWhile1 what passes

theorem readsNat: Parse.Reads nat (read n => Not (read = []) ∧ read.all Parse.isDigit = True ∧ n = Parse.digitsValue read)
    unfolding nat
:= Parse.readsNat
theorem readsChar ∀ (c: Char): Parse.Reads (() => char c) (read u => read = [c])
    unfolding char
:= Parse.readsChar c
theorem readsSatisfy ∀ (what: Text) (passes: Char → Bool): Parse.Reads (() => satisfy what passes) (read char => read = [char] ∧ passes char = True)
    unfolding satisfy
:= Parse.readsSatisfy what passes
theorem readsText ∀ (t: Text): Parse.Reads (() => text t) (read u => read = t.toList)
    unfolding text
:= Parse.readsText t
theorem readsTakeWhile1 ∀ (what: Text) (passes: Char → Bool):
    Parse.Reads (() => takeWhile1 what passes) (read taken => Not (read = []) ∧ read.all passes = True ∧ taken = Text.fromList read)
    unfolding takeWhile1
:= Parse.readsTakeWhile1 what passes

type Entry = { low: Nat, high: Nat, letter: Char, password: Text }

def line(): {Parse} Entry :=
  let low := nat()
  char '-'
  let high := nat()
  char ' '
  let letter := satisfy "a lowercase letter" Char.isAsciiLowercase
  text ": "
  let password := takeWhile1 "a password" Char.isAsciiLowercase
  { low, high, letter, password }

def Digits (read: List Char) (n: Nat): Prop :=
  Not (read = []) ∧ read.all Parse.isDigit = True ∧ n = Parse.digitsValue read

def Written (line: List Char) (entry: Entry): Prop :=
  ∃ (low: List Char) => ∃ (high: List Char) =>
    line = low ++ ['-'] ++ high ++ [' ', entry.letter, ':', ' '] ++ entry.password.toList
      ∧ Digits low entry.low ∧ Digits high entry.high ∧ entry.letter.isAsciiLowercase = True
      ∧ Not (entry.password.toList = []) ∧ entry.password.toList.all Char.isAsciiLowercase = True

theorem readsLine: Parse.Reads line Written :=
  Parse.readsWeaken line _ _
    (Parse.readsBind _ _ _ _ readsNat (low =>
      Parse.readsBind _ _ _ _ (readsChar '-') (u1 =>
        Parse.readsBind _ _ _ _ readsNat (high =>
          Parse.readsBind _ _ _ _ (readsChar ' ') (u2 =>
            Parse.readsBind _ _ _ _ (readsSatisfy "a lowercase letter" Char.isAsciiLowercase) (letter =>
              Parse.readsBind _ _ _ _ (readsText ": ") (u3 =>
                Parse.readsBind _ _ _ _ (readsTakeWhile1 "a password" Char.isAsciiLowercase) (password =>
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
