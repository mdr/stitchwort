-- A proof about a parser of twelve steps, each step's lemma nested in the
-- one before it, with a blank for every parser and spec (SW-1226, D2342). Each
-- `readsBind`'s conclusion is about its `_`s, and its last argument is a
-- lambda whose type has unknowns only that conclusion fixes. Checked in
-- place first, such a lambda failed, and was checked again once the
-- conclusion had been compared with the goal; with every nested lambda
-- going through both checks, the work doubled at each level (about 240
-- million evaluation steps here, half a minute). Now the conclusion is
-- compared with the goal first, each lambda is checked once, and this takes
-- about a quarter of a million. The steps are opaque, so `_` can be solved
-- for each step's parser (proofs-about-definitions.md §2.3).
import Std (Char, Parse)

opaque def nat(): {Parse} Nat := Parse.nat()
opaque def char (c: Char): {Parse} () := Parse.char c
theorem readsNat: Parse.Reads nat (read n =>
      Not (read = []) ∧ read.all Parse.isDigit = True ∧ n = Parse.digitsValue read)
    unfolding nat :=
  Parse.readsNat
theorem readsChar ∀ (c: Char): Parse.Reads (() => char c) (read u => read = [c]) unfolding char := Parse.readsChar c

type R = { fx0: Nat, fx2: Nat, fx4: Nat, fx6: Nat, fx8: Nat, fx10: Nat }

def p12(): {Parse} R :=
  let x0 := nat()
  char '-'
  let x2 := nat()
  char '-'
  let x4 := nat()
  char '-'
  let x6 := nat()
  char '-'
  let x8 := nat()
  char '-'
  let x10 := nat()
  char '-'
  { fx0 = x0, fx2 = x2, fx4 = x4, fx6 = x6, fx8 = x8, fx10 = x10 }

theorem reads12: Parse.Reads p12 (read value => read = read) :=
  Parse.readsWeaken
    [p := p12]
    (Parse.readsBind _ _ _ _ readsNat (x0 =>
      Parse.readsBind _ _ _ _ (readsChar '-') (u1 =>
        Parse.readsBind _ _ _ _ readsNat (x2 =>
          Parse.readsBind _ _ _ _ (readsChar '-') (u3 =>
            Parse.readsBind _ _ _ _ readsNat (x4 =>
              Parse.readsBind _ _ _ _ (readsChar '-') (u5 =>
                Parse.readsBind _ _ _ _ readsNat (x6 =>
                  Parse.readsBind _ _ _ _ (readsChar '-') (u7 =>
                    Parse.readsBind _ _ _ _ readsNat (x8 =>
                      Parse.readsBind _ _ _ _ (readsChar '-') (u9 =>
                        Parse.readsBind _ _ _ _ readsNat (x10 =>
                          Parse.readsBind _ _ _ _ (readsChar '-') (u11 =>
                            Parse.readsPure {
                              fx0 = x0,
                              fx2 = x2,
                              fx4 = x4,
                              fx6 = x6,
                              fx8 = x8,
                              fx10 = x10
                            })))))))))))))
    (read value h => rfl)
