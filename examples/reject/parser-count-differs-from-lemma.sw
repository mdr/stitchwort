-- expect-error: E-TYPE-MISMATCH
-- A parser that reads 35 digits, and a lemma about one that reads 36. The
-- two calls of `Parse.exactly` differ in their count. The checker says so
-- within a second: comparing what the two compute to, level by level, both
-- by arguments and by unfoldings, would take about 2³⁵ steps (SW-1506).
import Std (Char, Fin, List, Parse)

def DigitWritten (read: List Char) (d: Fin 10): Prop := ∃ (char: Char) => read = [char] ∧ char.toDigit = Some d

theorem readsDigits: Parse.Reads (() => Parse.exactly 35 Parse.digit) (read values => Parse.Each DigitWritten read values ∧ values.length = 36) :=
  Parse.readsExactly 36 Parse.digit DigitWritten Parse.readsDigit
