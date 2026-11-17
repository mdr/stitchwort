-- A rule's open argument that the left side's value doesn't depend on:
-- `(printer.newline indent).words` computes to the same words whatever
-- the indent, so matching by computing leaves `indent` unknown. The call
-- the goal shows says what it is, and the rewrite takes it from there
-- (SW-3530; before, `E-UNSOLVED`).
import Std (Bool, Eq, List, Nat, Text)

type Printer = { written: List Text, pending: List Text, indent: Nat }

def Printer.words (printer: Printer): List Text := printer.written ++ printer.pending

def Printer.newline (printer: Printer) (indent: Nat): Printer :=
  { written = printer.written ++ printer.pending, pending = [], indent = indent }

theorem newline ∀
    (newlineWords: ∀ (printer: Printer) (indent: Nat) => (printer.newline indent).words = printer.words)
    (printer: Printer) (indent: Nat) (rest: List Text):
    (printer.newline indent).words ++ rest = printer.words ++ rest :=
  rewrite newlineWords
