-- `cases in t` splits first on the condition of an `if` the goal shows
-- (SW-3530): `t` is written against the goal as shown, and each case's goal
-- keeps the branch's calls for it (`(printer.newline indent).words`). What
-- the condition is stuck on inside its definitions (`flat`, then
-- `printer.pending`) is split only if a case still needs it. Splitting
-- those first, as plain `cases` does, computes each case's goal past the
-- call `t` names, so `rewrite newlineWords` finds nothing.
-- (docs/syntax.md, "cases".)
import Std (Bool, Eq, List, Nat, Text)

type Printer = { written: List Text, pending: List Text, indent: Nat }

def Printer.words (printer: Printer): List Text := printer.written ++ printer.pending

def Printer.newline (printer: Printer) (indent: Nat): Printer :=
  { written = printer.written ++ printer.pending, pending = [], indent = indent }

-- `newlineWords`'s argument `indent` is left open: its words don't depend
-- on it, so matching what the call computes to can't say what it is; the
-- call's own arguments do.
theorem softLine ∀
    (newlineWords: ∀ (printer: Printer) (indent: Nat) => (printer.newline indent).words = printer.words)
    (flat: Bool) (printer: Printer) (indent: Nat) (rest: List Text):
    (if flat && printer.pending.isEmpty then (printer, rest) else (printer.newline indent, rest)).fst.words
      ++ (if flat && printer.pending.isEmpty then (printer, rest) else (printer.newline indent, rest)).snd
      = printer.words ++ rest :=
  cases in (rewrite newlineWords in rfl)
