-- `rewrite` with a rule's arguments left open finds a call the goal shows,
-- even when that call computes because an argument is known (SW-3529).
-- After `rewrite flat`, the goal shows `(printer.write " ").words`; read back
-- folded, `printer.write " "` is what it steps to (`" ".isEmpty` is
-- decided), so neither that search nor the one over what the goal computes
-- to finds the rule's left side, which is stuck on its unknown text. The
-- goal as printed, every call kept, has the call, and the rule's unknowns
-- are solved from its arguments. (docs/syntax.md, "rewrite".)
import Std (Bool, Eq, List, Nat, Text)

type Printer = { written: List Text, pending: List Text }

def Printer.words (printer: Printer): List Text := printer.written ++ printer.pending

-- Empty text writes nothing; anything else goes after what is pending.
def Printer.write (printer: Printer) (text: Text): Printer :=
  if text.isEmpty then printer else { written = printer.written ++ printer.pending ++ [text], pending = [] }

theorem writeSpace ∀
    (writeWords: ∀ (printer: Printer) (text: Text) => (printer.write text).words = printer.words ++ [text])
    (printer: Printer) (rest: List Text) (result: (Printer, List Text))
    (flat: result = (printer.write " ", rest)):
    result.fst.words ++ result.snd = printer.words ++ [" "] ++ rest :=
  rewrite flat then rewrite writeWords, List.appendAssoc then byComputing

-- The arguments given, as before.
theorem writeSpaceGiven ∀
    (writeWords: ∀ (printer: Printer) (text: Text) => (printer.write text).words = printer.words ++ [text])
    (printer: Printer) (rest: List Text) (result: (Printer, List Text))
    (flat: result = (printer.write " ", rest)):
    result.fst.words ++ result.snd = printer.words ++ [" "] ++ rest :=
  rewrite flat then rewrite writeWords printer " ", List.appendAssoc then byComputing
