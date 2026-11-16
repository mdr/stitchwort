-- expect-error: E-REWRITE-NOTHING

-- A rule found neither in the goal as shown nor in what it computes to,
-- with every call kept or not, is still `E-REWRITE-NOTHING` (SW-3529).
import Std (Bool, Eq, List, Nat, Text)

type Printer = { written: List Text, pending: List Text }

def Printer.words (printer: Printer): List Text := printer.written ++ printer.pending

def Printer.write (printer: Printer) (text: Text): Printer :=
  if text.isEmpty then printer else { written = printer.written ++ printer.pending ++ [text], pending = [] }

-- Text after a blank line: not in the goal, as shown or computed.
def Printer.blank (printer: Printer) (text: Text): Printer :=
  if text.isEmpty then printer else { written = printer.written ++ ["", text], pending = printer.pending }

theorem noBlank ∀
    (blankWords: ∀ (printer: Printer) (text: Text) => (printer.blank text).words = printer.words ++ ["", text])
    (printer: Printer) (rest: List Text) (result: (Printer, List Text))
    (flat: result = (printer.write " ", rest)):
    result.fst.words ++ result.snd = printer.words ++ [" "] ++ rest :=
  rewrite flat in rewrite blankWords printer " " in rfl
