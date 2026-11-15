-- expect-error: E-TYPE-MISMATCH
-- A computation type pairs the row `{Parse Char}` with results that aren't
-- the row's own: here `both`'s explicit `r` is `o => Nat`, not the row's
-- results. So a plain value isn't made into a computation in the row
-- (SW-851), and the note names the row, showing the ability's argument
-- (SW-3303). The parser passed as `d` solves the row's operations.
import Std (Nat, Parse)
import Std.Effect (Comp)
import Std.Parse (nat)

def parser(): {Parse Char} Nat := nat()

def both (r: e → Type) (d: Comp e s Nat) (c: Comp e r Nat): Nat := 0

def bad: Nat := both (o => Nat) parser() (1 + 1)
