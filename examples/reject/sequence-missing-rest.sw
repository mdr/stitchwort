-- expect-error: E-PARSE
-- A sequence `(a; b)` needs an expression after each `;`: a trailing `;`
-- is not a statement terminator.
import Std (Nat, Parse)
import Std.Parse (char, nat)

def number(): {Parse} Nat := (char ','; nat();)
