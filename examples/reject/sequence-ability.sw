-- expect-error: E-ABILITY
-- A sequence's first part runs for its effects, as a block line does, so
-- the function must allow them: `char ','` performs `Parse`.
import Std (Nat, Parse)
import Std.Parse (char)

def comma(): Nat := (char ','; 1)
