-- expect-error: E-ARITY
-- `Parse` takes what it reads: a parser of text is `{Parse Char}`. A bare
-- `{Parse}` names the parameter and shows the row written with it.
import Std (Nat, Parse)
import Std.Parse (nat)

def number(): {Parse} Nat := nat()
