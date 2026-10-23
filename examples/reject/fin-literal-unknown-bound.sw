-- expect-error: E-FIN-LITERAL
-- A numeral is a `Fin n` only where n is a known number (D1073): here n is
-- a variable, so `2 < n` can't be computed.
import Std (Fin)

def third (n: Nat): Fin n := 2

-- And here nothing says what n is.
def unsaid: Nat := Fin.toNat 3
