-- expect-error: E-FIN-LITERAL
-- A numeral is a `Fin n` only when it's below n (D1073): 7 isn't below 5.
import Std (Fin, List)

def small: Fin 5 := 7

def digits: List (Fin 10) := [1, 10]
