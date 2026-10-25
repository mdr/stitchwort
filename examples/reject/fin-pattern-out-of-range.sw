-- expect-error: E-FIN-LITERAL
-- A number pattern on a `Fin n` must be below n too (D1073).
import Std (Fin)

def name: Fin 2 → Text
  | 0 => "zero"
  | 1 => "one"
  | 2 => "two"
