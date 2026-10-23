-- expect-error: E-NONEXHAUSTIVE
-- A missing number in a `match` expression on a `Fin n` is worded as for
-- any other type: no alternative of this `match` matches it.
import Std (Fin)

def name (index: Fin 3): Text :=
  match index with
    | 0 => "zero"
    | 2 => "two"
