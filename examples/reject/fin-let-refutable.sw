-- expect-error: E-LET-REFUTABLE
-- A number pattern on a `Fin n` only matches that number, as on a `Nat`.
import Std (Fin)

def first (index: Fin 2): Nat :=
  let 0 := index
  1
