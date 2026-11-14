-- expect-error: E-REFL
-- `rfl` between two parsers, one stuck on `b`. Computed, the left side
-- holds `Parse.exactly 2^128 Parse.digit` unfolded 2^128 levels deep, so
-- the notes that read the sides back whole stop at a size a message can
-- use, and show it as `…`: reading it back to the size limit took 18 s and
-- 1.2 GB (SW-2580).
import Std (Fin, Parse)

def choose (b: Bool) (p: () → {Parse} List (Fin 10)): () → {Parse} List (Fin 10) := match b with
  | True => p
  | False => p

theorem lem (b: Bool): choose b (() => Parse.exactly 340282366920938463463374607431768211456 Parse.digit) = (() => Parse.exactly 35 Parse.digit) := rfl
