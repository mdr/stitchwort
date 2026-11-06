-- expect-error: E-TYPE-MISMATCH
-- A lemma applied with `_`, whose statement holds a parser that reads 36
-- digits, against a goal whose parser reads 35. The `_` can only be solved
-- from the arguments of `tagged`, so those are compared as more than a
-- shortcut, and the two calls of `Parse.exactly` in them are unfolded there,
-- level by level, as well as in `tagged`'s unfolding. The checker still says
-- they differ within a second: each pair of calls found different is
-- answered at once when it is met again, where comparing every level twice
-- over would take about 2³⁵ steps (SW-1521).
import Std (Fin, Parse)

def choose (b: Bool) (p: () → {Parse} List (Fin 10)): () → {Parse} List (Fin 10) := match b with
  | True => p
  | False => p

def tagged (b: Bool) (p: () → {Parse} List (Fin 10)): () → {Parse} List (Fin 10) := choose b p

theorem lem (b: Bool): tagged b (() => Parse.exactly 36 Parse.digit) = (() => Parse.exactly 36 Parse.digit) := match b with
  | True => rfl
  | False => rfl

theorem use: tagged True (() => Parse.exactly 35 Parse.digit) = (() => Parse.exactly 36 Parse.digit) := lem _
