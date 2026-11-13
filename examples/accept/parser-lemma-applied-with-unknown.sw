-- A lemma applied with `_`, whose statement holds a parser that reads 36
-- digits, against a goal with the same parser: the `_` is solved from the
-- arguments of `tagged`, and the calls of `Parse.exactly` in them are
-- equal. The counterpart of reject/parser-count-differs-from-lemma-with-unknown
-- (SW-1521): remembering pairs of calls found different must not lose this.
import Std (Fin, Parse)

def choose (b: Bool) (p: () → {Parse} List (Fin 10)): () → {Parse} List (Fin 10) := match b with
  | True => p
  | False => p

def tagged (b: Bool) (p: () → {Parse} List (Fin 10)): () → {Parse} List (Fin 10) := choose b p

theorem lem (b: Bool): tagged b (() => Parse.exactly 36 Parse.digit) = (() => Parse.exactly 36 Parse.digit) :=
  match b with
    | True => rfl
    | False => rfl

theorem use: tagged True (() => Parse.exactly 36 Parse.digit) = (() => Parse.exactly 36 Parse.digit) := lem _
