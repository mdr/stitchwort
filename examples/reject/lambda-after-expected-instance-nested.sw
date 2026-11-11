-- expect-error: E-INSTANCE-UNKNOWN-TYPE
-- The call's own dictionary is found from the expected type, but the one
-- made inside the other argument's lambda (`z == z`, `z` of a type nothing
-- fixes) is in a deeper context and is not guessed: it stays the plain
-- "can't tell which type" error.
import Std (DecEq)

theorem nested [auto eq: DecEq a] [x: a] [y: a] (h: x ≠ y) (f: b → c): ((x != y): Bool) = True :=
  DecEq.trueOfNe h

theorem otherArgument (a b n: Nat) (differ: a ≠ b) (total: a + b = n): ((a + a != n): Bool) = True :=
  nested (same => differ (omega)) (z => z == z)
