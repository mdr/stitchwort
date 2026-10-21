-- expect-error: E-UNKNOWN-NAME
-- `List.lenght` names a function of `List`'s, and there's none: the error
-- says so, with the near misses, rather than reading `List` as a value
-- (it was `E-ARITY: List needs 1 argument(s)`, and for `Text.lenght`,
-- `E-NO-NAMESPACE`). Each line is one error.
import Std (List, Text)

def a: Nat := List.lenght [1, 2, 3]
def b: Nat := Text.lenght "abc"
def c: Nat := Nat.frobnicate 3
