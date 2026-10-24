-- A type can take an effect as a parameter, of type `Effects`. This record
-- holds a callback, and its effects are part of the record's type. You don't
-- write a particular `Effects` value: it is worked out from the callback.
import Std (Fail, List)
import Std.Effect (Effects)
import Std.Fail (fail, toResult)

type Checker (e: Effects) = {
  name: Text,
  check: Nat -> {e} Nat
}

def Checker.run (c: Checker e) (xs: List Nat): {e} (List Nat) := xs.mapIn c.check

def double (n: Nat): Nat := n * 2

def nonZero (n: Nat): {Fail} Nat := if n == 0 then fail "zero" else n

-- A pure callback makes a pure `Checker`; one that may fail makes a
-- `Checker` that may fail. `run` is the same function either way.
test "a pure checker" := Checker.run { name = "double", check = double } [1, 2] == [2, 4]

def failing: Result (List Nat) Text :=
  toResult (() => Checker.run { name = "non-zero", check = nonZero } [1, 0])

test "a failing checker" := failing == Err "zero"
