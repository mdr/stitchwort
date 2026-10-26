-- An opaque definition is checked like any other and runs like any other,
-- but other declarations see only its name and type: its body takes no part
-- in deciding what's equal. A proof that needs the body says `unfolding f`
-- after its type, or rewrites with the generated equation `f.unfold`.
-- (docs/syntax.md, "Opaque definitions"; docs/proposals/opaque-definitions.md.)
import Std (Nat)

opaque def double (n: Nat): Nat := n + n

-- With `unfolding double`, this proof's body sees `double`'s.
theorem doubleThree: double 3 = 6 unfolding double := rfl

-- `double.unfold n: double n = double.%body n`, where `double.%body` is a
-- copy of the body that computes when something looks inside it.
theorem doubleTwo: double 2 = 4 :=
  rewrite double.unfold in rfl

-- Calls are compared by their arguments, as for a function variable.
theorem sameCall (a: Nat) (b: Nat) (e: a = b): double a = double b :=
  rewrite e in rfl

-- A transparent definition may call it; a theorem about that one unfolds
-- what it needs. (`double.%body` stays folded inside arithmetic, so
-- rewriting with `double.unfold` twice here wouldn't compute to `4`.)
def quadruple (n: Nat): Nat := double (double n)

theorem quadrupleOne: quadruple 1 = 4 unfolding double := rfl

-- An opaque definition may unfold another; its own body sees both.
opaque def triple (n: Nat): Nat
    unfolding double
:=
  double n + n

theorem tripleTwo: triple 2 = 6 unfolding triple := rfl

-- A constant can be opaque too.
opaque def answer: Nat := 42

theorem answerIs: answer = 42 := answer.unfold

-- Running a program uses the bodies as always.
test "double runs" := double 21 == answer
test "triple runs" := triple 3 == 9
test "quadruple runs" := quadruple 5 == 20
