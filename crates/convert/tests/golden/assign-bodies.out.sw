-- := bodies: values, same-variable columns, theorems, tests, export.

def answer : Nat := 42

def double (n : Nat) : Nat := n + n

def addAll (a : Nat) (b : Nat) (c : Nat) : Nat := a + b + c

theorem plusZero : 0 + 0 = 0 := rfl

theorem doubleZero : double 0 = 0 := rfl

test "answer" := answer == 42
test "double" := double 4 == 8

export def identityNat (n : Nat) : Nat := n

export def constFive (n : Nat) : Nat := 5
