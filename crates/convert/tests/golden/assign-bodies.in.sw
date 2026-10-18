-- := bodies: values, same-variable columns, theorems, tests, export.

answer : Nat
answer = 42

double : Nat -> Nat
double n = n + n

addAll : Nat -> Nat -> Nat -> Nat
addAll a b c = a + b + c

theorem plusZero : 0 + 0 = 0
plusZero = rfl

theorem doubleZero : double 0 = 0
doubleZero = rfl

test "answer" = answer == 42
test "double" = double 4 == 8

export identityNat : Nat -> Nat
identityNat n = n

export
constFive : Nat -> Nat
constFive n = 5
