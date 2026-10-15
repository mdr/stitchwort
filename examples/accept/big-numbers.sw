-- Numbers are stored compactly, and arithmetic on them is native, so large
-- numbers are cheap. They still mean `Succ (Succ … Zero)`: matching on one
-- takes the `Zero` or `Succ` branch, and `3` is the same as `Succ 2`.

-- Checked by computing both sides, natively.
theorem bigSum : 1000000 + 1000000 = 2000000
bigSum = rfl

theorem bigProduct : 123456789 * 987654321 = 121932631112635269
bigProduct = rfl

theorem literalIsSucc : 1000000 = Succ 999999
literalIsSucc = rfl

-- Matching on a literal takes the `Succ` branch without counting down.
isZero : Nat -> Bool
isZero Zero     = True
isZero (Succ n) = False

test "a big number isn't zero" = not (isZero 1000000000000)

-- Unification works through literals: `Succ k` matches `5000` with `k = 4999`.
predOf : (n : Nat) -> Nat
predOf (Succ k) = k
predOf Zero     = 0

test "pred" = eqNat (predOf 5000) 4999
test "division" = eqNat (1000000 / 7) 142857
test "remainder" = eqNat (1000000 % 7) 1
test "subtraction stops at zero" = eqNat (3 - 5) 0
test "comparison" = leq 99999999999 100000000000

-- `auto` decides propositions about big numbers natively too.
under : (n : Nat) -> [auto ok : n < 100000000000] -> Nat
under n = n

test "auto" = eqNat (under 99999999999) 99999999999
test "equal" = eqNat (if h : 123456789 = 123456789 then 1 else 0) 1
test "not equal" = eqNat (if h : 123456789 = 123456788 then 1 else 0) 0

-- Literals can be any size, not just 64 bits.
theorem hugeLiteral : 18446744073709551616 * 18446744073709551616 = 340282366920938463463374607431768211456
hugeLiteral = rfl

test "huge subtraction" = eqNat (340282366920938463463374607431768211456 - 18446744073709551616) 340282366920938463444927863358058659840
