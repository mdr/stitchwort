-- Named parameters plus arms, where rule 2 of 5.3 succeeds.

total : Nat -> List Nat -> Nat
total k Nil = k
total k (Cons l ls) = total (k + l) ls

-- Two named columns, then arms on the last.
countFrom : Nat -> Nat -> List Nat -> Nat
countFrom a b Nil = a + b
countFrom a b (Cons x xs) = countFrom a (b + x) xs

-- A Pi binder with a different name that is unused later: the header uses v.
scale : (n : Nat) -> List Nat -> List Nat
scale k Nil = Nil
scale k (Cons x xs) = Cons (k * x) (scale k xs)

-- Implicit binder before a named column moves into the header.
lengthPlus : [a : Type] -> Nat -> List a -> Nat
lengthPlus k Nil = k
lengthPlus k (Cons x xs) = lengthPlus (k + 1) xs

-- Implicit binder after the named column stays after the colon.
dropTo : Nat -> [a : Type] -> List a -> Nat
dropTo k Nil = k
dropTo k (Cons x xs) = dropTo (k + 1) xs
