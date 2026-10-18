-- Named parameters plus arms, where rule 2 of 5.3 succeeds.

def total (k : Nat) : List Nat -> Nat
  | Nil => k
  | Cons l ls => total (k + l) ls

-- Two named columns, then arms on the last.
def countFrom (a : Nat) (b : Nat) : List Nat -> Nat
  | Nil => a + b
  | Cons x xs => countFrom a (b + x) xs

-- A Pi binder with a different name that is unused later: the header uses v.
def scale (k : Nat) : List Nat -> List Nat
  | Nil => Nil
  | Cons x xs => Cons (k * x) (scale k xs)

-- Implicit binder before a named column moves into the header.
def lengthPlus [a : Type] (k : Nat) : List a -> Nat
  | Nil => k
  | Cons x xs => lengthPlus (k + 1) xs

-- Implicit binder after the named column stays after the colon.
def dropTo (k : Nat) : [a : Type] -> List a -> Nat
  | Nil => k
  | Cons x xs => dropTo (k + 1) xs
