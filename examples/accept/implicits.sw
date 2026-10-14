-- Implicit arguments: inferred, supplied by name, or left as holes.

-- `a` and `b` are bound automatically, because they're only used as types.
mapList : (a -> b) -> List a -> List b
mapList f Nil         = Nil
mapList f (Cons x xs) = Cons (f x) (mapList f xs)

-- Inferred from the arguments.
lengths : List Nat
lengths = mapList (\xs -> length xs) [[1], [2, 3]]

-- Supplied by name, or as a hole for the compiler to fill in.
named : Nat
named = length [a := Nat] [1, 2]

holes : List Nat
holes = mapList [a := _] Succ [1, 2]

-- Propositions can be bound automatically too: here `p q : Prop`.
type Or (p : Prop) (q : Prop) : Prop =
  | Inl (left : p)
  | Inr (right : q)

theorem orComm : Or p q -> Or q p
orComm (Inl h) = Inr h
orComm (Inr h) = Inl h

-- Implicit parameters are in scope in the equations, by name.
theorem appendNil : (xs : List a) -> append xs Nil = xs
appendNil Nil         = rfl
appendNil (Cons x xs) = cong (\ys -> Cons x ys) (appendNil xs)

theorem plusZeroNat : (n : Nat) -> n + 0 = n
plusZeroNat Zero     = rfl
plusZeroNat (Succ m) = cong Succ (plusZeroNat m)

-- `sym` and `trans` from the prelude, with everything implicit.
theorem twoWays : (n : Nat) -> n + 0 = 0 + n
twoWays n = trans (plusZeroNat n) (sym rfl)
