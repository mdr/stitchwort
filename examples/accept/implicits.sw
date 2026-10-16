-- Implicit arguments: inferred, supplied by name, or left as holes.

-- `a` and `b` are bound automatically, because they're only used as types.
mapList : (a -> b) -> List a -> List b
mapList f Nil         = Nil
mapList f (Cons x xs) = Cons (f x) (mapList f xs)

-- Inferred from the arguments.
lengths : List Nat
lengths = mapList (\xs -> List.length xs) [[1], [2, 3]]

-- Supplied by name, or as a hole for the compiler to fill in.
named : Nat
named = List.length [a := Nat] [1, 2]

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
theorem appendNil : (xs : List a) -> List.append xs Nil = xs
appendNil Nil         = rfl
appendNil (Cons x xs) = Eq.cong (\ys -> Cons x ys) (appendNil xs)

theorem plusZeroNat : (n : Nat) -> n + 0 = n
plusZeroNat Zero     = rfl
plusZeroNat (Succ m) = Eq.cong Succ (plusZeroNat m)

-- `Eq.sym` and `Eq.trans` from the prelude, with everything implicit.
theorem twoWays : (n : Nat) -> n + 0 = 0 + n
twoWays n = Eq.trans (plusZeroNat n) (Eq.sym rfl)

-- An implicit parameter between two explicit ones: `b` is in scope by name.
constant : a -> [b : Type] -> b -> a
constant x y = x

-- A later implicit parameter, supplied by name (`Eq.cong` has `a` before `b`).
theorem succCong : (m : Nat) -> (n : Nat) -> m = n -> Succ m = Succ n
succCong m n p = Eq.cong [b := Nat] Succ p

-- A definition without patterns still has its implicit parameters in scope.
identity : [a : Type] -> a -> a
identity = \x -> x

-- A lambda passed where a polymorphic function is expected.
applyToThree : ([a : Type] -> a -> a) -> Nat
applyToThree f = f 3

three : Nat
three = applyToThree (\x -> x)

-- A constructor with both fields missing, used as a function.
foldr : (a -> b -> b) -> b -> List a -> b
foldr f z Nil         = z
foldr f z (Cons x xs) = f x (foldr f z xs)

copy : List Nat -> List Nat
copy xs = foldr Cons Nil xs

theorem copyWorks : copy [1, 2] = [1, 2]
copyWorks = rfl

-- The largest number literal allowed (`Nat` is unary for now).
twoHundred : Nat
twoHundred = 200
