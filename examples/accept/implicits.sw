-- Implicit arguments: inferred, supplied by name, or left as holes.

-- `a` and `b` are bound automatically, because they're only used as types.
import Std (Eq)

def mapList (f: a -> b): List a -> List b
  | Nil       => Nil
  | Cons x xs => Cons (f x) (mapList f xs)

-- Inferred from the arguments.
def lengths: List Nat := mapList (\xs => List.length xs) [[1], [2, 3]]

-- Supplied by name, or as a hole for the compiler to fill in.
def named: Nat := List.length [a := Nat] [1, 2]

def holes: List Nat := mapList [a := _] Succ [1, 2]

-- Propositions can be bound automatically too: here `p q: Prop`.
type Or (p: Prop) (q: Prop): Prop =
  | Inl (left: p)
  | Inr (right: q)

theorem orComm: Or p q -> Or q p
  | Inl h => Inr h
  | Inr h => Inl h

-- Implicit parameters are in scope in the equations, by name.
theorem appendNil: (xs: List a) -> xs.append Nil = xs
  | Nil       => rfl
  | Cons x xs => Eq.cong (\ys => Cons x ys) (appendNil xs)

theorem plusZeroNat: (n: Nat) -> n + 0 = n
  | Zero   => rfl
  | Succ m => Eq.cong Succ (plusZeroNat m)

-- `Eq.sym` and `Eq.trans` from the prelude, with everything implicit.
theorem twoWays (n: Nat): n + 0 = 0 + n := Eq.trans (plusZeroNat n) (Eq.sym rfl)

-- An implicit parameter between two explicit ones: `b` is in scope by name.
def constant (x: a) [b: Type] (y: b): a := x

-- A later implicit parameter, supplied by name (`Eq.cong` has `a` before `b`).
theorem succCong (m: Nat) (n: Nat) (p: m = n): Succ m = Succ n := Eq.cong [b := Nat] Succ p

-- A definition without patterns still has its implicit parameters in scope.
def identity: [a: Type] -> a -> a := \x => x

-- A lambda passed where a polymorphic function is expected.
def applyToThree (f: [a: Type] -> a -> a): Nat := f 3

def three: Nat := applyToThree (\x => x)

-- A constructor with both fields missing, used as a function.
def foldRight (f: a -> b -> b) (z: b): List a -> b
  | Nil       => z
  | Cons x xs => f x (foldRight f z xs)

def copy (xs: List Nat): List Nat := foldRight Cons Nil xs

theorem copyWorks: copy [1, 2] = [1, 2] := rfl

-- The largest number literal allowed (`Nat` is unary for now).
def twoHundred: Nat := 200
