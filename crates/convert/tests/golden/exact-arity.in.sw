-- Arms get one pattern per explicit argument after the colon.

-- A lambda's parameter moves into the arm; otherwise a fresh name is added.
f : Nat -> Nat -> Nat
f Zero     = \y -> y
f (Succ x) = g x

g : Nat -> Nat -> Nat
g a b = a + b

-- A lambda whose parameter clashes with a pattern variable isn't moved.
h : Nat -> Nat -> Nat
h (Succ x) = \x -> x
h Zero     = \y -> y

-- A body that starts on the next line, applied to a fresh name.
k : Bool -> Nat -> Nat
k True =
  let z = 1
  g z
k False = \y -> y

-- An absurd arm gets `_`.
type Empty : Type

absurd2 : Empty -> Nat -> Nat
absurd2 ()
