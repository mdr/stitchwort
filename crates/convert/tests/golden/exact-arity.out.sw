-- Arms get one pattern per explicit argument after the colon.

-- A lambda's parameter moves into the arm; otherwise a fresh name is added.
def f : Nat -> Nat -> Nat
  | Zero,   y  => y
  | Succ x, a1 => g x a1

def g (a : Nat) (b : Nat) : Nat := a + b

-- A lambda whose parameter clashes with a pattern variable isn't moved.
def h : Nat -> Nat -> Nat
  | Succ x, a1 => (\x => x) a1
  | Zero,   y  => y

-- A body that starts on the next line, applied to a fresh name.
def k : Bool -> Nat -> Nat
  | True, a1 => (
    let z := 1
    g z) a1
  | False, y => y

-- An absurd arm gets `_`.
type Empty : Type

def absurd2 : Empty -> Nat -> Nat
  | (), _

-- converter report:
-- line 5: f: moved lambda parameter(s) y
-- line 6: f: applied the body to fresh a1
-- line 13: h: applied the body to fresh a1
-- line 14: h: moved lambda parameter(s) y
-- line 18: k: applied the body to fresh a1
-- line 21: k: moved lambda parameter(s) y
-- line 27: absurd2: absurd arm, added 1 `_`
