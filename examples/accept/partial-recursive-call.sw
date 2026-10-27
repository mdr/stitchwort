-- A recursive call given only some of its arguments can be passed along,
-- when the ones it's given include one that gets smaller: every call made
-- through `sumWith n` passes the same smaller `n`.
-- Neighbour: reject/partial-recursive-call.sw, where it isn't given.
import Std (List)

def applyTo (f: Nat → Nat) (x: Nat): Nat := f x

def sumWith: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => applyTo (sumWith n) (acc + Succ n)

-- With implicit parameters, and a helper that calls what it's given twice.
def twice [a: Type] (f: a → a) (x: a): a := f (f x)

def countDown [a: Type] (step: a → a): Nat → a → a
  | Zero, x => x
  | Succ n, x => twice (countDown step n) (step x)

theorem sumWithThree: sumWith 3 0 = 6 := rfl

theorem countDownTwo: countDown Succ 2 0 = 3 := rfl

-- A local definition in a cycle with its owner, used unapplied: it's given
-- what it captures, here the smaller `rest`.
def addAll (f: Nat → Nat): List Nat → List Nat
  | Nil => Nil
  | Cons x xs => Cons (f x) (addAll f xs)

def owner: List Nat → List Nat
  | Nil => Nil
  | Cons _ rest =>
    def shift (n: Nat): Nat := n + List.length (owner rest)
    addAll shift rest
