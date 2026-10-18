-- Ability rows after the colon, multi-line signatures, arm-form
-- continuation lines, and later-line arm bodies.

type Empty : Type

def countIO (n : Nat) : {IO} Nat := n

def pick : Nat ->
    List Nat ->
    Nat -> List Nat -> (Nat, List Nat)
  | Zero, ds, d, after => (d, after)
  | Succ w, Nil, d, after => (d, after)
  | Succ w, Cons x rest, d, after =>
    if Nat.leq (d + 1) x then pick w rest x rest
    else pick w rest d after

def long (a : Type)
  (xs : List a) :
  Nat := List.length xs

ability Abort where
  abort : () -> {Abort} Empty

def run (n : Nat) () : {IO, Abort} Nat := n
