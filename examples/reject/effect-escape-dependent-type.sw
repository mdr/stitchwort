-- expect-error: E-EFFECT-ESCAPE
-- `payload n` has type `PayloadType n`, and `n` here is what `ask` answers
-- when it runs: the type really depends on an operation's result.

import Std (Bool, Nat)

ability Ask where
  ask: () → {Ask} Nat

def PayloadType: Nat → Type
  | 0 => Nat
  | Succ _ => Bool

def payload: (n: Nat) → PayloadType n
  | 0 => 0
  | Succ _ => True

def answered (): {Ask} Nat :=
  let answer := payload (ask ())
  0
