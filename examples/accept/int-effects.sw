-- Arithmetic on `Int` with operands that perform operations: they run left
-- to right, as written, whatever order their types are worked out in
-- (docs/proposals/integers.md, "Effects and evaluation order").

import Std (Nat)

def fstOf: Pair a b -> a
  | MkPair x y => x

def sndOf: Pair a b -> b
  | MkPair x y => y

def eqNats: List Nat -> List Nat -> Bool
  | Nil,       Nil       => True
  | Cons x xs, Cons y ys => if x == y then eqNats xs ys else False
  | _,         _         => False

ability Log where
  say: Nat -> {Log} ()

def collect (prog: () -> {Log | e} a): {e} Pair (List Nat) a :=
  handle prog() with
    | return x     => MkPair Nil x
    | say n, k     =>
      let rest := k()
      MkPair (Cons n (fstOf rest)) (sndOf rest)

def loudInt (n: Nat): {Log} Int :=
  say n
  Nat.toInt n

def loudNat (n: Nat): {Log} Nat :=
  say n
  n

-- Effectful leaves on both sides of a nested node, typed as one group.
def nested(): {Log} Int := (loudInt 1 * 0 + 5) - loudInt 2 * (loudInt 3 + 1)

-- `-` around an effectful call.
def negated(): {Log} Int := -(loudInt 4) + -(loudInt 5)

-- A nested node whose own leaves decide nothing: only the whole group
-- says `Int`.
def whole(): {Log} Int := (1 + loudInt 6) * (2 - loudInt 7)

def cmp(): {Log} Bool := loudInt 8 + 1 == loudInt 12 - 3

test "nested order" :=
  let r := collect nested
  if eqNats (fstOf r) [1, 2, 3] then sndOf r == -3 else False

test "negated order" :=
  let r := collect negated
  if eqNats (fstOf r) [4, 5] then sndOf r == -9 else False

test "whole order" :=
  let r := collect whole
  if eqNats (fstOf r) [6, 7] then sndOf r == -35 else False

test "cmp" :=
  let r := collect cmp
  if eqNats (fstOf r) [8, 12] then sndOf r else False
