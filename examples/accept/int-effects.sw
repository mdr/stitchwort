-- Arithmetic on `Int` with operands that perform operations: they run left
-- to right, as written, whatever order their types are worked out in
-- (docs/proposals/integers.md, "Effects and evaluation order").

fstOf : Pair a b -> a
fstOf (MkPair x y) = x

sndOf : Pair a b -> b
sndOf (MkPair x y) = y

eqNats : List Nat -> List Nat -> Bool
eqNats Nil         Nil         = True
eqNats (Cons x xs) (Cons y ys) = if x == y then eqNats xs ys else False
eqNats _           _           = False

ability Log where
  say : Nat -> {Log} ()

collect : (() -> {Log | e} a) -> {e} Pair (List Nat) a
collect prog =
  handle prog () with
    | return x     -> MkPair Nil x
    | say n => k   ->
      let rest = k ()
      MkPair (Cons n (fstOf rest)) (sndOf rest)

loudInt : Nat -> {Log} Int
loudInt n =
  say n
  Nat.toInt n

loudNat : Nat -> {Log} Nat
loudNat n =
  say n
  n

-- Effectful leaves on both sides of a nested node, typed as one group.
nested : () -> {Log} Int
nested u = (loudInt 1 * 0 + 5) - loudInt 2 * (loudInt 3 + 1)

-- `-` around an effectful call.
negated : () -> {Log} Int
negated u = -(loudInt 4) + -(loudInt 5)

-- A nested node whose own leaves decide nothing: only the whole group
-- says `Int`.
whole : () -> {Log} Int
whole u = (1 + loudInt 6) * (2 - loudInt 7)

cmp : () -> {Log} Bool
cmp u = loudInt 8 + 1 == loudInt 12 - 3

test "nested order" =
  let r = collect nested
  if eqNats (fstOf r) [1, 2, 3] then sndOf r == -3 else False

test "negated order" =
  let r = collect negated
  if eqNats (fstOf r) [4, 5] then sndOf r == -9 else False

test "whole order" =
  let r = collect whole
  if eqNats (fstOf r) [6, 7] then sndOf r == -35 else False

test "cmp" =
  let r = collect cmp
  if eqNats (fstOf r) [8, 12] then sndOf r else False
