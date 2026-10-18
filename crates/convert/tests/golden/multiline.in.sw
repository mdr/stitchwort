-- Ability rows after the colon, multi-line signatures, arm-form
-- continuation lines, and later-line arm bodies.

type Empty : Type

countIO : Nat
  -> {IO} Nat
countIO n = n

pick : Nat ->
  List Nat ->
  Nat -> List Nat -> (Nat, List Nat)
pick Zero ds d after = (d, after)
pick (Succ w) Nil d after = (d, after)
pick (Succ w) (Cons x rest) d after =
  if Nat.leq (d + 1) x then pick w rest x rest
  else pick w rest d after

long : (a : Type) ->
  (xs : List a) ->
  Nat
long a xs = List.length xs

ability Abort where
  abort : () -> {Abort} Empty

run : Nat -> () -> {IO, Abort} Nat
run n u = n
