-- An omitted `Zero` arm is fine when a later column's type, `Fin n`, is then
-- empty (SW-181): `Fin Zero` has no values.

def pick: (n: Nat) -> (i: Fin n) -> Nat
  | Succ k, FZero            => 0
  | Succ k, FSucc [n := j] i => Succ (Fin.toNat i)

test "first" := pick 3 FZero == 0
test "second" := pick 3 (FSucc FZero) == 1
