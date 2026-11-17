-- `match step: ok x with` replaces `ok x` in the goal, inside lambdas too, so
-- the right side is `anyR (ys => all2 ok ys) rest` in the `True` branch. But
-- `gIs` brings in a new `ok x`, inside the lambda, after the `match` (SW-882).
-- `byComputing`, closing the `rewrite`, rewrites it along `step` and tries
-- again (match-refinement.md R3); the `False` branch does that by hand.
def all2 (ok: Nat → Bool): List Nat → Bool
  | Nil => True
  | Cons x xs => ok x && all2 ok xs

def anyR (holds: List Nat → Bool): List Nat → Bool
  | Nil => False
  | Cons x xs => holds xs || anyR (ys => holds (Cons x ys)) xs

-- Stuck on the list, so it doesn't mention `ok x` until `gIs` unfolds it.
def g (ok: Nat → Bool) (x: Nat): List Nat → Bool
  | Nil => False
  | Cons y ys => anyR (zs => all2 ok (Cons x zs)) (Cons y ys)

theorem gIs ∀ (ok: Nat → Bool) (x: Nat) (rest: List Nat): g ok x rest = anyR (ys => all2 ok (Cons x ys)) rest :=
  match rest with
    | Nil => byComputing
    | Cons y ys => byComputing

theorem fromLemma ∀ (ok: Nat → Bool) (x: Nat) (rest: List Nat): g ok x rest = anyR (ys => ok x && all2 ok ys) rest :=
  match step: ok x with
    | True => rewrite gIs ok x rest
    | False => rewrite gIs ok x rest, step
