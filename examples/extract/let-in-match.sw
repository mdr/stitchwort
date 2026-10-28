-- A `let` used in a `match` arm inside a callback. The `match` becomes a
-- function of its own, which takes the `let`'s value from the caller, as a
-- closure would: the value is computed once, not once per element. Where a
-- proof in an arm needs the `let`'s value, not just its type, that function
-- computes the `let` again instead.
--
-- run: shifted [1, 2, 3] (Some 4)
-- run: shifted [1, 2, 3] None
-- run: nested [[1, 2], [], [3]] 5
-- run: known [1, 2] True
-- run: known [1, 2] False

import Std (Bool, List, Nat, Option)

export def shifted (xs: List Nat) (extra: Option Nat): List Nat :=
  let total := xs.sum
  xs.map (x =>
    match extra with
      | Some more => x + total + more
      | None => x)

-- Two `match`es, one inside the other, both using the `let`.
export def nested (rows: List (List Nat)) (k: Nat): List Nat :=
  let scale := k * 2
  rows.map (row =>
    match row with
      | Nil => scale
      | Cons first rest =>
        match rest with
          | Nil => first * scale
          | Cons _ _ => first + scale)

type Above (n: Nat) = { value: Nat, above: n < value }

-- The arm's proof that `n < bigger` needs `bigger`'s value.
export def known (xs: List Nat) (flag: Bool): List Nat :=
  let n := xs.length
  let bigger := n + 1
  xs.map (x =>
    match flag with
      | True => x + (({ value = bigger, above = omega }: Above n)).value
      | False => x)
