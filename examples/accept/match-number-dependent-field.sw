-- A `match` on a number a later field depends on (a character's code,
-- which its proof of being a scalar value mentions), then a `match` inside
-- its last arm: the copies the generalisation makes come in the order of
-- what they mention, so the equation `c = MkChar code valid`, bound before
-- `code` and `valid`, is copied after `valid` (SW-3752; it was
-- `E-MATCH-MOTIVE`).
def digitOrSpace (c: Char): Bool := match c with
  | ' ' => False
  | _ => 48 <= c.toNat && c.toNat <= 57

theorem atMostNine ∀ (c: Char) (h: digitOrSpace c = True): c.toNat <= 57 := match split: c with
  | MkChar code valid =>
    match number: code with
      | 32 => cases
      | other =>
        match low: 48 <= other with
          | True => cases
