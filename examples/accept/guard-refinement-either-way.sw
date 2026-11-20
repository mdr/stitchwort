-- A guard on a `Bool` column with arms below that split the same column
-- (SW-4388): the guard refines the goal, and the arms below are checked in
-- the cases they split, as they were before guards refined (D3688).

theorem eitherWay ∀ (n: Nat) (b: Bool): b = True ∨ b = False := match n, b with
  | 0, c if g: c => Inl g
  | _, True => Inl byComputing
  | _, False => Inr byComputing
