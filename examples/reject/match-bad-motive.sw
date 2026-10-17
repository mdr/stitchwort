-- expect-error: E-MATCH-MOTIVE
two : (m : Nat) -> m = 2 -> Bool -> Nat
two m p True = m
two m p False = 0

-- Generalising `length [1, 1]` (which is 2) makes `q`'s type ill-formed.
bad : (b : Bool) -> (q : two (List.length [1, 1]) rfl b = 2) -> Nat
bad b q = match List.length [1, 1] with
  | Zero -> 0
  | Succ k -> k
