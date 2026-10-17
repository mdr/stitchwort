-- expect-error: E-MATCH-MOTIVE
-- The second scrutinee's type mentions the first (`List.length xs`), so they
-- can't be matched together. Write a helper with a signature instead.
type Tagged (n : Nat) : Type =
  | MkTagged

tag : (xs : List Nat) -> Tagged (List.length xs)
tag xs = MkTagged

bad : List Nat -> Nat
bad xs = 1 + match List.length xs, tag xs with
  | Zero, _ -> 0
  | Succ k, _ -> k
