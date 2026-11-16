import Std (List)

-- `rewrite repeatedly [rules]` rewrites with each rule wherever it fits,
-- over and over, until none does, and then finishes the proof by
-- computing. No need to say which rule goes where, or in what order.
theorem regroup ∀ (xs ys zs: List Nat): ((xs ++ ys) ++ zs) ++ [] = xs ++ (ys ++ zs) :=
  rewrite repeatedly [List.appendAssoc, List.appendNil]

-- Facts you have are rules too: here the proof by arms uses itself, on the
-- shorter list, as one of them.
theorem reverseSnoc ∀ (xs: List Nat) (x: Nat): (xs ++ [x]).reverse = [x, ..xs.reverse] := match xs with
  | [] => byComputing
  | [y, ..rest] => rewrite repeatedly [List.reverseCons, reverseSnoc rest x]

-- What the rules leave can be finished by another proof after `then`. Best
-- one that doesn't depend on its exact shape, such as `arithmetic`.
theorem stillShort ∀ (xs: List Nat) (n: Nat) (h: n < xs.length): n < (xs ++ []).length + 1 :=
  rewrite repeatedly [List.appendNil] then arithmetic
