-- List lemmas the proofs use that std doesn't have (std candidates, each
-- general).
namespace Trip.Proofs

import Std (List, Option, Eq, Void, Bool, Decidable, DecEq)

-- A key of either list is a key of `appendNewBy`.
theorem keyKeptLeft [auto eq: DecEq k] (key: a → k) (xs: List a) (ys: List a) (x: a) (m: x ∈ xs):
    key x ∈ List.map (List.appendNewBy xs ys key) key :=
  List.memMap (List.appendNewBy xs ys key) x (List.memAppendLeft x xs (List.differenceBy ys xs key) m) key

theorem keyKeptRight [auto eq: DecEq k] (key: a → k) (xs: List a) (ys: List a) (y: a) (m: y ∈ ys):
    key y ∈ List.map (List.appendNewBy xs ys key) key :=
  match List.decMem (key y) (List.map xs key) with
    | Yes h =>
    rewrite List.mapAppend xs (List.differenceBy ys xs key) key in
    List.memAppendLeft (key y) (List.map xs key) (List.map (List.differenceBy ys xs key) key) h
    | No h =>
    List.memMap (List.appendNewBy xs ys key) y
      (List.memAppendRight y xs (List.differenceBy ys xs key) ((List.memDifferenceBy y ys xs key).backward (Both m h)))
      key

-- The parts of a list with no repeats have none, and nothing in common.
theorem distinctAppendLeft: (xs: List a) → (ys: List a) → List.Distinct (List.append xs ys) → List.Distinct xs
  | Nil, ys, d => Trivial
  | Cons x rest, ys, Both out d => Both (m => out (List.memAppendLeft x rest ys m)) (distinctAppendLeft rest ys d)

theorem distinctAppendRight: (xs: List a) → (ys: List a) → List.Distinct (List.append xs ys) → List.Distinct ys
  | Nil, ys, d => d
  | Cons x rest, ys, Both out d => distinctAppendRight rest ys d

theorem distinctAppendApart: (xs: List a) → (ys: List a) → List.Distinct (List.append xs ys) → (z: a) → z ∈ xs → z ∈ ys → Void
  | Nil, ys, d, z, inXs, inYs => inXs
  | Cons x rest, ys, Both out d, z, Inl e, inYs => out (List.memAppendRight x rest ys (rewrite e in inYs))
  | Cons x rest, ys, Both out d, z, Inr inRest, inYs => distinctAppendApart rest ys d z inRest inYs

-- `filterMap` after `map`, when each element maps to itself.
theorem filterMapMapSelf (g: a → b) (f: b → Option a): (xs: List a) → ((x: a) → x ∈ xs → f (g x) = Some x)
    → List.filterMap (List.map xs g) f = xs
  | Nil, h => rfl
  | Cons x rest, h => rewrite h x (Inl rfl) in Eq.cong (Cons x) (filterMapMapSelf g f rest (y m => h y (Inr m)))

-- A permutation, the other way round.
theorem permSym (xs: List a) (ys: List a) (h: List.Perm xs ys): List.Perm ys xs := p => Eq.sym (h p)

theorem ifSame: (c: Bool) → (x: a) → (if c then x else x) = x
  | True, x => rfl
  | False, x => rfl
