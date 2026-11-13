--| A cube's neighbours are exactly the spec's: each cube the spec calls a
--| neighbour is in `Cube.neighbours` once, and no other cube is.

namespace Aoc.Year2020.Day17.Proofs
import Aoc.Year2020.Day17 (..)
import Aoc.Year2020.Day17 (Spec)
import Std (Bool, DecEq, Eq, Int, List, Nat, Void)

theorem countPrefixed ∀ (here: Int) (others: List (List Int)) (y: Int) (ys: List Int):
    (others.map (more => [here, ..more])).count (== [y, ..ys]) = (if here == y then others.count (== ys) else 0) :=
  rewrite List.countMap others (== [y, ..ys]) (more => [here, ..more]) in
    rewrite List.countCongMem others (more => [here, ..more] == [y, ..ys]) (more => here == y ∧ more == ys) (more _ => List.beqCons here more y ys) in
      match here == y with
        | True => rfl
        | False => List.countFalse others

theorem countPrefixedNil ∀ (here: Int) (others: List (List Int)): (others.map (more => [here, ..more])).count (== []) = 0 :=
  rewrite List.countMap others (== []) (more => [here, ..more]) in List.countFalse others

--| Of `x - 1`, `x` and `x + 1`, `y` is one exactly when it is within 1
--| of `x`.
theorem window ∀ (x: Int) (y: Int):
    (if x + (-1) == y then 1 else 0) + (if x == y then 1 else 0) + (if x + 1 == y then 1 else 0) = Bool.toNat (x + (-1) <= y && y <= x + 1) :=
  cases

theorem windowAnd ∀ (x: Int) (y: Int) (rest: Bool):
    (if x + (-1) == y then Bool.toNat rest else 0) + (if x == y then Bool.toNat rest else 0) + (if x + 1 == y then Bool.toNat rest else 0)
    = Bool.toNat (x + (-1) <= y && y <= x + 1 && rest) := match rest with
      | True => rewrite Bool.andTrue (y <= x + 1) in window x y
      | False => rewrite Bool.andFalse (y <= x + 1), Bool.andFalse (x + (-1) <= y) in cases

theorem countWithin1 ∀ (xs ys: List Int): (within1 xs).count (== ys) = Bool.toNat (Spec.within1 xs ys) :=
  match xs, ys with
    | [], [] => rfl
    | [], [y, ..ys] => rfl
    | [x, ..xs], [] =>
      rewrite List.countFlatMap (here => (within1 xs).map (more => [here, ..more])) (== []) [x - 1, x, x + 1] in
        rewrite countPrefixedNil (x - 1) (within1 xs), countPrefixedNil x (within1 xs), countPrefixedNil (x + 1) (within1 xs) in rfl
    | [x, ..xs], [y, ..ys] =>
      rewrite List.countFlatMap (here => (within1 xs).map (more => [here, ..more])) (== [y, ..ys]) [x - 1, x, x + 1] in
        rewrite countPrefixed (x - 1) (within1 xs) y ys, countPrefixed x (within1 xs) y ys, countPrefixed (x + 1) (within1 xs) y ys, countWithin1 xs ys in windowAnd x y (Spec.within1 xs ys)

theorem equalCubes ∀ (here: List Int) (there: List Int): (({ coordinates = here }: Cube) == { coordinates = there }) = (here == there) :=
  rfl

theorem differentCubes ∀ (here: List Int) (there: List Int): ((({ coordinates = here }: Cube) != { coordinates = there }): Bool) = ((here != there): Bool) :=
  rfl

theorem countNeighbours ∀ (cube other: Cube): cube.neighbours.count (== other) = Bool.toNat (Spec.neighbours cube other) :=
  match cube, other with
    | { coordinates = here }, { coordinates = there } =>
      rewrite List.countMap ((within1 here).filter (coordinates => coordinates != here)) (== { coordinates = there }) (coordinates => { coordinates }) in
        rewrite List.countCongMem ((within1 here).filter (coordinates => coordinates != here)) _ (== there) (coordinates _ => equalCubes coordinates there) in
          rewrite differentCubes here there in
            match e: here != there with
              | True =>
                rewrite List.countFilter (within1 here) (== there) (coordinates => coordinates != here)
                  (coordinates same => rewrite same.read in (differ => e.read.read (Eq.sym differ))) in
                  countWithin1 here there
              | False =>
                rewrite DecEq.neFalse here there e in
                  Eq.trans
                    (List.countCongMem ((within1 there).filter (coordinates => coordinates != there)) (== there) (coordinates => False)
                      (coordinates member =>
                        match same: coordinates == there with
                          | True => Void.exfalso (DecEq.neTrue (And.right (List.memFilter _ _ member)) same.read)
                          | False => rfl))
                    (List.countFalse _)
