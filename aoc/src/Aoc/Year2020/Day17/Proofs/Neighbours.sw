--| A cube's neighbours are exactly the spec's: each cube the spec calls a
--| neighbour is in `Cube.neighbours` once, and no other cube is.

namespace Aoc.Year2020.Day17.Proofs
import Aoc.Year2020.Day17 (..)
import Aoc.Year2020.Day17 (Spec)
import Std (Bool, DecEq, Eq, Int, List, Nat, Void)

theorem countPrefixed ∀ (here: Int) (others: List (List Int)) (y: Int) (ys: List Int):
    (others.map (more => [here, ..more])).count (== [y, ..ys]) = (if here == y then others.count (== ys) else 0) :=
  rewrite List.countMap others (== [y, ..ys]) (more => [here, ..more]),
      List.countCongMem others (more => [here, ..more] == [y, ..ys]) (more => here == y ∧ more == ys) (more _ =>
        List.beqCons here more y ys) then
    match here == y with
      | True => byComputing
      | False => List.countFalse others

theorem countPrefixedNil ∀ (here: Int) (others: List (List Int)):
    (others.map (more => [here, ..more])).count (== []) = 0 :=
  rewrite List.countMap others (== []) (more => [here, ..more]) then List.countFalse others

--| Of `x - 1`, `x` and `x + 1`, `y` is one exactly when it is within 1
--| of `x`.
theorem window ∀ (x y: Int):
    (if x + (-1) == y then 1 else 0) + (if x == y then 1 else 0) + (if x + 1 == y then 1 else 0)
      = Bool.toNat (x + (-1) <= y && y <= x + 1) :=
  cases

theorem windowAnd ∀ (x y: Int) (rest: Bool):
    (if x + (-1) == y then Bool.toNat rest else 0)
      + (if x == y then Bool.toNat rest else 0)
      + (if x + 1 == y then Bool.toNat rest else 0)
      = Bool.toNat (x + (-1) <= y && y <= x + 1 && rest) :=
  match rest with
    | True => rewrite Bool.andTrue (y <= x + 1) then window x y
    | False => rewrite Bool.andFalse (y <= x + 1), Bool.andFalse (x + (-1) <= y) then cases

theorem countWithin1 ∀ (xs ys: List Int): (within1 xs).count (== ys) = Bool.toNat (Spec.within1 xs ys) :=
  match xs, ys with
    | [], [] => byComputing
    | [], [y, ..ys] => byComputing
    | [x, ..xs], [] =>
      rewrite List.countFlatMap (here => (within1 xs).map (more => [here, ..more])) (== []) [
        x - 1,
        x,
        x + 1
      ], countPrefixedNil (x - 1) (within1 xs), countPrefixedNil x (within1 xs), countPrefixedNil (x + 1) (within1 xs)
    | [x, ..xs], [y, ..ys] =>
      rewrite List.countFlatMap (here => (within1 xs).map (more => [here, ..more])) (== [y, ..ys]) [x - 1, x, x + 1],
          countPrefixed (x - 1) (within1 xs) y ys,
          countPrefixed x (within1 xs) y ys,
          countPrefixed (x + 1) (within1 xs) y ys,
          countWithin1 xs ys then
        windowAnd x y (Spec.within1 xs ys)

theorem equalCubes ∀ (here there: List Int):
    (({ coordinates = here }: Cube) == { coordinates = there }) = (here == there) :=
  byComputing

theorem differentCubes ∀ (here there: List Int):
    ((({ coordinates = here }: Cube) != { coordinates = there }): Bool) = ((here != there): Bool) :=
  byComputing

theorem countNeighbours ∀ (cube other: Cube):
    cube.neighbours.count (== other) = Bool.toNat (Spec.neighbours cube other) :=
  match cube, other with
    | { coordinates = here }, { coordinates = there } =>
      rewrite List.countMap
            ((within1 here).filter (coordinates => coordinates != here))
            (== { coordinates = there })
            (coordinates => { coordinates }),
          List.countCongMem ((within1 here).filter (coordinates => coordinates != here)) _ (== there) (coordinates _ =>
            equalCubes coordinates there),
          differentCubes here there then
        match e: here != there with
          | True =>
            rewrite List.countFilter (within1 here) (== there) (coordinates => coordinates != here) (coordinates same =>
                  rewrite same.read then (differ => e.read.read differ.flipped)) then
              countWithin1 here there
          | False =>
            rewrite DecEq.neFalse here there e then
              Eq.trans
                (List.countCongMem
                  ((within1 there).filter (coordinates => coordinates != there))
                  (== there)
                  (coordinates => False)
                  (coordinates member =>
                    match same: coordinates == there with
                      | True => Void.impossible (DecEq.neTrue (List.memFilter _ _ member).right same.read)
                      | False => byComputing))
                (List.countFalse _)
