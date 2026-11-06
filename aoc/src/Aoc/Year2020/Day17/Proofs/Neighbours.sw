--| A cube's neighbours are exactly the spec's: each cube the spec calls a
--| neighbour is in `Cube.neighbours` once, and no other cube is.

namespace Aoc.Year2020.Day17.Proofs
import Aoc.Year2020.Day17 (..)
import Aoc.Year2020.Day17 (Spec)
import Std (Bool, DecEq, Eq, Int, List, Nat, Void)

--| Two lists with a first element are equal when their first elements are
--| and the rests are.
theorem equalCons [auto eq: DecEq a] (x: a) (xs: List a) (y: a) (ys: List a): ([x, ..xs] == [y, ..ys]) = (x == y ∧ xs == ys) :=
  Bool.eqOf _ _
    (same =>
      let lists := DecEq.sound same
      rewrite List.consInjectiveHead x y xs ys lists, (Eq.cong (.drop 1) lists: xs = ys) in Bool.andIntro (DecEq.refl y) (DecEq.refl ys))
    (both => rewrite DecEq.sound (Bool.andLeft both), DecEq.sound (Bool.andRight both) in DecEq.refl [y, ..ys])

theorem countPrefixed (here: Int) (others: List (List Int)) (y: Int) (ys: List Int):
    (others.map (more => [here, ..more])).count (== [y, ..ys]) = (if here == y then others.count (== ys) else 0) :=
  rewrite List.countMap others (== [y, ..ys]) (more => [here, ..more]) in
    rewrite List.countCongMem others (more => [here, ..more] == [y, ..ys]) (more => here == y ∧ more == ys) (more _ => equalCons here more y ys) in
      match here == y with
        | True => rfl
        | False => List.countFalse others

theorem countPrefixedNil (here: Int) (others: List (List Int)): (others.map (more => [here, ..more])).count (== []) = 0 :=
  rewrite List.countMap others (== []) (more => [here, ..more]) in List.countFalse others

--| Of `x - 1`, `x` and `x + 1`, `y` is one exactly when it is within 1
--| of `x`.
theorem window (x: Int) (y: Int):
    (if x + (-1) == y then 1 else 0) + (if x == y then 1 else 0) + (if x + 1 == y then 1 else 0) = Bool.toNat (x + (-1) <= y && y <= x + 1) :=
  match d: x + (-1) <= y && y <= x + 1 with
    | True => match a: x + (-1) == y with
      | True => match b: x == y with
        | True => omega
        | False => match c: x + 1 == y with
          | True => omega
          | False => omega
      | False => match b: x == y with
        | True => match c: x + 1 == y with
          | True => omega
          | False => omega
        | False => match c: x + 1 == y with
          | True => omega
          | False => omega
    | False => match a: x + (-1) == y with
      | True => omega
      | False => match b: x == y with
        | True => omega
        | False => match c: x + 1 == y with
          | True => omega
          | False => omega

theorem windowAnd (x: Int) (y: Int) (rest: Bool):
    (if x + (-1) == y then Bool.toNat rest else 0) + (if x == y then Bool.toNat rest else 0) + (if x + 1 == y then Bool.toNat rest else 0)
      = Bool.toNat (x + (-1) <= y && y <= x + 1 && rest) :=
  match rest with
    | True => rewrite Bool.andTrue (y <= x + 1) in window x y
    | False => rewrite Bool.andFalse (y <= x + 1), Bool.andFalse (x + (-1) <= y) in cases

theorem countWithin1: (xs: List Int) → (ys: List Int) → (within1 xs).count (== ys) = Bool.toNat (Spec.within1 xs ys)
  | [], [] => rfl
  | [], [y, ..ys] => rfl
  | [x, ..xs], [] =>
    rewrite List.countFlatMap (here => (within1 xs).map (more => [here, ..more])) (== []) [x - 1, x, x + 1] in
      rewrite countPrefixedNil (x - 1) (within1 xs), countPrefixedNil x (within1 xs), countPrefixedNil (x + 1) (within1 xs) in rfl
  | [x, ..xs], [y, ..ys] =>
    rewrite List.countFlatMap (here => (within1 xs).map (more => [here, ..more])) (== [y, ..ys]) [x - 1, x, x + 1] in
      rewrite countPrefixed (x - 1) (within1 xs) y ys, countPrefixed x (within1 xs) y ys, countPrefixed (x + 1) (within1 xs) y ys, countWithin1 xs ys in windowAnd x y (Spec.within1 xs ys)

theorem equalCubes (here: List Int) (there: List Int): (({ coordinates = here }: Cube) == { coordinates = there }) = (here == there) :=
  Bool.eqOf _ _
    (same => rewrite (Eq.cong (.coordinates) (DecEq.sound same): here = there) in DecEq.refl there)
    (same => rewrite DecEq.sound same in DecEq.refl ({ coordinates = there }: Cube))

theorem differentSelf [auto eq: DecEq a] (x: a): ((x != x): Bool) = False :=
  match e: ((x != x): Bool) with
    | True => Void.exfalso (DecEq.neTrue e rfl)
    | False => rfl

theorem differentCubes (here: List Int) (there: List Int): ((({ coordinates = here }: Cube) != { coordinates = there }): Bool) = ((here != there): Bool) :=
  match e: ((here != there): Bool) with
    | True => DecEq.trueOfNe (same => DecEq.neTrue e (Eq.cong (.coordinates) same))
    | False => rewrite DecEq.neFalse here there e in differentSelf ({ coordinates = there }: Cube)

theorem countNeighbours: (cube: Cube) → (other: Cube) → cube.neighbours.count (== other) = Bool.toNat (Spec.neighbours cube other)
  | { coordinates = here }, { coordinates = there } =>
    rewrite List.countMap ((within1 here).filter (coordinates => coordinates != here)) (== { coordinates = there }) (coordinates => { coordinates }) in
      rewrite List.countCongMem ((within1 here).filter (coordinates => coordinates != here)) _ (== there) (coordinates _ => equalCubes coordinates there) in
        rewrite differentCubes here there in
          match e: here != there with
            | True =>
              rewrite List.countFilter (within1 here) (== there) (coordinates => coordinates != here)
                (coordinates same => rewrite DecEq.sound same in DecEq.trueOfNe (differ => DecEq.neTrue e (Eq.sym differ))) in
                countWithin1 here there
            | False =>
              rewrite DecEq.neFalse here there e in
                Eq.trans
                  (List.countCongMem ((within1 there).filter (coordinates => coordinates != there)) (== there) (coordinates => False)
                    (coordinates member =>
                      match same: coordinates == there with
                        | True => Void.exfalso (DecEq.neTrue (And.right (List.memFilter _ _ member)) (DecEq.sound same))
                        | False => rfl))
                  (List.countFalse _)
