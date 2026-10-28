-- Fences: in a region, a side of a plot faces the same plant exactly when
-- it touches a plot of the region (`sameAcrossFaces`), so the program's
-- perimeter, which counts sides not facing the same plant, is the spec's
-- (`perimeterCorrect`).

namespace Aoc.Year2024.Day12.Proofs
import Aoc.Year2024.Day12 (..)
import Aoc.Year2024.Day12.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, List, Nat, Option, Or, Void)

-- Sums agree when their terms agree on the list's members.
theorem sumByCongMem: (xs: List a) → (f: a → Nat) → (g: a → Nat) → ((x: a) → x ∈ xs → f x = g x) → xs.sumBy f = xs.sumBy g
  | Nil, f, g, agree => rfl
  | Cons x rest, f, g, agree =>
    rewrite List.sumByCons rest x f, List.sumByCons rest x g, agree x (Inl rfl), sumByCongMem rest f g (y member => agree y (Inr member)) in rfl

-- A side of a plot in a region faces the same plant exactly when it
-- touches a plot of the region.
theorem sameAcrossFaces (garden: Garden) (start: Position) (plant: Char) (grows: garden.plantAt start = Some plant) (region: List Position)
    (isRegion: IsRegion garden start region) (plot: Position) (member: plot ∈ region) (side: Direction):
    garden.sameAcross plot side = facesRegion region plot side :=
  let joined := (isRegion plot).forward member
  let plotGrows := joinedPlant garden plant start plot grows joined
  match stepped: plot.step side with
    | None => rewrite plotGrows in rfl
    | Some other =>
      rewrite plotGrows in
        match otherGrows: garden.plantAt other == Some plant with
          | True =>
            let touching: touches garden plot other = True :=
              Bool.andIntro _ _ (orthogonalIntro plot other (stepOrthogonal plot side other stepped))
                (growSameIntro garden plot other plant plotGrows (DecEq.sound _ _ otherGrows))
            Eq.sym ((anyEqual region other).backward ((isRegion other).backward (joinedStep garden start plot other joined touching)))
          | False =>
            match found: region.any (candidate => candidate == other) with
              | False => rfl
              | True =>
                let otherIn := (anyEqual region other).forward found
                let sameGrows := joinedPlant garden plant start other grows ((isRegion other).forward otherIn)
                Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym otherGrows) (rewrite sameGrows in DecEq.refl (Some plant))))

-- The program's perimeter of a region is the spec's.
theorem perimeterCorrect (garden: Garden) (start: Position) (plant: Char) (grows: garden.plantAt start = Some plant) (region: List Position)
    (isRegion: IsRegion garden start region): garden.perimeter region = perimeter region :=
  sumByCongMem region garden.fences (plot => directions.count (side => !facesRegion region plot side)) (plot member =>
    List.countCongMem directions (side => !garden.sameAcross plot side) (side => !facesRegion region plot side) (side inDirections =>
      rewrite sameAcrossFaces garden start plant grows region isRegion plot member side in rfl))

-- Part 1: the program's total is the spec's total price over the
-- program's regions, which are the map's regions, each once
-- (`regionsAreRegions`, `inOneRegion`).
theorem part1Correct (garden: Garden): solvePart1 garden = totalPrice garden.regions perimeter :=
  sumByCongMem garden.regions (region => region.length * garden.perimeter region) (region => area region * perimeter region) (region member =>
    Exists.elim (regionsAreRegions garden region member) (start both =>
      Exists.elim (And.left both) (plant grows => rewrite perimeterCorrect garden start plant grows region (And.left (And.right both)) in rfl)))
