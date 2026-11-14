-- `fillCorrect` (Fill.sw) again, by the generated `Garden.fill.induct`
-- (docs/proposals/function-equations.md §6.1, stage 2a): no decrease
-- proofs, no step lemmas, no `rewrite` with an equation (the unfolding
-- form gives each case the branch's right side). The statement is
-- `fillCorrect`'s. To run it, copy it into a copy of the AoC project as
-- `src/Aoc/Year2024/Day12/Proofs/Induct.sw` and run `stitchwort check
-- --no-cache Aoc.Year2024.Day12.Proofs` there.

namespace Aoc.Year2024.Day12.Proofs
import Aoc.Year2024.Day12 (..)
import Aoc.Common (Direction, Position, directions)
import Aoc.Year2024.Day12.Spec (..)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Iff, List, Nat, Option, Or, Set, Void)

theorem fillCorrectByInduct ∀ (garden: Garden) (plant: Char) (start: Position) (stack: List Position)
    (visited: Set Position) (members: List Position)
    (state: FillState garden plant start stack visited members):
    FillResult garden plant start stack members (Garden.fill garden plant stack visited members) :=
  Garden.fill.induct garden plant
    (stack visited members result =>
      FillState garden plant start stack visited members → FillResult garden plant start stack members result)
    (visited members state =>
      let (Both visitedMembers (Both distinct (Both sound (Both stacked closed)))) := state
      Both distinct
        (Both sound
          (Both
            (member isMember next pushed =>
              match closed member isMember next pushed with
                | Inl inMembers => inMembers
                | Inr none => Void.exfalso none)
            (Both (position member => member) (position none => Void.exfalso none)))))
    (visited members position rest fresh grows ih state =>
      let (Both distinct (Both sound (Both closed (Both kept fromStack)))) :=
        ih (takeKeeps garden plant start position rest visited members state fresh grows)
      Both distinct
        (Both sound
          (Both closed
            (Both (other member => kept other (Inr member)) (other onStack otherGrows =>
              match onStack with
                | Inl here => kept other (Inl here)
                | Inr later =>
                  fromStack other
                    (List.memAppendRight other (garden.neighboursGrowing plant position) rest later)
                    otherGrows)))))
    (visited members position rest fresh other ih state =>
      let (Both distinct (Both sound (Both closed (Both kept fromStack)))) :=
        ih (popKeeps garden plant start position rest visited members state (Inr other))
      Both distinct
        (Both sound
          (Both closed
            (Both kept (candidate onStack grows =>
              match onStack with
                | Inl here => Void.exfalso (other (rewrite here in grows))
                | Inr later => fromStack candidate later grows)))))
    (visited members position rest notFresh ih state =>
      let isMember := (And.left state position).forward notFresh
      let (Both distinct (Both sound (Both closed (Both kept fromStack)))) :=
        ih (popKeeps garden plant start position rest visited members state (Inl isMember))
      Both distinct
        (Both sound
          (Both closed
            (Both kept (other onStack grows =>
              match onStack with
                | Inl here => kept other (rewrite <- here in isMember)
                | Inr later => fromStack other later grows)))))
    stack
    visited
    members
    state
