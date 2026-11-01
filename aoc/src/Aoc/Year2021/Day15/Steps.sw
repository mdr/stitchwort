-- What the graph for the search needs: every step leads to a position on
-- the map.

namespace Aoc.Year2021.Day15
import Aoc.Year2021.Day09 (Position)
import Std (Bool, Eq, Exists, List, Nat, Option, Void)

-- A position with a level is on the map.
theorem RiskMap.onMapOfLevel (risks: RiskMap) (position: Position) (level: Nat) (found: risks.levelAt position = Some level):
    (position.row < risks.height && position.column < risks.width) = True :=
  match onMap: (position.row < risks.height && position.column < risks.width) with
    | True => rfl
    | False => Void.exfalso (Option.noneNotSome level found)

-- Every position on the map is listed.
theorem RiskMap.memPositions (risks: RiskMap): (position: Position) → (position.row < risks.height && position.column < risks.width) = True →
    position ∈ risks.positions
  | { row, column }, onMap =>
    let below: row < risks.height := Bool.andLeft _ _ onMap
    let before: column < risks.width := Bool.andRight _ _ onMap
    List.memFlatMapIntro (row => List.range risks.width |> .map (column => ({ row, column }: Position))) row { row, column } (List.range risks.height)
      (List.memRangeFromIntro row risks.height 0 (omega) (omega [below]))
      (List.memMap (List.range risks.width) column (List.memRangeFromIntro column risks.width 0 (omega) (omega [before])) (column => ({ row, column }: Position)))

-- Each step leads to a position on the map.
theorem RiskMap.edgesListed (risks: RiskMap) (position: Position) (next: Position) (weight: Nat) (edge: (next, weight) ∈ risks.edges position):
    next ∈ risks.positions :=
  Exists.elim (List.anyMember _ position.neighbours (List.memFilterMapElim (other => risks.levelAt other |> .map (level => (other, level))) (next, weight) position.neighbours edge))
    (other both =>
      match found: risks.levelAt other with
        | None => Void.exfalso (Option.noneNotSome (next, weight) (And.right both))
        | Some level =>
          let same: other = next := Eq.cong Pair.fst (Option.someInjective _ _ (And.right both))
          rewrite <- same in risks.memPositions other (risks.onMapOfLevel other level found))
