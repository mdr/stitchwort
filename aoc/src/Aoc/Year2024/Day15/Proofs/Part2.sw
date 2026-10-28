namespace Aoc.Year2024.Day15.Proofs
import Aoc.Year2024.Day15 (..)
import Aoc.Year2024.Day15.Spec (..)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Iff, Int, List, Map, Nat, Not, Option, Or, Set, Void)

-- A cell a box covers after a step is one it moves into, or one of its own.
theorem frontOrOwn (box: Position) (direction: Direction) (cell: Position) (covered: cell ∈ cellsOf (box.step direction)):
    Or (cell ∈ frontOf box direction) (cell ∈ cellsOf box) :=
  match DecEq.decide cell box with
    | Yes atBox => Inr (Inl (Eq.sym atBox))
    | No notBox =>
      match DecEq.decide cell (box.step Right) with
        | Yes atRight => Inr (Inr (Inl (Eq.sym atRight)))
        | No notRight =>
          let notOwn: Not (cell ∈ cellsOf box) := own =>
            match own with
              | Inl same => notBox (Eq.sym same)
              | Inr (Inl same) => notRight (Eq.sym same)
              | Inr (Inr none) => none
          Inl
            (List.memFilterIntro (cellsOf (box.step direction)) (other => other ∉ cellsOf box) cell covered
              (rewrite Decidable.toBoolOfNot (List.decMem cell (cellsOf box)) notOwn in rfl))
