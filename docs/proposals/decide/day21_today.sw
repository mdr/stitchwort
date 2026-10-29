-- Day 21's hand-written finite proofs (aoc/src/Aoc/Year2024/Day21), with
-- the types and definitions they need copied here: can today's `cases`
-- do them?
import Std (Bool, List, Nat)

type Direction =
  | Up
  | Down
  | Left
  | Right

type DirectionKey =
  | Arrow (direction: Direction)
  | Activate

type NumericKey =
  | Digit0
  | Digit1
  | Digit2
  | Digit3
  | Digit4
  | Digit5
  | Digit6
  | Digit7
  | Digit8
  | Digit9
  | Enter

type Costs = DirectionKey → DirectionKey → Nat

def directionKeys: List DirectionKey := [Arrow Up, Arrow Down, Arrow Left, Arrow Right, Activate]

def numericKeys: List NumericKey := [Digit0, Digit1, Digit2, Digit3, Digit4, Digit5, Digit6, Digit7, Digit8, Digit9, Enter]

def DirectionKey.index (key: DirectionKey): Nat :=
  match key with
    | Arrow Up => 0
    | Arrow Down => 1
    | Arrow Left => 2
    | Arrow Right => 3
    | Activate => 4

def Costs.tabulate (costs: Costs): Costs :=
  let table := directionKeys.map (from => directionKeys.map (to => costs from to))
  from to => table.getOr from.index [] |> .getOr to.index 0

-- Presses.sw's `tabulateSame` is 25 arms of `rfl`; `costs` is a variable,
-- so each case is closed by computing with it unknown.
theorem tabulateSame (costs: Costs) (from: DirectionKey) (to: DirectionKey): costs.tabulate from to = costs from to :=
  cases

-- Typing.sw's `everyNumericKey` is eleven arms of `Inr (… (Inl rfl))`.
-- `cases` can't split `key` in `key ∈ numericKeys` (a disjunction of
-- propositions, not stuck on `key`), but it can in the `Bool` form, and
-- `List.memContains` turns that into membership.
theorem containsNumericKey (key: NumericKey): numericKeys.contains key = True := cases

theorem everyNumericKey (key: NumericKey): key ∈ numericKeys :=
  (List.memContains numericKeys key).forward (containsNumericKey key)
