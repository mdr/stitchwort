-- The program's steps are the spec's: `uphill` gives exactly the positions
-- on the map one orthogonal step away and one higher (`memUphill`), each
-- once, and `positions` lists every position with a height, each once.

namespace Aoc.Year2024.Day10.Proofs
import Aoc.Year2024.Day10 (..)
import Aoc.Year2024.Day10.Spec (..)
import Std (And, Bool, DecEq, Eq, Iff, List, Nat, Option, Void)

-- Each neighbour is one orthogonal step away.
theorem neighbourOrthogonal: (from: Position) → (to: Position) → to ∈ from.neighbours → isOrthogonalStep from to = True
  | { row = Zero, column = Zero }, to, Inl same => rewrite <- same in omega
  | { row = Zero, column = Zero }, to, Inr (Inl same) => rewrite <- same in omega
  | { row = Zero, column = Zero }, to, Inr (Inr none) => Void.exfalso none
  | { row = Zero, column = Succ previous }, to, Inl same => rewrite <- same in omega
  | { row = Zero, column = Succ previous }, to, Inr (Inl same) => rewrite <- same in omega
  | { row = Zero, column = Succ previous }, to, Inr (Inr (Inl same)) => rewrite <- same in omega
  | { row = Zero, column = Succ previous }, to, Inr (Inr (Inr none)) => Void.exfalso none
  | { row = Succ up, column = Zero }, to, Inl same => rewrite <- same in omega
  | { row = Succ up, column = Zero }, to, Inr (Inl same) => rewrite <- same in omega
  | { row = Succ up, column = Zero }, to, Inr (Inr (Inl same)) => rewrite <- same in omega
  | { row = Succ up, column = Zero }, to, Inr (Inr (Inr none)) => Void.exfalso none
  | { row = Succ up, column = Succ previous }, to, Inl same => rewrite <- same in omega
  | { row = Succ up, column = Succ previous }, to, Inr (Inl same) => rewrite <- same in omega
  | { row = Succ up, column = Succ previous }, to, Inr (Inr (Inl same)) => rewrite <- same in omega
  | { row = Succ up, column = Succ previous }, to, Inr (Inr (Inr (Inl same))) => rewrite <- same in omega
  | { row = Succ up, column = Succ previous }, to, Inr (Inr (Inr (Inr none))) => Void.exfalso none

-- One orthogonal step, by direction: right or left in the same row, or down
-- or up in the same column. `omega` gives it from `isOrthogonalStep`.
def Orthogonal (from: Position) (to: Position): Prop :=
  Or (And (from.row = to.row) (Or (from.column + 1 = to.column) (to.column + 1 = from.column)))
    (And (from.column = to.column) (Or (from.row + 1 = to.row) (to.row + 1 = from.row)))

-- Each position one orthogonal step away is a neighbour.
theorem orthogonalNeighbour: (from: Position) → (to: Position) → Orthogonal from to → to ∈ from.neighbours
  | { row, column }, { row = toRow, column = toColumn }, Inl (Both rows (Inl right)) =>
    let from: Position := { row, column }
    rewrite <- rows, <- right in List.memAppendRight _ from.above (from.leftOf ++ from.rightAndBelow) (List.memAppendRight _ from.leftOf from.rightAndBelow (Inl rfl))
  | { row, column = Zero }, { row = toRow, column = toColumn }, Inl (Both rows (Inr left)) => Void.exfalso (omega)
  | { row, column = Succ previous }, { row = toRow, column = toColumn }, Inl (Both rows (Inr left)) =>
    let from: Position := { row, column = Succ previous }
    let same: previous = toColumn := omega
    rewrite <- rows, <- same in List.memAppendRight _ from.above (from.leftOf ++ from.rightAndBelow) (List.memAppendLeft _ from.leftOf from.rightAndBelow (Inl rfl))
  | { row, column }, { row = toRow, column = toColumn }, Inr (Both columns (Inl down)) =>
    let from: Position := { row, column }
    rewrite <- columns, <- down in List.memAppendRight _ from.above (from.leftOf ++ from.rightAndBelow) (List.memAppendRight _ from.leftOf from.rightAndBelow (Inr (Inl rfl)))
  | { row = Zero, column }, { row = toRow, column = toColumn }, Inr (Both columns (Inr up)) => Void.exfalso (omega)
  | { row = Succ above, column }, { row = toRow, column = toColumn }, Inr (Both columns (Inr up)) =>
    let from: Position := { row = Succ above, column }
    let same: above = toRow := omega
    rewrite <- columns, <- same in List.memAppendLeft _ from.above (from.leftOf ++ from.rightAndBelow) (Inl rfl)

-- Positions in different rows, or different columns, are different.
theorem rowsApart (first: Position) (second: Position) (apart: Not (first.row = second.row)): Not (first = second) :=
  same => apart (Eq.cong (position => position.row) same)

theorem columnsApart (first: Position) (second: Position) (apart: Not (first.column = second.column)): Not (first = second) :=
  same => apart (Eq.cong (position => position.column) same)

theorem notCons (position: Position) (first: Position) (rest: List Position) (apart: Not (first = position)) (notRest: position ∉ rest):
    position ∉ Cons first rest :=
  member =>
    match member with
      | Inl same => apart same
      | Inr later => notRest later

-- The neighbours are four different positions, or fewer at an edge.
theorem neighboursDistinct: (from: Position) → List.Distinct from.neighbours
  | { row = Zero, column = Zero } => Both (notCons _ _ _ (rowsApart _ _ (omega)) (none => none)) (Both (none => none) Trivial)
  | { row = Zero, column = Succ previous } =>
    Both (notCons _ _ _ (columnsApart _ _ (omega)) (notCons _ _ _ (rowsApart _ _ (omega)) (none => none)))
      (Both (notCons _ _ _ (rowsApart _ _ (omega)) (none => none)) (Both (none => none) Trivial))
  | { row = Succ up, column = Zero } =>
    Both (notCons _ _ _ (rowsApart _ _ (omega)) (notCons _ _ _ (rowsApart _ _ (omega)) (none => none)))
      (Both (notCons _ _ _ (rowsApart _ _ (omega)) (none => none)) (Both (none => none) Trivial))
  | { row = Succ up, column = Succ previous } =>
    Both (notCons _ _ _ (rowsApart _ _ (omega)) (notCons _ _ _ (rowsApart _ _ (omega)) (notCons _ _ _ (rowsApart _ _ (omega)) (none => none))))
      (Both (notCons _ _ _ (columnsApart _ _ (omega)) (notCons _ _ _ (rowsApart _ _ (omega)) (none => none)))
        (Both (notCons _ _ _ (rowsApart _ _ (omega)) (none => none)) (Both (none => none) Trivial)))

-- The positions in row `row`.
def rowPositions (map: TopographicMap) (row: Nat): List Position :=
  List.range (map.rows.getOr row Nil).length |> .map (column => ({ row, column }: Position))

-- Every position with a height is on the list.
theorem positionsComplete (map: TopographicMap): (position: Position) → (height: Nat) → map.heightAt position = Some height → position ∈ map.positions
  | { row, column }, height, has =>
    match rowInside: row < map.rows.length with
      | False => Void.exfalso (Option.noneNotSome height (rewrite List.getOrPast map.rows row Nil (omega) at has))
      | True =>
        match columnInside: column < (map.rows.getOr row Nil).length with
          | False => Void.exfalso (Option.noneNotSome height (rewrite List.getOrPast (map.rows.getOr row Nil) column None (omega) at has))
          | True =>
            List.memFlatMapIntro (rowPositions map) row { row, column } (List.range map.rows.length)
              (List.memRangeFromIntro row map.rows.length 0 (omega) (omega))
              (List.memMap (List.range (map.rows.getOr row Nil).length) column
                (List.memRangeFromIntro column (map.rows.getOr row Nil).length 0 (omega) (omega)) (column => ({ row, column }: Position)))

-- Each position is on the list once.
theorem positionsDistinct (map: TopographicMap): List.Distinct map.positions :=
  List.distinctFlatMap (rowPositions map) (position => position.row) (List.range map.rows.length) (List.distinctRangeFrom map.rows.length 0)
    (row inRows =>
      List.distinctMap (List.range (map.rows.getOr row Nil).length) (List.distinctRangeFrom (map.rows.getOr row Nil).length 0)
        (column => ({ row, column }: Position)) (first second same => Eq.cong (position => position.column) same))
    (row inRows position member =>
      List.anyElim (column => ({ row, column }: Position) = position) (position.row = row) (List.range (map.rows.getOr row Nil).length)
        (List.memMapAny (List.range (map.rows.getOr row Nil).length) (column => ({ row, column }: Position)) position member)
        (column inColumns built => rewrite <- built in rfl))

-- A position one higher than another has a height, so it is on the map.
theorem higherOnMap (map: TopographicMap) (from: Position) (to: Position) (higher: increasesByOne map from to = True): to ∈ map.positions :=
  match known: map.heightAt from with
    | Some height => positionsComplete map to (height + 1) (DecEq.sound _ _ higher)
    | None => Void.exfalso (Bool.falseNotTrue higher)

-- `uphill` is the spec's steps from `from`.
theorem memUphill (map: TopographicMap) (from: Position) (to: Position): to ∈ map.uphill from ↔ And (to ∈ map.positions) (isStep map from to = True) := {
  forward = member =>
    let both := List.memFilter from.neighbours (map.isOneHigher from) to member
    Both (higherOnMap map from to (And.right both))
      (Bool.andIntro _ _ (neighbourOrthogonal from to (And.left both)) (And.right both)),
  backward = has =>
    let step := And.right has
    List.memFilterIntro from.neighbours (map.isOneHigher from) to (orthogonalNeighbour from to (omega))
      (Bool.andRight _ _ step)
}

theorem uphillDistinct (map: TopographicMap) (from: Position): List.Distinct (map.uphill from) :=
  List.distinctFilter from.neighbours (map.isOneHigher from) (neighboursDistinct from)

-- `uphill` is the spec's steps from `from` among the positions, in another
-- order.
theorem uphillPerm (map: TopographicMap) (from: Position): List.Perm (map.positions.filter (isStep map from)) (map.uphill from) :=
  List.permOfSameMembers (map.positions.filter (isStep map from)) (map.uphill from)
    (List.distinctFilter map.positions (isStep map from) (positionsDistinct map)) (uphillDistinct map from)
    (to member => (memUphill map from to).backward (List.memFilter map.positions (isStep map from) to member))
    (to member =>
      let both := (memUphill map from to).forward member
      List.memFilterIntro map.positions (isStep map from) to (And.left both) (And.right both))
