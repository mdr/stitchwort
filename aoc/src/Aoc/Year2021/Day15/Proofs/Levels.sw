--| The program's maps have the spec's levels: the cave's own (`levelsAgree`)
--| and the full cave's (`tiledLevelsAgree`), on a rectangle. The cave's
--| levels are looked up in the shared grid code's table (`lookupOrAt`), and
--| on a rectangle a position has a level exactly when it is on the map
--| (`atOfWithin`, `withinOfAt`).

namespace Aoc.Year2021.Day15.Proofs
import Aoc.Year2021.Day15 (..)
import Aoc.Year2021.Day15.Spec (..)
import Aoc.Common (Position, cellAt, firstWidth)
import Aoc.Common.Proofs (atOfWithin, cellAtMapCells, lookupOrAt, withinOfAt)
import Std (Bool, DecEq, Eq, Exists, Fin, List, Map, Nat, Option, Void)

--| The spec's level is the digit at the position.
theorem levelAtCell ∀ (cave: Cave) (position: Position): levelAt cave position = (cellAt cave.grid.rows position).map Fin.toNat :=
  match cave.grid.rows.get position.row with
    | None => rfl
    | Some row => rfl

--| The program's level is the digit at the position, or 0 off the cave.
theorem levelsAt ∀ (cave: Cave) (position: Position): cave.levels position = ((cellAt cave.grid.rows position).map Fin.toNat).getOrElse 0 :=
  rewrite lookupOrAt (cave.grid.map (_ digit => digit.toNat)) 0 position in
    Eq.cong (found => Option.getOrElse found 0) (cellAtMapCells cave.grid.rows (_ digit => digit.toNat) position)

--| On a rectangle, the cave's map has the spec's levels.
theorem levelsAgree ∀ (cave: Cave) (rectangle: Rectangle cave) (position: Position): levelAt cave position = cave.risks.levelAt position :=
  rewrite levelAtCell cave position in
    match inside: position.within cave.height cave.width with
      | True =>
        Exists.elim (atOfWithin cave.grid (And.right rectangle) position inside) (digit found =>
          let level: cave.levels position = digit.toNat := rewrite levelsAt cave position, found in rfl
          rewrite found, level in rfl)
      | False =>
        match found: cellAt cave.grid.rows position with
          | None => rfl
          | Some digit => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym inside) (withinOfAt cave.grid (And.right rectangle) position digit found)))

--| `wrap` leaves a level up to 9...
theorem wrapSmall ∀ (level: Nat) (small: level ≤ 9): wrap level = level := rewrite Nat.leqFalseOfLess level 10 (omega [small]) in rfl

--| ...and takes 9 from one above.
theorem wrapLarge ∀ (level: Nat) (large: 9 < level): wrap level = level - 9 := rewrite large in rfl

theorem iterateRaise ∀ (count level: Nat) (low: level ≤ 9) (sum: level + count ≤ 17): count.iterate raise level = wrap (level + count) :=
  match count with
    | Zero => rewrite Nat.addZero level, wrapSmall level low in rfl
    | Succ count =>
      match nine: level == 9 with
        | True =>
          let same := nine
          let later := iterateRaise count 1 (omega) (omega [sum, same])
          rewrite later, wrapSmall (1 + count) (omega [sum, same]), wrapLarge (level + Succ count) (omega [same]) in omega [same]
        | False =>
          let other := nine
          let later := iterateRaise count (level + 1) (omega [low, other]) (omega [sum])
          let same: level + 1 + count = level + Succ count := omega
          rewrite later, same in rfl

--| A cave with a row and a column tiles in full.
theorem tiledIsTiles ∀ (cave: Cave) (tall: cave.height ≠ 0) (wide: cave.width ≠ 0): cave.tiled = cave.tiles :=
  match h: cave.height with
    | Zero => Void.exfalso (tall h)
    | Succ _ =>
      match w: cave.width with
        | Zero => Void.exfalso (wide w)
        | Succ _ => rfl

--| On a cave with a row and a column, the spec's level is its test of the
--| position alone.
theorem tiledLevelAtOn ∀ (cave: Cave) (tall: cave.height ≠ 0) (wide: cave.width ≠ 0) (position: Position):
    tiledLevelAt cave position =
      (if position.row < 5 * cave.height && position.column < 5 * cave.width then
        levelAt cave { row = position.row % cave.height, column = position.column % cave.width }
          |> .map (level => (position.row / cave.height + position.column / cave.width).iterate raise level)
      else None) :=
  match h: cave.height with
    | Zero => Void.exfalso (tall h)
    | Succ _ =>
      match w: cave.width with
        | Zero => Void.exfalso (wide w)
        | Succ _ => rfl

--| On a rectangle, the full cave's map has the spec's levels.
theorem tiledLevelsAgree ∀ (cave: Cave) (rectangle: Rectangle cave) (position: Position): tiledLevelAt cave position = cave.tiled.levelAt position :=
  let wide: cave.width ≠ 0 := omega [And.left rectangle]
  let tall: cave.height ≠ 0 := heightNotZero cave rectangle
  rewrite tiledIsTiles cave tall wide, tiledLevelAtOn cave tall wide position in
    match rowIn: position.row < 5 * cave.height with
      | False => rfl
      | True =>
        match columnIn: position.column < 5 * cave.width with
          | False => rfl
          | True =>
            let place: Position := { row = position.row % cave.height, column = position.column % cave.width }
            let onMap: (place.row < cave.risks.height && place.column < cave.risks.width) = True :=
              Both (Nat.modLess position.row cave.height tall) (Nat.modLess position.column cave.width wide)
            let base := cave.levels place
            let found: levelAt cave place = Some base := Eq.trans (levelsAgree cave rectangle place) (levelAtOn cave.risks place onMap)
            let tileRow := Nat.divLeOfLtMul position.row 4 cave.height (omega [rowIn])
            let tileColumn := Nat.divLeOfLtMul position.column 4 cave.width (omega [columnIn])
            let raised :=
              iterateRaise (position.row / cave.height + position.column / cave.width) base (omega [levelBelow10 cave place base found])
                (omega [levelBelow10 cave place base found, tileRow, tileColumn])
            rewrite found, raised in rfl

--| A rectangle has a row.
theorem heightNotZero ∀ (cave: Cave) (rectangle: Rectangle cave): cave.height ≠ 0 :=
  zero => omega [And.left rectangle, noRowsNoWidth cave.grid.rows zero]

--| Without rows there is no first row to have a width.
theorem noRowsNoWidth ∀ (rows: List (List (Fin 10))) (zero: rows.length = 0): firstWidth rows = 0 := match rows with
  | [] => rfl
  | [first, ..rest] => omega [zero]

--| A level of the cave is a digit's.
theorem levelBelow10 ∀ (cave: Cave) (position: Position) (level: Nat) (found: levelAt cave position = Some level): level < 10 :=
  match r: cave.grid.rows.get position.row with
    | Some cells =>
      match c: cells.get position.column with
        | Some digit => rewrite <- Option.someInjective found in Fin.toNatLt digit
