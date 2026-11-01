-- The program's maps have the spec's levels: the cave's own (`levelsAgree`)
-- and the full cave's (`tiledLevelsAgree`), on a rectangle.

namespace Aoc.Year2021.Day15.Proofs
import Aoc.Year2021.Day15 (..)
import Aoc.Year2021.Day15.Spec (..)
import Aoc.Year2021.Day09 (Position)
import Std (Bool, Eq, Exists, Fin, List, Map, Nat, Option, Void)

-- The table's entry is the cave's digit.
theorem lookUpGet (rows: List (List (Fin 10))) (row: Nat) (column: Nat) (cells: List (Fin 10)) (digit: Fin 10)
    (foundRow: rows.get row = Some cells) (foundCell: cells.get column = Some digit): lookUp (Cave.table { rows }) row column = digit.toNat :=
  let byRow := (r: List (Fin 10)) => r.map Fin.toNat |> Map.byPosition
  let rowMap: Map.getOr (Map.byPosition (rows.map byRow)) row Map.empty = byRow cells :=
    rewrite Map.getOrByPosition (rows.map byRow) row Map.empty in
      List.getOrOfGet (rows.map byRow) row Map.empty (byRow cells) (rewrite List.getMap rows byRow row, foundRow in rfl)
  calc lookUp (Cave.table { rows }) row column
    _ = Map.getOr (byRow cells) column 0 := rewrite rowMap in rfl
    _ = List.getOr (cells.map Fin.toNat) column 0 := Map.getOrByPosition (cells.map Fin.toNat) column 0
    _ = digit.toNat := List.getOrOfGet (cells.map Fin.toNat) column 0 digit.toNat (rewrite List.getMap cells Fin.toNat column, foundCell in rfl)

-- On a rectangle, the cave's map has the spec's levels.
theorem levelsAgree: (cave: Cave) → Rectangle cave → (position: Position) → levelAt cave position = cave.risks.levelAt position
  | { rows }, rectangle, { row, column } =>
    let inRows := (List.getInRange rows row).forward
    match below: row < rows.length with
      | False => rewrite List.getPast rows row (omega [Nat.leqFalse (Succ row) rows.length below]) in rfl
      | True =>
        let someRow := inRows rfl
        match foundRow: rows.get row with
          | None => Void.exfalso (Bool.falseNotTrue someRow)
          | Some cells =>
            let cellsWidth: cells.length = width rows := And.right rectangle cells (List.memOfGet rows row cells foundRow)
            match before: column < width rows with
              | False => rewrite List.getPast cells column (omega [cellsWidth, Nat.leqFalse (Succ column) (width rows) before]) in rfl
              | True =>
                let someCell := (List.getInRange cells column).forward (omega [cellsWidth, before])
                match foundCell: cells.get column with
                  | None => Void.exfalso (Bool.falseNotTrue someCell)
                  | Some digit => rewrite lookUpGet rows row column cells digit foundRow foundCell in rfl

-- `wrap` leaves a level up to 9...
theorem wrapSmall (level: Nat) (small: level ≤ 9): wrap level = level := rewrite Nat.leqFalseOfLess level 10 (omega [small]) in rfl

-- ...and takes 9 from one above.
theorem wrapLarge (level: Nat) (large: 9 < level): wrap level = level - 9 := rewrite large in rfl

-- Raising a level `count` times, wrapping past 9 to 1, is adding `count`
-- and wrapping once, while the sum stays below 18 (as it does for a digit
-- raised up to 8 times).
theorem iterateRaise: (count: Nat) → (level: Nat) → level ≤ 9 → level + count ≤ 17 → count.iterate raise level = wrap (level + count)
  | Zero, level, low, sum => rewrite Nat.addZero level, wrapSmall level low in rfl
  | Succ count, level, low, sum =>
    match nine: Nat.decEq level 9 with
      | Yes same =>
        let later := iterateRaise count 1 (omega) (omega [sum, same])
        rewrite later, wrapSmall (1 + count) (omega [sum, same]), wrapLarge (level + Succ count) (omega [same]) in omega [same]
      | No other =>
        let later := iterateRaise count (level + 1) (omega [low, other]) (omega [sum])
        let same: level + 1 + count = level + Succ count := omega
        rewrite later, same in rfl

-- On a rectangle, the full cave's map has the spec's levels.
theorem tiledLevelsAgree (cave: Cave) (rectangle: Rectangle cave) (position: Position): tiledLevelAt cave position = cave.tiled.levelAt position :=
  let wide: Not (cave.width = 0) := omega [And.left rectangle]
  let tall: Not (cave.height = 0) := heightNotZero cave rectangle
  match h: Nat.decEq cave.height 0 with
    | Yes zero => Void.exfalso (tall zero)
    | No _ =>
      match w: Nat.decEq cave.width 0 with
        | Yes zero => Void.exfalso (wide zero)
        | No _ =>
          match rowIn: position.row < 5 * cave.height with
            | False => rfl
            | True =>
              match columnIn: position.column < 5 * cave.width with
                | False => rfl
                | True =>
                  let place: Position := { row = position.row % cave.height, column = position.column % cave.width }
                  let onMap: (place.row < cave.risks.height && place.column < cave.risks.width) = True :=
                    Bool.andIntro _ _ (Nat.modLess position.row cave.height tall) (Nat.modLess position.column cave.width wide)
                  let base := lookUp cave.table place.row place.column
                  let found: levelAt cave place = Some base := Eq.trans (levelsAgree cave rectangle place) (levelAtOn cave.risks place onMap)
                  let tileRow := Nat.divLeOfLtMul position.row 4 cave.height (omega [rowIn])
                  let tileColumn := Nat.divLeOfLtMul position.column 4 cave.width (omega [columnIn])
                  let raised :=
                    iterateRaise (position.row / cave.height + position.column / cave.width) base (omega [levelBelow10 cave place base found])
                      (omega [levelBelow10 cave place base found, tileRow, tileColumn])
                  rewrite found, raised in rfl

-- A rectangle has a row.
theorem heightNotZero: (cave: Cave) → Rectangle cave → Not (cave.height = 0)
  | { rows = Nil }, rectangle, zero => omega [And.left rectangle]
  | { rows = Cons first rest }, rectangle, zero => omega [zero]

-- A level of the cave is a digit's.
theorem levelBelow10 (cave: Cave) (position: Position) (level: Nat) (found: levelAt cave position = Some level): level < 10 :=
  match r: cave.rows.get position.row with
    | None => Void.exfalso (Option.noneNotSome level found)
    | Some cells =>
      match c: cells.get position.column with
        | None => Void.exfalso (Option.noneNotSome level found)
        | Some digit => rewrite <- Option.someInjective _ _ found in Fin.toNatLt digit
