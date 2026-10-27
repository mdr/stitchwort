-- Every cell anyone can stand on is on the screen. A level is `Framed`
-- when its terrain is 20 rows of 66 cells and every floor cell is among
-- them. Every room the generator makes fits inside its section, whatever
-- the rolls (`roomFits`), and every level `layOut` makes from rooms that fit
-- is framed, as its corridors run between the rooms' middles
-- (`layOutFramed`); and a turn keeps the level framed (`stepFramed`), as
-- every generated level is (`generatedFramed`, Generated.sw). So in a sound
-- state the player and every monster are drawn where they stand, with no
-- assumption about where that is (`drawnPlayer`, `drawnMonster`).

namespace Rogue.Proofs
import Rogue (..)
import Std (Bool, Eq, List, Nat, Void)

-- A cell on the screen.
type OnScreen (position: Position): Prop = { low: position.row < levelRows, narrow: position.column < levelColumns }

-- An area whose cells are all on the screen (on the map).
type OnMap (area: Area): Prop = { bottom: area.corner.row + area.down < levelRows, right: area.corner.column + area.across < levelColumns }

theorem containedOnScreen (area: Area) (fits: OnMap area) (position: Position) (contained: area.contains position = True): OnScreen position :=
  let inside := insideOf area position contained
  let bottom := inside.bottom
  let right := inside.right
  let areaBottom := fits.bottom
  let areaRight := fits.right
  { low = omega, narrow = omega }

theorem middleOnScreen (area: Area) (fits: OnMap area): OnScreen area.middle :=
  containedOnScreen area fits area.middle (middleInside area)

-- Room `index` of six sits in its section, with room to spare.
theorem sectionFits (top: Nat) (down: Nat) (offset: Nat) (downSmall: down < 4) (offsetSmall: offset < Succ (10 - 3 - (2 + down))) (topSmall: top ≤ 11):
    top + offset + (2 + down) < 20 :=
  omega

theorem sectionFitsAcross (left: Nat) (across: Nat) (offset: Nat) (acrossSmall: across < 11) (offsetSmall: offset < Succ (22 - 3 - (4 + across))) (leftSmall: left ≤ 45):
    left + offset + (4 + across) < 66 :=
  omega

-- The top row and left column of section `index`, for the six sections.
type Corner (index: Nat): Prop = { top: (index / 3) * sectionRows + 1 ≤ 11, left: (index % 3) * sectionColumns + 1 ≤ 45 }

theorem sectionCorner: (index: Nat) → index < 6 → Corner index
  | Zero, small => { top = omega, left = omega }
  | Succ Zero, small => { top = omega, left = omega }
  | Succ (Succ Zero), small => { top = omega, left = omega }
  | Succ (Succ (Succ Zero)), small => { top = omega, left = omega }
  | Succ (Succ (Succ (Succ Zero))), small => { top = omega, left = omega }
  | Succ (Succ (Succ (Succ (Succ Zero)))), small => { top = omega, left = omega }
  | Succ (Succ (Succ (Succ (Succ (Succ more))))), small => Void.exfalso (Bool.falseNotTrue small)

-- A room as `roomFrom` makes it in section `index`, from any rolls below
-- their bounds (`roll most` is below `Succ most`), fits on the map.
theorem roomFits (index: Nat) (small: index < 6) (downRoll: Nat) (acrossRoll: Nat) (rowRoll: Nat) (columnRoll: Nat)
    (downSmall: downRoll < 4) (acrossSmall: acrossRoll < 11)
    (rowSmall: rowRoll < Succ (sectionRows - 3 - (2 + downRoll))) (columnSmall: columnRoll < Succ (sectionColumns - 3 - (4 + acrossRoll))):
    OnMap ({
      corner = { row = (index / 3) * sectionRows + 1 + rowRoll, column = (index % 3) * sectionColumns + 1 + columnRoll },
      down = 2 + downRoll,
      across = 4 + acrossRoll
    }: Area) :=
  let corner := sectionCorner index small
  {
    bottom = sectionFits ((index / 3) * sectionRows + 1) downRoll rowRoll downSmall rowSmall corner.top,
    right = sectionFitsAcross ((index % 3) * sectionColumns + 1) acrossRoll columnRoll acrossSmall columnSmall corner.left
  }

-- So does any room picked from them by number.
theorem getOrFits (fallback: Area) (fallbackFits: OnMap fallback):
    (rooms: List Area) → ((area: Area) → List.Mem area rooms → OnMap area) → (index: Nat) → OnMap (rooms.getOr index fallback)
  | [], fit, index => fallbackFits
  | Cons room rest, fit, Zero => fit room (Inl rfl)
  | Cons room rest, fit, Succ index => getOrFits fallback fallbackFits rest (area listed => fit area (Inr listed)) index

theorem roomOfFits (rooms: List Area) (fit: (area: Area) → List.Mem area rooms → OnMap area) (index: Nat): OnMap (roomOf rooms index) :=
  let fallbackFits: OnMap (rooms.headOr fallbackRoom) :=
    match rooms with
      | [] => { bottom = omega, right = omega }
      | Cons room rest => fit room (Inl rfl)
  getOrFits (rooms.headOr fallbackRoom) fallbackFits rooms fit index

-- A corridor between two cells on the screen fits.
theorem minPlusDistance (m: Nat) (n: Nat) (bound: Nat) (mSmall: m < bound) (nSmall: n < bound): Nat.min m n + distanceBetween m n < bound :=
  match below: Nat.leq m n with
    | True => omega
    | False => omega

theorem corridorFits (origin: Position) (target: Position) (from: OnScreen origin) (to: OnScreen target):
    (area: Area) → List.Mem area (corridorBetween origin target) → OnMap area
  | area, Inl same =>
    let originRow := from.low
    rewrite <- same in { bottom = omega, right = minPlusDistance origin.column target.column levelColumns from.narrow to.narrow }
  | area, Inr (Inl same) =>
    let targetColumn := to.narrow
    rewrite <- same in { bottom = minPlusDistance origin.row target.row levelRows from.low to.low, right = omega }
  | area, Inr (Inr nothing) => Void.exfalso nothing

-- So do the corridors between rooms that fit.
theorem corridorsFit (rooms: List Area) (fit: (area: Area) → List.Mem area rooms → OnMap area) (extra: Nat)
    (area: Area) (listed: List.Mem area (corridorsOf rooms extra)): OnMap area :=
  let corridorsFor: (Nat, Nat) → List Area := ((one, other)) => corridorBetween (roomOf rooms one).middle (roomOf rooms other).middle
  List.anyElim (link => List.Mem area (corridorsFor link)) (OnMap area) (roomLinks extra)
    (List.memFlatMapElim corridorsFor area (roomLinks extra) listed)
    (link linked within =>
      match link with
        | (one, other) =>
          corridorFits (roomOf rooms one).middle (roomOf rooms other).middle
            (middleOnScreen (roomOf rooms one) (roomOfFits rooms fit one)) (middleOnScreen (roomOf rooms other) (roomOfFits rooms fit other)) area within)

-- Every floor cell of a level whose areas all fit is on the screen.
theorem floorOnScreen (level: Level) (entranceFits: OnMap level.entrance) (exitFits: OnMap level.exit)
    (roomsFit: (area: Area) → List.Mem area level.rooms → OnMap area) (corridorsFit: (area: Area) → List.Mem area level.corridors → OnMap area)
    (position: Position) (open: isWall level position = False): OnScreen position :=
  match inEntrance: level.entrance.contains position with
    | True => containedOnScreen level.entrance entranceFits position inEntrance
    | False =>
      match inExit: level.exit.contains position with
        | True => containedOnScreen level.exit exitFits position inExit
        | False =>
          match inRoom: level.rooms.any (.contains position) with
            | True =>
              List.anyTrueElim level.rooms (.contains position) (OnScreen position) inRoom
                (area listed contained => containedOnScreen area (roomsFit area listed) position contained)
            | False =>
              match inCorridor: level.corridors.any (.contains position) with
                | True =>
                  List.anyTrueElim level.corridors (.contains position) (OnScreen position) inCorridor
                    (area listed contained => containedOnScreen area (corridorsFit area listed) position contained)
                | False => Void.exfalso (Bool.falseNotTrue (Eq.sym open))

-- The terrain is drawn 20 rows by 66 columns, whatever the level.
theorem terrainRows (level: Level): (drawTerrain level).length = levelRows :=
  Eq.trans (List.lengthMap (List.range levelRows) (row => List.range levelColumns |> .map (column => terrainAt level { row, column })))
    (List.lengthRangeFrom levelRows 0)

theorem terrainColumns (level: Level) (row: Nat) (small: row < levelRows): ((drawTerrain level).getOr row []).length = levelColumns :=
  let cellsOf: Nat → List Char := index => List.range levelColumns |> .map (column => terrainAt level { row = index, column })
  let picked: (drawTerrain level).getOr row [] = cellsOf (row + 0) := List.getOrMapRange cellsOf [] levelRows 0 row small
  let counted: (cellsOf (row + 0)).length = levelColumns :=
    Eq.trans (List.lengthMap (List.range levelColumns) (column => terrainAt level { row = row + 0, column })) (List.lengthRangeFrom levelColumns 0)
  Eq.trans (Eq.cong List.length picked) counted

-- A level fits the screen: its terrain is 20 rows of 66 cells, and every
-- floor cell is among them.
type Framed (level: Level): Prop = {
  rows: level.terrain.length = levelRows,
  columns: (row: Nat) → row < levelRows → (level.terrain.getOr row []).length = levelColumns,
  floor: (position: Position) → isWall level position = False → OnScreen position
}

theorem buildFramed (depth: Nat) (entrance: Area) (exit: Area) (rooms: List Area) (corridors: List Area)
    (entranceFits: OnMap entrance) (exitFits: OnMap exit)
    (roomsFit: (area: Area) → List.Mem area rooms → OnMap area) (corridorsFit: (area: Area) → List.Mem area corridors → OnMap area):
    Framed (Level.build depth entrance exit rooms corridors) :=
  let undrawn: Level := { depth, entrance, exit, rooms, corridors, terrain = [] }
  {
    rows = terrainRows undrawn,
    columns = terrainColumns undrawn,
    floor = floorOnScreen (Level.build depth entrance exit rooms corridors) entranceFits exitFits roomsFit corridorsFit
  }

-- Every level `layOut` makes from rooms that all fit is framed.
theorem layOutFramed (depth: Nat) (rooms: List Area) (entranceIndex: Nat) (exitIndex: Nat) (extra: Nat)
    (fit: (area: Area) → List.Mem area rooms → OnMap area):
    Framed (layOut depth rooms entranceIndex exitIndex extra)
    unfolding layOut
:=
  buildFramed depth (roomOf rooms entranceIndex) (roomOf rooms exitIndex) rooms (corridorsOf rooms extra)
    (roomOfFits rooms fit entranceIndex) (roomOfFits rooms fit exitIndex) fit (corridorsFit rooms fit extra)

-- A turn keeps the level, or goes down to a generated one.
theorem playerMovesLevel (dice: Dice) (state: State) (direction: Direction): (playerMoves dice state direction).level = state.level :=
  match found: monsterAt (state.player.toward direction) state.monsters with
    | Some monster => rfl
    | None =>
      match wall: isWall state.level (state.player.toward direction) with
        | True => rfl
        | False => enterLevel state (state.player.toward direction)

theorem resolveFramed (dice: Dice) (state: State) (command: Command) (framed: Framed state.level): Framed (resolve dice state command).level :=
  match phase: state.phase with
    | Playing =>
      match command with
        | Quit => framed
        | Wait => rewrite monstersTurnLevel dice { state | message = "You wait." } in framed
        | Move direction => rewrite monstersTurnLevel dice (playerMoves dice state direction), playerMovesLevel dice state direction in framed
        | Drink =>
          match none: state.potions == 0 with
            | True => framed
            | False => rewrite monstersTurnLevel dice (drink state) in framed
        | Descend =>
          match stairs: isStairs state.level state.player with
            | True => generatedFramed dice.seed (state.level.depth + 1)
            | False => framed
    | Won => framed
    | Died => framed
    | GaveUp => framed

theorem stepFramed (seed: Nat) (state: State) (command: Command) (framed: Framed state.level):
    Framed (Random.withSeed seed (() => step state command)).level :=
  resolveFramed { seed = lcg seed / 65536 } state command framed

-- A state of a real game: valid, on a framed level.
type Sound (state: State): Prop = { valid: Valid state, framed: Framed state.level }

-- A new game on a framed level is sound, and so is every game after any
-- number of turns.
theorem startingSound (plan: Plan) (framed: Framed plan.level): Sound (startingState plan) :=
  { valid = startingValid plan, framed }

theorem replaySound: (turns: List (Nat, Command)) → (state: State) → Sound state → Sound (replay state turns)
  | [], state, sound => sound
  | Cons (seed, command) rest, state, sound =>
    replaySound rest (Random.withSeed seed (() => step state command)) { valid = stepValid seed state command sound.valid, framed = stepFramed seed state command sound.framed }

-- In a sound state, `render` draws `@` at the player's row and column,
-- with nothing assumed about where that is.
theorem drawnPlayer (state: State) (sound: Sound state):
    render state |> .getOr state.player.row "" |> .toList |> .getOr state.player.column ' ' = '@' :=
  let onScreen := sound.framed.floor state.player sound.valid.outOfWalls
  let tall: state.player.row < state.level.terrain.length := rewrite sound.framed.rows in onScreen.low
  let wide: state.player.column < (state.level.terrain.getOr state.player.row []).length :=
    rewrite sound.framed.columns state.player.row onScreen.low in onScreen.narrow
  renderPlayer state tall wide

-- And each monster's letter at its row and column.
theorem drawnMonster (state: State) (sound: Sound state) (monster: Monster) (listed: List.Mem monster state.monsters):
    render state |> .getOr monster.position.row "" |> .toList |> .getOr monster.position.column ' ' = monster.kind.glyph :=
  let onFloor := List.allMem ((other: Monster) => isWall state.level other.position = False) monster state.monsters sound.valid.onFloor listed
  let onScreen := sound.framed.floor monster.position onFloor
  let tall: monster.position.row < state.level.terrain.length := rewrite sound.framed.rows in onScreen.low
  let wide: monster.position.column < (state.level.terrain.getOr monster.position.row []).length :=
    rewrite sound.framed.columns monster.position.row onScreen.low in onScreen.narrow
  renderEveryMonster state sound.valid monster listed tall wide
