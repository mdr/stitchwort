-- The way on can be walked to from the start of every level the generator
-- lays out (`goalReachable`). A walk is a list of moves, each onto floor
-- (`Walk`). Within a rectangle of floor any cell can be walked to from any
-- other, along the row and then along the column (`walkWithin`); a
-- corridor is two such rectangles meeting at its bend, so its two ends are
-- joined both ways (`corridorJoins`); and the corridors `roomLinks` names
-- form a snake through all six rooms, 0, 1, 2, 5, 4, 3, so every room's
-- middle is joined to room 0's (`hubJoins`), the entrance's and the exit's
-- included.
--
-- The proofs are about a `Level` whose corridors are `corridorsOf` (an
-- equation); only `goalReachable` unfolds the opaque `layOut`, and only to
-- read off that equation. `generateLevel` builds its level with `layOut`,
-- with rooms numbered below 6 (it isn't proved for the generator itself:
-- PROOFS.md §3).

namespace Rogue.Proofs
import Rogue (..)
import Std (Bool, Eq, Exists, List, Nat, Void)

-- Walking `moves` from `origin` stays on floor and ends at `target`.
def Walk (level: Level): Position → List Direction → Position → Prop
  | origin, [], target => origin = target
  | origin, Cons direction rest, target => isWall level (origin.toward direction) = False ∧ Walk level (origin.toward direction) rest target

theorem walkAppend (level: Level) (second: List Direction) (target: Position):
    (origin: Position) → (first: List Direction) → (middle: Position) → Walk level origin first middle → Walk level middle second target → Walk level origin (first ++ second) target
  | origin, [], middle, same, rest => rewrite same in rest
  | origin, Cons direction others, middle, Both open walk, rest => Both open (walkAppend level second target (origin.toward direction) others middle walk rest)

theorem walkEast (level: Level) (row: Nat):
    (steps: Nat) → (column: Nat) → ((j: Nat) → column < j → j ≤ column + steps → isWall level { row, column = j } = False) →
    Walk level { row, column } (List.replicate steps East) { row, column = column + steps }
  | Zero, column, floor => rewrite Nat.addZero column in rfl
  | Succ steps, column, floor =>
    let shift: column + Succ steps = (column + 1) + steps := omega
    Both (floor (column + 1) omega omega)
      (rewrite shift in walkEast level row steps (column + 1) (j after before => floor j omega omega))

theorem walkWest (level: Level) (row: Nat):
    (steps: Nat) → (column: Nat) → ((j: Nat) → column ≤ j → j < column + steps → isWall level { row, column = j } = False) →
    Walk level { row, column = column + steps } (List.replicate steps West) { row, column }
  | Zero, column, floor => rewrite Nat.addZero column in rfl
  | Succ steps, column, floor =>
    let back: column + Succ steps - 1 = column + steps := omega
    rewrite back in Both (floor (column + steps) omega omega) (walkWest level row steps column (j after before => floor j omega omega))

theorem walkSouth (level: Level) (column: Nat):
    (steps: Nat) → (row: Nat) → ((i: Nat) → row < i → i ≤ row + steps → isWall level { row = i, column } = False) →
    Walk level { row, column } (List.replicate steps South) { row = row + steps, column }
  | Zero, row, floor => rewrite Nat.addZero row in rfl
  | Succ steps, row, floor =>
    let shift: row + Succ steps = (row + 1) + steps := omega
    Both (floor (row + 1) omega omega)
      (rewrite shift in walkSouth level column steps (row + 1) (i after before => floor i omega omega))

theorem walkNorth (level: Level) (column: Nat):
    (steps: Nat) → (row: Nat) → ((i: Nat) → row ≤ i → i < row + steps → isWall level { row = i, column } = False) →
    Walk level { row = row + steps, column } (List.replicate steps North) { row, column }
  | Zero, row, floor => rewrite Nat.addZero row in rfl
  | Succ steps, row, floor =>
    let back: row + Succ steps - 1 = row + steps := omega
    rewrite back in Both (floor (row + steps) omega omega) (walkNorth level column steps row (i after before => floor i omega omega))

-- Every cell of `area` is floor.
def Open (level: Level) (area: Area): Prop := (position: Position) → area.contains position = True → isWall level position = False

theorem containsOf (area: Area) (position: Position) (top: area.corner.row ≤ position.row) (bottom: position.row ≤ area.corner.row + area.down)
    (left: area.corner.column ≤ position.column) (right: position.column ≤ area.corner.column + area.across): area.contains position = True :=
  rewrite top, bottom, left, right in rfl

-- What `contains` says, as four facts.
type Inside (area: Area) (position: Position): Prop = {
  top: area.corner.row ≤ position.row,
  bottom: position.row ≤ area.corner.row + area.down,
  left: area.corner.column ≤ position.column,
  right: position.column ≤ area.corner.column + area.across
}

theorem insideOf (area: Area) (position: Position) (contained: area.contains position = True): Inside area position :=
  match top: Nat.leq area.corner.row position.row with
    | False => Void.exfalso (Bool.falseNotTrue contained)
    | True =>
      match bottom: Nat.leq position.row (area.corner.row + area.down) with
        | False => Void.exfalso (Bool.falseNotTrue contained)
        | True =>
          match left: Nat.leq area.corner.column position.column with
            | False => Void.exfalso (Bool.falseNotTrue contained)
            | True => { top, bottom, left, right = contained }

theorem walkCong (level: Level) (moves: List Direction) (origin: Position) (origin2: Position) (target: Position) (target2: Position)
    (sameOrigin: origin = origin2) (sameTarget: target = target2) (walk: Walk level origin moves target): Walk level origin2 moves target2 :=
  rewrite <- sameOrigin, <- sameTarget in walk

def across (origin: Position) (target: Position): List Direction :=
  if origin.column ≤ target.column then List.replicate (target.column - origin.column) East else List.replicate (origin.column - target.column) West

def down (origin: Position) (target: Position): List Direction :=
  if origin.row ≤ target.row then List.replicate (target.row - origin.row) South else List.replicate (origin.row - target.row) North

theorem walkAcross (level: Level) (area: Area) (open: Open level area) (origin: Position) (target: Position)
    (from: Inside area origin) (to: Inside area target): Walk level origin (across origin target) { row = origin.row, column = target.column } :=
  let top := from.top
  let bottom := from.bottom
  let leftmost := area.corner.column
  let fromLeft := from.left
  let fromRight := from.right
  let toLeft := to.left
  let toRight := to.right
  match east: Nat.leq origin.column target.column with
    | True =>
      let walk := walkEast level origin.row (target.column - origin.column) origin.column (j after before =>
        open { row = origin.row, column = j } (containsOf area { row = origin.row, column = j } top bottom omega omega))
      walkCong level (List.replicate (target.column - origin.column) East) { row = origin.row, column = origin.column } origin { row = origin.row, column = origin.column + (target.column - origin.column) } { row = origin.row, column = target.column }
        (Eq.sym (positionEta origin)) (rewrite (omega: origin.column + (target.column - origin.column) = target.column) in rfl) walk
    | False =>
      let walk := walkWest level origin.row (origin.column - target.column) target.column (j after before =>
        open { row = origin.row, column = j } (containsOf area { row = origin.row, column = j } top bottom omega omega))
      walkCong level (List.replicate (origin.column - target.column) West) { row = origin.row, column = target.column + (origin.column - target.column) } origin { row = origin.row, column = target.column } { row = origin.row, column = target.column }
        (rewrite (omega: target.column + (origin.column - target.column) = origin.column) in Eq.sym (positionEta origin)) rfl walk

theorem walkDown (level: Level) (area: Area) (open: Open level area) (origin: Position) (target: Position)
    (top: area.corner.row ≤ origin.row) (bottom: origin.row ≤ area.corner.row + area.down) (to: Inside area target):
    Walk level { row = origin.row, column = target.column } (down origin target) target :=
  let left := to.left
  let right := to.right
  let toTop := to.top
  let toBottom := to.bottom
  match south: Nat.leq origin.row target.row with
    | True =>
      let walk := walkSouth level target.column (target.row - origin.row) origin.row (i after before =>
        open { row = i, column = target.column } (containsOf area { row = i, column = target.column } omega omega left right))
      walkCong level (List.replicate (target.row - origin.row) South) { row = origin.row, column = target.column } { row = origin.row, column = target.column }
        { row = origin.row + (target.row - origin.row), column = target.column } target
        rfl (rewrite (omega: origin.row + (target.row - origin.row) = target.row) in Eq.sym (positionEta target)) walk
    | False =>
      let walk := walkNorth level target.column (origin.row - target.row) target.row (i after before =>
        open { row = i, column = target.column } (containsOf area { row = i, column = target.column } omega omega left right))
      walkCong level (List.replicate (origin.row - target.row) North) { row = target.row + (origin.row - target.row), column = target.column }
        { row = origin.row, column = target.column } { row = target.row, column = target.column } target
        (rewrite (omega: target.row + (origin.row - target.row) = origin.row) in rfl) (Eq.sym (positionEta target)) walk

-- Any cell of an open area can be walked to from any other.
theorem walkWithin (level: Level) (area: Area) (open: Open level area) (origin: Position) (target: Position)
    (from: area.contains origin = True) (to: area.contains target = True): Walk level origin (across origin target ++ down origin target) target :=
  let inOrigin := insideOf area origin from
  let inTarget := insideOf area target to
  walkAppend level (down origin target) target origin (across origin target) { row = origin.row, column = target.column }
    (walkAcross level area open origin target inOrigin inTarget) (walkDown level area open origin target inOrigin.top inOrigin.bottom inTarget)

theorem openCorridor (level: Level) (area: Area) (listed: List.Mem area level.corridors): Open level area :=
  position contained =>
    rewrite List.anyOfMem level.corridors (.contains position) area contained listed, Bool.orTrue (level.rooms.any (.contains position)),
      Bool.orTrue (level.exit.contains position), Bool.orTrue (level.entrance.contains position) in rfl

theorem minDistanceLeft (m: Nat) (n: Nat): m ≤ Nat.min m n + distanceBetween m n :=
  match below: Nat.leq m n with
    | True => omega
    | False => omega

theorem minDistanceRight (m: Nat) (n: Nat): n ≤ Nat.min m n + distanceBetween m n :=
  match below: Nat.leq m n with
    | True => omega
    | False => omega

-- A corridor's two legs, and the cell where they meet.
def bend (origin: Position) (target: Position): Position := { row = origin.row, column = target.column }

theorem alongContains (origin: Position) (target: Position) (position: Position) (sameRow: position.row = origin.row)
    (left: Nat.min origin.column target.column ≤ position.column) (right: position.column ≤ Nat.min origin.column target.column + distanceBetween origin.column target.column):
    ({ corner = { row = origin.row, column = Nat.min origin.column target.column }, down = 0, across = distanceBetween origin.column target.column }: Area).contains position = True :=
  containsOf { corner = { row = origin.row, column = Nat.min origin.column target.column }, down = 0, across = distanceBetween origin.column target.column } position omega omega left right

theorem upContains (origin: Position) (target: Position) (position: Position) (sameColumn: position.column = target.column)
    (top: Nat.min origin.row target.row ≤ position.row) (bottom: position.row ≤ Nat.min origin.row target.row + distanceBetween origin.row target.row):
    ({ corner = { row = Nat.min origin.row target.row, column = target.column }, down = distanceBetween origin.row target.row, across = 0 }: Area).contains position = True :=
  containsOf { corner = { row = Nat.min origin.row target.row, column = target.column }, down = distanceBetween origin.row target.row, across = 0 } position top bottom omega omega

-- `target` can be walked to from `origin`, by some moves.
def Reachable (level: Level) (origin: Position) (target: Position): Prop := exists (moves: List Direction) => Walk level origin moves target

theorem reachTrans (level: Level) (origin: Position) (middle: Position) (target: Position)
    (first: Reachable level origin middle) (second: Reachable level middle target): Reachable level origin target :=
  match first with
    | Witness firstMoves firstWalk =>
      match second with
        | Witness secondMoves secondWalk => Witness (firstMoves ++ secondMoves) (walkAppend level secondMoves target origin firstMoves middle firstWalk secondWalk)

theorem reachWithin (level: Level) (area: Area) (open: Open level area) (origin: Position) (target: Position)
    (from: area.contains origin = True) (to: area.contains target = True): Reachable level origin target :=
  Witness (across origin target ++ down origin target) (walkWithin level area open origin target from to)

-- Both ends of a corridor the level has can be reached from each other.
type Joined (level: Level) (origin: Position) (target: Position): Prop = { there: Reachable level origin target, back: Reachable level target origin }

theorem corridorJoins (level: Level) (origin: Position) (target: Position)
    (listed: (area: Area) → List.Mem area (corridorBetween origin target) → List.Mem area level.corridors): Joined level origin target :=
  let along: Area := { corner = { row = origin.row, column = Nat.min origin.column target.column }, down = 0, across = distanceBetween origin.column target.column }
  let up: Area := { corner = { row = Nat.min origin.row target.row, column = target.column }, down = distanceBetween origin.row target.row, across = 0 }
  let alongOpen := openCorridor level along (listed along (Inl rfl))
  let upOpen := openCorridor level up (listed up (Inr (Inl rfl)))
  let corner := bend origin target
  let originAlong := alongContains origin target origin rfl (Nat.minLeLeft origin.column target.column) (minDistanceLeft origin.column target.column)
  let cornerAlong := alongContains origin target corner rfl (Nat.minLeRight origin.column target.column) (minDistanceRight origin.column target.column)
  let cornerUp := upContains origin target corner rfl (Nat.minLeLeft origin.row target.row) (minDistanceLeft origin.row target.row)
  let targetUp := upContains origin target target rfl (Nat.minLeRight origin.row target.row) (minDistanceRight origin.row target.row)
  {
    there = reachTrans level origin corner target (reachWithin level along alongOpen origin corner originAlong cornerAlong) (reachWithin level up upOpen corner target cornerUp targetUp),
    back = reachTrans level target corner origin (reachWithin level up upOpen target corner targetUp cornerUp) (reachWithin level along alongOpen corner origin cornerAlong originAlong)
  }

theorem joinedTrans (level: Level) (origin: Position) (middle: Position) (target: Position)
    (first: Joined level origin middle) (second: Joined level middle target): Joined level origin target := {
      there = reachTrans level origin middle target first.there second.there,
      back = reachTrans level target middle origin second.back first.back
    }

-- The middle of room number `index`.
def middleOf (rooms: List Area) (index: Nat): Position := roomOf rooms index |> .middle

-- Each pair of rooms `roomLinks` names is joined, on a level with those corridors.
theorem linkJoins (level: Level) (rooms: List Area) (extra: Nat) (wired: level.corridors = corridorsOf rooms extra) (first: Nat) (second: Nat)
    (linked: List.Mem (first, second) (roomLinks extra)): Joined level (middleOf rooms first) (middleOf rooms second) :=
  corridorJoins level (middleOf rooms first) (middleOf rooms second) (area leg =>
    let corridorsFor: (Nat, Nat) → List Area := ((one, other)) => corridorBetween (roomOf rooms one).middle (roomOf rooms other).middle
    rewrite wired in List.memFlatMapIntro corridorsFor (first, second) area (roomLinks extra) linked leg)

-- Room 0 is joined to every room, along the snake: 0, 1, 2, 5, 4, 3.
theorem hubTwo (level: Level) (rooms: List Area) (extra: Nat) (wired: level.corridors = corridorsOf rooms extra):
    Joined level (middleOf rooms 0) (middleOf rooms 2) :=
  joinedTrans level (middleOf rooms 0) (middleOf rooms 1) (middleOf rooms 2) (linkJoins level rooms extra wired 0 1 (Inl rfl)) (linkJoins level rooms extra wired 1 2 (Inr (Inl rfl)))

theorem hubFive (level: Level) (rooms: List Area) (extra: Nat) (wired: level.corridors = corridorsOf rooms extra):
    Joined level (middleOf rooms 0) (middleOf rooms 5) :=
  joinedTrans level (middleOf rooms 0) (middleOf rooms 2) (middleOf rooms 5) (hubTwo level rooms extra wired) (linkJoins level rooms extra wired 2 5 (Inr (Inr (Inl rfl))))

theorem hubFour (level: Level) (rooms: List Area) (extra: Nat) (wired: level.corridors = corridorsOf rooms extra):
    Joined level (middleOf rooms 0) (middleOf rooms 4) :=
  joinedTrans level (middleOf rooms 0) (middleOf rooms 5) (middleOf rooms 4) (hubFive level rooms extra wired) (linkJoins level rooms extra wired 5 4 (Inr (Inr (Inr (Inl rfl)))))

theorem hubJoins (level: Level) (rooms: List Area) (extra: Nat) (wired: level.corridors = corridorsOf rooms extra):
    (index: Nat) → index < 6 → Joined level (middleOf rooms 0) (middleOf rooms index)
  | Zero, small => { there = Witness [] rfl, back = Witness [] rfl }
  | Succ Zero, small => linkJoins level rooms extra wired 0 1 (Inl rfl)
  | Succ (Succ Zero), small => hubTwo level rooms extra wired
  | Succ (Succ (Succ Zero)), small =>
    joinedTrans level (middleOf rooms 0) (middleOf rooms 4) (middleOf rooms 3) (hubFour level rooms extra wired) (linkJoins level rooms extra wired 4 3 (Inr (Inr (Inr (Inr (Inl rfl))))))
  | Succ (Succ (Succ (Succ Zero))), small => hubFour level rooms extra wired
  | Succ (Succ (Succ (Succ (Succ Zero)))), small => hubFive level rooms extra wired
  | Succ (Succ (Succ (Succ (Succ (Succ more))))), small => Void.exfalso (Bool.falseNotTrue small)

-- The way on (the stairs, or the amulet) can be walked to from the start,
-- on every level `layOut` makes from rooms numbered below 6, as
-- `generateLevel` always picks. Monsters may stand in the way, but walking
-- into one attacks it, so they block nothing for good.
theorem goalReachable (depth: Nat) (rooms: List Area) (entranceIndex: Nat) (exitIndex: Nat) (extra: Nat)
    (entranceSmall: entranceIndex < 6) (exitSmall: exitIndex < 6):
      Reachable (layOut depth rooms entranceIndex exitIndex extra) (layOut depth rooms entranceIndex exitIndex extra).start (layOut depth rooms entranceIndex exitIndex extra).goal
    unfolding layOut
:=
  let level := layOut depth rooms entranceIndex exitIndex extra
  let wired: level.corridors = corridorsOf rooms extra := rfl
  reachTrans level (middleOf rooms entranceIndex) (middleOf rooms 0) (middleOf rooms exitIndex)
    (hubJoins level rooms extra wired entranceIndex entranceSmall).back
    (hubJoins level rooms extra wired exitIndex exitSmall).there
