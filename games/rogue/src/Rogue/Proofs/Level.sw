-- Every level is entered valid, whatever the generator made: the player
-- starts on floor (`startOnFloor`, true of every `Level`), and the monsters
-- and items `arrive` places are on floor and off the player's cell
-- (`placeMonstersClear`, `placeMonstersOnFloor`, `placeItemsFit`).
--
-- That the stairs can be reached from the start is in Reach.sw
-- (`goalReachable`); Tests/Generate.sw also checks it on many seeds, by a
-- search over the cells.

namespace Rogue.Proofs
import Rogue (..)
import Std (Bool, Decidable, Eq, List, Nat, Option, Void)

theorem halfAtMost (n: Nat): n / 2 ≤ n := omega

-- The middle of an area is in it.
theorem middleInside (area: Area): area.contains area.middle = True :=
  rewrite Nat.leAddRight area.corner.row (area.down / 2), Nat.leAddCong area.corner.row (area.down / 2) area.down (halfAtMost area.down),
    Nat.leAddRight area.corner.column (area.across / 2), Nat.leAddCong area.corner.column (area.across / 2) area.across (halfAtMost area.across)

-- The start of every level is floor: it's the middle of the entrance.
theorem startOnFloor (level: Level): isWall level level.start = False :=
  rewrite middleInside level.entrance

-- So is the goal: the middle of the exit.
theorem goalOnFloor (level: Level): isWall level level.goal = False :=
  rewrite middleInside level.exit, Bool.orTrue (level.entrance.contains level.exit.middle) in rfl

-- No placed monster stands on the start...
theorem placeMonstersClear (level: Level) (start: Position):
    (placed: List Monster) → (planned: List Monster) → Clear start placed → Clear start (placeMonsters level start placed planned)
  | placed, [], clear => clear
  | placed, Cons monster rest, clear =>
    match picked: pickFree level [monster.position] start placed with
      | Some position =>
        let away := pickFreeAway level start placed [monster.position] position picked
        placeMonstersClear level start (placed ++ [{ monster | position }]) rest (clearSnoc start { monster | position } away placed clear)
      | None => placeMonstersClear level start placed rest clear

-- ...or in a wall.
theorem placeMonstersOnFloor (level: Level) (start: Position):
    (placed: List Monster) → (planned: List Monster) → OnFloor level placed → OnFloor level (placeMonsters level start placed planned)
  | placed, [], onFloor => onFloor
  | placed, Cons monster rest, onFloor =>
    match picked: pickFree level [monster.position] start placed with
      | Some position =>
        let inside := pickFreeOnFloor level start placed [monster.position] position picked
        placeMonstersOnFloor level start (placed ++ [{ monster | position }]) rest (onFloorSnoc level { monster | position } inside placed onFloor)
      | None => placeMonstersOnFloor level start placed rest onFloor

-- An item lies on floor, and not on the player's start.
def Fits (level: Level) (start: Position) (item: Item): Prop := isWall level item.position = False ∧ (item.position == start) = False

theorem placeItemsFit (level: Level) (start: Position):
    (placed: List Item) → (planned: List Item) → List.All (Fits level start) placed → List.All (Fits level start) (placeItems level start placed planned)
  | placed, [], fit => fit
  | placed, Cons item rest, fit =>
    match wall: isWall level item.position with
      | True => placeItemsFit level start placed rest fit
      | False =>
        match same: item.position == start with
          | True => placeItemsFit level start placed rest fit
          | False =>
            match stairs: isStairs level item.position with
              | True => placeItemsFit level start placed rest fit
              | False =>
                match taken: (itemAt item.position placed).isSome with
                  | True => placeItemsFit level start placed rest fit
                  | False => placeItemsFit level start (placed ++ [item]) rest (List.allAppend (Fits level start) placed [item] fit (Both (Both wall same) Trivial))

-- Whatever the generator planned, the items of a level entered fit.
theorem arriveItemsFit (state: State) (plan: Plan): List.All (Fits plan.level plan.level.start) (arrive state plan).items :=
  placeItemsFit plan.level plan.level.start [] plan.items Trivial
