-- Proofs about `generateLevel` itself, as written, rolling as it goes.
--
-- `generatedLaidOut` is about the generator alone, for every value each
-- roll could give (std's `Effect.Always`): the level it makes is `layOut` of
-- six rooms that fit, with the entrance and exit numbered below 6. So
-- whatever is true of every such level is true of every generated one.
-- `withSeedAlways` carries that to the seeded handler, for every seed: the
-- handler answers each roll with some number, and `Always` holds for all.

namespace Rogue.Proofs
import Rogue (..)
import Std (Effect, List, Nat)
import Std.Effect.AlwaysTreeOf (AlwaysCall)

-- A roll is below its bound: `roll most` under the seeded handler is at
-- most `most`. (Under any handler, `roll most` is a remainder by
-- `Succ most`; `Random.withSeed` is the handler the game and its tests use.)
theorem rollBelow (seed: Nat) (most: Nat): Random.withSeed seed (() => roll most) < Succ most := Nat.modLt (lcg seed / 65536) (Succ most)

-- What every result of a computation satisfies, its result under the seeded
-- handler satisfies, for every seed.
theorem withSeedAlways (property: a → Prop) (prog: () → {Random} a) (holds: Effect.AlwaysTree property (prog ())) (seed: Nat): property (Random.withSeed seed prog) :=
  match reify prog with
    | return x => Effect.AlwaysTree.done property x holds
    | Random.next (), k =>
      match holds with
        | AlwaysCall _ _ later => withSeedAlways property (() => k (lcg seed / 65536)) (later (lcg seed / 65536)) (lcg seed)

-- Whatever number a roll is given, its result is below its bound.
theorem rollBound (drawn: Nat) (most: Nat): drawn % Succ most < Succ most := Nat.modLt drawn (Succ most)

-- Every room fits on the map. Opaque, so that a list of rooms stays a list
-- while the proof below works out which rooms the generator made.
opaque def RoomsFit (rooms: List Area): Prop := List.All (area => OnMap area) rooms

theorem sixFit (room0: Area) (room1: Area) (room2: Area) (room3: Area) (room4: Area) (room5: Area)
    (fits0: OnMap room0) (fits1: OnMap room1) (fits2: OnMap room2) (fits3: OnMap room3) (fits4: OnMap room4) (fits5: OnMap room5):
    RoomsFit [room0, room1, room2, room3, room4, room5]
    unfolding RoomsFit
:=
  Both fits0 (Both fits1 (Both fits2 (Both fits3 (Both fits4 (Both fits5 Trivial)))))

theorem roomsFitMem (rooms: List Area) (fit: RoomsFit rooms) (area: Area) (listed: List.Mem area rooms): OnMap area
    unfolding RoomsFit
:=
  List.allMem (area => OnMap area) area rooms fit listed

-- A property of every level `layOut` makes from rooms that fit, with the
-- entrance and exit numbered below 6.
def LaidOut (depth: Nat) (property: Level → Prop): Prop :=
  (rooms: List Area) → (entranceIndex: Nat) → (exitIndex: Nat) → (extra: Nat) → entranceIndex < 6 → exitIndex < 6 → RoomsFit rooms →
    property (layOut depth rooms entranceIndex exitIndex extra)

-- Such a property holds of the level `generateLevel` makes, whatever its
-- rolls give: an argument per roll, in the order the generator makes them
-- (four per room, then the entrance, the exit and the extra corridor, then
-- the first two monsters' four each, until the monster count is unknown),
-- and `alwaysBind` past the monsters and the sword, whose rolls the level
-- doesn't use.
theorem generatedLaidOut (depth: Nat) (property: Level → Prop) (laidOut: LaidOut depth property):
    Effect.Always ((plan: Plan) => property plan.level) (generateLevel depth)
    unfolding generateLevel
:=
  down0 across0 row0 column0 down1 across1 row1 column1 down2 across2 row2 column2
    down3 across3 row3 column3 down4 across4 row4 column4 down5 across5 row5 column5
    entrance exit extra monster0Room monster0Kind monster0Row monster0Column monster1Room monster1Kind monster1Row monster1Column =>
    Effect.alwaysBind (x => Unit) ((plan: Plan) => property plan.level) _ _ (Effect.alwaysUnit _) (monsters always =>
      potion0Room potion0Row potion0Column potion1Room potion1Row potion1Column =>
        Effect.alwaysBind (x => Unit) ((plan: Plan) => property plan.level) _ _ (Effect.alwaysUnit _) (swords alwaysSword =>
          laidOut _ _ _ _ (rollBound entrance 5) (rollBound _ 5)
            (sixFit _ _ _ _ _ _
              (roomFits 0 rfl _ _ _ _ (rollBound down0 _) (rollBound across0 _) (rollBound row0 _) (rollBound column0 _))
              (roomFits 1 rfl _ _ _ _ (rollBound down1 _) (rollBound across1 _) (rollBound row1 _) (rollBound column1 _))
              (roomFits 2 rfl _ _ _ _ (rollBound down2 _) (rollBound across2 _) (rollBound row2 _) (rollBound column2 _))
              (roomFits 3 rfl _ _ _ _ (rollBound down3 _) (rollBound across3 _) (rollBound row3 _) (rollBound column3 _))
              (roomFits 4 rfl _ _ _ _ (rollBound down4 _) (rollBound across4 _) (rollBound row4 _) (rollBound column4 _))
              (roomFits 5 rfl _ _ _ _ (rollBound down5 _) (rollBound across5 _) (rollBound row5 _) (rollBound column5 _)))))

-- Whatever is true of every laid-out level is true of every level the game
-- generates, for every seed and depth.
theorem generatedHolds (property: Level → Prop) (laidOut: (depth: Nat) → LaidOut depth property) (seed: Nat) (depth: Nat):
    property (Random.withSeed seed (() => generateLevel depth)).level :=
  let always := generatedLaidOut depth property (laidOut depth)
  withSeedAlways ((plan: Plan) => property plan.level) (() => generateLevel depth) (Effect.Always.tree _ _ always) seed

-- On every level the game generates, for every seed and depth, the way on
-- can be walked to from the start.
theorem generatedReachable (seed: Nat) (depth: Nat):
    GoalReachable (Random.withSeed seed (() => generateLevel depth)).level :=
  generatedHolds (level => GoalReachable level)
    (depth rooms entranceIndex exitIndex extra entranceSmall exitSmall fit => goalReachable depth rooms entranceIndex exitIndex extra entranceSmall exitSmall)
    seed depth

-- Every level the game generates, for every seed and depth, is framed.
theorem generatedFramed (seed: Nat) (depth: Nat): Framed (Random.withSeed seed (() => generateLevel depth)).level :=
  generatedHolds (level => Framed level)
    (depth rooms entranceIndex exitIndex extra entranceSmall exitSmall fit => layOutFramed depth rooms entranceIndex exitIndex extra (roomsFitMem rooms fit))
    seed depth

-- Every new game, as the program starts it, is sound, for every seed.
theorem newGameSound (seed: Nat): Sound (Random.withSeed seed (() => newGame())) :=
  let framedLevel := generatedLaidOut 1 (level => Framed level)
    (rooms entranceIndex exitIndex extra entranceSmall exitSmall fit => layOutFramed 1 rooms entranceIndex exitIndex extra (roomsFitMem rooms fit))
  let always: Effect.Always (state => Sound state) (newGame()) :=
    Effect.alwaysBind ((plan: Plan) => Framed plan.level) (state => Sound state) _ _ framedLevel (plan framed => startingSound plan framed)
  withSeedAlways (state => Sound state) (() => newGame()) (Effect.Always.tree _ _ always) seed
