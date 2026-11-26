--| Proofs about `generateLevel` itself, as written, rolling as it goes.
--|
--| `generatedLaidOut` is about the generator alone, for every value each roll
--| could give (std's `Effect.Always`): the level it makes is `layOut` of six
--| rooms that fit, with the entrance and exit numbered below 6. So whatever
--| is true of every such level is true of every generated one.
--| `withSeedAlways` carries that to the seeded handler, for every seed: the
--| handler answers each roll with some number, and `Always` holds for all.

namespace Rogue.Proofs
import Rogue (..)
import Std (Effect, List, Nat)
import Std.Effect.AlwaysTreeOf (AlwaysCall)

--| A roll is below its bound: `roll most` under the seeded handler is at most
--| `most`. (Under any handler, `roll most` is a remainder by `Succ most`;
--| `Random.withSeed` is the handler the game and its tests use.)
theorem rollBelow ∀ (seed most: Nat): Random.withSeed seed (() => roll most) < Succ most :=
  Nat.modLt (lcg seed / 65536) (Succ most)

--| What every result of a computation satisfies, its result under the seeded
--| handler satisfies, for every seed.
theorem withSeedAlways ∀ (property: a → Prop) (prog: () → {Random} a)
    (holds: Effect.AlwaysTree property (prog ())) (seed: Nat):
    property (Random.withSeed seed prog) :=
  match reify prog with
    | return x => Effect.AlwaysTree.done property x holds
    | Random.next (), k =>
      match holds with
        | AlwaysCall later => withSeedAlways property (() => k (lcg seed / 65536)) (later (lcg seed / 65536)) (lcg seed)

--| Whatever number a roll is given, its result is below its bound.
--| Every room fits on the map.
--
-- Opaque, so that a list of rooms stays a list while the proof
-- below works out which rooms the generator made.
opaque def RoomsFit (rooms: List Area): Prop := List.All (area => OnMap area) rooms

theorem sixFit ∀ [room0 room1 room2 room3 room4 room5: Area]
    (fits0: OnMap room0)
    (fits1: OnMap room1)
    (fits2: OnMap room2)
    (fits3: OnMap room3)
    (fits4: OnMap room4)
    (fits5: OnMap room5):
    RoomsFit [room0, room1, room2, room3, room4, room5]
    unfolding RoomsFit :=
  Both fits0 (Both fits1 (Both fits2 (Both fits3 (Both fits4 (Both fits5 Trivial)))))

theorem roomsFitMem ∀ (rooms: List Area)
    (fit: RoomsFit rooms) (area: Area)
    (listed: List.Mem area rooms):
    OnMap area
    unfolding RoomsFit :=
  List.allMem (area => OnMap area) area rooms fit listed

--| A property of every level `layOut` makes from rooms that fit, with the
--| entrance and exit numbered below 6.
def LaidOut (depth: Nat) (property: Level → Prop): Prop :=
  ∀ (rooms: List Area) (entranceIndex exitIndex extra: Nat) => entranceIndex < 6
    → exitIndex < 6
    → RoomsFit rooms
    → property (layOut depth rooms entranceIndex exitIndex extra)

--| Such a property holds of the level `generateLevel` makes, whatever its
--| rolls give: an argument per roll, in the order the generator makes them
--| (four per room, then the entrance, the exit and the extra corridor, then
--| the first two monsters' four each, until the monster count is unknown),
--| and `alwaysBind` past the monsters and the sword, whose rolls the level
--| doesn't use.
theorem generatedLaidOut ∀ (depth: Nat) (property: Level → Prop)
    (laidOut: LaidOut depth property):
    Effect.Always ((plan: Plan) => property plan.level) (generateLevel depth)
    unfolding generateLevel :=
  down0 across0 row0 column0 down1 across1 row1 column1 down2 across2 row2 column2 down3 across3 row3 column3 down4
      across4 row4 column4 down5 across5 row5 column5 entrance exit extra monster0Room monster0Kind monster0Row
      monster0Column monster1Room monster1Kind monster1Row monster1Column =>
    Effect.alwaysBind (x => Unit) ((plan: Plan) => property plan.level) _ _ (Effect.alwaysUnit _) (monsters always =>
      potion0Room potion0Row potion0Column potion1Room potion1Row potion1Column =>
        Effect.alwaysBind
          (x => Unit)
          ((plan: Plan) => property plan.level) _ _
          (Effect.alwaysUnit _)
          (swords alwaysSword =>
            laidOut _ _ _ _
              (Nat.modLt entrance (Succ 5))
              (Nat.modLt _ (Succ 5))
              (sixFit
                (roomFits 0 byComputing _ _ _ _
                  (Nat.modLt down0 (Succ _))
                  (Nat.modLt across0 (Succ _))
                  (Nat.modLt row0 (Succ _))
                  (Nat.modLt column0 (Succ _)))
                (roomFits 1 byComputing _ _ _ _
                  (Nat.modLt down1 (Succ _))
                  (Nat.modLt across1 (Succ _))
                  (Nat.modLt row1 (Succ _))
                  (Nat.modLt column1 (Succ _)))
                (roomFits 2 byComputing _ _ _ _
                  (Nat.modLt down2 (Succ _))
                  (Nat.modLt across2 (Succ _))
                  (Nat.modLt row2 (Succ _))
                  (Nat.modLt column2 (Succ _)))
                (roomFits 3 byComputing _ _ _ _
                  (Nat.modLt down3 (Succ _))
                  (Nat.modLt across3 (Succ _))
                  (Nat.modLt row3 (Succ _))
                  (Nat.modLt column3 (Succ _)))
                (roomFits 4 byComputing _ _ _ _
                  (Nat.modLt down4 (Succ _))
                  (Nat.modLt across4 (Succ _))
                  (Nat.modLt row4 (Succ _))
                  (Nat.modLt column4 (Succ _)))
                (roomFits 5 byComputing _ _ _ _
                  (Nat.modLt down5 (Succ _))
                  (Nat.modLt across5 (Succ _))
                  (Nat.modLt row5 (Succ _))
                  (Nat.modLt column5 (Succ _))))))

--| Whatever is true of every laid-out level is true of every level the game
--| generates, for every seed and depth.
theorem generatedHolds ∀ (property: Level → Prop)
    (laidOut: ∀ (depth: Nat) => LaidOut depth property) (seed depth: Nat):
    property (Random.withSeed seed (() => generateLevel depth)).level :=
  let always := generatedLaidOut depth property (laidOut depth)
  withSeedAlways ((plan: Plan) => property plan.level) (() => generateLevel depth) (Effect.Always.tree _ _ always) seed

--| On every level the game generates, for every seed and depth, the way on
--| can be walked to from the start.
theorem generatedReachable ∀ (seed depth: Nat):
    GoalReachable (Random.withSeed seed (() => generateLevel depth)).level :=
  generatedHolds
    (level => GoalReachable level)
    (depth rooms entranceIndex exitIndex extra entranceSmall exitSmall fit =>
      goalReachable depth rooms entranceIndex exitIndex extra entranceSmall exitSmall)
    seed
    depth

--| Every level the game generates, for every seed and depth, is framed.
theorem generatedFramed ∀ (seed depth: Nat): Framed (Random.withSeed seed (() => generateLevel depth)).level :=
  generatedHolds
    (level => Framed level)
    (depth rooms entranceIndex exitIndex extra entranceSmall exitSmall fit =>
      layOutFramed depth rooms entranceIndex exitIndex extra (roomsFitMem rooms fit))
    seed
    depth

--| Every new game, as the program starts it, is sound, for every seed.
theorem newGameSound ∀ (seed: Nat): Sound (Random.withSeed seed (() => newGame())) :=
  let framedLevel :=
    generatedLaidOut 1 (level => Framed level) (rooms entranceIndex exitIndex extra entranceSmall exitSmall fit =>
      layOutFramed 1 rooms entranceIndex exitIndex extra (roomsFitMem rooms fit))
  let always: Effect.Always (state => Sound state) (newGame()) :=
    Effect.alwaysBind ((plan: Plan) => Framed plan.level) (state => Sound state) _ _ framedLevel (plan framed =>
      startingSound plan framed)
  withSeedAlways (state => Sound state) (() => newGame()) (Effect.Always.tree _ _ always) seed
