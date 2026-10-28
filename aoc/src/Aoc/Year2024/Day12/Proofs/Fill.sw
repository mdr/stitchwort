-- The flood fill finds the region: from a plot growing `plant`,
-- `regionOf` lists every plot joined to it, and nothing else
-- (`regionOfIsRegion`), each once (`regionOfDistinct`).

namespace Aoc.Year2024.Day12.Proofs
import Aoc.Year2024.Day12 (..)
import Aoc.Year2024.Day12.Spec (..)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Iff, List, Nat, Option, Or, Set, Void)

-- What holds at each step of a fill from `start`: `visited` has exactly
-- the members, each listed once; every member grows `plant` and is joined
-- to `start`, as is every position on the stack; and each neighbour a
-- member pushed is a member or still on the stack.
def FillState (garden: Garden) (plant: Char) (start: Position) (stack: List Position) (visited: Set Position) (members: List Position): Prop :=
  And ((position: Position) → Iff (visited.contains position = True) (position ∈ members))
    (And (List.Distinct members)
      (And ((position: Position) → position ∈ members → And (garden.plantAt position = Some plant) (Joined garden start position))
        (And ((position: Position) → position ∈ stack → Joined garden start position)
          ((member: Position) → member ∈ members → (next: Position) → next ∈ garden.neighboursGrowing plant member →
            Or (next ∈ members) (next ∈ stack)))))

-- What a fill returns: plots listed once, each growing `plant` and joined
-- to `start`, with every neighbour growing `plant`; the members it started
-- with, and the plots growing `plant` on its stack.
def FillResult (garden: Garden) (plant: Char) (start: Position) (stack: List Position) (members: List Position) (result: List Position): Prop :=
  And (List.Distinct result)
    (And ((position: Position) → position ∈ result → And (garden.plantAt position = Some plant) (Joined garden start position))
      (And ((member: Position) → member ∈ result → (next: Position) → next ∈ garden.neighboursGrowing plant member → next ∈ result)
        (And ((position: Position) → position ∈ members → position ∈ result)
          ((position: Position) → position ∈ stack → garden.plantAt position = Some plant → position ∈ result))))

-- Popping a position already visited, or not growing `plant`, keeps the
-- state.
theorem popKeeps (garden: Garden) (plant: Char) (start: Position) (position: Position) (rest: List Position) (visited: Set Position)
    (members: List Position) (state: FillState garden plant start (Cons position rest) visited members)
    (skipped: Or (position ∈ members) (Not (garden.plantAt position = Some plant))): FillState garden plant start rest visited members :=
  let (Both visitedMembers (Both distinct (Both sound (Both stacked closed)))) := state
  Both visitedMembers
    (Both distinct
      (Both sound
        (Both (position inRest => stacked position (Inr inRest))
          (member isMember next pushed =>
            match closed member isMember next pushed with
              | Inl inMembers => Inl inMembers
              | Inr (Inr inRest) => Inr inRest
              | Inr (Inl same) =>
                match skipped with
                  | Inl inMembers => Inl (rewrite <- same in inMembers)
                  | Inr other =>
                    Void.exfalso (other (rewrite same in And.right ((memNeighboursGrowing garden plant member next).forward pushed)))))))

-- Popping a position not yet visited that grows `plant`, and pushing its
-- neighbours growing `plant`, keeps the state.
theorem takeKeeps (garden: Garden) (plant: Char) (start: Position) (position: Position) (rest: List Position) (visited: Set Position)
    (members: List Position) (state: FillState garden plant start (Cons position rest) visited members)
    (fresh: visited.contains position = False) (grows: garden.plantAt position = Some plant):
    FillState garden plant start (garden.neighboursGrowing plant position ++ rest) (visited.insert position) (Cons position members) :=
  let (Both visitedMembers (Both distinct (Both sound (Both stacked closed)))) := state
  let joinedHere := stacked position (Inl rfl)
  Both
    (other =>
      match same: other == position with
        | True =>
          rewrite DecEq.sound other position same in {
            forward = contains => Inl rfl,
            backward = member => Set.containsInsert position visited
          }
        | False =>
          let apart := DecEq.soundFalse other position same
          rewrite Set.containsInsertOther visited position other apart in {
            forward = contains => Inr ((visitedMembers other).forward contains),
            backward = member =>
              match member with
                | Inl here => Void.exfalso (apart (Eq.sym here))
                | Inr later => (visitedMembers other).backward later
          })
    (Both (Both (member => Bool.falseNotTrue (Eq.trans (Eq.sym fresh) ((visitedMembers position).backward member))) distinct)
      (Both
        (other member =>
          match member with
            | Inl here => rewrite <- here in Both grows joinedHere
            | Inr later => sound other later)
        (Both
          (other onStack =>
            match List.memAppend other (garden.neighboursGrowing plant position) rest onStack with
              | Inl pushed => joinedStep garden start position other joinedHere (growingTouches garden plant position other grows pushed)
              | Inr inRest => stacked other (Inr inRest))
          (member isMember next pushed =>
            match isMember with
              | Inl here => Inr (List.memAppendLeft next (garden.neighboursGrowing plant position) rest (rewrite here in pushed))
              | Inr earlier =>
                match closed member earlier next pushed with
                  | Inl inMembers => Inl (Inr inMembers)
                  | Inr (Inl same) => Inl (Inl same)
                  | Inr (Inr inRest) => Inr (List.memAppendRight next (garden.neighboursGrowing plant position) rest inRest)))))

-- One step of the fill: a position already visited is dropped...
theorem fillSkip (garden: Garden) (plant: Char) (position: Position) (rest: List Position) (visited: Set Position) (members: List Position)
    (taken: visited.contains position = True): Garden.fill garden plant (Cons position rest) visited members = Garden.fill garden plant rest visited members :=
  rewrite Garden.fill.unfold garden plant (Cons position rest) visited members in
    Decidable.elimEq _ _ _ _ (fresh => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym fresh) taken))) (other => rfl)

-- ...one growing `plant` is taken and its neighbours growing `plant` pushed...
theorem fillTake (garden: Garden) (plant: Char) (position: Position) (rest: List Position) (visited: Set Position) (members: List Position)
    (fresh: visited.contains position = False) (grows: garden.plantAt position = Some plant):
    Garden.fill garden plant (Cons position rest) visited members
      = Garden.fill garden plant (garden.neighboursGrowing plant position ++ rest) (visited.insert position) (Cons position members) :=
  rewrite Garden.fill.unfold garden plant (Cons position rest) visited members in
    Decidable.elimEq _ _ _ _ (isFresh => Decidable.elimEq _ _ _ _ (isGrowing => rfl) (notGrowing => Void.exfalso (notGrowing grows)))
      (notFresh => Void.exfalso (notFresh fresh))

-- ...and one growing something else is dropped.
theorem fillOther (garden: Garden) (plant: Char) (position: Position) (rest: List Position) (visited: Set Position) (members: List Position)
    (other: Not (garden.plantAt position = Some plant)):
    Garden.fill garden plant (Cons position rest) visited members = Garden.fill garden plant rest visited members :=
  rewrite Garden.fill.unfold garden plant (Cons position rest) visited members in
    Decidable.elimEq _ _ _ _ (isFresh => Decidable.elimEq _ _ _ _ (isGrowing => Void.exfalso (other isGrowing)) (notGrowing => rfl)) (notFresh => rfl)

-- The fill returns what `FillResult` says, from any state.
theorem fillCorrect (garden: Garden) (plant: Char) (start: Position) (stack: List Position) (visited: Set Position) (members: List Position)
    (state: FillState garden plant start stack visited members): FillResult garden plant start stack members (Garden.fill garden plant stack visited members)
    decreasing (garden.unvisited visited, stack.length)
:=
  match stack with
    | Nil =>
      rewrite Garden.fill.unfold garden plant Nil visited members in
        let (Both visitedMembers (Both distinct (Both sound (Both stacked closed)))) := state
        Both distinct
          (Both sound
            (Both
              (member isMember next pushed =>
                match closed member isMember next pushed with
                  | Inl inMembers => inMembers
                  | Inr none => Void.exfalso none)
              (Both (position member => member) (position none => Void.exfalso none))))
    | Cons position rest =>
      let visitedMembers := And.left state
      match taken: visited.contains position with
        | True =>
        let isMember := (visitedMembers position).forward taken
        let result := fillCorrect garden plant start rest visited members (popKeeps garden plant start position rest visited members state (Inl isMember))
          [decreasing := Nat.LexLess.Second rfl (omega)]
        let (Both distinct (Both sound (Both closed (Both kept fromStack)))) := result
        rewrite fillSkip garden plant position rest visited members taken in
          Both distinct
            (Both sound
              (Both closed
                (Both kept
                  (other onStack grows =>
                    match onStack with
                      | Inl here => kept other (rewrite <- here in isMember)
                      | Inr later => fromStack other later grows))))
        | False =>
        let fresh := taken
        match growing: garden.plantAt position == Some plant with
          | True =>
          let grows: garden.plantAt position = Some plant := DecEq.sound _ _ growing
          let result :=
            fillCorrect garden plant start (garden.neighboursGrowing plant position ++ rest) (visited.insert position) (Cons position members)
              (takeKeeps garden plant start position rest visited members state fresh grows)
              [decreasing := Nat.LexLess.First (garden.unvisitedInsert visited position plant grows fresh)]
          let (Both distinct (Both sound (Both closed (Both kept fromStack)))) := result
          rewrite fillTake garden plant position rest visited members fresh grows in
            Both distinct
              (Both sound
                (Both closed
                  (Both (other member => kept other (Inr member))
                    (other onStack otherGrows =>
                      match onStack with
                        | Inl here => kept other (Inl here)
                        | Inr later =>
                          fromStack other (List.memAppendRight other (garden.neighboursGrowing plant position) rest later) otherGrows))))
          | False =>
          let other: Not (garden.plantAt position = Some plant) := same => Bool.falseNotTrue (Eq.trans (Eq.sym growing) (rewrite same in DecEq.refl (Some plant)))
          let result := fillCorrect garden plant start rest visited members (popKeeps garden plant start position rest visited members state (Inr other))
            [decreasing := Nat.LexLess.Second rfl (omega)]
          let (Both distinct (Both sound (Both closed (Both kept fromStack)))) := result
          rewrite fillOther garden plant position rest visited members other in
            Both distinct
              (Both sound
                (Both closed
                  (Both kept
                    (candidate onStack grows =>
                      match onStack with
                        | Inl here => Void.exfalso (other (rewrite here in grows))
                        | Inr later => fromStack candidate later grows))))

-- The fill from `start` alone, with nothing visited.
theorem fillFromStart (garden: Garden) (plant: Char) (start: Position):
    FillResult garden plant start [start] Nil (Garden.fill garden plant [start] Set.empty Nil) :=
  fillCorrect garden plant start [start] Set.empty Nil
    (Both (position => { forward = contains => Void.exfalso (Bool.falseNotTrue contains), backward = none => Void.exfalso none })
      (Both Trivial
        (Both (position none => Void.exfalso none)
          (Both
            (position onStack =>
              match onStack with
                | Inl here => rewrite <- here in joinedRefl garden start
                | Inr none => Void.exfalso none)
            (member none => Void.exfalso none)))))

-- Every plot joined to a member of a closed list of plots is a member.
theorem closedChain (garden: Garden) (plant: Char) (result: List Position)
    (sound: (position: Position) → position ∈ result → garden.plantAt position = Some plant)
    (closed: (member: Position) → member ∈ result → (next: Position) → next ∈ garden.neighboursGrowing plant member → next ∈ result):
    (from: Position) → (chain: List Position) → (to: Position) → from ∈ result → isChain garden from chain to = True → to ∈ result
  | from, Nil, to, member, same => rewrite <- DecEq.sound from to same in member
  | from, Cons next rest, to, member, chained =>
    closedChain garden plant result sound closed next rest to
      (closed from member next (touchingGrowing garden plant from next (sound from member) (Bool.andLeft _ _ chained))) (Bool.andRight _ _ chained)

-- From a plot growing `plant`, the region is a fill.
theorem regionOfFill (garden: Garden) (start: Position) (plant: Char) (grows: garden.plantAt start = Some plant):
    garden.regionOf start = Garden.fill garden plant [start] Set.empty Nil :=
  rewrite grows in rfl

-- From a plot growing `plant`, the region the fill finds.
theorem regionOfIsRegion (garden: Garden) (start: Position) (plant: Char) (grows: garden.plantAt start = Some plant):
    IsRegion garden start (garden.regionOf start) :=
  rewrite regionOfFill garden start plant grows in
    let (Both distinct (Both sound (Both closed (Both kept fromStack)))) := fillFromStart garden plant start
    let result := Garden.fill garden plant [start] Set.empty Nil
    other => {
      forward = member => And.right (sound other member),
      backward = joined =>
        Exists.elim joined (chain chained =>
          closedChain garden plant result (position member => And.left (sound position member)) closed start chain other
            (fromStack start (Inl rfl) grows) chained)
    }

theorem regionOfDistinct (garden: Garden) (start: Position): List.Distinct (garden.regionOf start) :=
  match grows: garden.plantAt start with
    | Some plant => And.left (fillFromStart garden plant start)
    | None => Trivial
