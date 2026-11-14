-- PROTOTYPE (SW-1028): what the generator would make for `Garden.fill`,
-- written by hand (its branch equations and its functional induction), and
-- `fillCorrect` proved again with them. To run it, copy it into a copy of the
-- AoC project as `src/Aoc/Year2024/Day12/Proofs/Induct.sw` and run
-- `stitchwort check --no-cache Aoc.Year2024.Day12.Proofs` there.

namespace Aoc.Year2024.Day12.Proofs
import Aoc.Year2024.Day12 (..)
import Aoc.Common (Direction, Position, directions)
import Aoc.Year2024.Day12.Spec (..)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Iff, List, Nat, Option, Or, Set, Void)

-- Missing from std; the generated proof of `Garden.fill.induct` turns the
-- `else` of `if fresh: b = False`, `Not (b = False)`, into `b = True` with it
-- (D2186), so the user's proof never sees the negated form.
theorem trueOfNotFalse: (b: Bool) → Not (b = False) → b = True
  | True, n => rfl
  | False, n => Void.exfalso (n rfl)

-- `Garden.fill.eq1`
theorem fillEq1 ∀ (garden: Garden) (plant: Char) (visited: Set Position) (members: List Position):
    Garden.fill garden plant Nil visited members = members :=
  rewrite Garden.fill.unfold garden plant Nil visited members in rfl

-- `Garden.fill.eq2.ifTrue.ifTrue`
theorem fillEq2IfTrueIfTrue ∀ (garden: Garden) (plant: Char) (position: Position) (rest: List Position)
    (visited: Set Position) (members: List Position)
    (fresh: visited.contains position = False)
    (grows: garden.plantAt position = Some plant):
    Garden.fill garden plant (Cons position rest) visited members
      = Garden.fill garden plant
        (garden.neighboursGrowing plant position ++ rest)
        (visited.insert position)
        (Cons position members) :=
  rewrite Garden.fill.unfold garden plant (Cons position rest) visited members in
    Decidable.elimEq _ _ _ _
      (isFresh => Decidable.elimEq _ _ _ _ (isGrowing => rfl) (notGrowing => Void.exfalso (notGrowing grows)))
      (notFresh => Void.exfalso (notFresh fresh))

-- `Garden.fill.eq2.ifTrue.ifFalse`
theorem fillEq2IfTrueIfFalse ∀ (garden: Garden) (plant: Char) (position: Position) (rest: List Position)
    (visited: Set Position) (members: List Position)
    (fresh: visited.contains position = False)
    (grows: Not (garden.plantAt position = Some plant)):
    Garden.fill garden plant (Cons position rest) visited members = Garden.fill garden plant rest visited members :=
  rewrite Garden.fill.unfold garden plant (Cons position rest) visited members in
    Decidable.elimEq _ _ _ _
      (isFresh => Decidable.elimEq _ _ _ _ (isGrowing => Void.exfalso (grows isGrowing)) (notGrowing => rfl))
      (notFresh => Void.exfalso (notFresh fresh))

-- `Garden.fill.eq2.ifFalse`
theorem fillEq2IfFalse ∀ (garden: Garden) (plant: Char) (position: Position) (rest: List Position)
    (visited: Set Position) (members: List Position)
    (notFresh: visited.contains position = True):
    Garden.fill garden plant (Cons position rest) visited members = Garden.fill garden plant rest visited members :=
  rewrite Garden.fill.unfold garden plant (Cons position rest) visited members in
    Decidable.elimEq _ _ _ _
      (isFresh => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym notFresh) isFresh)))
      (other => rfl)

-- `Garden.fill.induct`: `garden` and `plant` are the same in every recursive
-- call, so they come first and the motive doesn't take them.
theorem fillInduct ∀ (garden: Garden) (plant: Char) (motive: List Position → Set Position → List Position → Prop)
    (eq1: (visited: Set Position) → (members: List Position) → motive Nil visited members)
    (eq2IfTrueIfTrue: (position: Position)
      → (rest: List Position)
      → (visited: Set Position)
      → (members: List Position)
      → (fresh: visited.contains position = False)
      → (grows: garden.plantAt position = Some plant)
      → motive (garden.neighboursGrowing plant position ++ rest) (visited.insert position) (Cons position members)
      → motive (Cons position rest) visited members)
    (eq2IfTrueIfFalse: (position: Position)
      → (rest: List Position)
      → (visited: Set Position)
      → (members: List Position)
      → (fresh: visited.contains position = False)
      → (grows: Not (garden.plantAt position = Some plant))
      → motive rest visited members
      → motive (Cons position rest) visited members)
    (eq2IfFalse: (position: Position)
      → (rest: List Position)
      → (visited: Set Position)
      → (members: List Position)
      → (notFresh: visited.contains position = True)
      → motive rest visited members
      → motive (Cons position rest) visited members) (stack: List Position) (visited: Set Position)
    (members: List Position):
    motive stack visited members
    decreasing (garden.unvisited visited, stack.length)
:=
  match stack with
    | Nil => eq1 visited members
    | Cons position rest =>
      if fresh: visited.contains position = False then
        if grows: garden.plantAt position = Some plant then
          eq2IfTrueIfTrue position rest visited members fresh grows
            (fillInduct garden plant motive eq1 eq2IfTrueIfTrue eq2IfTrueIfFalse eq2IfFalse
              (garden.neighboursGrowing plant position ++ rest)
              (visited.insert position)
              (Cons position members)
              [decreasing := Nat.LexLess.First (garden.unvisitedInsert visited position plant grows fresh)])
        else
          eq2IfTrueIfFalse position rest visited members fresh grows
            (fillInduct garden plant motive eq1 eq2IfTrueIfTrue eq2IfTrueIfFalse eq2IfFalse rest visited members
              [decreasing := Nat.LexLess.Second rfl (omega)])
      else
        eq2IfFalse position rest visited members
          (trueOfNotFalse _ fresh)
          (fillInduct garden plant motive eq1 eq2IfTrueIfTrue eq2IfTrueIfFalse eq2IfFalse rest visited members
            [decreasing := Nat.LexLess.Second rfl (omega)])

-- `fillCorrect` (Fill.sw) again, by `Garden.fill.induct` and the equations.
theorem fillCorrectByInduct ∀ (garden: Garden) (plant: Char) (start: Position) (stack: List Position)
    (visited: Set Position) (members: List Position)
    (state: FillState garden plant start stack visited members):
    FillResult garden plant start stack members (Garden.fill garden plant stack visited members) :=
  fillInduct garden plant
    (stack visited members =>
      FillState garden plant start stack visited members
        → FillResult garden plant start stack members (Garden.fill garden plant stack visited members))
    (visited members state =>
      rewrite fillEq1 garden plant visited members in
        let (Both visitedMembers (Both distinct (Both sound (Both stacked closed)))) := state
        Both distinct
          (Both sound
            (Both
              (member isMember next pushed =>
                match closed member isMember next pushed with
                  | Inl inMembers => inMembers
                  | Inr none => Void.exfalso none)
              (Both (position member => member) (position none => Void.exfalso none)))))
    (position rest visited members fresh grows ih state =>
      let (Both distinct (Both sound (Both closed (Both kept fromStack)))) :=
        ih (takeKeeps garden plant start position rest visited members state fresh grows)
      rewrite fillEq2IfTrueIfTrue garden plant position rest visited members fresh grows in
        Both distinct
          (Both sound
            (Both closed
              (Both (other member => kept other (Inr member)) (other onStack otherGrows =>
                match onStack with
                  | Inl here => kept other (Inl here)
                  | Inr later =>
                    fromStack other
                      (List.memAppendRight other (garden.neighboursGrowing plant position) rest later)
                      otherGrows)))))
    (position rest visited members fresh other ih state =>
      let (Both distinct (Both sound (Both closed (Both kept fromStack)))) :=
        ih (popKeeps garden plant start position rest visited members state (Inr other))
      rewrite fillEq2IfTrueIfFalse garden plant position rest visited members fresh other in
        Both distinct
          (Both sound
            (Both closed
              (Both kept (candidate onStack grows =>
                match onStack with
                  | Inl here => Void.exfalso (other (rewrite here in grows))
                  | Inr later => fromStack candidate later grows)))))
    (position rest visited members notFresh ih state =>
      let isMember := (And.left state position).forward notFresh
      let (Both distinct (Both sound (Both closed (Both kept fromStack)))) :=
        ih (popKeeps garden plant start position rest visited members state (Inl isMember))
      rewrite fillEq2IfFalse garden plant position rest visited members notFresh in
        Both distinct
          (Both sound
            (Both closed
              (Both kept (other onStack grows =>
                match onStack with
                  | Inl here => kept other (rewrite <- here in isMember)
                  | Inr later => fromStack other later grows)))))
    stack
    visited
    members
    state
