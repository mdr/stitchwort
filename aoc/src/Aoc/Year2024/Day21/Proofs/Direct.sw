--| The walk fact when you press the keys yourself, every press costing one:
--| a walk is at least as long as the moves along rows and columns between
--| its ends (`walkDistance`), which is the length of every route the program
--| considers. So with no robots on directional keypads the program's length
--| is the shortest (`shortestWithoutRobots`), and the directional keypad
--| nearest you has the walk fact for any number of robots.

namespace Aoc.Year2024.Day21.Proofs
import Aoc.Year2024.Day21 (..)
import Aoc.Year2024.Day21.Spec (..)
import Std (Bool, Eq, List, Nat, Option, Void)

--| One move changes the distance to anywhere by at most one.
theorem movedNear (aim: Position) (to: Position) (direction: Direction) (next: Position) (step: moved aim direction = Some next):
    distance aim to ≤ distance next to + 1 :=
  match direction with
    | Up =>
      match top: aim.row == 0 with
        | False => rewrite <- Option.someInjective step in omega [top]
    | Down => rewrite <- Option.someInjective step in omega
    | Left =>
      match edge: aim.column == 0 with
        | False => rewrite <- Option.someInjective step in omega [edge]
    | Right => rewrite <- Option.someInjective step in omega

--| A walk has at least as many moves as the distance between its ends.
theorem walkDistance (rows: List (List (Option k))) (start: Position) (route: List Direction) (end: Position)
    (walked: walk rows start route = Some end): distance start end ≤ route.length :=
  match route with
    | [] => rewrite <- Option.someInjective walked in omega
    | [direction, ..rest] =>
      match step: moved start direction with
        | Some next =>
          match found: keyAt rows next with
            | Some key => omega [movedNear start end direction next step, walkDistance rows next rest end walked]

--| Pressing a route's keys yourself takes a press per move and one for A.
theorem routeCostYours (route: List Direction): Costs.yours.routeCost route = route.length + 1 :=
  rewrite sequenceCostFrom Costs.yours (routeKeys route), costFromOnes Activate (routeKeys route), List.lengthAppend (route.map Arrow) [Activate],
    List.lengthMap route Arrow
    in rfl

--| A key's place is the only one where an arm aims at it.
theorem numericPlaceOf (row column: Nat) (key: NumericKey) (found: keyAt numericRows { row, column } = Some key):
    ({ row, column }: Position) = Keypad.numeric.place key :=
  match row, column with
    | 0, 0 => rewrite <- Option.someInjective found in rfl
    | 0, 1 => rewrite <- Option.someInjective found in rfl
    | 0, 2 => rewrite <- Option.someInjective found in rfl
    | 1, 0 => rewrite <- Option.someInjective found in rfl
    | 1, 1 => rewrite <- Option.someInjective found in rfl
    | 1, 2 => rewrite <- Option.someInjective found in rfl
    | 2, 0 => rewrite <- Option.someInjective found in rfl
    | 2, 1 => rewrite <- Option.someInjective found in rfl
    | 2, 2 => rewrite <- Option.someInjective found in rfl
    | 3, 0 => Void.exfalso (Option.noneNotSome key found)
    | 3, 1 => rewrite <- Option.someInjective found in rfl
    | 3, 2 => rewrite <- Option.someInjective found in rfl
    | 0, Succ (Succ (Succ column)) => Void.exfalso (Option.noneNotSome key found)
    | 1, Succ (Succ (Succ column)) => Void.exfalso (Option.noneNotSome key found)
    | 2, Succ (Succ (Succ column)) => Void.exfalso (Option.noneNotSome key found)
    | 3, Succ (Succ (Succ column)) => Void.exfalso (Option.noneNotSome key found)
    | Succ (Succ (Succ (Succ row))), column => Void.exfalso (Option.noneNotSome key found)

theorem directionalPlaceOf (row column: Nat) (key: DirectionKey) (found: keyAt directionalRows { row, column } = Some key):
    ({ row, column }: Position) = Keypad.directional.place key :=
  match row, column with
    | 0, 0 => Void.exfalso (Option.noneNotSome key found)
    | 0, 1 => rewrite <- Option.someInjective found in rfl
    | 0, 2 => rewrite <- Option.someInjective found in rfl
    | 1, 0 => rewrite <- Option.someInjective found in rfl
    | 1, 1 => rewrite <- Option.someInjective found in rfl
    | 1, 2 => rewrite <- Option.someInjective found in rfl
    | 0, Succ (Succ (Succ column)) => Void.exfalso (Option.noneNotSome key found)
    | 1, Succ (Succ (Succ column)) => Void.exfalso (Option.noneNotSome key found)
    | Succ (Succ row), column => Void.exfalso (Option.noneNotSome key found)

--| The walk fact for your own presses, on a keypad where each key has one place.
theorem cheapestWalksYours (fit: Fitted k)
    (placeOf: ∀ (row column: Nat) (key: k) => keyAt fit.rows { row, column } = Some key → ({ row, column }: Position) = fit.keypad.place key):
    CheapestWalks fit.keypad fit.rows (robotCosts 0) :=
  start from onFrom route end walked to onTo =>
    let startPlace := placeOf start.row start.column from onFrom
    let endPlace := placeOf end.row end.column to onTo
    let walkBound := walkDistance fit.rows start route end walked
    rewrite routeCostYours route, routeCostYours (Costs.yours.cheapestRoute (fit.keypad.routes from to)), fit.cheapestLength Costs.yours from to,
      <- startPlace, <- endPlace
      in omega [walkBound]

theorem numericWalksYours: CheapestWalks Keypad.numeric numericRows (robotCosts 0) := cheapestWalksYours numericFitted numericPlaceOf

theorem directionalWalksYours: CheapestWalks Keypad.directional directionalRows (robotCosts 0) := cheapestWalksYours directionalFitted directionalPlaceOf

theorem optimalWithoutRobots: Optimal 0 := optimalIfCheapestWalks 0 (level below => Void.exfalso (omega [below])) numericWalksYours

--| With you pressing the door's keypad's keys yourself, the program's length
--| is the shortest.
theorem shortestWithoutRobots (code: Code): Shortest 0 code ((robotCosts 0).shortestLength code) :=
  shortestIfOptimal 0 optimalWithoutRobots code

--| And the sum of complexities is the puzzle's answer for any codes.
theorem answerWithoutRobots (codes: List Code): Answer 0 codes (complexities 0 codes) := complexitiesAnswer 0 optimalWithoutRobots codes
