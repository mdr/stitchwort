-- The walk fact when you press the keys yourself, every press costing one:
-- a walk is at least as long as the moves along rows and columns between
-- its ends (`walkDistance`), which is the length of every route the program
-- considers. So with no robots on directional keypads the program's length
-- is the shortest (`shortestWithoutRobots`), and the directional keypad
-- nearest you has the walk fact for any number of robots.

namespace Aoc.Year2024.Day21.Proofs
import Aoc.Year2024.Day21 (..)
import Aoc.Year2024.Day21.Spec (..)
import Std (Bool, Eq, List, Nat, Option, Void)

-- One move changes the distance to anywhere by at most one.
theorem movedNear (aim: Position) (to: Position): (direction: Direction) → (next: Position) → moved aim direction = Some next →
    distance aim to ≤ distance next to + 1
  | Up, next, step =>
    match top: aim.row == 0 with
      | True => Void.exfalso (Option.noneNotSome next step)
      | False => rewrite <- Option.someInjective _ next step in omega [top]
  | Down, next, step => rewrite <- Option.someInjective _ next step in omega
  | Left, next, step =>
    match edge: aim.column == 0 with
      | True => Void.exfalso (Option.noneNotSome next step)
      | False => rewrite <- Option.someInjective _ next step in omega [edge]
  | Right, next, step => rewrite <- Option.someInjective _ next step in omega

-- A walk has at least as many moves as the distance between its ends.
theorem walkDistance (rows: List (List (Option k))): (start: Position) → (route: List Direction) → (end: Position) →
    walk rows start route = Some end → distance start end ≤ route.length
  | start, Nil, end, walked => rewrite <- Option.someInjective start end walked in omega
  | start, Cons direction rest, end, walked =>
    match step: moved start direction with
      | None => Void.exfalso (Option.noneNotSome end walked)
      | Some next =>
        match found: keyAt rows next with
          | None => Void.exfalso (Option.noneNotSome end walked)
          | Some key => omega [movedNear start end direction next step, walkDistance rows next rest end walked]

-- Pressing a route's keys yourself takes a press per move and one for A.
theorem routeCostYours (route: List Direction): routeCost yourCosts route = route.length + 1 :=
  rewrite sequenceCostFrom yourCosts (routeKeys route), costFromOnes Activate (routeKeys route), List.lengthAppend (route.map Arrow) [Activate],
    List.lengthMap route Arrow
    in rfl

-- A key's place is the only one where an arm aims at it.
theorem numericPlaceOf: (row: Nat) → (column: Nat) → (key: NumericKey) → keyAt numericRows { row, column } = Some key →
    ({ row, column }: Position) = numericKeypad.place key
  | 0, 0, key, found => rewrite <- Option.someInjective Digit7 key found in rfl
  | 0, 1, key, found => rewrite <- Option.someInjective Digit8 key found in rfl
  | 0, 2, key, found => rewrite <- Option.someInjective Digit9 key found in rfl
  | 1, 0, key, found => rewrite <- Option.someInjective Digit4 key found in rfl
  | 1, 1, key, found => rewrite <- Option.someInjective Digit5 key found in rfl
  | 1, 2, key, found => rewrite <- Option.someInjective Digit6 key found in rfl
  | 2, 0, key, found => rewrite <- Option.someInjective Digit1 key found in rfl
  | 2, 1, key, found => rewrite <- Option.someInjective Digit2 key found in rfl
  | 2, 2, key, found => rewrite <- Option.someInjective Digit3 key found in rfl
  | 3, 0, key, found => Void.exfalso (Option.noneNotSome key found)
  | 3, 1, key, found => rewrite <- Option.someInjective Digit0 key found in rfl
  | 3, 2, key, found => rewrite <- Option.someInjective Enter key found in rfl
  | 0, Succ (Succ (Succ column)), key, found => Void.exfalso (Option.noneNotSome key found)
  | 1, Succ (Succ (Succ column)), key, found => Void.exfalso (Option.noneNotSome key found)
  | 2, Succ (Succ (Succ column)), key, found => Void.exfalso (Option.noneNotSome key found)
  | 3, Succ (Succ (Succ column)), key, found => Void.exfalso (Option.noneNotSome key found)
  | Succ (Succ (Succ (Succ row))), column, key, found => Void.exfalso (Option.noneNotSome key found)

theorem directionalPlaceOf: (row: Nat) → (column: Nat) → (key: DirectionKey) → keyAt directionalRows { row, column } = Some key →
    ({ row, column }: Position) = directionalKeypad.place key
  | 0, 0, key, found => Void.exfalso (Option.noneNotSome key found)
  | 0, 1, key, found => rewrite <- Option.someInjective (Arrow Up) key found in rfl
  | 0, 2, key, found => rewrite <- Option.someInjective Activate key found in rfl
  | 1, 0, key, found => rewrite <- Option.someInjective (Arrow Left) key found in rfl
  | 1, 1, key, found => rewrite <- Option.someInjective (Arrow Down) key found in rfl
  | 1, 2, key, found => rewrite <- Option.someInjective (Arrow Right) key found in rfl
  | 0, Succ (Succ (Succ column)), key, found => Void.exfalso (Option.noneNotSome key found)
  | 1, Succ (Succ (Succ column)), key, found => Void.exfalso (Option.noneNotSome key found)
  | Succ (Succ row), column, key, found => Void.exfalso (Option.noneNotSome key found)

-- The walk fact for your own presses, on a keypad where each key has one place.
theorem cheapestWalksYours (fit: Fitted k)
    (placeOf: (row: Nat) → (column: Nat) → (key: k) → keyAt fit.rows { row, column } = Some key → ({ row, column }: Position) = fit.keypad.place key):
    CheapestWalks fit.keypad fit.rows (robotCosts 0) :=
  start from onFrom route end walked to onTo =>
    let startPlace := placeOf start.row start.column from onFrom
    let endPlace := placeOf end.row end.column to onTo
    let walkBound := walkDistance fit.rows start route end walked
    rewrite routeCostYours route, routeCostYours (cheapestRoute yourCosts (routes fit.keypad from to)), fit.cheapestLength yourCosts from to,
      <- startPlace, <- endPlace
      in omega [walkBound]

theorem numericWalksYours: CheapestWalks numericKeypad numericRows (robotCosts 0) := cheapestWalksYours numericFitted numericPlaceOf

theorem directionalWalksYours: CheapestWalks directionalKeypad directionalRows (robotCosts 0) := cheapestWalksYours directionalFitted directionalPlaceOf

-- With you pressing the door's keypad's keys yourself, the program's length
-- is the shortest.
theorem shortestWithoutRobots (code: Code): Shortest 0 code (shortestLength (robotCosts 0) code) :=
  shortestIfOptimal 0 (optimalIfCheapestWalks 0 (level below => Void.exfalso (omega [below])) numericWalksYours) code
