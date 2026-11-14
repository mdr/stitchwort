--| The presses from `pressesFor` type the code (`pressesForTypes`).
--
-- On one keypad, a route's arrows walk the arm from one key to the next
-- without aiming at a gap, and A presses it (`routeTypes`); that is
-- checked by computing, for every pair of keys on both keypads
-- (`numericFits`, `directionalFits`). Down the chain, each keypad's keys
-- are typed by the keys of the keypad before (`yourPressesThrough`).

namespace Aoc.Year2024.Day21.Proofs
import Aoc.Year2024.Day21 (..)
import Aoc.Year2024.Day21.Spec (..)
import Std (Bool, DecEq, Eq, Finite, List, Nat, NonEmptyList, Option, Void)

--| Where the arrows of `route` take an arm from `aim`: none if it is ever
--| aimed at a gap or off the keypad.
def walk (rows: List (List (Option k))) (aim: Position): List Direction → Option Position
  | [] => Some aim
  | [direction, ..rest] =>
    moved aim direction |> .flatMap (next => keyAt rows next |> .flatMap (key => walk rows next rest))

--| Arrows, then other keys: the arrows walk the arm first.
theorem operateArrows ∀ (rows: List (List (Option k))) (aim: Position)
    (route: List Direction) (rest: List DirectionKey):
    operate rows aim (List.append (route.map Arrow) rest)
      = walk rows aim route |> .flatMap (end => operate rows end rest) :=
  match route with
    | [] => rfl
    | [direction, ..others] =>
      match step: moved aim direction with
        | None => rfl
        | Some next =>
          match found: keyAt rows next with
            | None => rfl
            | Some key => operateArrows rows next others rest

--| The number of moves between two places, along rows and columns.
def distance (from to: Position): Nat :=
  from.row - to.row + (to.row - from.row) + (from.column - to.column) + (to.column - from.column)

--| Whether `route` walks from `from` to `to` on `rows`, as few moves as
--| there can be.
def routeFits (rows: List (List (Option k))) (from to: Position) (route: List Direction): Bool :=
  walk rows from route == Some to && route.length == distance from to

--| How the keys of `keypad` sit on its rows: each key is where the program
--| places it, and there are routes between any two keys, all fitting. Every
--| key is `Finite.all`, the list derived for the key type, whose
--| `Finite.complete` says no key is missing.
def fits [auto decEq: DecEq k] [auto fin: Finite k] (keypad: Keypad k) (rows: List (List (Option k))): Bool :=
  List.all Finite.all (to => keyAt rows (keypad.place to) == Some to)
    && List.all Finite.all (from =>
      List.all Finite.all (to => (keypad.routes from to).all (routeFits rows (keypad.place from) (keypad.place to))))

theorem numericFits: fits Keypad.numeric numericRows = True := rfl

theorem directionalFits: fits Keypad.directional directionalRows = True := rfl

--| What `fits` gives for one pair of keys.
type Fitted (k: Type) = {
  keypad: Keypad k,
  rows: List (List (Option k)),
  onKey: ∀ (to: k) => keyAt rows (keypad.place to) = Some to,
  cheapestWalks: ∀ (costs: Costs) (from to: k) => walk rows
    (keypad.place from)
    (costs.cheapestRoute (keypad.routes from to))
    = Some (keypad.place to),
  cheapestLength: ∀ (costs: Costs) (from to: k) => (costs.cheapestRoute (keypad.routes from to)).length
    = distance (keypad.place from) (keypad.place to)
}

--| The cheapest of the routes passes a test they all pass.
theorem cheapestPasses ∀ (costs: Costs) (passes: List Direction → Bool) (choices: NonEmptyList (List Direction))
    (all: choices.all passes = True):
    passes (costs.cheapestRoute choices) = True :=
  minByStepPasses costs.routeCost passes choices.head (Bool.andLeft all) choices.tail (Bool.andRight all)

theorem cheapestFits ∀ [auto decEq: DecEq k] [auto fin: Finite k] (keypad: Keypad k) (rows: List (List (Option k)))
    (checked: fits keypad rows = True)
    (costs: Costs) (from to: k):
    routeFits rows (keypad.place from) (keypad.place to) (costs.cheapestRoute (keypad.routes from to)) = True :=
  let pairs := checked.right
  let fromChecked := Finite.check _ pairs from
  let pairChecked := Finite.check _ fromChecked to
  cheapestPasses costs (routeFits rows (keypad.place from) (keypad.place to)) (keypad.routes from to) pairChecked

def fitted [auto decEq: DecEq k] [auto fin: Finite k] (keypad: Keypad k) (rows: List (List (Option k)))
    (checked: fits keypad rows = True):
    Fitted k :=
  {
    keypad,
    rows,
    onKey = to => DecEq.sound (Finite.check (to => keyAt rows (keypad.place to) == Some to) checked.left to),
    cheapestWalks = costs from to => DecEq.sound (Bool.andLeft (cheapestFits keypad rows checked costs from to)),
    cheapestLength = costs from to => DecEq.sound (Bool.andRight (cheapestFits keypad rows checked costs from to))
  }

def numericFitted: Fitted NumericKey := fitted Keypad.numeric numericRows numericFits

def directionalFitted: Fitted DirectionKey := fitted Keypad.directional directionalRows directionalFits

--| A robot driven by `drivingKeys` presses the keys, its arm first on `from`.
theorem drivingKeysType ∀ (fit: Fitted k) (costs: Costs) (from: k) (keys: List k):
    operate fit.rows (fit.keypad.place from) (drivingKeys fit.keypad costs from keys) = Some keys :=
  match keys with
    | [] => rfl
    | [to, ..rest] =>
      let route := costs.cheapestRoute (fit.keypad.routes from to)
      rewrite List.appendAssoc (route.map Arrow) [Activate] (drivingKeys fit.keypad costs to rest),
          operateArrows fit.rows (fit.keypad.place from) route [Activate, ..drivingKeys fit.keypad costs to rest],
          fit.cheapestWalks costs from to,
          fit.onKey to,
          drivingKeysType fit costs to rest in
        rfl

--| Your presses passed through `robots` robots on directional keypads.
def throughRobots: (robots: Nat) → List DirectionKey → Option (List DirectionKey)
  | Zero, presses => Some presses
  | Succ others, presses => operate directionalRows directionalStart presses |> .flatMap (throughRobots others)

theorem typedThrough ∀ (robots: Nat) (presses: List DirectionKey):
    typed robots presses = throughRobots robots presses |> .flatMap (operate numericRows numericStart) :=
  match robots with
    | Zero => rfl
    | Succ others =>
      match driven: operate directionalRows directionalStart presses with
        | None => rfl
        | Some keys => typedThrough others keys

--| The robot nearest the door is the last one the presses pass through.
theorem throughRobotsLast ∀ (robots: Nat) (presses: List DirectionKey):
    throughRobots (Succ robots) presses
      = throughRobots robots presses |> .flatMap (operate directionalRows directionalStart) :=
  match robots with
    | Zero => flatMapIntoSome (operate directionalRows directionalStart presses)
    | Succ others =>
      match driven: operate directionalRows directionalStart presses with
        | None => rfl
        | Some keys => throughRobotsLast others keys

theorem yourPressesThrough ∀ (level: Nat) (keys: List DirectionKey):
    throughRobots level (yourPresses level keys) = Some keys :=
  match level with
    | Zero => rfl
    | Succ level =>
      let driving := drivingKeys Keypad.directional (robotCosts level) Activate keys
      rewrite throughRobotsLast level (yourPresses level driving), yourPressesThrough level driving in
        drivingKeysType directionalFitted (robotCosts level) Activate keys

theorem pressesForTypes ∀ (robots: Nat) (code: Code): Types robots code (pressesFor robots code) :=
  rewrite typedThrough robots (pressesFor robots code),
      yourPressesThrough robots (drivingKeys Keypad.numeric (robotCosts robots) Enter code) in
    drivingKeysType numericFitted (robotCosts robots) Enter code
