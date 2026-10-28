-- The presses from `pressesFor` type the code (`pressesForTypes`). On one
-- keypad, a route's arrows walk the arm from one key to the next without
-- aiming at a gap, and A presses it (`routeTypes`); that is checked by
-- computing, for every pair of keys on both keypads (`numericFits`,
-- `directionalFits`). Down the chain, each keypad's keys are typed by the
-- keys of the keypad before (`yourPressesThrough`).

namespace Aoc.Year2024.Day21.Proofs
import Aoc.Year2024.Day21 (..)
import Aoc.Year2024.Day21.Spec (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Void)

-- Where the arrows of `route` take an arm from `aim`: none if it is ever
-- aimed at a gap or off the keypad.
def walk (rows: List (List (Option k))) (aim: Position): List Direction → Option Position
  | Nil => Some aim
  | Cons direction rest => moved aim direction |> .flatMap (next => keyAt rows next |> .flatMap (key => walk rows next rest))

-- Arrows, then other keys: the arrows walk the arm first.
theorem operateArrows (rows: List (List (Option k))): (aim: Position) → (route: List Direction) → (rest: List DirectionKey) →
    operate rows aim (List.append (route.map Arrow) rest) = walk rows aim route |> .flatMap (end => operate rows end rest)
  | aim, Nil, rest => rfl
  | aim, Cons direction others, rest =>
    match step: moved aim direction with
      | None => rfl
      | Some next =>
        match found: keyAt rows next with
          | None => rfl
          | Some key => operateArrows rows next others rest

-- Whether there are any.
def hasSome: List a → Bool
  | Nil => False
  | Cons first rest => True

-- The number of moves between two places, along rows and columns.
def distance (from: Position) (to: Position): Nat := from.row - to.row + (to.row - from.row) + (from.column - to.column) + (to.column - from.column)

-- Whether `route` walks from `from` to `to` on `rows`, as few moves as
-- there can be.
def routeFits (rows: List (List (Option k))) (from: Position) (to: Position) (route: List Direction): Bool :=
  walk rows from route == Some to && route.length == distance from to

-- How the keys of `keypad` sit on its rows: each key is where the program
-- places it, and there are routes between any two keys, all fitting.
def fits [auto decEq: DecEq k] (keys: List k) (keypad: Keypad k) (rows: List (List (Option k))): Bool :=
  keys.all (to => keyAt rows (keypad.place to) == Some to)
    && keys.all (from =>
      keys.all (to =>
        hasSome (routes keypad from to) && (routes keypad from to).all (routeFits rows (keypad.place from) (keypad.place to))))

def numericKeys: List NumericKey := [Digit0, Digit1, Digit2, Digit3, Digit4, Digit5, Digit6, Digit7, Digit8, Digit9, Enter]

theorem numericFits: fits numericKeys numericKeypad numericRows = True := rfl

theorem directionalFits: fits directionKeys directionalKeypad directionalRows = True := rfl

theorem everyNumericKey: (key: NumericKey) → key ∈ numericKeys
  | Digit0 => Inl rfl
  | Digit1 => Inr (Inl rfl)
  | Digit2 => Inr (Inr (Inl rfl))
  | Digit3 => Inr (Inr (Inr (Inl rfl)))
  | Digit4 => Inr (Inr (Inr (Inr (Inl rfl))))
  | Digit5 => Inr (Inr (Inr (Inr (Inr (Inl rfl)))))
  | Digit6 => Inr (Inr (Inr (Inr (Inr (Inr (Inl rfl))))))
  | Digit7 => Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl rfl)))))))
  | Digit8 => Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl rfl))))))))
  | Digit9 => Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl rfl)))))))))
  | Enter => Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl rfl))))))))))

theorem everyDirectionKey: (key: DirectionKey) → key ∈ directionKeys
  | Arrow Up => Inl rfl
  | Arrow Down => Inr (Inl rfl)
  | Arrow Left => Inr (Inr (Inl rfl))
  | Arrow Right => Inr (Inr (Inr (Inl rfl)))
  | Activate => Inr (Inr (Inr (Inr (Inl rfl))))

-- What `fits` gives for one pair of keys.
type Fitted (k: Type) = {
  keypad: Keypad k,
  rows: List (List (Option k)),
  onKey: (to: k) → keyAt rows (keypad.place to) = Some to,
  cheapestWalks: (costs: Costs) → (from: k) → (to: k) →
    walk rows (keypad.place from) (cheapestRoute costs (routes keypad from to)) = Some (keypad.place to),
  cheapestLength: (costs: Costs) → (from: k) → (to: k) →
    (cheapestRoute costs (routes keypad from to)).length = distance (keypad.place from) (keypad.place to)
}

-- The cheapest of a non-empty list of routes passes a test they all pass.
theorem cheapestPasses (costs: Costs) (passes: List Direction → Bool): (choices: List (List Direction)) → hasSome choices = True →
    List.all choices passes = True → passes (cheapestRoute costs choices) = True
  | Nil, some, all => Void.exfalso (Bool.falseNotTrue some)
  | Cons first others, some, all => minByStepPasses (routeCost costs) passes first (Bool.andLeft _ _ all) others (Bool.andRight _ _ all)

theorem cheapestFits [auto decEq: DecEq k] (keys: List k) (every: (key: k) → key ∈ keys) (keypad: Keypad k) (rows: List (List (Option k)))
    (checked: fits keys keypad rows = True) (costs: Costs) (from: k) (to: k):
    routeFits rows (keypad.place from) (keypad.place to) (cheapestRoute costs (routes keypad from to)) = True :=
  let pairs := Bool.andRight _ _ checked
  let fromChecked := allMember _ keys pairs from (every from)
  let pairChecked := allMember _ keys fromChecked to (every to)
  cheapestPasses costs (routeFits rows (keypad.place from) (keypad.place to)) (routes keypad from to) (Bool.andLeft _ _ pairChecked)
    (Bool.andRight _ _ pairChecked)

def fitted [auto decEq: DecEq k] (keys: List k) (every: (key: k) → key ∈ keys) (keypad: Keypad k) (rows: List (List (Option k)))
    (checked: fits keys keypad rows = True): Fitted k := {
  keypad,
  rows,
  onKey = to => DecEq.sound _ _ (allMember (to => keyAt rows (keypad.place to) == Some to) keys (Bool.andLeft _ _ checked) to (every to)),
  cheapestWalks = costs from to => DecEq.sound _ _ (Bool.andLeft _ _ (cheapestFits keys every keypad rows checked costs from to)),
  cheapestLength = costs from to => DecEq.sound _ _ (Bool.andRight _ _ (cheapestFits keys every keypad rows checked costs from to))
}

def numericFitted: Fitted NumericKey := fitted numericKeys everyNumericKey numericKeypad numericRows numericFits

def directionalFitted: Fitted DirectionKey := fitted directionKeys everyDirectionKey directionalKeypad directionalRows directionalFits

-- A robot driven by `drivingKeys` presses the keys, its arm first on `from`.
theorem drivingKeysType (fit: Fitted k) (costs: Costs): (from: k) → (keys: List k) →
    operate fit.rows (fit.keypad.place from) (drivingKeys fit.keypad costs from keys) = Some keys
  | from, Nil => rfl
  | from, Cons to rest =>
    let route := cheapestRoute costs (routes fit.keypad from to)
    rewrite List.appendAssoc (route.map Arrow) [Activate] (drivingKeys fit.keypad costs to rest),
      operateArrows fit.rows (fit.keypad.place from) route (Cons Activate (drivingKeys fit.keypad costs to rest)),
      fit.cheapestWalks costs from to,
      fit.onKey to,
      drivingKeysType fit costs to rest
      in rfl

-- Your presses passed through `robots` robots on directional keypads.
def throughRobots: (robots: Nat) → List DirectionKey → Option (List DirectionKey)
  | Zero, presses => Some presses
  | Succ others, presses => operate directionalRows directionalStart presses |> .flatMap (throughRobots others)

theorem typedThrough: (robots: Nat) → (presses: List DirectionKey) →
    typed robots presses = throughRobots robots presses |> .flatMap (operate numericRows numericStart)
  | Zero, presses => rfl
  | Succ others, presses =>
    match driven: operate directionalRows directionalStart presses with
      | None => rfl
      | Some keys => typedThrough others keys

-- The robot nearest the door is the last one the presses pass through.
theorem throughRobotsLast: (robots: Nat) → (presses: List DirectionKey) →
    throughRobots (Succ robots) presses = throughRobots robots presses |> .flatMap (operate directionalRows directionalStart)
  | Zero, presses => flatMapIntoSome (operate directionalRows directionalStart presses)
  | Succ others, presses =>
    match driven: operate directionalRows directionalStart presses with
      | None => rfl
      | Some keys => throughRobotsLast others keys

theorem yourPressesThrough: (level: Nat) → (keys: List DirectionKey) → throughRobots level (yourPresses level keys) = Some keys
  | Zero, keys => rfl
  | Succ level, keys =>
    let driving := drivingKeys directionalKeypad (robotCosts level) Activate keys
    rewrite throughRobotsLast level (yourPresses level driving), yourPressesThrough level driving in
      drivingKeysType directionalFitted (robotCosts level) Activate keys

theorem pressesForTypes (robots: Nat) (code: Code): Types robots code (pressesFor robots code) :=
  rewrite typedThrough robots (pressesFor robots code), yourPressesThrough robots (drivingKeys numericKeypad (robotCosts robots) Enter code) in
    drivingKeysType numericFitted (robotCosts robots) Enter code
