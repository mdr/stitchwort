-- The presses behind the program's lengths: on each keypad, the cheapest
-- route between each key and the next, then A, and those keys typed the
-- same way on the keypad before, out to yours (`pressesFor`). Their number
-- is the program's length (`pressesForLength`).

namespace Aoc.Year2024.Day21.Proofs
import Aoc.Year2024.Day21 (..)
import Std (Eq, List, Nat)

-- The keys to press on the keypad driving a robot for it to press `keys`
-- in turn, its arm first on `from`: the cheapest route to each, then A.
def drivingKeys (keypad: Keypad k) (costs: Costs) (from: k): List k → List DirectionKey
  | Nil => Nil
  | Cons to rest => List.append (routeKeys (cheapestRoute costs (routes keypad from to))) (drivingKeys keypad costs to rest)

-- Your presses for the keypad `level` keypads from yours to press `keys`.
def yourPresses: (level: Nat) → List DirectionKey → List DirectionKey
  | Zero, keys => keys
  | Succ level, keys => yourPresses level (drivingKeys directionalKeypad (robotCosts level) Activate keys)

-- Your presses for the door's robot to type `code`, with `robots` robots on
-- directional keypads.
def pressesFor (robots: Nat) (code: Code): List DirectionKey := yourPresses robots (drivingKeys numericKeypad (robotCosts robots) Enter code)

-- The cost of the cheapest route between two keys, then A.
def cheapestBetween (keypad: Keypad k) (costs: Costs) (from: k) (to: k): Nat := cheapestCost costs (routes keypad from to)

theorem sequenceCostFrom (costs: Costs) (keys: List DirectionKey): sequenceCost costs keys = costFrom costs Activate keys := sumByPairs costs Activate keys

-- Each route's keys end with A, so the next route starts from it.
theorem drivingKeysCost (keypad: Keypad k) (costs: Costs): (from: k) → (keys: List k) →
    costFrom costs Activate (drivingKeys keypad costs from keys) = costFrom (cheapestBetween keypad costs) from keys
  | from, Nil => rfl
  | from, Cons to rest =>
    let route := cheapestRoute costs (routes keypad from to)
    rewrite costFromAppend costs Activate (routeKeys route) (drivingKeys keypad costs to rest),
      lastFromAppendOne Activate (route.map Arrow) Activate,
      drivingKeysCost keypad costs to rest,
      <- sequenceCostFrom costs (routeKeys route)
      in rfl

-- Tabulating changes no cost.
theorem tabulateSame (costs: Costs): (from: DirectionKey) → (to: DirectionKey) → tabulate costs from to = costs from to
  | Arrow Up, Arrow Up => rfl
  | Arrow Up, Arrow Down => rfl
  | Arrow Up, Arrow Left => rfl
  | Arrow Up, Arrow Right => rfl
  | Arrow Up, Activate => rfl
  | Arrow Down, Arrow Up => rfl
  | Arrow Down, Arrow Down => rfl
  | Arrow Down, Arrow Left => rfl
  | Arrow Down, Arrow Right => rfl
  | Arrow Down, Activate => rfl
  | Arrow Left, Arrow Up => rfl
  | Arrow Left, Arrow Down => rfl
  | Arrow Left, Arrow Left => rfl
  | Arrow Left, Arrow Right => rfl
  | Arrow Left, Activate => rfl
  | Arrow Right, Arrow Up => rfl
  | Arrow Right, Arrow Down => rfl
  | Arrow Right, Arrow Left => rfl
  | Arrow Right, Arrow Right => rfl
  | Arrow Right, Activate => rfl
  | Activate, Arrow Up => rfl
  | Activate, Arrow Down => rfl
  | Activate, Arrow Left => rfl
  | Activate, Arrow Right => rfl
  | Activate, Activate => rfl

-- The program's next costs are the cheapest routes on a directional keypad.
theorem nextCostsCheapest (costs: Costs) (from: DirectionKey) (to: DirectionKey):
    nextCosts costs from to = cheapestBetween directionalKeypad costs from to :=
  tabulateSame (from to => cheapestCost costs (routes directionalKeypad from to)) from to

theorem yourPressesLength: (level: Nat) → (keys: List DirectionKey) → (yourPresses level keys).length = costFrom (robotCosts level) Activate keys
  | Zero, keys => Eq.sym (costFromOnes Activate keys)
  | Succ level, keys =>
    rewrite yourPressesLength level (drivingKeys directionalKeypad (robotCosts level) Activate keys),
      drivingKeysCost directionalKeypad (robotCosts level) Activate keys,
      Nat.iterateSuccLast nextCosts level yourCosts
      in
    costFromCong (cheapestBetween directionalKeypad (robotCosts level)) (nextCosts (robotCosts level))
      (from to => Eq.sym (nextCostsCheapest (robotCosts level) from to)) Activate keys

-- As many presses as the program's length.
theorem pressesForLength (robots: Nat) (code: Code): (pressesFor robots code).length = shortestLength (robotCosts robots) code :=
  rewrite yourPressesLength robots (drivingKeys numericKeypad (robotCosts robots) Enter code),
    drivingKeysCost numericKeypad (robotCosts robots) Enter code
    in Eq.sym (sumByPairs (cheapestBetween numericKeypad (robotCosts robots)) Enter code)
