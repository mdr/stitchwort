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
  | Cons to rest => List.append (routeKeys (costs.cheapestRoute (keypad.routes from to))) (drivingKeys keypad costs to rest)

-- Your presses for the keypad `level` keypads from yours to press `keys`.
def yourPresses: (level: Nat) → List DirectionKey → List DirectionKey
  | Zero, keys => keys
  | Succ level, keys => yourPresses level (drivingKeys Keypad.directional (robotCosts level) Activate keys)

-- Your presses for the door's robot to type `code`, with `robots` robots on
-- directional keypads.
def pressesFor (robots: Nat) (code: Code): List DirectionKey := yourPresses robots (drivingKeys Keypad.numeric (robotCosts robots) Enter code)

-- The cost of the cheapest route between two keys, then A.
def cheapestBetween (keypad: Keypad k) (costs: Costs) (from: k) (to: k): Nat := costs.cheapestCost (keypad.routes from to)

theorem sequenceCostFrom (costs: Costs) (keys: List DirectionKey): costs.sequenceCost keys = costFrom costs Activate keys := sumByPairs costs Activate keys

-- Each route's keys end with A, so the next route starts from it.
theorem drivingKeysCost (keypad: Keypad k) (costs: Costs): (from: k) → (keys: List k) →
    costFrom costs Activate (drivingKeys keypad costs from keys) = costFrom (cheapestBetween keypad costs) from keys
  | from, Nil => rfl
  | from, Cons to rest =>
    let route := costs.cheapestRoute (keypad.routes from to)
    rewrite costFromAppend costs Activate (routeKeys route) (drivingKeys keypad costs to rest),
      lastFromAppendOne Activate (route.map Arrow) Activate,
      drivingKeysCost keypad costs to rest,
      <- sequenceCostFrom costs (routeKeys route)
      in rfl

-- Tabulating changes no cost.
theorem tabulateSame (costs: Costs): (from: DirectionKey) → (to: DirectionKey) → costs.tabulate from to = costs from to :=
  cases

-- The program's next costs are the cheapest routes on a directional keypad.
theorem nextCostsCheapest (costs: Costs) (from: DirectionKey) (to: DirectionKey):
    costs.next from to = cheapestBetween Keypad.directional costs from to :=
  tabulateSame (from to => costs.cheapestCost (Keypad.directional.routes from to)) from to

theorem yourPressesLength: (level: Nat) → (keys: List DirectionKey) → (yourPresses level keys).length = costFrom (robotCosts level) Activate keys
  | Zero, keys => Eq.sym (costFromOnes Activate keys)
  | Succ level, keys =>
    rewrite yourPressesLength level (drivingKeys Keypad.directional (robotCosts level) Activate keys),
      drivingKeysCost Keypad.directional (robotCosts level) Activate keys,
      Nat.iterateSuccLast Costs.next level Costs.yours
      in
    costFromCong (cheapestBetween Keypad.directional (robotCosts level)) ((robotCosts level).next)
      (from to => Eq.sym (nextCostsCheapest (robotCosts level) from to)) Activate keys

-- As many presses as the program's length.
theorem pressesForLength (robots: Nat) (code: Code): (pressesFor robots code).length = (robotCosts robots).shortestLength code :=
  rewrite yourPressesLength robots (drivingKeys Keypad.numeric (robotCosts robots) Enter code),
    drivingKeysCost Keypad.numeric (robotCosts robots) Enter code
    in Eq.sym (sumByPairs (cheapestBetween Keypad.numeric (robotCosts robots)) Enter code)
