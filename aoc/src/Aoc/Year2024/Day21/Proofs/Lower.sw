-- Optimality, reduced to one fact per keypad and level: if every walk of an
-- arm between two keys costs at least the program's cheapest route between
-- them (`CheapestWalks`), then no presses typing a code are shorter than the
-- program's length (`optimalIfCheapestWalks`). Any presses on a keypad are
-- walks, each ended by an A, so they cost at least the cheapest routes
-- between the keys they press (`walksCost`); down the chain, that bounds
-- each keypad's cost by the one before it, out to your presses.

namespace Aoc.Year2024.Day21.Proofs
import Aoc.Year2024.Day21 (..)
import Aoc.Year2024.Day21.Spec (..)
import Std (Eq, List, Nat, Option, Void)

-- Every walk of an arm on `keypad` from a key to a key, typed with
-- `costs`, costs at least the program's cheapest route between the keys.
def CheapestWalks (keypad: Keypad k) (rows: List (List (Option k))) (costs: Costs): Prop :=
  (start: Position) → (from: k) → keyAt rows start = Some from → (route: List Direction) → (end: Position) →
    walk rows start route = Some end → (to: k) → keyAt rows end = Some to → cheapestBetween keypad costs from to ≤ routeCost costs route

-- A walk, then more of it.
theorem walkAppend (rows: List (List (Option k))): (aim: Position) → (route: List Direction) → (more: List Direction) →
    walk rows aim (List.append route more) = walk rows aim route |> .flatMap (end => walk rows end more)
  | aim, Nil, more => rfl
  | aim, Cons direction others, more =>
    match step: moved aim direction with
      | None => rfl
      | Some next =>
        match found: keyAt rows next with
          | None => rfl
          | Some key => walkAppend rows next others more

-- The keys a robot presses cost, by the cheapest routes between them, at
-- most what its driving keys cost, those keys following a walk `route`
-- from a key `from` to the arm's `aim`.
theorem walksCost (keypad: Keypad k) (rows: List (List (Option k))) (costs: Costs) (cheapest: CheapestWalks keypad rows costs):
    (keys: List DirectionKey) → (start: Position) → (from: k) → keyAt rows start = Some from → (route: List Direction) → (aim: Position) →
      walk rows start route = Some aim → (pressed: List k) → operate rows aim keys = Some pressed →
      costFrom (cheapestBetween keypad costs) from pressed ≤ costFrom costs Activate (List.append (route.map Arrow) keys)
  | Nil, start, from, onFrom, route, aim, walked, pressed, operated => rewrite <- Option.someInjective Nil pressed operated in omega
  | Cons Activate rest, start, from, onFrom, route, aim, walked, pressed, operated =>
    match found: keyAt rows aim with
      | None => Void.exfalso (Option.noneNotSome pressed operated)
      | Some to =>
        match later: operate rows aim rest with
          | None => Void.exfalso (Option.noneNotSome pressed operated)
          | Some laterKeys =>
            let bound := walksCost keypad rows costs cheapest rest aim to found Nil aim rfl laterKeys later
            let routeBound := cheapest start from onFrom route aim walked to found
            rewrite <- Option.someInjective (Cons to laterKeys) pressed operated,
              <- List.appendAssoc (route.map Arrow) [Activate] rest,
              costFromAppend costs Activate (routeKeys route) rest,
              lastFromAppendOne Activate (route.map Arrow) Activate,
              <- sequenceCostFrom costs (routeKeys route)
              in omega [bound, routeBound]
  | Cons (Arrow direction) rest, start, from, onFrom, route, aim, walked, pressed, operated =>
    match step: moved aim direction with
      | None => Void.exfalso (Option.noneNotSome pressed operated)
      | Some next =>
        match found: keyAt rows next with
          | None => Void.exfalso (Option.noneNotSome pressed operated)
          | Some key =>
            let walkedOn: walk rows start (List.append route [direction]) = Some next :=
              rewrite walkAppend rows start route [direction], walked, step, found in rfl
            let shape: List.append ((List.append route [direction]).map Arrow) rest = List.append (route.map Arrow) (Cons (Arrow direction) rest) :=
              rewrite List.mapAppend route [direction] Arrow, List.appendAssoc (route.map Arrow) [Arrow direction] rest in rfl
            rewrite <- shape in walksCost keypad rows costs cheapest rest start from onFrom (List.append route [direction]) next walkedOn pressed operated

-- Your presses cost at least what the keys they make the robot `level`
-- keypads away press cost, with the walk fact at each level before.
theorem throughRobotsCost:
    (level: Nat) → (walks: (below: Nat) → below < level → CheapestWalks directionalKeypad directionalRows (robotCosts below)) →
      (presses: List DirectionKey) → (keys: List DirectionKey) → throughRobots level presses = Some keys →
      costFrom (robotCosts level) Activate keys ≤ presses.length
  | Zero, walks, presses, keys, through => rewrite <- Option.someInjective presses keys through, costFromOnes Activate presses in omega
  | Succ level, walks, presses, keys, through =>
    let via := rewrite throughRobotsLast level presses at through in through
    match before: throughRobots level presses with
      | None => Void.exfalso (Option.noneNotSome keys via)
      | Some driving =>
        let operated: operate directionalRows directionalStart driving = Some keys := via
        let pressedBound :=
          walksCost directionalKeypad directionalRows (robotCosts level) (walks level (omega)) driving directionalStart Activate rfl Nil directionalStart rfl keys
            operated
        let drivingBound := throughRobotsCost level (below lower => walks below (omega [lower])) presses driving before
        let same :=
          costFromCong (nextCosts (robotCosts level)) (cheapestBetween directionalKeypad (robotCosts level)) (nextCostsCheapest (robotCosts level))
            Activate keys
        rewrite Nat.iterateSuccLast nextCosts level yourCosts in omega [pressedBound, drivingBound, same]

-- With the walk fact on each directional keypad between you and the door,
-- and on the numeric one, the program's length is the least.
theorem optimalIfCheapestWalks (robots: Nat) (walks: (level: Nat) → level < robots → CheapestWalks directionalKeypad directionalRows (robotCosts level))
    (numericWalks: CheapestWalks numericKeypad numericRows (robotCosts robots)): Optimal robots :=
  code presses types =>
    let typedVia: (throughRobots robots presses |> .flatMap (operate numericRows numericStart)) = Some code := rewrite <- typedThrough robots presses in types
    match before: throughRobots robots presses with
      | None => Void.exfalso (Option.noneNotSome code typedVia)
      | Some driving =>
        let pressedBound := walksCost numericKeypad numericRows (robotCosts robots) numericWalks driving numericStart Enter rfl Nil numericStart rfl code typedVia
        let drivingBound := throughRobotsCost robots walks presses driving before
        let same: shortestLength (robotCosts robots) code = costFrom (cheapestBetween numericKeypad (robotCosts robots)) Enter code :=
          sumByPairs (cheapestBetween numericKeypad (robotCosts robots)) Enter code
        omega [same, pressedBound, drivingBound]
