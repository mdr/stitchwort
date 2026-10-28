-- Day 21's tests: the example from the puzzle, the spec's simulation, and
-- the program against a brute-force search for small numbers of robots.
-- Kept apart from the program, so `stitchwort run Aoc.Year2024.Day21.main`
-- doesn't check them.

namespace Aoc.Year2024.Day21.Tests
import Aoc.Year2024.Day21 (..)
import Aoc.Year2024.Day21.Spec (directionalRows, keyAt, moved, numericRows, numericStart, directionalStart, typed)
import Aoc.Year2024.Day21.Proofs (cheapestBetween, numericKeys, pressesFor, walk)
import Std (Fail, List, Nat, Option, Result, Set, Text)

def parsed (input: Text): Result (List Code) Text := Fail.toResult (() => parseCodes input)

-- A code from its characters, for writing tests.
def codeOf (characters: Text): Code :=
  characters.toList.map (character =>
    match character with
      | '0' => Digit0
      | '1' => Digit1
      | '2' => Digit2
      | '3' => Digit3
      | '4' => Digit4
      | '5' => Digit5
      | '6' => Digit6
      | '7' => Digit7
      | '8' => Digit8
      | '9' => Digit9
      | _ => Enter)

-- Directional key presses from the puzzle's characters.
def pressesOf (characters: Text): List DirectionKey :=
  characters.toList.map (character =>
    match character with
      | '^' => Arrow Up
      | 'v' => Arrow Down
      | '<' => Arrow Left
      | '>' => Arrow Right
      | _ => Activate)

def exampleCodes: List Code := ["029A", "980A", "179A", "456A", "379A"].map codeOf

def lengthFor (robots: Nat) (code: Text): Nat := (robotCosts robots).shortestLength (codeOf code)

test "example, part 1" := solvePart1 exampleCodes == 126384
test "example, part 2" := solvePart2 exampleCodes == 154115708116294

-- "68 * 29, 60 * 980, 68 * 179, 64 * 456, and 64 * 379".
test "example, the shortest lengths" := ["029A", "980A", "179A", "456A", "379A"].map (lengthFor 2) == [68, 60, 68, 64, 64]
test "example, the numeric parts" := exampleCodes.map Code.numericPart == [29, 980, 179, 456, 379]

-- "three shortest possible sequences ... <A^A>^^AvvvA, <A^A^>^AvvvA, and
-- <A^A^^>AvvvA", and the puzzle's sequences one and two keypads further out.
test "example, the puzzle's sequences type 029A" :=
  ["<A^A>^^AvvvA", "<A^A^>^AvvvA", "<A^A^^>AvvvA"].all (presses => typed 0 (pressesOf presses) == Some (codeOf "029A"))
    && typed 1 (pressesOf "v<<A>>^A<A>AvA<^AA>A<vAAA>^A") == Some (codeOf "029A")
    && typed 2 (pressesOf "<vA<AA>>^AvAA<^A>A<v<A>>^AvA^A<vA>^A<v<A>^A>AAvA^A<v<A>A>^AAAvA<^A>A") == Some (codeOf "029A")

test "example, the puzzle's sequence for 379A" :=
  typed 2 (pressesOf "<v<A>>^AvA^A<vA<AA>>^AAvA<^A>AAvA^A<vA>^AA<A>A<v<A>A>^AAAvA<^A>A") == Some (codeOf "379A")

test "the spec panics at a gap" := typed 0 (pressesOf "<<A") == None && typed 1 (pressesOf "<<A") == None
test "the spec panics off the keypad" := typed 0 (pressesOf ">A") == None && typed 0 (pressesOf "vA") == None

-- The program's own press sequence types each code and is as long as it says.
test "example, the program's sequences type the codes" :=
  exampleCodes.all (code => typed 2 (pressesFor 2 code) == Some code && (pressesFor 2 code).length == (robotCosts 2).shortestLength code)

test "more robots" := [0, 1, 3, 10].map (robots => lengthFor robots "029A") == [12, 28, 164, 94910]
test "an empty code needs no presses" := lengthFor 2 "" == 0 && Code.numericPart [] == 0
test "pressing A again and again" := lengthFor 25 "AAA" == 3
test "repeated digits" := lengthFor 2 "00A" == 29
test "the far corner" := lengthFor 2 "7A" == 52 && lengthFor 3 "70A" == 149
test "leading zeroes are ignored" := (codeOf "007A").numericPart == 7

-- 100 robots: far past 64 bits.
test "lengths beyond 64 bits" := lengthFor 100 "029A" == 39623698645360671878530501931953158941494

-- A brute-force search, independent of the program: every robot's arm and
-- how many of the code's keys the door has, after each of your presses.
type State = { aims: List Position, done: Nat }

-- The state after you press `key`, passed down the robots' arms (the last
-- arm on the numeric keypad); none if a robot panics or the door gets a
-- key that isn't the code's next.
def pushed (code: Code) (done: Nat): (aims: List Position) → (key: DirectionKey) → Option State
  | Nil, key => None
  | Cons aim Nil, Arrow direction =>
    moved aim direction |> .flatMap (next => keyAt numericRows next |> .map (found => { aims = [next], done }))
  | Cons aim Nil, Activate =>
    keyAt numericRows aim |> .flatMap (found => if code.get done == Some found then Some ({ aims = [aim], done = done + 1 }) else None)
  | Cons aim (Cons below others), Arrow direction =>
    moved aim direction |> .flatMap (next => keyAt directionalRows next |> .map (found => { aims = Cons next (Cons below others), done }))
  | Cons aim (Cons below others), Activate =>
    keyAt directionalRows aim |> .flatMap (found =>
      pushed code done (Cons below others) found |> .map (state => { state | aims = Cons aim state.aims }))

def stateKey (state: State): List Nat := Cons state.done (state.aims.flatMap (aim => [aim.row, aim.column]))

-- Breadth first: the number of presses after which some state has the
-- whole code, giving up after `fuel` presses.
def searchFrom (code: Code) (fuel: Nat) (presses: Nat) (frontier: List State) (seen: Set (List Nat)): Option Nat :=
  match fuel with
    | Zero => None
    | Succ fuel =>
      let reached := frontier.flatMap (state => directionKeys.filterMap (pushed code state.done state.aims))
      if reached.any (state => state.done == code.length) then
        Some (presses + 1)
      else
        let (fresh, seenNow) :=
          reached.foldLeft ([], seen) (((kept, seenSoFar)) state =>
            if seenSoFar.contains (stateKey state) then (kept, seenSoFar) else (Cons state kept, seenSoFar.insert (stateKey state)))
        searchFrom code fuel (presses + 1) fresh seenNow

def bruteForce (robots: Nat) (code: Code): Option Nat :=
  let start: State := { aims = List.append (List.replicate robots directionalStart) [numericStart], done = 0 }
  if code == [] then Some 0 else searchFrom code 200 0 [start] (Set.fromList [stateKey start])

test "brute force agrees on the example codes, up to two robots" :=
  [0, 1, 2].all (robots => exampleCodes.all (code => bruteForce robots code == Some ((robotCosts robots).shortestLength code)))

test "brute force agrees on short codes, up to three robots" :=
  [0, 1, 2, 3].all (robots =>
    ["A", "0A", "1A", "5A", "7A", "00A", "70A", "A7A"].all (code =>
      bruteForce robots (codeOf code) == Some (lengthFor robots code)))

-- Every list of at most `count` moves.
def moveLists: (count: Nat) → List (List Direction)
  | Zero => [Nil]
  | Succ count => Cons Nil ([Up, Down, Left, Right].flatMap (direction => moveLists count |> .map (Cons direction)))

-- The walk fact the optimality proof needs (`CheapestWalks`), for walks of
-- at most `count` moves: each costs at least the program's cheapest route
-- between the keys at its ends.
def cheapestWalksUpTo (keys: List k) (keypad: Keypad k) (rows: List (List (Option k))) (costs: Costs) (count: Nat): Bool :=
  keys.all (from =>
    moveLists count |> .all (route =>
      walk rows (keypad.place from) route
        |> .flatMap (keyAt rows)
        |> .all (to => cheapestBetween keypad costs from to <= costs.routeCost route)))

test "the walk fact for walks of up to six moves, one to three robots" :=
  [1, 2, 3].all (level =>
    cheapestWalksUpTo numericKeys Keypad.numeric numericRows (robotCosts level) 6
      && cheapestWalksUpTo directionKeys Keypad.directional directionalRows (robotCosts level) 6)

test "parse" := parsed "029A\n980A\n179A\n456A\n379A\n" == Ok exampleCodes
test "parse without a final line break" := parsed "029A\n1A" == Ok [codeOf "029A", codeOf "1A"]
test "a bad key" := parsed "02B9A\n" == Err "line 1, column 3: expected a key (0 to 9 or A) or the end of the line, got 'B'"
test "no codes" := parsed "" == Err "line 1, column 1: expected a key (0 to 9 or A), got the end of the input"
