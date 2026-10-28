-- `Std.Parse`: parsers are direct-style code with the `Parse` ability. A
-- runner gives them the input and turns a failure into a `Fail` that names
-- the line and column.
import Std (Fail, Int, List, Nat, Parse, Result, Text)
import Std.Fail (toResult)
import Std.Parse (char, int, label, lines, many1, nat, oneOf, optional, pick, recursive, sepBy, text)

-- "162,817,812": one box per line, read with `Parse.eachLine`.
type Point = { x: Nat, y: Nat, z: Nat }

def point(): {Parse} Point :=
  let x := nat()
  char ','
  let y := nat()
  char ','
  let z := nat()
  { x, y, z }

def parsePoints (input: Text): {Fail} (List Point) := Parse.eachLine input point

test "points" := toResult (() => parsePoints "162,817,812\n57,618,57\n") ==
  Ok [{ x = 162, y = 817, z = 812 }, { x = 57, y = 618, z = 57 }]
test "a bad point" := toResult (() => parsePoints "162,817,812\n57,6x8,57\n") == Err "line 2, column 5: expected ','"

-- "L68": a keyword table, then a number.
type Turn =
  | Left (distance: Nat)
  | Right (distance: Nat)

def turn(): {Parse} Turn :=
  let direction := label "a turn like L68" (() => pick [("L", Left), ("R", Right)])
  direction (nat())

test "turns" := toResult (() => Parse.eachLine "L68\nR5" turn) == Ok [Left 68, Right 5]
test "a bad turn" := toResult (() => Parse.eachLine "L68\nX5" turn) == Err "line 2, column 1: expected a turn like L68"

-- "p=0,4 v=3,-3": literal text and signed numbers.
type Robot = { px: Int, py: Int, vx: Int, vy: Int }

def robot(): {Parse} Robot :=
  text "p="
  let px := int()
  char ','
  let py := int()
  text " v="
  let vx := int()
  char ','
  let vy := int()
  { px, py, vx, vy }

test "robot" := toResult (() => Parse.line "p=0,4 v=3,-3" robot) == Ok ({ px = 0, py = 4, vx = 3, vy = -3 }: Robot)
test "a bad robot" := toResult (() => Parse.line "p=0,4 w=3,-3" robot) == Err "column 6: expected ' v='"

-- A grid of cells; the error names the furthest point and all that was
-- expected there.
type Cell = | Roll | Floor

def cells(): {Parse} (List (List Cell)) := Parse.grid (() => pick [("@", Roll), (".", Floor)])

test "grid" := toResult (() => Parse.all "@.\n.@\n" cells) == Ok [[Roll, Floor], [Floor, Roll]]
test "a bad grid" := toResult (() => Parse.all "@.\n.x\n" cells) ==
  Err "line 2, column 2: expected '@' or '.' or a line break or the end"

-- Choice backs up: "move 3" and "mark" share their first letters.
type Command =
  | Move (steps: Nat)
  | Mark

def command(): {Parse} Command :=
  oneOf [
    () =>
      text "move "
      Move (nat()),
    () =>
      text "mark"
      Mark
  ]

test "commands" := toResult (() => Parse.eachLine "move 3\nmark" command) == Ok [Move 3, Mark]
test "a bad command" := toResult (() => Parse.line "mov 3" command) == Err "column 1: expected 'move ' or 'mark'"

-- Nested input with `recursive`: "[1,[2,3],[]]", the depth of the deepest list.
def depth(): {Parse} Nat :=
  recursive (nested =>
    oneOf [
      () =>
        let number := nat()
        0,
      () =>
        char '['
        let depths := sepBy nested (() => char ',')
        char ']'
        depths.foldLeft 0 Nat.max + 1
    ])

test "depth" := toResult (() => Parse.line "[1,[2,[3]],[]]" depth) == Ok 3
test "a bad nesting" := toResult (() => Parse.line "[1,[2,3]" depth) == Err "column 9: expected ',' or ']'"

-- An optional sign, then digits, one at a time.
def signedDigits(): {Parse} (Bool, List Nat) :=
  let minus := optional (() => char '-')
  (minus.isSome, many1 (() => Parse.digit().toNat))

test "digits" := toResult (() => Parse.line "-307" signedDigits) == Ok (True, [3, 0, 7])
