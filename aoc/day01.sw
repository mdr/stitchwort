-- Advent of Code 2025, day 1: a dial numbered 0 to 99 starts at 50 and is
-- turned left or right. Part 1 counts the turns that end on 0; part 2 counts
-- every click that passes 0.
--
--   $ stitchwort run aoc/day01.sw < aoc/inputs/day01.txt
--
-- The puzzle input is not in git (aoc/inputs/ is ignored).

type Turn =
  | Left (clicks : Nat)
  | Right (clicks : Nat)

-- "L68" is `Left 68`.
parseTurn : Text -> Maybe Turn
parseTurn t =
  match Text.uncons t with
    | Nothing           -> Nothing
    | Just (c, rest)    -> turnOf c (Text.toNat rest)

turnOf : Char -> Maybe Nat -> Maybe Turn
turnOf c Nothing  = Nothing
turnOf c (Just n) = if c == 'L' then Just (Left n) else if c == 'R' then Just (Right n) else Nothing

-- A turn as a signed distance: left is negative.
signed : Turn -> Int
signed (Left n)  = -(Nat.toInt n)
signed (Right n) = Nat.toInt n

-- Where the dial is after a turn (always on 0 to 99), and how many times
-- it clicked onto 0 during it. Going right, 0 is passed each time the
-- position reaches a multiple of 100, which counts landing on it; going left
-- is the same on the mirror image, where 0 sits at 100 - pos.
turn : (Nat, Nat) -> Turn -> (Nat, Nat)
turn (pos, passes) t =
  let to = Int.modNat (Nat.toInt pos + signed t) 100
  let from = match t with
    | Right n -> pos + n
    | Left n  -> (100 - pos) % 100 + n
  (to, passes + from / 100)

-- The state is (position, zeros landed on, zeros passed).
step : (Nat, Nat, Nat) -> Turn -> (Nat, Nat, Nat)
step (pos, landed, passes) t = settle (turn (pos, passes) t) landed

settle : (Nat, Nat) -> Nat -> (Nat, Nat, Nat)
settle (pos, passes) landed = (pos, if pos == 0 then landed + 1 else landed, passes)

solve : List Text -> (Nat, Nat)
solve lines =
  final (List.foldl step (50, 0, 0) (lines.mapMaybe parseTurn))

final : (Nat, Nat, Nat) -> (Nat, Nat)
final (pos, landed, passes) = (landed, passes)

main : () -> {IO, Partial} ()
main u = report (solve (IO.readAllLines ()))

report : (Nat, Nat) -> {IO} ()
report (a, b) =
  print ("Part 1: " ++ Nat.toText a)
  print ("Part 2: " ++ Nat.toText b)

example : List Text
example = ["L68", "L30", "R48", "L5", "R60", "L55", "L1", "L99", "R14", "L82"]

test "example" = solve example == (3, 6)
test "parse" = Maybe.map signed (parseTurn "L68") == Just (-68)
test "parse right" = Maybe.map signed (parseTurn "R5") == Just 5
test "parse junk" = Maybe.map signed (parseTurn "X5") == Nothing
test "left past zero" = turn (10, 0) (Left 40) == (70, 1)
test "left onto zero" = turn (20, 0) (Left 20) == (0, 1)
test "right onto zero" = turn (0, 0) (Right 100) == (0, 1)
test "left from zero" = turn (0, 0) (Left 42) == (58, 0)
test "left a full turn from zero" = turn (0, 0) (Left 200) == (0, 2)
test "negative mod" = Int.modNat (-18) 100 == 82

theorem exampleAnswer : solve example = (3, 6)
exampleAnswer = rfl
