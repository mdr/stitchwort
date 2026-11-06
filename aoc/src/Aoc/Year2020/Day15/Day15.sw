--| Advent of Code 2020, day 15: the elves' memory game. The players first
--| read out the starting numbers (the input, one line separated by commas),
--| one a turn. Then each turn considers the number spoken last: if that was
--| its first time, the player says 0; otherwise they say how many turns
--| apart it is from when it was spoken before. Part 1 is the 2020th number
--| spoken, part 2 the 30,000,000th.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day15.main < inputs/2020/day15.txt
--|
--| The game keeps a `Map` from each number to the turn it was last spoken
--| (before the latest turn), so a turn is a lookup and an insert. The proofs,
--| that the parser reads the puzzle's format and that the game says what the
--| puzzle's rules say on every turn, are in `Aoc.Year2020.Day15.Proofs`
--| (Proofs/), and the tests in `Aoc.Year2020.Day15.Tests` (Tests/); `run`
--| checks neither.

namespace Aoc.Year2020.Day15
import Std (Fail, IO, List, Map, Nat, NonEmptyList, Parse)

def main(): {IO, Fail} () :=
  let starting := parseStarting IO.readAll()
  IO.print "Part 1: ${starting.numberSpoken 2020}"
  IO.print "Part 2: ${starting.numberSpoken 30000000}"

type Starting = { numbers: NonEmptyList Nat }

def starting(): {Parse} Starting := { numbers = Parse.sepBy1 Parse.nat (() => Parse.char ',') }

def parseStarting (input: Text): {Fail} Starting := Parse.all input starting

--| The game after some turns: the turn just taken (from 1), the number
--| spoken on it, and for every number spoken on an earlier turn, the latest
--| such turn.
type Game = { turn: Nat, last: Nat, lastSeen: Map Nat Nat }

--| After the first turn, which says `first`.
def Game.begin (first: Nat): Game := { turn = 1, last = first, lastSeen = Map.empty }

def Game.say (game: Game) (number: Nat): Game :=
  { turn = game.turn + 1, last = number, lastSeen = game.lastSeen.insert game.last game.turn }

--| What the rules say after the last number: 0 if it was new, else how
--| many turns ago it was spoken before.
def Game.reply (game: Game): Nat :=
  match game.lastSeen.get game.last with
    | Some before => game.turn - before
    | None => 0

--| What the next turn says: the next starting number while there is one,
--| then the rules' reply.
def Starting.next (starting: Starting) (game: Game): Nat :=
  if game.turn < starting.numbers.length then starting.numbers.toList.getOr game.turn 0 else game.reply

def Starting.takeTurn (starting: Starting) (game: Game): Game := game.say (starting.next game)

--| The number spoken on `turn`, counting from 1; 0 for turn 0.
def Starting.numberSpoken (starting: Starting) (turn: Nat): Nat :=
  match turn with
    | Zero => 0
    | Succ later => Nat.iterate later starting.takeTurn (Game.begin starting.numbers.head) |> .last
