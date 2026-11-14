--| Advent of Code 2020, day 15: the elves' memory game. The players first
--| read out the starting numbers (the input, one line separated by commas),
--| one a turn. Then each turn considers the number spoken last: if that was
--| its first time, the player says 0; otherwise they say how many turns
--| apart it is from when it was spoken before. Part 1 is the 2020th number
--| spoken, part 2 the 30,000,000th.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day15.main < inputs/2020/day15.txt
--|
--| A number of turns after `--` replaces part 2's 30,000,000 (bench/compare
--| times it at 3,000,000).
--|
--| The game keeps an `Array`, by number, of the turn each number was last
--| spoken (before the latest turn), 0 for one not spoken yet, so a turn is a
--| read and a write, each O(1) and the write in place. The proofs,
--| that the parser reads the puzzle's format and that the game says what the
--| puzzle's rules say on every turn, are in `Aoc.Year2020.Day15.Proofs`
--| (Proofs/), and the tests in `Aoc.Year2020.Day15.Tests` (Tests/); `run`
--| checks neither.

namespace Aoc.Year2020.Day15
import Std (Array, Fail, IO, List, Nat, NonEmptyList, Parse)

def main(): {IO, Fail} () :=
  let turns := turnsFrom IO.args()
  let starting := parseStarting IO.readAll()
  IO.print "Part 1: ${starting.numberSpoken 2020}"
  IO.print "Part 2: ${starting.numberSpoken turns}"

def turnsFrom (args: List Text): {Fail} Nat :=
  let usage := "expected no arguments, or the number of turns for part 2"
  match args with
    | [] => 30000000
    | [turnsText] => Fail.need turnsText.toNat usage
    | _ => Fail.fail usage

type Starting = { numbers: NonEmptyList Nat }

def starting(): {Parse} Starting := { numbers = Parse.sepBy1 Parse.nat (() => Parse.char ',') }

def parseStarting (input: Text): {Fail} Starting := Parse.all input starting

--| The game after some turns: the turn just taken (from 1), the number
--| spoken on it, and by number, the latest earlier turn that spoke it, or 0
--| if none did. Turns count from 1, so 0 is never a turn.
type Game = { turn: Nat, last: Nat, lastSeen: Array Nat }

--| After the first turn, which says `first`, with room for the numbers below `room`.
def Game.begin (room first: Nat): Game := { turn = 1, last = first, lastSeen = Array.replicate (count := room) 0 }

def Game.say (game: Game) (number: Nat): Game :=
  { turn = game.turn + 1, last = number, lastSeen = game.lastSeen.set game.last game.turn }

--| What the rules say after the last number: 0 if it was new, else how
--| many turns ago it was spoken before.
def Game.reply (game: Game): Nat :=
  let before := game.lastSeen.getOr game.last 0
  if before == 0 then 0 else game.turn - before

--| What the next turn says: the next starting number while there is one,
--| then the rules' reply. `count` is the number of starting numbers; the
--| game loop passes it in, so a turn does not count the list again.
def Starting.nextAfter (starting: Starting) (count: Nat) (game: Game): Nat :=
  if game.turn < count then starting.numbers.toList.getOr game.turn 0 else game.reply

def Starting.next (starting: Starting) (game: Game): Nat := starting.nextAfter starting.numbers.length game

def Starting.takeTurn (starting: Starting) (game: Game): Game := game.say (starting.next game)

--| Room for every number spoken in the first `turns` turns: a reply is less
--| than the turn it's said on, and a starting number at most the largest.
def Starting.room (starting: Starting) (turns: Nat): Nat := turns + starting.numbers.toList.maximum.getOrElse 0 + 1

--| The number spoken on `turn`, counting from 1; 0 for turn 0.
def Starting.numberSpoken (starting: Starting) (turn: Nat): Nat := match turn with
  | Zero => 0
  | Succ later =>
    let count := starting.numbers.length
    Nat.iterate later
      (game => game.say (starting.nextAfter count game))
      (Game.begin (starting.room turn) starting.numbers.head)
      |> .last
