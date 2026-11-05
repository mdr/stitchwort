--| The parser reads exactly the puzzle's format: if `parseMap` reads `input`
--| as `map`, each line of the input is its row of the map written with `.`
--| for an open square and `#` for a tree, nothing dropped, added or changed.
--| With the answers proved for every rectangle (Proofs.sw), the answers for
--| a parsed input are the puzzle's.

namespace Aoc.Year2020.Day03.Proofs
import Aoc.Common (Grid, checkGrid, parseGrid)
import Aoc.Common.Proofs (checkGridRows, isRectangleIff, parseGridRectangle)
import Aoc.Year2020.Day03 (..)
import Aoc.Year2020.Day03.Spec (..)
import Std (DecEq, Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Text, Void)

--| How the puzzle writes a square.
def symbol: Square → Char
  | Open => '.'
  | Tree => '#'

--| A character the parser accepts is the symbol of the square it makes.
theorem symbolOfChar (char: Char) (allowed: isSquare char = True): symbol (Square.ofChar char) = char :=
  match tree: char == '#' with
    | True => Eq.sym (DecEq.sound tree)
    | False =>
      match open: char == '.' with
        | True => Eq.sym (DecEq.sound open)
        | False => cases

theorem readsSquare: Parse.Reads square (read square => read = [symbol square]) :=
  Parse.readsWeaken [p := square]
    (Parse.readsMap (() => Parse.satisfy "'.' or '#'" isSquare) Square.ofChar _ (Parse.readsSatisfy))
    (read square h =>
      match h with
        | Witness char (Both (Both one allowed) made) => rewrite made, one, symbolOfChar char allowed in rfl)

--| Squares read one after another are the row written out.
theorem eachSquare: (read: List Char) → (row: List Square) → Parse.Each (read square => read = [symbol square]) read row → read = row.map symbol
  | read, [], each => each
  | read, [square, ..rest], Witness first (Witness after (Both split (Both one more))) =>
    rewrite split, one, eachSquare after rest more in rfl

--| A row read as a `NonEmptyList` of squares is its squares written out.
theorem rowWritten (read: List Char) (row: List Square)
    (each: ∃ (squares: NonEmptyList Square) => Parse.Each (read square => read = [symbol square]) read squares.toList ∧ row = squares.toList): read = row.map symbol :=
  match each with
    | Witness squares (Both written same) => rewrite same in eachSquare read squares.toList written

--| Every line of the input is its row of the map written out.
theorem parseWritten (input: Text) (map: Grid Square) (parsed: Fail.toResult (() => parseMap input) = Ok map):
    List.All2 (line row => line = row.map symbol) (input.lines.map Text.toList) map.rows :=
  let split := rewrite Fail.toResultThen (() => Parse.eachLine input (() => Parse.many1 square |> .toList)) checkGrid at parsed
  Result.flatMapEqOk _ (rows => Fail.toResult (() => checkGrid rows)) map split (rows read checked =>
    rewrite <- checkGridRows rows map checked in
      List.all2Weaken rowWritten _ _
        (Parse.eachLineReads input (() => Parse.many1 square |> .toList) _ rows read
          (Parse.readsMap (() => Parse.many1 square) NonEmptyList.toList _ (Parse.readsMany1 square _ readsSquare))))

--| On any input the parser reads, both answers are the puzzle's.
theorem answersCorrect (input: Text) (map: Grid Square) (parsed: Fail.toResult (() => parseMap input) = Ok map):
    solvePart1 map = part1Answer map ∧ solvePart2 map = part2Answer map :=
  let rectangle := (isRectangleIff map).backward (And.left (parseGridRectangle input square map parsed))
  Both (part1Correct map rectangle) (part2Correct map rectangle)
