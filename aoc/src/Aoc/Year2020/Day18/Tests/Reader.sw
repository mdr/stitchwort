--| The uniqueness proof's reader (`Proofs.readLevel`) gives the parser's
--| tree for every example line and every line of the input.

namespace Aoc.Year2020.Day18.Tests
import Aoc.Year2020.Day18 (..)
import Aoc.Year2020.Day18.Proofs (readLevel)
import Std (List, Option, Result, Text)

def readerAgrees (input: Text) (precedence: Precedence): Bool :=
  match parsed input precedence with
    | Ok homework =>
      List.zip (input.lines.map Text.toList) homework.expressions |> .all (pair =>
        readLevel precedence.levels (pair.fst.length + 1) precedence.levels pair.fst == Some (pair.snd, []))
    | Err message => False

test "the reader agrees with the parser on the examples" := readerAgrees examples samePrecedence && readerAgrees examples additionFirst
test "the reader agrees with the parser on the input" := readerAgrees input samePrecedence && readerAgrees input additionFirst
