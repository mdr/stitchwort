--| The real puzzle input (aoc/inputs/2020/day21.txt, committed), through
--| `include`: the answers are checked on it when the tests run, and editing
--| the input reruns exactly these tests.
namespace Aoc.Year2020.Day21.Tests
import Aoc.Year2020.Day21 (..)
import Std (List, Option, Result, Text)

def input: Text := include "../../../../../inputs/2020/day21.txt"

test "real input, 40 foods" := (parsed input).map (list => list.foods.length) == Ok 40
test "real input, part 1" := (parsed input).map (.safeAppearances) == Ok 2380
test "real input, part 2" :=
  (parsed input).map (.dangerousList) == Ok (Some "ktpbgdn,pnpfjb,ndfb,rdhljms,xzfj,bfgcms,fkcmf,hdqkqhh")
