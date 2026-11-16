--| The disturber over the goldens' formatted texts, 50 seeds each. These
--| tests check the disturber itself, that it changes layout and nothing
--| else; `Parsing.sw` runs the test that matters, that each disturbed text
--| formats back to the golden.

namespace Toy.Fmt.Tests
import Toy.Syntax (..)
import Std (List, Option, Text)

def goldens: List Golden := [groups, headers, bodies, calls, lists, operators, conditionals, comments, blankLines,
  longText, order, route, parameterGroups]

def seeds: List Nat := List.range 0 50

def Golden.disturbed (golden: Golden) (seed: Nat): Text := disturb golden.formatted seed

--| Whether every disturbed text formats back to the golden: idempotence and
--| independence from the author's layout, on real shapes.
def Golden.survivesDisturbance (golden: Golden) (format: Text → Option Text): Bool :=
  seeds.all (seed => format (golden.disturbed seed) == Some golden.formatted)

test "the disturber keeps every token" :=
  goldens.all (golden => seeds.all (seed => significant (golden.disturbed seed) == significant golden.formatted))

test "the disturber changes every golden's layout" :=
  goldens.all (golden => seeds.any (seed => golden.disturbed seed != golden.formatted))

test "most seeds change the layout" :=
  goldens.all (golden => seeds.count (seed => golden.disturbed seed != golden.formatted) >= 40)

test "the same seed disturbs the same way" := goldens.all (golden => golden.disturbed 7 == golden.disturbed 7)
