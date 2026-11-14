--| The spec's error rate and departure product, run directly.

namespace Aoc.Year2020.Day16.Tests
import Aoc.Year2020.Day16 (..)
import Aoc.Year2020.Day16 (Spec)
import Std (List, Option, Result)

test "the spec's error rate on the example" := (parsed example).map Spec.errorRate == Ok 71
test "the spec's error rate on the input" := (parsed input).map Spec.errorRate == Ok 21071

test "the spec's departure product on the input's order" :=
  (parsed input).map (notes => notes.fieldOrder.map (order => Spec.departureProduct order notes.yours.values))
    == Ok (Some 3429967441937)
