--| Day 4's specification (Spec/Spec.sw) on the puzzle's examples and the
--| real input.

namespace Aoc.Year2020.Day04.Tests
import Aoc.Year2020.Day04 (Passport)
import Aoc.Year2020.Day04.Spec (..)
import Std (List, Result, Text)

def specAnswers (passports: Result (List Passport) Text): Result (Nat, Nat) Text :=
  passports.map (all => (part1Answer all, part2Answer all))

test "example, the spec" := specAnswers (parsed example) == Ok (2, 2)
test "part 2's examples, the spec" :=
  (specAnswers (parsed invalidExample), specAnswers (parsed validExample)) == (Ok (4, 0), Ok (4, 4))
test "real input, the spec" := specAnswers inputPassports == Ok (200, 116)
