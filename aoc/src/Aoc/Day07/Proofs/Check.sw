-- Day 7, proved: the strict reader `main` uses gives the same manifold as
-- the total parser the other proofs are about, whenever it accepts. So
-- `part1Correct` and `part2Correct` describe what `main` prints. Kept apart
-- from the program, so `stitchwort run Aoc.Day07.main` doesn't check it.

namespace Aoc.Day07.Proofs
import Aoc.Day07 (..)
import Std (Eq, List, Option, Result, Text)

-- The accepted manifold, or a fallback for a rejection.
def acceptedOr (fallback: Option Manifold): Result Manifold Text -> Option Manifold
  | Ok manifold => Some manifold
  | Err message => fallback

theorem acceptedOrCheck (lines: List Text): acceptedOr (parseManifold lines) (checkManifold lines) = parseManifold lines :=
  match manifoldError lines with
    | Some message => rfl
    | None =>
      match parseManifold lines with
        | Some manifold => rfl
        | None => rfl

-- Whenever `checkManifold` accepts, `parseManifold lines` is `Some` of what it gives.
theorem checkManifoldParses (lines: List Text) (manifold: Manifold) (accepted: checkManifold lines = Ok manifold):
    parseManifold lines = Some manifold :=
  Eq.trans (Eq.sym (acceptedOrCheck lines)) (Eq.cong (acceptedOr (parseManifold lines)) accepted)
