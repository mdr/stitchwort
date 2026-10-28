-- Imports only P.Proofs, so doesn't see P.Spec's functions by dot notation
-- (imports aren't passed on), but can write their full names.
namespace P.Tests

import P (Grid)
import P.Proofs (..)

def small: Grid := { width = 1 }

test "full name" := P.Spec.Grid.probe small == 2
test "own of P.Proofs" := small.twice == 20
