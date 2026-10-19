-- Imports from N, which uses no name of this namespace.
namespace Aoc

import N (Aoc)

def y (a: Aoc): Nat := 2

test "y" := y N.x == 2
