-- Adds `Grid.probe` to P's type.
namespace P.Spec

import P (Grid)

def Grid.probe (grid: Grid): Nat := grid.width + 1

def sample: Grid := { width = 3 }
