-- The type.
namespace P

type Grid = { width: Nat }

def use (grid: Grid): Nat := grid.probe
