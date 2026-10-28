-- The type, with a function of its own.
namespace P

type Grid = { width: Nat }

def Area: Type := Grid

def Grid.size (grid: Grid): Nat := grid.width
