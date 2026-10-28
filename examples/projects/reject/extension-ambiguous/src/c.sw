namespace C

import P (Grid)
import A (..)
import B (..)

def full (grid: Grid): Nat := A.Grid.probe grid

def dot (grid: Grid): Nat := grid.probe

def qualified (grid: Grid): Nat := Grid.probe grid
