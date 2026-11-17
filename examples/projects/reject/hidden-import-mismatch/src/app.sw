-- The file's own `closerAhead` wins over the one `Lib` brings, and the
-- mismatch says which hid which.
namespace App
import Lib (..)

def closerAhead (xs: List Nat): Bool := xs.isEmpty

def next (n: Nat): Nat := closerAhead n
