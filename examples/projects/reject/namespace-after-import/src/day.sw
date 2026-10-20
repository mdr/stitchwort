-- Uses Lib's type by import, by dot notation, and written in full.
import Lib (Range)
namespace Day

def width (r: Range): Nat := r.size

def parsed: Range := Range.parse 4

def qualified (r: Lib.Range): Nat := Lib.Range.size r

test "width" := width parsed == 4
test "qualified" := qualified parsed == 4
