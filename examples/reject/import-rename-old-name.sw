-- expect-error: E-UNKNOWN-NAME
-- `import M (x as y)` brings `y`, not `x`: the note says what `length` is
-- called in this file.
import Std.List (length as count)

def x: Nat := length [1, 2]
