-- expect-error: E-PARSE
-- There's no `import M as A`: the note says to import the namespace by
-- its own last name, `import Std (List)`, and that `L` can't stand for it.
import Std.List as L

def x: Nat := 0
