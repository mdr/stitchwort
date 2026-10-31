-- expect-error: E-PARSE
-- There's no `import M as A`: the note gives the item form,
-- `import Std (List as L)`, or `import Std (List)` to write `List.x`.
import Std.List as L

def x: Nat := 0
