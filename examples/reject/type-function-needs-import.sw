-- expect-error: E-UNKNOWN-NAME
-- `List.concat` exists but, `List` being a prelude type, its functions need
-- `import Std (List)` (D260). That hint wins over "no function `concat` in
-- `List`"; a name `List` really lacks is the latter, even without the
-- import. `IO.simulate` is the same: `IO.print`, an operation of the
-- ability, comes with `IO`; a function in its namespace doesn't.

def a: List Nat := List.concat [[1], [2]]
def b: Nat := List.lenght [1, 2, 3]
def c: Nat := (IO.simulate [] (() => IO.print "hi")).fst.length
