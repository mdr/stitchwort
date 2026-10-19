-- expect-error: E-TYPE-MISMATCH
-- Literals belong to the library's `Int`: a user's own type called `Int` takes none.
type Int: Type =
  | MkInt

def r: Int := 5
