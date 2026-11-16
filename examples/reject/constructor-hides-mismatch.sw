-- expect-error: E-TYPE-MISMATCH
-- A file's own `None` hides the prelude's, so `| None` in a match on an
-- `Option` is a `Cell`'s: the mismatch says the name is hidden and how to
-- write the `Option`'s (no W-CTOR-HIDES: the file never writes `Option.None`).
type Cell = | Wall | None

def get (o: Option Nat): Nat := match o with
  | Some n => n
  | None => 0
