-- expect-error: E-TYPE-MISMATCH
-- The match has no type to read its number patterns at when it is checked,
-- so they are read as `Nat`s, and the error says so.
def m (x: Int): Nat :=
  let f := match | 1 => 1 | _ => 0
  f x
