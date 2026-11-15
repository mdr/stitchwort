-- expect-error: E-TYPE-MISMATCH
-- The match has no type to read its text pattern at when it is checked, so
-- the pattern makes the matched value a `Text`. The mismatch with a `List
-- Char` at the use points back at the pattern.
def m (cs: List Char): Nat :=
  let f := match | "a" => 1 | _ => 0
  f cs
