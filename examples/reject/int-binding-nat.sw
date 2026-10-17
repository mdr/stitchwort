-- expect-error: E-TYPE-MISMATCH
-- A let-binding keeps its own type: `m` is a `Nat` (`3 - 5` has no expected
-- type to make it `Int`), and is not reinterpreted when used with an `Int`.
r : Int -> Bool
r i =
  let m = 3 - 5
  m + i == 0
