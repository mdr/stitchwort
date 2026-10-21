-- expect-error: E-DATA-AUTO
-- A type's `auto` parameter is found by instance search, so it must ask for
-- an interface.

type Checked (n: Nat) [auto ok: n = n] =
  { value: Nat }
