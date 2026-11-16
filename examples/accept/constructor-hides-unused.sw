-- A file that declares its own `Option`-like type, with constructors named
-- like the prelude's, never reaching for the prelude's: nothing to warn
-- about (`W-CTOR-HIDES` is for a file that also writes the hidden
-- constructor, as `constructor-clash-qualified` does).
type Maybe = | Some (n: Nat) | None

def orZero (m: Maybe): Nat := match m with
  | Some n => n
  | None => 0

theorem orZeroNone: orZero None = 0 := byComputing
