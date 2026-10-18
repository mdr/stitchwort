-- expect-error: E-EXPORT
-- The generated module already exports a class with this name.
type StitchwortInputError : Type =
  | Oops

export def oops (n : Nat) : StitchwortInputError := Oops
