-- expect-error: E-EXPORT
-- The generated module already exports a class with this name.
type StitchwortInputError : Type =
  | Oops

export
oops : Nat -> StitchwortInputError
oops n = Oops
