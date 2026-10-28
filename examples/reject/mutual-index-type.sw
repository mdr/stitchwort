-- expect-error: E-MUTUAL-KIND
-- A data type's index type names a definition whose body names the type
-- back: a cycle, even though the use is in the index telescope.
def Q: Type := List T
type T: Q → Type =
  | A: T Nil
