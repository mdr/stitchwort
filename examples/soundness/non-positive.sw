-- expect-error: E-POSITIVITY
-- If this were allowed, `Bad` could be used to prove anything.
type Bad: Type =
  | MkBad (f: Bad -> Nat)
