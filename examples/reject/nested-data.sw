-- expect-error: E-POSITIVITY
-- A type can't occur inside another type applied to it (a nested type): its
-- positivity would depend on how `List` uses its parameter. Write it as two
-- types defined together instead (`Rose`/`Roses` in accept/mutual-data.sw).
type Rose: Type =
  | Bloom (value: Nat) (kids: List Rose)
