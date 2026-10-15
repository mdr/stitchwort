-- expect-error: E-POSITIVITY
-- Each type looks positive on its own: `Bad1` mentions only `Bad2`, and
-- `Bad2` only `Bad1`. Together, `Bad1` occurs to the left of an arrow inside
-- itself (through `Bad2`), exactly like `type Bad = MkBad (Bad -> Void)`, and
-- they prove `Void`. Positivity is checked across the whole group. Pairs with
-- accept/mutual-data.sw.
type Bad1 : Type =
  | MkBad1 (f : Bad2 -> Void)

type Bad2 : Type =
  | MkBad2 (b : Bad1)

-- Neither function is recursive, so both would pass the termination check.
notBad : Bad1 -> Void
notBad (MkBad1 f) = f (MkBad2 (MkBad1 f))

unwrap : Bad2 -> Void
unwrap (MkBad2 b) = notBad b

theorem boom : Void
boom = notBad (MkBad1 unwrap)
