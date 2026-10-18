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
def notBad : Bad1 -> Void
  | MkBad1 f => f (MkBad2 (MkBad1 f))

def unwrap : Bad2 -> Void
  | MkBad2 b => notBad b

theorem boom : Void := notBad (MkBad1 unwrap)
