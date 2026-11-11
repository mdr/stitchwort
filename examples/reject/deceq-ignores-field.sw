-- expect-error: E-REFL
-- A hand-written `DecEq` can't treat values with different fields as equal:
-- `Decidable.yes` needs a proof that they're equal, and there is none. So the `Ord`
-- derived from the fields always agrees with a type's own `==`
-- (docs/proposals/interfaces.md §5.11). This `==` ignores `minor`.

import Std (Decidable, Eq)

type Version = { major: Nat, minor: Nat }

def Version.decide (x: Version) (y: Version): Decidable (x = y) :=
  if h: x.major = y.major then Decidable.yes rfl
  else Decidable.no (e => h (Eq.cong Version.major e))

instance Version.instDecEq: DecEq Version := { decide = Version.decide }
