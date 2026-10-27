-- A type whose module writes its own `DecEq` instance still gets a derived
-- `Ord` (docs/proposals/interfaces.md §5.11): it's derived once that
-- instance is checked, and uses it as its `eq`. The order compares the
-- fields in order: `Version`s by `major`, then `minor`.

import Std (Eq, List, Ord)

type Version = { major: Nat, minor: Nat }

def Version.decide (x: Version) (y: Version): Decidable (x = y) :=
  if h: (x.major, x.minor) = (y.major, y.minor) then Yes (Version.sameParts x y h)
  else No (e => h (Eq.cong (v => (v.major, v.minor)) e))

theorem Version.sameParts: (x: Version) → (y: Version) → (x.major, x.minor) = (y.major, y.minor) → x = y
  | { major = a1, minor = b1 }, { major = a2, minor = b2 }, h =>
    rewrite Eq.cong Pair.fst h, Eq.cong Pair.snd h in rfl

instance Version.instDecEq: DecEq Version := { decide = Version.decide }

def old: Version := { major = 1, minor = 9 }
def mid: Version := { major = 2, minor = 0 }
def new: Version := { major = 2, minor = 3 }

test "major first" := old < mid
test "then minor" := mid < new
test "not less than itself" := not (new < new)
test "equal" := Ord.compare mid mid == Equal
test "sorted" := List.sort [new, old, mid] == [old, mid, new]
