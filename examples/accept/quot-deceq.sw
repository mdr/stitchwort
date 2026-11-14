-- A quotient's `==` is the one written for it (docs/proposals/map-equality.md
-- §7.6 R4, test A10): nothing compares the values quotients were made from,
-- but a `DecEq` instance that's proved lawful is used like any other, and
-- `==` is derived for a record containing it. Here every `Bool` is related
-- to every other, so the instance always answers `Yes`, proved by two
-- `Quot.ind`s and `Quot.sound`. An instance is for a type name, so the
-- quotient is wrapped in a record, `Q`, as `Map` will be. `boxF == boxT` is
-- `True` in the kernel (`rfl`) and in every runner.
--
--   $ stitchwort run examples/accept/quot-deceq.sw
--   True
--   True
import Std (Decidable, Eq, IO)

def AllTrue (x y: Bool): Prop := Unit

type Q = { raw: Quot Bool AllTrue }

-- Any two elements of the quotient are equal.
theorem rawSame ∀ (p q: Quot Bool AllTrue): p = q :=
  Quot.ind [p := p' => p' = q] (x => Quot.ind [p := q' => Quot.mk x = q'] (y => Quot.sound Trivial) q) p

theorem same ∀ (p q: Q): p = q := match p, q with
  | { raw = a }, { raw = b } => Eq.cong (r => ({ raw = r }: Q)) (rawSame a b)

instance qDecEq: DecEq Q := { decide = p q => Decidable.yes (same p q) }

-- `==` is derived for `Box`, using `qDecEq` for its field.
type Box = { q: Q }

def boxF: Box := { q = { raw = Quot.mk False } }
def boxT: Box := { q = { raw = Quot.mk True } }

theorem boxesEqual: (boxF == boxT) = True := rfl

test "boxes made from different values are equal" := boxF == boxT

def main(): {IO} () :=
  IO.print (if boxF == boxT then "True" else "False")
  IO.print (if boxT == boxF then "True" else "False")
