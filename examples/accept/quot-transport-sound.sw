-- Transport along `Quot.sound` (docs/proposals/map-equality.md §9.1, test
-- A3). In the kernel `J` on `Quot.sound` is stuck, so `n` is a closed `Nat`
-- that isn't a numeral (reject/quot-transport-sound-stuck.sw). When running,
-- `Quot.sound` is the erased placeholder and `J` takes its base, so every
-- runner (`run --reference`, `test`, `run`, `run --js`) gives `0`, through
-- a theorem and with `Quot.sound` written inline (D862).
--
--   $ stitchwort run examples/accept/quot-transport-sound.sw
--   0
--   0
import Std (IO, Nat)

def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

theorem same: (Quot.mk False: Q) = Quot.mk True := Quot.sound Trivial

def n: Nat := J (y p => Nat) 0 same

def nInline: Nat :=
  J (y p => Nat) 0 (Quot.sound [x := False] [y := True] Trivial: (Quot.mk False: Q) = Quot.mk True)

test "transport along a theorem" := n == 0
test "transport along an inline Quot.sound" := nInline == 0

def main(): {IO} () :=
  IO.print (Nat.toText n)
  IO.print (Nat.toText nInline)
