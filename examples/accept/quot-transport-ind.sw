-- Transport along a proof made by `Quot.ind`, with no `Quot.sound` anywhere
-- (docs/proposals/map-equality.md §7.4.4, test A6). `Quot.ind` doesn't
-- compute, so in the kernel `n` is stuck
-- (reject/quot-transport-ind-stuck.sw). When running, `Quot.ind` is the
-- erased placeholder and `J` takes its base, so every runner
-- (`run --reference`, `test`, `run`, `run --js`) gives `0`, through a
-- definition and inline.
--
--   $ stitchwort run examples/accept/quot-transport-ind.sw
--   0
--   0
import Std (IO, Nat)

def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

def p: 0 = 0 := Quot.ind [p := q => 0 = 0] (b => rfl) (Quot.mk False: Q)

def n: Nat := J (y proof => Nat) 0 p

def nInline: Nat := J (y proof => Nat) 0 (Quot.ind [p := q => 0 = 0] (b => rfl) (Quot.mk False: Q))

test "transport along a Quot.ind proof" := n == 0
test "and along one written inline" := nInline == 0

def main(): {IO} () :=
  IO.print (Nat.toText n)
  IO.print (Nat.toText nInline)
