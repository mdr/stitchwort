-- A lift whose result is a proof (docs/proposals/map-equality.md §7.4.3,
-- test A5): the checker marks it erased (D921), so when running it's the
-- placeholder, `f`, `h` and the quotient aren't computed, and `J` takes its
-- base. Every runner (`run --reference`, `test`, `run`, `run --js`) gives
-- `0`, through a definition and inline. In the kernel the lift computes to
-- `byComputing`, so `J` does too.
--
--   $ stitchwort run examples/accept/quot-lift-proof.sw
--   0
--   0
import Std (IO, Nat)

def AllTrue (x y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

def p: 0 = 0 := Quot.lift (b => byComputing) (x y related => byComputing) (Quot.mk False: Q)

def n: Nat := J (y proof => Nat) 0 p

def nInline: Nat :=
  J (y proof => Nat) 0 (Quot.lift [b := 0 = 0] (b => byComputing) (x y related => byComputing) (Quot.mk False: Q))

theorem nInlineIsZero: nInline = 0 := byComputing

-- Through `p` too: a definition with a proof for its result unfolds in the
-- kernel, so the lift computes.
theorem nIsZero: n = 0 := byComputing

test "transport along a proof-valued lift" := n == 0
test "and along one written inline" := nInline == 0

def main(): {IO} () :=
  IO.print (Nat.toText n)
  IO.print (Nat.toText nInline)
