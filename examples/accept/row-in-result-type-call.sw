-- A call whose result type mentions its own row (`{e} (Nat → {e} Nat)`) is left to the
-- expected type, not settled as pure (SW-1564).
import Std (Abort, List)

def mk (): {e} (Nat → {e} Nat) := x => x

type Box = { n: Nat }

def Box.mk (b: Box): {e} (Nat → {e} Nat) := x => x + b.n

-- The expected type fixes the row.
def g1 (): {Abort} (Nat → {Abort} Nat) := mk()

def g2 (b: Box): {Abort} (Nat → {Abort} Nat) := b.mk

def g3 (b: Box): {Abort} Nat :=
  let k := if True then b.mk else (x => Abort.need (Some x))
  k 1
