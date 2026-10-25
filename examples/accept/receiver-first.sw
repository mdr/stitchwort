-- The main value goes first (D303, D306): `T.f`'s first explicit parameter is
-- a `T`, so `x.f a b`, `x |> T.f a b` and `T.f x a b` are the same call. Other
-- arguments come next and functions last, so a trailing lambda reads well.
-- A definition in `T`'s namespace that takes a `T`, but not first, gets the
-- warning W-RECEIVER-NOT-FIRST, unless it is marked `@[noReceiver]`: a helper
-- not meant to be called with `.` or `|>` (D309).

import Std (List)

type Meter = { v: Nat }

def Meter.scale (m: Meter) (k: Nat): Meter := { v = k * m.v }

def Meter.combine (m: Meter) (other: Meter) (f: Nat → Nat → Nat): Meter :=
  { v = f m.v other.v }

def m3: Meter := { v = 3 }

test "dot" := (m3.scale 2).v == 6
test "pipe" := (m3 |> Meter.scale 2).v == 6
test "direct" := (Meter.scale m3 2).v == 6
test "chain" := (m3 |> .scale 2 |> .scale 5).v == 30
test "function last" := (m3.combine m3 (a b => a * b)).v == 9

-- A helper whose order suits its own recursion, not dot notation: the
-- attribute says so, and there's no warning.
@[noReceiver]
def Meter.sumOnto (acc: Nat): List Meter → Nat
  | Nil => acc
  | Cons m rest => Meter.sumOnto (acc + m.v) rest

-- Not a `Meter` first, but no `Meter` at all: nothing to warn about.
def Meter.fromNat (n: Nat): Meter := { v = n }

test "helper" := Meter.sumOnto 0 [m3, Meter.fromNat 4] == 7
