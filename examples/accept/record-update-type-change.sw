-- A record update may change the record's type parameters, as Haskell's
-- does: a parameter can change only if every field whose type mentions it is
-- replaced.
import Std (Int, Nat)

type Timed (a: Type) = { start: a, end: a, label: Text }

-- Both fields that mention `a` are replaced, so `Timed Int` becomes `Timed Nat`.
def toNat (t: Timed Int): Timed Nat :=
  { t | start = Int.toNat t.start, end = Int.toNat t.end }

-- The same with no expected type: the result type is inferred.
def viaLet (t: Timed Int): Timed Nat :=
  let u := { t | start = Int.toNat t.start, end = Int.toNat t.end }
  u

-- Updates that keep the parameters are as they were: `5` is an `Int` here.
def shifted (t: Timed Int): Timed Int := { t | start = 5 }
def shiftedLet (t: Timed Int): Timed Int :=
  let u := { t | start = 5 }
  u

-- A parameter only some fields mention: `label` is kept, and has no `a`.
type Span (i: Type) (n: Type) = { from: i, length: n, label: Text }

def widen (s: Span Int Nat): Span Int Int := { s | length = Nat.toInt s.length }
def retime (s: Span Int Nat): Span Nat Nat := { s | from = Int.toNat s.from }
def both (s: Span Int Nat): Span Nat Int :=
  { s | from = Int.toNat s.from, length = Nat.toInt s.length }

-- A parameter no replaced field mentions stays.
def relabel (s: Span Int Nat): Span Int Nat := { s | label = "other" }

test "type-changing update" :=
  (toNat { start = -3, end = 4, label = "t" }).end == 4

test "type-changing update, inferred" :=
  (viaLet { start = 2, end = 4, label = "t" }).start == 2

test "one parameter changes" :=
  (retime { from = 7, length = 3, label = "s" }).from == 7

test "an update that keeps the type" :=
  (shiftedLet { start = 1, end = -4, label = "t" }).start == 5
