namespace Probe.Cursor

import Std (Nat)
import Probe.Walk (Stream, Cells)

-- Timing only, no laws: a stream with a cursor. `front` holds the cells from
-- here on, for some number of values left; `tail` steps along it, and when it
-- runs out walks again from this stream with twice the count. `steps` counts
-- the tails taken, to size the next walk.
type Cursor (a: Type) = { stream: Stream a, front: Cells a, steps: Nat }

@[noReceiver]
def Cursor.of (s: Stream a): Cursor a := { stream = s, front = Done, steps = 0 }

def Cursor.refill (c: Cursor a): Cells a := match c.front with
  | Done => c.stream.walk (2 * c.steps + 2)
  | Cell x rest => c.front

def Cursor.head (c: Cursor a): a := match c.refill with
  | Done => c.stream.at 0
  | Cell x rest => x

def Cursor.tail (c: Cursor a): Cursor a := { stream = c.stream.tail, front = c.refill.tail, steps = c.steps + 1 }

test "cursor" := (Cursor.of (Stream.iterate (* 2) 1)).tail.tail.tail.tail.tail.head == 32

def Cells.drop (c: Cells a) (n: Nat): Cells a := match n with
  | Zero => c
  | Succ k => c.tail.drop k

-- The same with the stream it started from and a count of tails, in place of
-- a stream wrapped once per tail: nothing holds the earlier cursors, so a long
-- loop runs in constant memory. Timing only, no laws.
type Origin (a: Type) = { origin: Stream a, offset: Nat, front: Cells a }

@[noReceiver]
def Origin.of (s: Stream a): Origin a := { origin = s, offset = 0, front = Done }

def Origin.refill (c: Origin a): Cells a := match c.front with
  | Done => (c.origin.walk (2 * c.offset + 2)).drop c.offset
  | Cell x rest => c.front

def Origin.head (c: Origin a): a := match c.refill with
  | Done => c.origin.at c.offset
  | Cell x rest => x

def Origin.tail (c: Origin a): Origin a := { origin = c.origin, offset = c.offset + 1, front = c.refill.tail }

test "origin" := (Origin.of (Stream.iterate (* 2) 1)).tail.tail.tail.tail.tail.head == 32
