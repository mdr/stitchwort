namespace Probe.RunTail

import Probe.Walk (Stream, Cells)
import Probe.Mach (Machine)
import Probe.Cursor (Cursor, Origin)
import Probe.Seq (Seq)
import Probe.N (which, n)

-- The loop as a newcomer writes it: head, then recurse on the tail.
def sumByTail (s: Stream Nat) (k acc: Nat): Nat := match k with
  | Zero => acc
  | Succ j => sumByTail s.tail j (acc + s.head)

def Machine.head (m: Machine a): a := match m with | MkMachine s start next => (next start).fst

-- The same loop on a state machine: what a runtime that kept a stream as
-- `unfold`'s step and state would do.
def sumMachine (m: Machine Nat) (k acc: Nat): Nat := match k with
  | Zero => acc
  | Succ j => sumMachine m.tail j (acc + m.head)

def sumCursor (c: Cursor Nat) (k acc: Nat): Nat := match k with
  | Zero => acc
  | Succ j => sumCursor c.tail j (acc + c.head)

def sumSeq (q: Seq Nat) (k acc: Nat): Nat := match k with
  | Zero => acc
  | Succ j => sumSeq q.tail j (acc + q.head)

def sumOrigin (c: Origin Nat) (k acc: Nat): Nat := match k with
  | Zero => acc
  | Succ j => sumOrigin c.tail j (acc + c.head)

def main(): {IO} () := match which with
  | 0 => IO.print "tail loop, three-field Stream: ${sumByTail (Stream.iterate (+ 1) 0) n 0}"
  | 1 => IO.print "tail loop, state machine: ${sumMachine (Machine.iterate (+ 1) 0) n 0}"
  | 2 => IO.print "tail loop, cursor: ${sumCursor (Cursor.of (Stream.iterate (+ 1) 0)) n 0}"
  | 5 => IO.print "tail loop, origin and offset: ${sumOrigin (Origin.of (Stream.iterate (+ 1) 0)) n 0}"
  | 4 => IO.print "tail loop, Seq: ${sumSeq (Seq.iterate (+ 1) 0) n 0}"
  | _ => IO.print "cells loop: ${((Stream.iterate (+ 1) 0).walk n).sum 0}"
