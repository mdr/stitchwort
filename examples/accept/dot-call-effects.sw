-- A dot call that performs operations runs where it's written, also with no
-- arguments (`b.say`), as an argument, and at the end of a chain whose
-- earlier calls are pure (`(Box.wrap n).say`, `w.toNat.orAbort`) (SW-217).
import Std.Abort (toOption)
import Std (Abort, IO, Nat)

type Box = { v: Nat }

def Box.say (b: Box): {IO} Nat :=
  IO.print "hi"
  b.v

def Box.wrap (n: Nat): Box := { v = n }

def asArgument (b: Box): {IO} Nat := Nat.add 1 b.say
def afterCall (n: Nat): {IO} Nat := (Box.wrap n).say
def inSum (n: Nat): {IO} Nat := 1 + (Box.wrap n).say

def chain (w: Text): {Abort} Nat := w.toNat.orAbort
def chainInSum (w: Text): {Abort} Nat := 1 + w.toNat.orAbort
def chainInPair (w: Text): {Abort} (Pair Nat Nat) := (1, w.toNat.orAbort)

test "as an argument" := IO.simulate [] (() => asArgument { v = 4 }) == (["hi"], 5)
test "after a call" := IO.simulate [] (() => afterCall 4) == (["hi"], 4)
test "in a sum" := IO.simulate [] (() => inSum 4) == (["hi"], 5)
test "a chain" := toOption (() => chain "41") == Some 41 && toOption (() => chain "x") == None
test "a chain in a sum" := toOption (() => chainInSum "41") == Some 42
test "a chain in a pair" := toOption (() => chainInPair "2") == Some (1, 2)
