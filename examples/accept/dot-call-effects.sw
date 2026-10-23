-- A dot call that performs operations runs where it's written, also with no
-- arguments (`b.say`), as an argument, and at the end of a chain whose
-- earlier calls are pure (`(Box.wrap n).say`, `w.toNat.orAbort`) (SW-217).
import Std.Abort (toOption)
import Std (Abort, Fail, IO, Nat, Text)

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

-- The receiver can be a literal or a `++` (D1056): the dot call runs as the
-- full-name call does, at the end of a handled lambda, in a chain, in a
-- `let` and in a sum.
def spaced: Text := " 4 "

test "a literal's dot call, last" := Fail.toResult (() => " 4".toNatOrFail) == Ok 4 && Fail.toResult (() => "x".toNatOrFail) == Err "expected a whole number, got 'x'"
test "as the full-name call" := Fail.toResult (() => " 4".toNatOrFail) == Fail.toResult (() => Text.toNatOrFail " 4")
test "a literal's chain, with Abort" := toOption (() => "4".toNat.orAbort) == Some 4 && toOption (() => "x".toNat.orAbort) == None
test "a chain after a pure call" := Fail.toResult (() => spaced.trim.toNatOrFail) == Ok 4 && Fail.toResult (() => " 4 ".trim.toNatOrFail) == Ok 4
test "an appended receiver" := Fail.toResult (() => (spaced ++ "2").toNatOrFail) == Err "expected a whole number, got ' 4 2'"
test "in a let" := Fail.toResult (() =>
  let n := " 4".toNatOrFail
  n + n) == Ok 8
test "a literal's chain in a sum" := toOption (() => 1 + "41".toNat.orAbort) == Some 42
test "pure dot calls are values" := " 4".trim == "4" && "4".toNat == Some 4 && 'a'.toText == "a"
