--| Slice 1's driver (`formatWithin1`), which the top theorems are about: what it formats and what it refuses.

namespace Fmt.Tests
import Std (Bool, Result, Text)
import Fmt.Driver1 (formatWithin1)

def formats1 (source expected: Text): Bool := formatWithin1 source == Ok expected

def refuses1 (source: Text): Bool := match formatWithin1 source with
  | Err message => message.startsWith "outside slice 1"
  | Ok _ => False

test "slice 1's driver formats a declaration that fits on one line" :=
  formats1 "-- a\ndef x:Nat:=f  (a,b)  [1,2,] -  -y -- b\n" "-- a\ndef x: Nat := f (a, b) [1, 2] - -y -- b\n"

test "slice 1's driver formats binary operators, which read-back doesn't cover yet" :=
  formats1 "def x: Nat := a+b * c\n" "def x: Nat := a + b * c\n"

test "slice 1's driver formats a declaration whose value goes on the next line and fits there" :=
  formats1
      "def long: Nat := someFunction argumentNumberOne argumentNumberTwo argumentNumberThree argumentNumberFour argumentNumberFive\n"
      "def long: Nat :=\n  someFunction argumentNumberOne argumentNumberTwo argumentNumberThree argumentNumberFour argumentNumberFive\n"

test "slice 1's driver refuses a declaration that doesn't fit on one line" :=
  refuses1
      "def long: Nat := someFunction argumentNumberOne argumentNumberTwo argumentNumberThree argumentNumberFour argumentNumberFive (another call here)\n"

test "slice 1's driver refuses a type broken over lines" := refuses1 "def d: ( -- t\n  a) := b\n"

test "slice 1's driver refuses a token outside the slice" := refuses1 "def d: A := List.map f\n"

test "slice 1's driver keeps a comment after a type's or value's last word on the line, after the closers that follow it" :=
  formats1 "def x: F (a -- c\n  ) := [b, d -- e\n  ]\n" "def x: F (a) -- c\n  :=\n  [b, d] -- e\n"

test "slice 1's driver refuses a comment above a later word of the value" := refuses1 "def x: T := f a\n  -- c\n  b\n"
