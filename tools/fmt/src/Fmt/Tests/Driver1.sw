--| Slice 1's driver (`formatWithin1`), which the top theorems are about: what it formats and what it refuses.

namespace Fmt.Tests
import Std (Bool, Result, Text)
import Fmt.Driver1 (formatWithin1)

def formats1 (source expected: Text): Bool := formatWithin1 source == Ok expected

def refuses1 (source message: Text): Bool := formatWithin1 source == Err message

test "slice 1's driver formats a declaration that fits on one line" :=
  formats1 "-- a\ndef x:Nat:=f  (a,b)  [1,2,] -  -y -- b\n" "-- a\ndef x: Nat := f (a, b) [1, 2] - -y -- b\n"

test "slice 1's driver formats binary operators, which read-back doesn't cover yet" :=
  formats1 "def x: Nat := a+b * c\n" "def x: Nat := a + b * c\n"

test "slice 1's driver formats a declaration whose value goes on the next line and fits there" :=
  formats1
      "def long: Nat := someFunction argumentNumberOne argumentNumberTwo argumentNumberThree argumentNumberFour argumentNumberFive\n"
      "def long: Nat :=\n  someFunction argumentNumberOne argumentNumberTwo argumentNumberThree argumentNumberFour argumentNumberFive\n"

test "slice 1's driver formats a declaration that doesn't fit on one line, over several" :=
  formats1
      "def long: Nat := someFunction argumentNumberOne argumentNumberTwo argumentNumberThree argumentNumberFour argumentNumberFive (another call here)\n"
      "def long: Nat :=\n  someFunction argumentNumberOne argumentNumberTwo argumentNumberThree argumentNumberFour argumentNumberFive\n    (another call here)\n"

test "slice 1's driver formats a type broken over lines" :=
  formats1 "def d: ( -- t\n  a) := b\n" "def d: ( -- t\n    a) :=\n  b\n"

test "slice 1's driver refuses a token outside the slice, naming it" :=
  refuses1 "def d: A := a |> f\n" "outside slice 1: the token `|>` isn't one slice 1 has"

test "slice 1's driver refuses a `->` before a comma, naming what follows" :=
  refuses1 "def d: A -> , B := x\n" "outside slice 1: a token out of place: `->` before `,`, which may not follow it"

test "slice 1's driver refuses a comma that starts a line and isn't a last comma" :=
  refuses1 "def x: T := [a\n  ,,]\n"
      "outside slice 1: a token out of place: a comma that starts a line, before `,`, which isn't a last comma"

test "slice 1's driver refuses a source that starts with a comma" :=
  refuses1 ", def x: T := a\n" "outside slice 1: the source starts with `,`"

test "slice 1's driver refuses a source that doesn't parse, saying so" := match formatWithin1 "def d\n" with
  | Err message => message.startsWith "parse error: "
  | Ok _ => False

test "slice 1's driver refuses a keyword slice 1 doesn't have, naming it" :=
  refuses1 "namespace A\n" "outside slice 1: the token `namespace` isn't one slice 1 has"

test "slice 1's driver refuses a definition with parameters, naming it" :=
  refuses1 "def f (x: A): B := x\n" "outside slice 1: parameters on the definition `f`"

test "slice 1's driver names the first declaration outside the slice" :=
  refuses1 "def a: T := x\n\ndef f (x: A): B := x\n\ndef g (y: A): B := y\n"
      "outside slice 1: parameters on the definition `f`"

test "slice 1's driver keeps a comment after a type's or value's last word on the line, after the closers that follow it" :=
  formats1 "def x: F (a -- c\n  ) := [b, d -- e\n  ]\n" "def x: F (a) -- c\n  :=\n  [b, d] -- e\n"

test "slice 1's driver formats a comment above a later word of the value" :=
  formats1 "def x: T := f a\n  -- c\n  b\n" "def x: T :=\n  f a\n    -- c\n    b\n"

test "slice 1's driver formats a last comma that starts its line, before the closer" :=
  formats1 "def k: List Nat := [1, 2\n  ,]\n" "def k: List Nat := [1, 2]\n"
