-- Parameter defaults (docs/proposals/signature-defaults.md): `(x: T := e)`
-- on an explicit parameter of a `def` or `theorem` header. A defaulted
-- parameter is given by name only; a call that doesn't name it gets its
-- default, so a factory takes just the values a test cares about.

import Std (Float, Vec)

type Guest = { name: Text }

type Booking = {
  id: Text,
  start: Float,
  duration: Float,
  room: Option Text,
  guests: List Guest,
  notes: Option Text
}

def makeBooking (id: Text)
    (start: Float := 0.0)
    (duration: Float := 60.0)
    (room: Option Text := None)
    (guests: List Guest := [])
    (notes: Option Text := None): Booking :=
  { id, start, duration, room, guests, notes }

-- The ids of the bookings shorter than an hour.
def flagged (bookings: List Booking): List Text :=
  bookings.filter (b => b.duration < 60.0) |> .map (b => b.id)

test "a short booking is flagged" :=
  let short := makeBooking "a" (duration := 30.0)
  flagged [short, makeBooking "b"] == ["a"]

test "bookings keep their order" :=
  let bookings := ["a", "b", "c"].map makeBooking
  bookings.map (b => b.id) == ["a", "b", "c"]

test "a left out list or option is its default" :=
  let booking := makeBooking "a" (room := Some "blue")
  booking.guests.length == 0 && booking.room == Some "blue" && booking.notes == None

-- A default may use the parameters before it.
def range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat := [start, stop, step]

def framed (title: Text) (width: Nat := title.length + 4): Nat := width

test "positional arguments skip defaulted parameters" := range 0 10 == [0, 10, 1]
test "a named argument replaces the default" := range 0 10 (step := 2) == [0, 10, 2]
test "a default uses an earlier parameter" := framed "abc" == 7 && framed "abc" (width := 3) == 3

-- A call that leaves a required parameter out before a defaulted one is a
-- function of the required one.
test "partial calls" := [10, 20].map (range 0) == [[0, 10, 1], [0, 20, 1]]

-- Dot calls, method sections and pipes fill defaults too.
type Clip = { length: Nat }

def Clip.trimmed (clip: Clip) (by: Nat := 1): Nat := clip.length - by

def clip: Clip := { length = 10 }

test "dot call" := clip.trimmed == 9 && clip.trimmed (by := 3) == 7
test "method section" := [clip, { length = 4 }].map .trimmed == [9, 3]
test "pipe" := (clip |> Clip.trimmed) == 9

-- A function whose result is a function: brackets finish the call before
-- the next argument.
def scaler (base: Nat) (factor: Nat := 1): Nat -> Nat := x => base * factor + x

test "a bracketed call is finished" := (scaler 5) 3 == 8
test "the default given by name" := scaler 5 (factor := 3) 1 == 16

-- A dependent default: a later parameter's type uses it.
def sized (n: Nat := 3) (xs: Vec Nat n): Nat := n

def three: Vec Nat 3 := Vec.replicate 3 0
def two: Vec Nat 2 := Vec.replicate 2 0

test "dependent defaults" := sized three == 3 && sized (n := 2) two == 2

-- Local definitions take defaults too, and recursive calls use them.
def sumTo (n: Nat): Nat :=
  def go (k: Nat) (acc: Nat := 0): Nat :=
    match k with
      | 0 => acc
      | Succ j => go j (acc := acc + k)
  go n

test "local definition" := sumTo 4 == 10

-- Leaving a default out is definitionally equal to giving it.
theorem rangeDefault (start: Nat) (stop: Nat): range start stop = range start stop (step := 1) := rfl

-- The bare name is the call with no arguments: a function of the required
-- parameters, with the defaults filled.
theorem bareRange: (range 0: (stop: Nat) -> List Nat) = ((stop: Nat) => range 0 stop) := rfl
