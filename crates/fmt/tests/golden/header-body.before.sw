-- A definition whose header spans lines: its body is indented as after a one-line header.
def makeBooking (id: Text)
    (start: Float := 0.0)
    (duration: Float := 60.0)
    (notes: Option Text := None): Booking :=
  { id = { value = id }, start, duration, notes }

def multi (id: Text)
    (start: Float := 0.0): Booking :=
  {
    id = id,
    start = start
  }

def m (x: Nat)
    (y: Nat := 0): Nat :=
  match x with
    | Zero => y
    | Succ n => n

def l (x: Nat)
    (y: Nat := 0): Nat :=
  let a := x
  let b := y
  a + b

def br (x: Nat)
    (y: Nat := 0): Booking := {
  id = x,
  start = y
}
