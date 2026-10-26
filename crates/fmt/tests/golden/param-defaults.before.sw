-- Parameter defaults in headers: spacing, and a header over several lines.
def range (start : Nat) (stop: Nat) (step : Nat:=1) : List Nat := [start, stop, step]

def makeBooking (guest: Text) (room: Nat)
  (nights: Nat := 1)   (breakfast: Bool:=False)
        (note: Text := "none"): Nat := room * nights

def outer (n: Nat): Nat :=
  def go (k: Nat) (acc: Nat:=0): Nat := k + acc
  go n (acc:=1)
