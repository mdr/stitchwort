import Std (Bool, List, Nat, Text)

-- A test is a `Bool`. A fact about it, such as `booking.fits 4`, can be taken
-- apart like the statement it stands for: `&&` gives `Both`.
type Booking = { name: Text, seats: Nat }

def Booking.fits (booking: Booking) (capacity: Nat): Bool :=
  0 < booking.seats && booking.seats <= capacity

theorem fitsSeats ∀ (booking: Booking) (capacity: Nat) (h: booking.fits capacity):
    booking.seats ≤ capacity := match h with
      | Both _ small => small

-- To use the whole fact as its statement, write `.read`. A fact is built the
-- way its statement is.
theorem fitsBoth ∀ (booking: Booking) (capacity: Nat) (h: booking.fits capacity):
    0 < booking.seats ∧ booking.seats ≤ capacity := h.read

theorem fitsFrom ∀ (booking: Booking) (capacity: Nat) (positive: 0 < booking.seats)
    (small: booking.seats ≤ capacity): booking.fits capacity :=
  Both positive small

-- A fact about `all` reads as "for every member": `.read`, then a member.
theorem allSmall ∀ (bookings: List Booking) (capacity: Nat)
    (h: bookings.all (b => b.fits capacity)) (b: Booking) (m: b ∈ bookings):
    b.seats ≤ capacity := (h.read b m).right
