-- begin booking
type Booking = { name: Text, seats: Nat, wheelchair: Bool }

def Booking.fits (booking: Booking) (capacity: Nat): Bool :=
  0 < booking.seats && booking.seats <= capacity

def ada: Booking := { name = "Ada", seats = 2, wheelchair = False }
def bo: Booking := { name = "Bo", seats = 5, wheelchair = False }

test "a booking that fits" := ada.fits 4
test "one that doesn't" := !bo.fits 4
-- end booking

-- begin pieces
theorem fitsSeats (booking: Booking) (capacity: Nat) (h: booking.fits capacity):
    booking.seats <= capacity := match h with
      | Both _ small => small

theorem fitsPositive (booking: Booking) (capacity: Nat) (h: booking.fits capacity):
    0 < booking.seats := h.left
-- end pieces

-- begin read
theorem fitsBoth (booking: Booking) (capacity: Nat) (h: booking.fits capacity):
    0 < booking.seats ∧ booking.seats ≤ capacity := h.read
-- end read

-- begin negative
theorem emptyOrTooBig (booking: Booking) (capacity: Nat) (h: booking.fits capacity = False):
    booking.seats = 0 ∨ capacity < booking.seats := match h with
      | Inl zero => Inl omega
      | Inr big => Inr big.read
-- end negative

-- begin build
theorem fitsFrom (booking: Booking) (capacity: Nat) (positive: 0 < booking.seats)
    (small: booking.seats ≤ capacity): booking.fits capacity :=
  Both positive small

theorem fitsOrBigger (booking: Booking) (capacity: Nat) (h: booking.fits capacity):
    booking.fits (capacity + 1) :=
  Both h.left omega
-- end build

-- begin build-from-proof
theorem noRoomLeft (booking: Booking) (capacity: Nat) (small: booking.seats < capacity):
    (capacity <= booking.seats) = False := small

theorem allFit (bookings: List Booking) (capacity: Nat)
    (each: ∀ (b: Booking) => b ∈ bookings → b.fits capacity):
    bookings.all (b => b.fits capacity) :=
  b m => each b m

theorem booked (bookings: List Booking) (b: Booking) (m: b ∈ bookings): bookings.contains b := m
-- end build-from-proof

-- begin same
theorem sameName (a: Booking) (b: Booking) (h: a == b): a.name = b.name :=
  rewrite h.read in rfl
-- end same

-- begin auto
def Booking.spare (booking: Booking) (capacity: Nat) [auto ok: booking.seats ≤ capacity]: Nat :=
  capacity - booking.seats

def spareFor (booking: Booking) (capacity: Nat) (h: booking.fits capacity): Nat :=
  booking.spare capacity

theorem allSmall (bookings: List Booking) (capacity: Nat)
    (h: bookings.all (b => b.fits capacity)) (b: Booking) (m: b ∈ bookings):
    b.seats ≤ capacity := (h.read b m).right
-- end auto

-- begin auto-all
def below (x: Nat) [auto ok: x < 5]: Nat := x

def firstBelow (xs: List Nat) (y: Nat) (m: y ∈ xs) (h: xs.all (x => x < 5)): Nat :=
  below y
-- end auto-all
