-- expect-error: E-TYPE-MISMATCH
-- A field's type is shown as the record declares it: `s.room` has type
-- `fits s.books s.capacity = True`, not what `fits` computes to.

def fits (count: Nat) (limit: Nat): Bool := count + 1 <= limit

type Shelf = { books: Nat, capacity: Nat, room: fits books capacity = True }

def wrong (s: Shelf): Nat := s.room
