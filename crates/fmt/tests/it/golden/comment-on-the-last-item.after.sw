-- A comment on a bracket's last item and one after its closer are the same
-- comment (rule N), so a bracket that fits joins its line either way.
def list: List Nat := [1, 2] -- on the last item

def call: Nat := g (a, b) -- on the last item

def record: Point := { x = 1, y = 2 } -- on the last item

-- One that breaks keeps it on the last item's line.
def long: List Nat :=
  [1000000000000, 2000000000000, 3000000000000, 4000000000000, 5000000000000, 6000000000000, 7000000000000] -- on the last item
