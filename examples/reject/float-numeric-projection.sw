-- expect-error: E-PARSE
-- There are no numeric projections: `pair.0.1` is `pair` `.` `0` `.` `1`,
-- never `pair` `.` `0.1`, so decimal literals can't get in their way later.
def pair: (Nat, Nat) := (1, 2)

def first: Nat := pair.0.1
