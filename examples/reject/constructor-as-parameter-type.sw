-- expect-error: E-NOT-A-TYPE
-- A constructor written where a type is wanted (`cavern: Step`) is a
-- partial application whose later parameters mention the earlier ones, and
-- naming it is reported as an error, not a panic or a message about unknowns.
type Cavern = { rows: List Nat }

def Closed (cavern: Cavern) (n: Nat): Prop := n ∈ cavern.rows → n = 0

type Run: Cavern → Prop =
  | Step [cavern: Cavern] (n: Nat) (closed: Closed cavern n): Run cavern

theorem runOf (cavern: Step) (n: Nat) (closed: Closed cavern n): Run cavern := Step n closed
