type Grid = { rows: List Nat }
type Cavern = { grid: Grid }

def Grid.cells (grid: Grid): List Nat := grid.rows.reverse

def Closed (cavern: Cavern) (n: Nat): Prop := n ∈ cavern.grid.cells → n = 0

type Run: Cavern → Prop =
  | Step [cavern: Cavern] (n: Nat) (closed: Closed cavern n): Run cavern

theorem probe (cavern: Cavern) (n: Nat) (closed: Closed cavern n): Run cavern := Step n closed
