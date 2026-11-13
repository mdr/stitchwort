-- An implicit record is solved through a field of a field: `Step n closed`
-- compares `Closed ?cavern n` with `closed`'s type, so `?cavern.grid.rows`
-- with `cavern.grid.rows`, where `cavern.grid` is kept as the call
-- `Cavern.grid cavern`. Their records are compared, the call by what it
-- computes to, `cavern.grid`, and then those records, solving `?cavern`
-- (SW-1998).

type Grid = { rows: List Nat }

type Cavern = { grid: Grid }

def Grid.cells (grid: Grid): List Nat := grid.rows.reverse

def Closed (cavern: Cavern) (n: Nat): Prop := n ∈ cavern.grid.cells → n = 0

type Run: Cavern → Prop =
  | Step [cavern: Cavern] (n: Nat) (closed: Closed cavern n): Run cavern

theorem runOf ∀ (cavern: Cavern) (n: Nat) (closed: Closed cavern n): Run cavern := Step n closed
