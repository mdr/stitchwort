-- A pattern `let` on a proof, in a proof, binds projections
-- (`crates/elab/src/patlet.rs`): `let (len, zero) := h` is
-- `let len := h.left` and `let zero := h.right`, rather than a `match`,
-- which would generalise the goal and every hypothesis over `h`, reading
-- each back computed. With the large list below in the goal and in a
-- hypothesis, each such `match` read back thousands of nodes.

def ones (n: Nat): List Nat := match n with
  | 0 => []
  | Succ k => [1, ..ones k]

theorem bigSplit ∀ (xs: List Nat)
    (big: xs = ones 2000)
    (h: xs.length = 2000 ∧ 0 = 0 ∧ 1 = 1):
    xs = ones 2000 ∧ xs.length = 2000 :=
  let (len, zero, one) := h
  let (again, (b, c)) := (len, (zero, one))
  (big, again)

-- A record of proofs, taken apart by field names.
type Bounds (x: Nat): Prop = { above: 0 < x, below: x < 10 }

theorem boundsSwap ∀ (x: Nat) (big: ones x = ones x) (bounds: Bounds x): x < 10 ∧ 0 < x :=
  let { above, below } := bounds
  (below, above)

-- A goal that computes on the proof needs the `match`'s refinement:
-- with projections `byComputing` meets `bothOk h`, stuck, so the `let`
-- is checked again as the `match`, whose goal is `bothOk (Both a b) = True`.
def bothOk (h: 1 = 1 ∧ 2 = 2): Bool := match h with | Both _ _ => True

theorem refined ∀ (h: 1 = 1 ∧ 2 = 2): bothOk h = True :=
  let (a, b) := h
  byComputing

-- On data, a proof's `let` is still a `match`, which refines the goal.
def swap (p: (Nat, Nat)): (Nat, Nat) := (p.snd, p.fst)

theorem swapTwice ∀ (p: (Nat, Nat)): swap (swap p) = p :=
  let (a, b) := p
  byComputing

-- A record pattern on a test fact reads it through its reading, as the
-- `match` does, in a proof and outside one (outside one this was an
-- internal error before SW-4629).
type InRange (lo x hi: Nat): Prop = { low: lo ≤ x, high: x ≤ hi }

def inRange (lo x hi: Nat): Bool := lo <= x && x <= hi

@[reading]
theorem inRangeReads ∀ (lo x hi: Nat): inRange lo x hi ↔ InRange lo x hi :=
  { forward = h => { low = h.left, high = h.right }, backward = r => Both r.low r.high }

theorem highOf ∀ (x: Nat) (h: inRange 1 x 9): x ≤ 9 :=
  let { low, high } := h
  high

def clamped (x: Nat) (h: inRange 1 x 9): Nat :=
  let { low, high } := h
  x
