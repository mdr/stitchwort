-- Rule I (docs/core.md, "Proof irrelevance"; stage 5 of
-- docs/proposals/full-proof-irrelevance.md): two proofs of one proposition
-- are equal, wherever they are compared and without looking at either. Each
-- declaration here was refused before it (docs/proposals/full-proof-irrelevance/
-- e2-only.sw probes 1, 2, 6, 7 and 9, and stuck-call-proof-field.sw).
import Std (Eq, List, Nat)

type Box (a: Prop): Type = | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

-- Two bare proofs.
theorem bare ∀ (a: Prop) (p q: a): p = q := byComputing

-- A proof passed to a local function.
theorem underLocal ∀ (a: Prop) (f: a → Nat) (p q: a): f p = f q := byComputing

-- `f p` and `f q` are one type, so `x` is accepted at either: the
-- subject-reduction gap of docs/proposals/proof-irrelevance.md §5.7 is gone.
def inlined (a: Prop) (p q: a) (f: a → Type) (x: f p): f q := x

-- Two unboxed proofs.
theorem unboxBoth ∀ (a: Prop) (p q: a): Box.unbox (MkBox p) = Box.unbox (MkBox q) := byComputing

-- A proof field under a call whose body is hidden: the arguments are
-- compared one by one, and proofs among them by rule I.
opaque def secret (b: Box (0 = 0)): Nat := 0

theorem underHidden ∀ (p q: 0 = 0): secret (MkBox p) = secret (MkBox q) := byComputing

-- Two stuck calls of `pick`, whose arguments differ only in a proof field:
-- the sealed `selfEq 0` against `byComputing` (SW-4661).
type Checked: Type = | MkChecked (n: Nat) (ok: n = n)

theorem selfEq ∀ (n: Nat): n = n := byComputing

def mk (n: Nat): Checked := MkChecked n (selfEq n)

def zero: Checked := MkChecked 0 byComputing

def pick (d: Checked): List Checked → Checked
  | [] => d
  | [x, ..rest] => x

theorem sameCall ∀ (xs: List Checked): pick (mk 0) xs = pick zero xs := byComputing
