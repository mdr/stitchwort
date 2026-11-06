-- A lemma bound with `let` before `match c: isBig n` is refined like a
-- hypothesis: in the `False` branch its premise is `False = False`. Both
-- `rfl` and the `match`'s own equation `c: isBig n = False` prove it: `c`
-- is rewritten along itself (SW-1538).

def isBig (n: Nat): Bool := 10 < n

def needsSmall (n: Nat) (small: isBig n = False): Nat := n

def halveSmall (n: Nat): Nat :=
  let use := (small: isBig n = False) => needsSmall n small
  match c: isBig n with
    | True => 0
    | False => use c

def halveSmallByRfl (n: Nat): Nat :=
  let use := (small: isBig n = False) => needsSmall n small
  match c: isBig n with
    | True => 0
    | False => use rfl
