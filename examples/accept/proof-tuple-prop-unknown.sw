-- A tuple pattern in a lambda checked before the argument that fixes its
-- parameter's type: the type is an unknown proposition, which a pair can't
-- be, so the lambda waits for `h` and the tuple takes apart `p ∧ q`
-- (docs/proposals/proof-tuples.md §4.2).

def applyP [p q: Prop] (f: p → q) (x: p): q := f x

theorem viaLambda ∀ (p q: Prop) (h: p ∧ q): q := applyP ((_, b) => b) h

theorem viaClause ∀ (p q: Prop) (h: p ∧ q): q := applyP (match | (_, b) => b) h

-- At an unknown type, a tuple is still a pair.
def applyT [a b: Type] (f: a → b) (x: a): b := f x

def second (n m: Nat): Nat := applyT ((_, y) => y) (n, m)

theorem secondIs: second 1 2 = 2 := byComputing
