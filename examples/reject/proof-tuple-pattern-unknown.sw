-- expect-error: E-CANNOT-INFER
-- Nothing says what proposition this tuple pattern takes apart when it is
-- read, so it is read as a pair, which a proposition can't be.
def wrapP [p q: Prop] (f: p → q): p → q := f
def t (a b: Nat): Nat :=
  let f := wrapP ((x, y) => x)
  1
