-- expect-error: E-DUPLICATE-ARGUMENT
-- Arguments fill parameters in the order they're written, a positional one
-- taking the first explicit parameter still free (D1112): in
-- `place 1 (x := 2)`, `1` has already filled `x`
-- (docs/proposals/named-arguments.md §4.2).

def place (x: Nat) (y: Nat): Nat := x * 10 + y

def twice: Nat := place 1 (x := 2)
