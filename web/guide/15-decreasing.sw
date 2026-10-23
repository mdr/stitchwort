-- Every function must provably finish. Recursion on a piece of an argument
-- (like `xs` in `Cons x xs`) is accepted as it is. When a call isn't on a
-- piece, say what shrinks with `decreasing`; the `if` supplies the proof
-- that it does.
def halvings (n: Nat) (count: Nat): Nat
  decreasing n
:=
  let next := n / 2
  if h: next < n then halvings next (count + 1) else count

test "halvings of 100" := halvings 100 0 == 7
theorem halvingsOf8: halvings 8 0 = 4 := rfl
