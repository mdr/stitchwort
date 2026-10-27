-- expect-error: E-TERMINATION
-- A recursive call passed along with only some of its arguments stands for a
-- function of the rest, and nothing is known about what that function is
-- applied to. Here `bad m` is given `m`, which is no smaller, and the smaller
-- `n` reaches the second argument only through `applyTo`, so it doesn't
-- count: `bad 0 0` calls `bad 0 0` again, and would prove `Void`.
-- Neighbour: accept/partial-recursive-call.sw, where the argument that gets
-- smaller is among those given.
def applyTo (f: Nat → Void) (x: Nat): Void := f x

def bad: Nat → Nat → Void
  | Zero,   m => applyTo (bad m) m
  | Succ n, m => applyTo (bad m) n

theorem oops: Void := bad 0 0
