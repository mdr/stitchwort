-- `Nat.iterate`: apply a function n times. A file of its own, so a program
-- that only iterates doesn't check the arithmetic lemmas.

-- `Nat.iterate n f x` is `f` applied `n` times to `x`: `Nat.iterate 3 f x` is
-- `f (f (f x))`. Written with `n.iterate f x` too.
def Nat.iterate: Nat -> (a -> a) -> a -> a
  | Zero,   f, x => x
  | Succ n, f, x => Nat.iterate n f (f x)

-- One more step is a step first.
theorem Nat.iterateSucc (n: Nat) (f: a -> a) (x: a): Nat.iterate (Succ n) f x = Nat.iterate n f (f x) := rfl

-- Or a step last.
theorem Nat.iterateSuccLast (f: a -> a): (n: Nat) -> (x: a) -> Nat.iterate (Succ n) f x = f (Nat.iterate n f x)
  | Zero,   x => rfl
  | Succ n, x => Nat.iterateSuccLast f n (f x)

test "Nat.iterate" := Nat.iterate 3 (x => x * 2) 1 == 8 && Nat.iterate 0 (x => x * 2) 5 == 5
test "Nat.iterate dot" := (2: Nat).iterate (x => Text.append x "!") "hi" == "hi!!"
