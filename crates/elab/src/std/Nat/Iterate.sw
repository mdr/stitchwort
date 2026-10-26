-- `Nat.iterate`: apply a function n times. A file of its own, so a program
-- that only iterates doesn't check the arithmetic lemmas.

-- `Nat.iterate n f x` is `f` applied `n` times to `x`: `Nat.iterate 3 f x` is
-- `f (f (f x))`. Written with `n.iterate f x` too.
def Nat.iterate: Nat → (a → a) → a → a
  | Zero, f, x => x
  | Succ n, f, x => Nat.iterate n f (f x)

-- One more step is a step first.
theorem Nat.iterateSucc (n: Nat) (f: a → a) (x: a): Nat.iterate (Succ n) f x = Nat.iterate n f (f x) := rfl

-- Or a step last.
theorem Nat.iterateSuccLast (f: a → a): (n: Nat) → (x: a) → Nat.iterate (Succ n) f x = f (Nat.iterate n f x)
  | Zero, x => rfl
  | Succ n, x => Nat.iterateSuccLast f n (f x)

test "Nat.iterate" := Nat.iterate 3 (* 2) 1 == 8 ∧ Nat.iterate 0 (* 2) 5 == 5
test "Nat.iterate dot" := (2: Nat).iterate (x => Text.append x "!") "hi" == "hi!!"

-- Apply `step` until it changes nothing: `Nat.iterateUntilStable x step
-- measure shrinks` is the first `Nat.iterate k step x` with `step` of it
-- equal to it. The loop may not end in general, so it takes what makes it
-- end: a `measure` that `shrinks` at every step that changes something.
-- Needs `DecEq` to see that nothing changed. A simulation reads:
-- `Nat.iterateUntilStable grid step size proof`.
def Nat.iterateUntilStable [auto eq: DecEq a] (x: a) (step: a → a) (measure: a → Nat)
    (shrinks: (y: a) → Not (step y = y) → measure (step y) < measure y): a
    decreasing measure x
:=
  if h: step x = x
  then x
  else Nat.iterateUntilStable (step x) step measure shrinks [decreasing := shrinks x h]

-- The decision `Nat.iterateUntilStable` makes, taken apart: the lemmas below
-- hand it to these.
theorem Nat.untilStableDecYes (p: Prop) (x: a) (r: a) (h: p): (d: Decidable p) → Decidable.elim d (y => x) (n => r) = x
  | Yes y => rfl
  | No n => Void.exfalso (n h)

theorem Nat.untilStableDecNo (p: Prop) (x: a) (r: a) (h: Not p): (d: Decidable p) → Decidable.elim d (y => x) (n => r) = r
  | Yes y => Void.exfalso (h y)
  | No n => rfl

-- A value `step` leaves alone is already the answer.
theorem Nat.iterateUntilStableStable [auto eq: DecEq a] (x: a) (step: a → a) (measure: a → Nat)
    (shrinks: (y: a) → Not (step y = y) → measure (step y) < measure y) (h: step x = x):
    Nat.iterateUntilStable x step measure shrinks = x :=
  rewrite Nat.iterateUntilStable.unfold x step measure shrinks in
  Nat.untilStableDecYes (step x = x) x (Nat.iterateUntilStable (step x) step measure shrinks) h (DecEq.decide (step x) x)

-- A value `step` changes goes on from the changed value.
theorem Nat.iterateUntilStableStep [auto eq: DecEq a] (x: a) (step: a → a) (measure: a → Nat)
    (shrinks: (y: a) → Not (step y = y) → measure (step y) < measure y) (h: Not (step x = x)):
    Nat.iterateUntilStable x step measure shrinks = Nat.iterateUntilStable (step x) step measure shrinks :=
  rewrite Nat.iterateUntilStable.unfold x step measure shrinks in
  Nat.untilStableDecNo (step x = x) x (Nat.iterateUntilStable (step x) step measure shrinks) h (DecEq.decide (step x) x)

-- What it returns is a fixed point: `step` leaves it alone.
theorem Nat.iterateUntilStableFixed [auto eq: DecEq a] (x: a) (step: a → a) (measure: a → Nat)
    (shrinks: (y: a) → Not (step y = y) → measure (step y) < measure y):
    step (Nat.iterateUntilStable x step measure shrinks) = Nat.iterateUntilStable x step measure shrinks
    decreasing measure x
:=
  rewrite Nat.iterateUntilStable.unfold x step measure shrinks in
  match DecEq.decide (step x) x with
    | Yes y => y
    | No n => Nat.iterateUntilStableFixed (step x) step measure shrinks [decreasing := shrinks x n]
