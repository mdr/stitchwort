-- expect-error: E-DECREASING
-- `Counter.runFrom` and `Counter.run` do call each other, through dot calls on
-- a `Counter`, whatever `Step.run` is called.
type Step = { by: Nat }
type Counter = { limit: Nat }

def Step.run (step: Step) (n: Nat): Nat := n + step.by

def Counter.runFrom (counter: Counter) (left: Nat) (n: Nat): Nat
    decreasing left
:=
  if h: 0 < left then counter.run else n

def Counter.run (counter: Counter): Nat := counter.runFrom counter.limit 0
