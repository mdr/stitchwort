-- `Step.run` shares its short name with `Counter.run`, which calls
-- `Counter.runFrom`. A dot call whose receiver has a written type means that
-- type's method only, so `Counter.runFrom` isn't in a group with `Counter.run`
-- and its `decreasing` is accepted.
type Step = { by: Nat }
type Counter = { limit: Nat }

def Step.run (step: Step) (n: Nat): Nat := n + step.by

def Counter.runFrom (counter: Counter) (step: Step) (left n: Nat): Nat
    decreasing left
:=
  if h: 0 < left then Counter.runFrom counter step (left - 1) (step.run n) [decreasing := omega] else n

def Counter.run (counter: Counter) (step: Step): Nat := counter.runFrom step counter.limit 0

-- The receiver's type written by an annotation.
def Counter.runOnes (counter: Counter) (left n: Nat): Nat
    decreasing left
:=
  if h: 0 < left then Counter.runOnes counter (left - 1) (({ by = 1 }: Step).run n) [decreasing := omega] else n

def Counter.runAll (counter: Counter): Nat := counter.runOnes counter.limit 0
