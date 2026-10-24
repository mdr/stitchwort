-- Named arguments in computations (docs/proposals/named-arguments.md §4.5):
-- the arguments run in the order they're written, the stages of a curried
-- effectful function after all of them, in parameter order; a call that
-- leaves a parameter out runs its head, receiver, piped value and given
-- arguments once, at the call, and the stages before the parameter left out
-- once too.

ability Log where
  say: Nat -> {Log} ()

-- What a computation says, in order, and its result.
def collect (program: () -> {Log | e} a): {e} (List Nat, a) :=
  handle program() with
    | return x => ([], x)
    | say n, k =>
      let rest := k()
      (Cons n rest.fst, rest.snd)

-- Says `n`, then returns it.
def given (n: Nat): {Log} Nat :=
  say n
  n

-- A curried function with a stage: says 100 + x when given `x`.
def staged (x: Nat): {Log} ((y: Nat) -> (z: Nat) -> Nat) :=
  say (100 + x)
  (y z => x * 100 + y * 10 + z)

def plain (a: Nat) (b: Nat) (c: Nat): Nat := a * 100 + b * 10 + c

-- Invariant 2: reordered named arguments run in written order, and the
-- stage after all of them, as in the positional call.
def reordered(): {Log} Nat := staged (z := given 3) (x := given 1) (y := given 2)
def positional(): {Log} Nat := staged (given 1) (given 2) (given 3)

test "named arguments run as written" := collect reordered == ([3, 1, 2, 101], 123)
test "positional arguments run as written" := collect positional == ([1, 2, 3, 101], 123)

-- Naming without reordering changes nothing.
def namedInOrder(): {Log} Nat := staged (x := given 1) (y := given 2) (z := given 3)
test "naming in order runs as positional" := collect namedInOrder == collect positional

-- Invariant 3: a parameter left out. The given argument and the stage
-- before the missing `y` run once, at the call; calling the function the
-- call makes twice runs neither again.
def skipping(): {Log} Nat :=
  let h := staged (z := given 3) (x := given 1)
  h 5 + h 6

test "a skip runs the call once" := collect skipping == ([3, 1, 101], 153 + 163)

-- A pure function: the given computations run once, at the call.
def skippingPure(): {Log} Nat :=
  let k := plain (c := given 3) (a := given 1)
  k 2 + k 4

test "a skip in a pure function runs the arguments once" :=
  collect skippingPure == ([3, 1], 123 + 143)

-- The value piped in runs first, then the arguments as written.
def piped(): {Log} Nat := given 7 |> plain (b := given 2) (a := given 1)

test "the piped value runs first" := collect piped == ([7, 2, 1], 127)

-- Dot notation: the receiver runs first.
type Counter = { count: Nat }

def Counter.add (counter: Counter) (by: Nat) (times: Nat): Nat := counter.count + by * times

def counterOf (n: Nat): {Log} Counter :=
  say n
  { count = n }

def dotted(): {Log} Nat := (counterOf 1).add (times := given 3) (by := given 2)

test "the receiver runs first" := collect dotted == ([1, 3, 2], 7)
