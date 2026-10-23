-- A local definition in an effectful block. `add` runs in the `State Nat`
-- ability of its owner, and the handler below runs the whole thing.

ability State (s: Type) where
  get: () -> {State s} s
  put: s -> {State s} ()

def runState (init: s) (prog: () -> {State s | e} a): {e} Pair a s :=
  let run: s -> {e} Pair a s :=
    handle prog() with
      | return x => st => MkPair x st
      | get u, k => st => k st st
      | put st2, k => st => k() st2
  run init

def tally (xs: List Nat) (u: ()): {State Nat} Nat :=
  let start := get()
  def add: List Nat -> {State Nat} ()
    | Nil => ()
    | Cons x rest =>
      put (get() + x)
      add rest
  add xs
  get() + start

def fstOf: Pair a b -> a
  | MkPair x y => x

test "tally" := fstOf (runState 10 (tally [1, 2, 3])) == 26
