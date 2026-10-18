-- handle with return and operation clauses; alignment of => kept. (The old
-- syntax allows only a name, `_` or `()` as a clause argument, so no tuple.)

ability State (s : Type) where
  get : () -> {State s} s
  put : s -> {State s} ()

ability Swap where
  swap : Pair Nat Nat -> {Swap} Nat

def runState (init : s) (prog : () -> {State s | e} a) : {e} Pair a s :=
  let run : s -> {e} Pair a s :=
    handle prog () with
      | return x       => \st => MkPair x st
      | get u, k       => \st => k st st
      | put st2, k     => \st => k () st2
  run init

def runSwap (prog : () -> {Swap | e} Nat) : {e} Nat :=
  handle prog () with
    | return x => x
    | swap p, k   => k (Pair.fst p + Pair.snd p)
