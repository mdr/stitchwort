-- R10, R11: `| P => e` with one space before `=>`, never aligned; a body on
-- the next line is at the `|` column + 2.
def runState (init: s) (prog: () -> {State s | e} a): {e} Pair a s :=
  let run: s -> {e} Pair a s :=
    handle prog() with
      | return x => st => MkPair x st
      | get u, k => st => k st st
      | put st2, k => st => k() st2
  run init

def collect (prog: () -> {Log | e} a): {e} Pair (List Nat) a :=
  handle prog() with
    | return x => MkPair Nil x
    | say n, k =>
      let rest := k()
      MkPair (Cons n (fstOf rest)) (sndOf rest)

def zip (xs: List a) (ys: List b): List (Pair a b) :=
  match xs, ys with
    | Nil, _ => Nil
    | _, Nil => Nil
    | Cons x xs, Cons y ys => Cons (MkPair x y) (zip xs ys)

def nest (x: Nat) (y: Nat): Nat :=
  match x with
    | Zero =>
      match y with
        | Zero => 0
        | Succ n => n
    | Succ m => m
