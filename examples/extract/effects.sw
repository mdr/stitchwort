-- Pure exports that use abilities and handlers inside. The handled
-- computations are trees in the generated JS too, so multi-shot handlers
-- (resuming twice) work there as in the reference evaluator.
--
-- run: subsetSums [1, 2, 4]
-- run: subsetSums []
-- run: countUp 5
-- run: divideOrZero 7 2
-- run: divideOrZero 7 0

def sndOf: Pair a b -> b
  | MkPair x y => y

type Empty: Type

def fromEmpty: Empty -> a
  | ()

ability Choose where
  choose: () -> {Choose} Bool

ability State (s: Type) where
  get: () -> {State s} s
  put: s -> {State s} ()

ability Abort where
  abort: () -> {Abort} Empty

def allResults (prog: () -> {Choose | e} a): {e} List a :=
  handle prog() with
    | return x       => [x]
    | choose u, k    => List.append (k True) (k False)

def runState (init: s) (prog: () -> {State s | e} a): {e} Pair a s :=
  let run: s -> {e} Pair a s :=
    handle prog() with
      | return x       => st => MkPair x st
      | get u, k       => st => k st st
      | put st2, k     => st => k() st2
  run init

def toMaybe (prog: () -> {Abort | e} a): {e} Maybe a :=
  handle prog() with
    | return x      => Just x
    | abort u, k    => Nothing

-- The sum of some of the numbers, chosen one by one.
def someSum: List Nat -> {Choose} Nat
  | Nil       => 0
  | Cons x xs =>
    let rest := someSum xs
    if choose() then x + rest else rest

export def subsetSums (xs: List Nat): List Nat := allResults (u => someSum xs)

def tick: Nat -> {State Nat} ()
  | 0      => ()
  | Succ n =>
    put (get() + 1)
    tick n

export def countUp (n: Nat): Nat := sndOf (runState 0 (u => tick n))

def safeDiv (n: Nat) (d: Nat): {Abort} Nat := if h: d != 0 then n / d else fromEmpty (abort())

def orZero: Maybe Nat -> Nat
  | Nothing => 0
  | Just x  => x

export def divideOrZero (n: Nat) (d: Nat): Nat := orZero (toMaybe (u => safeDiv n d))
