-- Abilities and handlers (docs/proposals/abilities.md). The same semantic
-- tests as handlers.sw, written in the source syntax: the compiler
-- translates them into `Comp` trees, and the kernel checks the result.

import Effect (Comp)

def fstOf : Pair a b -> a
  | MkPair x y => x

def sndOf : Pair a b -> b
  | MkPair x y => y

type Empty : Type

def fromEmpty : Empty -> a
  | ()

def eqNats : List Nat -> List Nat -> Bool
  | Nil,       Nil       => True
  | Cons x xs, Cons y ys => if x == y then eqNats xs ys else False
  | _,         _         => False

def eqPairs : List (Pair Nat Nat) -> List (Pair Nat Nat) -> Bool
  | Nil,                  Nil                  => True
  | Cons (MkPair a b) xs, Cons (MkPair c d) ys =>
    if a == c then (if b == d then eqPairs xs ys else False) else False
  | _,                    _                    => False

-- Abilities

ability State (s : Type) where
  get : () -> {State s} s
  put : s -> {State s} ()

ability Choose where
  choose : () -> {Choose} Bool

ability Abort where
  abort : () -> {Abort} Empty

ability Log where
  say : Nat -> {Log} ()

-- Handlers. Each removes one ability from any row (`e` is the rest).

-- The handler builds a function waiting for the state: `k st` resumes with
-- `st`, giving another such function.
def runState (init : s) (prog : () -> {State s | e} a) : {e} Pair a s :=
  let run : s -> {e} Pair a s :=
    handle prog () with
      | return x       => \st => MkPair x st
      | get u, k       => \st => k st st
      | put st2, k     => \st => k () st2
  run init

-- Resumes twice: every outcome, `True` first.
def allResults (prog : () -> {Choose | e} a) : {e} List a :=
  handle prog () with
    | return x       => [x]
    | choose u, k    => List.append (k True) (k False)

-- Never resumes.
def toMaybe (prog : () -> {Abort | e} a) : {e} Maybe a :=
  handle prog () with
    | return x      => Just x
    | abort u, k    => Nothing

-- Collects what's said, in order.
def collect (prog : () -> {Log | e} a) : {e} Pair (List Nat) a :=
  handle prog () with
    | return x     => MkPair Nil x
    | say n, k     =>
      let rest := k ()
      MkPair (Cons n (fstOf rest)) (sndOf rest)

-- Handler order

-- choose, then put 1 if it said yes, then get
def p () : {State Nat, Choose} Nat :=
  let b := choose ()
  if b then put 1 else ()
  get ()

test "state inside choice: each branch has its own state" :=
  eqPairs (allResults (\u => runState 0 p)) [MkPair 1 1, MkPair 0 0]

test "choice inside state: the state threads through" :=
  let r := runState 0 (\u => allResults p)
  if eqNats (fstOf r) [1, 1] then sndOf r == 1 else False

-- A clause's own `get` goes to the next `State` handler out.
def scaleGets (prog : () -> {State Nat | e} a) : {State Nat | e} a :=
  handle prog () with
    | return x      => x
    | get u, k      =>
      let m := get ()
      k (m * 10)
    | put n, k      =>
      put n
      k ()

test "a clause's own get goes to the outer handler" :=
  fstOf (runState 5 (\u => scaleGets (\v => get () + 1))) == 51

-- Abort

def safeDiv (n : Nat) (d : Nat) : {Abort} Nat :=
  if h : d != 0 then n / d else fromEmpty (abort ())

def orZero : Maybe Nat -> Nat
  | Nothing => 0
  | Just x  => x

test "abort stops" := orZero (toMaybe (\u => safeDiv 7 0)) == 0
test "no abort" :=
  orZero (toMaybe (\u => safeDiv 100 (safeDiv 7 2))) == 33

-- Order of operations: arguments run left to right, and lines in order.

def counted () : {Log} Nat :=
  say 1
  let x := say 2
  say 3
  4

test "lines run in order" := eqNats (fstOf (collect counted)) [1, 2, 3]

def loud (n : Nat) : {Log} Nat :=
  say n
  n

test "arguments run left to right" :=
  let r := collect (\u => loud 1 + loud 2 * loud 3)
  if eqNats (fstOf r) [1, 2, 3] then sndOf r == 7 else False

-- An operation's argument can perform operations too.
def increment () : {State Nat} () := put (get () + 1)

test "an effectful argument" :=
  sndOf (runState 41 (\u => increment ())) == 42

-- Functions in state

-- A function using `Choose` stored in `State`: fine, because its effects
-- don't refer back to the state's own ability.
def storeAndRun () : {State (Nat -> {Choose} Nat)} (List Nat) :=
  put (\n => if choose () then n + 10 else n)
  let g := get ()
  allResults (\v => g 5)

test "an effectful function in state" :=
  eqNats (fstOf (runState ((\n => n) : Nat -> {Choose} Nat) storeAndRun)) [15, 5]
