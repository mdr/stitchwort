-- Less common shapes of effectful code, each checked against an exact
-- result. (abilities.sw has the main semantic tests.)

def fstOf : Pair a b -> a
  | MkPair x y => x

def sndOf : Pair a b -> b
  | MkPair x y => y

def eqNats : List Nat -> List Nat -> Bool
  | Nil,       Nil       => True
  | Cons x xs, Cons y ys => if x == y then eqNats xs ys else False
  | _,         _         => False

ability State (s : Type) where
  get : () -> {State s} s
  put : s -> {State s} ()

ability Log where
  say : Nat -> {Log} ()

ability Choose where
  choose : () -> {Choose} Bool

ability Ask where
  ask : () -> {Ask} Nat

def runState (init : s) (prog : () -> {State s | e} a) : {e} Pair a s :=
  let run : s -> {e} Pair a s :=
    handle prog () with
      | return x       => \st => MkPair x st
      | get (), k      => \st => k st st
      | put st2, k     => \st => k () st2
  run init

def collect (prog : () -> {Log | e} a) : {e} Pair (List Nat) a :=
  handle prog () with
    | return x     => MkPair Nil x
    | say n, k     =>
      let rest := k ()
      MkPair (Cons n (fstOf rest)) (sndOf rest)

def allResults (prog : () -> {Choose | e} a) : {e} List a :=
  handle prog () with
    | return x       => [x]
    | choose _, k    => List.append (k True) (k False)

def answer (n : Nat) (prog : () -> {Ask | e} a) : {e} a :=
  handle prog () with
    | return x     => x
    | ask (), k    => k n

-- Pure lines and pure `let`s among effectful ones.
def mixed () : {State Nat} Nat :=
  let x := 5
  3
  let y := get ()
  x + y

test "pure let and pure lines" := fstOf (runState 2 mixed) == 7

-- Effects inside list literals, annotations and named arguments, run left
-- to right.
def idNat [a : Type] (x : a) : a := x

def loud (n : Nat) : {Log} Nat :=
  say n
  n

def shapes () : {Log} (List Nat) := [(loud 1 : Nat), idNat [a := Nat] (loud 2), List.length [loud 3]]

test "list, annotation, named argument" :=
  let r := collect shapes
  if eqNats (fstOf r) [1, 2, 3] then eqNats (sndOf r) [1, 2, 1] else False

-- A computation that isn't a function.
def current : {State Nat} Nat := get ()

test "a computation used twice runs twice" :=
  fstOf (runState 4 (\u => current + current)) == 8

-- A value read first and captured by a pure function.
def adder () : {State Nat} (Nat -> Nat) :=
  let s := get ()
  \n => n + s

test "captured" := (fstOf (runState 3 adder)) 4 == 7

-- Four abilities. Handlers remove them one at a time, from the inside out,
-- in an order different from the declaration order.
def everything () : {State Nat, Log, Choose, Ask} Nat :=
  let n := ask ()
  say n
  if choose () then put (get () + n) else say 0
  get ()

-- `say 10` happens once, before the choice; the `False` branch then says 0.
-- `collect` is outside `allResults`, so both branches share one log, and
-- `runState` is outermost, so they share the state: the `True` branch sets
-- it to 11, which the `False` branch then reads.
test "four abilities, handled in another order" :=
  let r := runState 1 (\u => collect (\v => allResults (\w => answer 10 everything)))
  let said := fstOf (fstOf r)
  let results := sndOf (fstOf r)
  if eqNats said [10, 0] then (if eqNats results [11, 11] then sndOf r == 11 else False) else False

-- Choice outermost: each branch has its own state and log. True: says 10,
-- state 11. False: says 10 then 0, state 1.
def pairNats : List (Pair (Pair (List Nat) Nat) Nat) -> List Nat
  | Nil                               => Nil
  | Cons (MkPair (MkPair said x) s) r => List.append said (Cons x (Cons s (pairNats r)))

test "four abilities, choice outermost" :=
  let r := allResults (\u => runState 1 (\v => collect (\w => answer 10 everything)))
  eqNats (pairNats r) [10, 11, 11, 10, 0, 1, 1]

-- A function that needs only some of the abilities in its caller's row.
def logTwice (n : Nat) : {Log} () :=
  say n
  say n

def bigger () : {State Nat, Log, Ask} Nat :=
  logTwice (ask ())
  get ()

test "a smaller row inside a bigger one" :=
  let r := runState 7 (\u => collect (\v => answer 2 bigger))
  if eqNats (fstOf (fstOf r)) [2, 2] then sndOf (fstOf r) == 7 else False

-- A partially applied effectful function is a value (it doesn't run yet).
def pickFrom (n : Nat) () : {Choose} Nat := if choose () then n else 0

test "a partial application is passed, not run" :=
  eqNats (allResults (pickFrom 3)) [3, 0]

-- A pure `let` in a function whose row and result mention variables.
def peek () : {State s | e} s :=
  let unused := 1
  get ()

test "a pure let under a row variable" := fstOf (runState 9 (\u => peek ())) == 9

-- A handler inside a function with other abilities: what it doesn't handle
-- (`say`) goes out to the function's own row.
def choicesLogged () : {Log} (List Nat) :=
  allResults (\v =>
    say 1
    if choose () then 10 else 20)

-- `say 1` runs once, before the choice; both results come back.
test "a handler forwards to a concrete row" :=
  let r := collect choicesLogged
  if eqNats (fstOf r) [1] then eqNats (sndOf r) [10, 20] else False

-- A row-polymorphic function passed where a concrete row, in another
-- order, is expected.
def anyChoice () : {Choose | e} Nat := if choose () then 1 else 2

def useBoth (f : () -> {State Nat, Choose} Nat) : {State Nat, Choose} Nat := f () + get ()

test "a row-polymorphic function, reordered" :=
  eqNats (allResults (\u => fstOf (runState 5 (\v => useBoth anyChoice)))) [6, 7]

-- A function that performs fewer abilities than a parameter allows.
def onlyChoice () : {Choose} Nat := if choose () then 1 else 2

test "fewer abilities than allowed" :=
  eqNats (allResults (\u => fstOf (runState 5 (\v => useBoth onlyChoice)))) [6, 7]

-- A `handle` written inside a function with a concrete row: `say` isn't
-- handled here, so it's forwarded to the function's own `Log`.
def chooseAndSay () : {Choose, Log} Nat :=
  say 5
  if choose () then 1 else 2

def handledHere () : {Log} (List Nat) :=
  handle chooseAndSay () with
    | return x       => [x]
    | choose _, k    => List.append (k True) (k False)

test "a handle expression forwards to a concrete row" :=
  let r := collect handledHere
  if eqNats (fstOf r) [5] then eqNats (sndOf r) [1, 2] else False

-- An operation on its own is a function: `choose` is `\x -> choose x`.
def countTrue (f : () -> {Choose} Bool) : {Choose} Nat := if f () then (if f () then 2 else 1) else 0

test "an operation as a value" := List.length (allResults choose) == 2
test "passing an operation" := eqNats (allResults (\u => countTrue choose)) [2, 1, 0]
