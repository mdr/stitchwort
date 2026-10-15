-- Less common shapes of effectful code, each checked against an exact
-- result. (abilities.sw has the main semantic tests.)

type Pair (a : Type) (b : Type) : Type =
  | MkPair (fst : a) (snd : b)

fstOf : Pair a b -> a
fstOf (MkPair x y) = x

sndOf : Pair a b -> b
sndOf (MkPair x y) = y

eqNats : List Nat -> List Nat -> Bool
eqNats Nil         Nil         = True
eqNats (Cons x xs) (Cons y ys) = if x == y then eqNats xs ys else False
eqNats _           _           = False

ability State (s : Type) where
  get : () -> {State s} s
  put : s -> {State s} ()

ability Log where
  say : Nat -> {Log} ()

ability Choose where
  choose : () -> {Choose} Bool

ability Ask where
  ask : () -> {Ask} Nat

runState : s -> (() -> {State s | e} a) -> {e} Pair a s
runState init prog =
  let run : s -> {e} Pair a s =
    handle prog () with
      | return x       -> \st -> MkPair x st
      | get () => k    -> \st -> k st st
      | put st2 => k   -> \st -> k () st2
  run init

collect : (() -> {Log | e} a) -> {e} Pair (List Nat) a
collect prog =
  handle prog () with
    | return x     -> MkPair Nil x
    | say n => k   ->
      let rest = k ()
      MkPair (Cons n (fstOf rest)) (sndOf rest)

allResults : (() -> {Choose | e} a) -> {e} List a
allResults prog =
  handle prog () with
    | return x       -> [x]
    | choose _ => k  -> append (k True) (k False)

answer : Nat -> (() -> {Ask | e} a) -> {e} a
answer n prog =
  handle prog () with
    | return x     -> x
    | ask () => k  -> k n

-- Pure lines and pure `let`s among effectful ones.
mixed : () -> {State Nat} Nat
mixed u =
  let x = 5
  3
  let y = get ()
  x + y

test "pure let and pure lines" = fstOf (runState 2 mixed) == 7

-- Effects inside list literals, annotations and named arguments, run left
-- to right.
idNat : [a : Type] -> a -> a
idNat x = x

loud : Nat -> {Log} Nat
loud n =
  say n
  n

shapes : () -> {Log} (List Nat)
shapes u = [(loud 1 : Nat), idNat [a := Nat] (loud 2), length [loud 3]]

test "list, annotation, named argument" =
  let r = collect shapes
  if eqNats (fstOf r) [1, 2, 3] then eqNats (sndOf r) [1, 2, 1] else False

-- A computation that isn't a function.
current : {State Nat} Nat
current = get ()

test "a computation used twice runs twice" =
  fstOf (runState 4 (\u -> current + current)) == 8

-- A value read first and captured by a pure function.
adder : () -> {State Nat} (Nat -> Nat)
adder u =
  let s = get ()
  \n -> n + s

test "captured" = (fstOf (runState 3 adder)) 4 == 7

-- Four abilities. Handlers remove them one at a time, from the inside out,
-- in an order different from the declaration order.
everything : () -> {State Nat, Log, Choose, Ask} Nat
everything u =
  let n = ask ()
  say n
  if choose () then put (get () + n) else say 0
  get ()

-- `say 10` happens once, before the choice; the `False` branch then says 0.
-- `collect` is outside `allResults`, so both branches share one log, and
-- `runState` is outermost, so they share the state: the `True` branch sets
-- it to 11, which the `False` branch then reads.
test "four abilities, handled in another order" =
  let r = runState 1 (\u -> collect (\v -> allResults (\w -> answer 10 everything)))
  let said = fstOf (fstOf r)
  let results = sndOf (fstOf r)
  if eqNats said [10, 0] then (if eqNats results [11, 11] then sndOf r == 11 else False) else False

-- Choice outermost: each branch has its own state and log. True: says 10,
-- state 11. False: says 10 then 0, state 1.
pairNats : List (Pair (Pair (List Nat) Nat) Nat) -> List Nat
pairNats Nil                                 = Nil
pairNats (Cons (MkPair (MkPair said x) s) r) = append said (Cons x (Cons s (pairNats r)))

test "four abilities, choice outermost" =
  let r = allResults (\u -> runState 1 (\v -> collect (\w -> answer 10 everything)))
  eqNats (pairNats r) [10, 11, 11, 10, 0, 1, 1]

-- A function that needs only some of the abilities in its caller's row.
logTwice : Nat -> {Log} ()
logTwice n =
  say n
  say n

bigger : () -> {State Nat, Log, Ask} Nat
bigger u =
  logTwice (ask ())
  get ()

test "a smaller row inside a bigger one" =
  let r = runState 7 (\u -> collect (\v -> answer 2 bigger))
  if eqNats (fstOf (fstOf r)) [2, 2] then sndOf (fstOf r) == 7 else False

-- A partially applied effectful function is a value (it doesn't run yet).
pickFrom : Nat -> () -> {Choose} Nat
pickFrom n u = if choose () then n else 0

test "a partial application is passed, not run" =
  eqNats (allResults (pickFrom 3)) [3, 0]

-- A pure `let` in a function whose row and result mention variables.
peek : () -> {State s | e} s
peek u =
  let unused = 1
  get ()

test "a pure let under a row variable" = fstOf (runState 9 (\u -> peek ())) == 9

-- A handler inside a function with other abilities: what it doesn't handle
-- (`say`) goes out to the function's own row.
choicesLogged : () -> {Log} (List Nat)
choicesLogged u =
  allResults (\v ->
    say 1
    if choose () then 10 else 20)

-- `say 1` runs once, before the choice; both results come back.
test "a handler forwards to a concrete row" =
  let r = collect choicesLogged
  if eqNats (fstOf r) [1] then eqNats (sndOf r) [10, 20] else False

-- A row-polymorphic function passed where a concrete row, in another
-- order, is expected.
anyChoice : () -> {Choose | e} Nat
anyChoice u = if choose () then 1 else 2

useBoth : (() -> {State Nat, Choose} Nat) -> {State Nat, Choose} Nat
useBoth f = f () + get ()

test "a row-polymorphic function, reordered" =
  eqNats (allResults (\u -> fstOf (runState 5 (\v -> useBoth anyChoice)))) [6, 7]

-- A function that performs fewer abilities than a parameter allows.
onlyChoice : () -> {Choose} Nat
onlyChoice u = if choose () then 1 else 2

test "fewer abilities than allowed" =
  eqNats (allResults (\u -> fstOf (runState 5 (\v -> useBoth onlyChoice)))) [6, 7]

-- A `handle` written inside a function with a concrete row: `say` isn't
-- handled here, so it's forwarded to the function's own `Log`.
chooseAndSay : () -> {Choose, Log} Nat
chooseAndSay u =
  say 5
  if choose () then 1 else 2

handledHere : () -> {Log} (List Nat)
handledHere u =
  handle chooseAndSay () with
    | return x       -> [x]
    | choose _ => k  -> append (k True) (k False)

test "a handle expression forwards to a concrete row" =
  let r = collect handledHere
  if eqNats (fstOf r) [5] then eqNats (sndOf r) [1, 2] else False
