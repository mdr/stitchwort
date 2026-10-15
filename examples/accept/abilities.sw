-- Abilities and handlers (docs/proposals/abilities.md). The same semantic
-- tests as handlers.sw, written in the source syntax: the compiler
-- translates them into `Comp` trees, and the kernel checks the result.

type Pair (a : Type) (b : Type) : Type =
  | MkPair (fst : a) (snd : b)

fstOf : Pair a b -> a
fstOf (MkPair x y) = x

sndOf : Pair a b -> b
sndOf (MkPair x y) = y

type Empty : Type

fromEmpty : Empty -> a
fromEmpty ()

eqNats : List Nat -> List Nat -> Bool
eqNats Nil         Nil         = True
eqNats (Cons x xs) (Cons y ys) = if x == y then eqNats xs ys else False
eqNats _           _           = False

eqPairs : List (Pair Nat Nat) -> List (Pair Nat Nat) -> Bool
eqPairs Nil                    Nil                    = True
eqPairs (Cons (MkPair a b) xs) (Cons (MkPair c d) ys) =
  if a == c then (if b == d then eqPairs xs ys else False) else False
eqPairs _                      _                      = False

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
runState : s -> (() -> {State s | e} a) -> {e} Pair a s
runState init prog =
  let run : s -> {e} Pair a s =
    handle prog () with
      | return x       -> \st -> MkPair x st
      | get u => k     -> \st -> k st st
      | put st2 => k   -> \st -> k () st2
  run init

-- Resumes twice: every outcome, `True` first.
allResults : (() -> {Choose | e} a) -> {e} List a
allResults prog =
  handle prog () with
    | return x       -> [x]
    | choose u => k  -> append (k True) (k False)

-- Never resumes.
toMaybe : (() -> {Abort | e} a) -> {e} Maybe a
toMaybe prog =
  handle prog () with
    | return x      -> Just x
    | abort u => k  -> Nothing

-- Collects what's said, in order.
collect : (() -> {Log | e} a) -> {e} Pair (List Nat) a
collect prog =
  handle prog () with
    | return x     -> MkPair Nil x
    | say n => k   ->
      let rest = k ()
      MkPair (Cons n (fstOf rest)) (sndOf rest)

-- Handler order

-- choose, then put 1 if it said yes, then get
p : () -> {State Nat, Choose} Nat
p u =
  let b = choose ()
  if b then put 1 else ()
  get ()

test "state inside choice: each branch has its own state" =
  eqPairs (allResults (\u -> runState 0 p)) [MkPair 1 1, MkPair 0 0]

test "choice inside state: the state threads through" =
  let r = runState 0 (\u -> allResults p)
  if eqNats (fstOf r) [1, 1] then sndOf r == 1 else False

-- A clause's own `get` goes to the next `State` handler out.
scaleGets : (() -> {State Nat | e} a) -> {State Nat | e} a
scaleGets prog =
  handle prog () with
    | return x      -> x
    | get u => k    ->
      let m = get ()
      k (m * 10)
    | put n => k    ->
      put n
      k ()

test "a clause's own get goes to the outer handler" =
  fstOf (runState 5 (\u -> scaleGets (\v -> get () + 1))) == 51

-- Abort

safeDiv : Nat -> Nat -> {Abort} Nat
safeDiv n d =
  if h : d != 0 then n / d else fromEmpty (abort ())

orZero : Maybe Nat -> Nat
orZero Nothing  = 0
orZero (Just x) = x

test "abort stops" = orZero (toMaybe (\u -> safeDiv 7 0)) == 0
test "no abort" =
  orZero (toMaybe (\u -> safeDiv 100 (safeDiv 7 2))) == 33

-- Order of operations: arguments run left to right, and lines in order.

counted : () -> {Log} Nat
counted u =
  say 1
  let x = say 2
  say 3
  4

test "lines run in order" = eqNats (fstOf (collect counted)) [1, 2, 3]

loud : Nat -> {Log} Nat
loud n =
  say n
  n

test "arguments run left to right" =
  let r = collect (\u -> loud 1 + loud 2 * loud 3)
  if eqNats (fstOf r) [1, 2, 3] then sndOf r == 7 else False

-- An operation's argument can perform operations too.
increment : () -> {State Nat} ()
increment u = put (get () + 1)

test "an effectful argument" =
  sndOf (runState 41 (\u -> increment ())) == 42

-- Functions in state

-- A function using `Choose` stored in `State`: fine, because its effects
-- don't refer back to the state's own ability.
storeAndRun : () -> {State (Nat -> {Choose} Nat)} (List Nat)
storeAndRun u =
  put (\n -> if choose () then n + 10 else n)
  let g = get ()
  allResults (\v -> g 5)

test "an effectful function in state" =
  eqNats (fstOf (runState ((\n -> n) : Nat -> {Choose} Nat) storeAndRun)) [15, 5]
