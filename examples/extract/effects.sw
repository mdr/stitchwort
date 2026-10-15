-- Pure exports that use abilities and handlers inside. The handled
-- computations are trees in the generated JS too, so multi-shot handlers
-- (resuming twice) work there as in the reference evaluator.
--
-- run: subsetSums [1, 2, 4]
-- run: subsetSums []
-- run: countUp 5
-- run: divideOrZero 7 2
-- run: divideOrZero 7 0

type Pair (a : Type) (b : Type) : Type =
  | MkPair (fst : a) (snd : b)

sndOf : Pair a b -> b
sndOf (MkPair x y) = y

type Empty : Type

fromEmpty : Empty -> a
fromEmpty ()

ability Choose where
  choose : () -> {Choose} Bool

ability State (s : Type) where
  get : () -> {State s} s
  put : s -> {State s} ()

ability Abort where
  abort : () -> {Abort} Empty

allResults : (() -> {Choose | e} a) -> {e} List a
allResults prog =
  handle prog () with
    | return x       -> [x]
    | choose u => k  -> append (k True) (k False)

runState : s -> (() -> {State s | e} a) -> {e} Pair a s
runState init prog =
  let run : s -> {e} Pair a s =
    handle prog () with
      | return x       -> \st -> MkPair x st
      | get u => k     -> \st -> k st st
      | put st2 => k   -> \st -> k () st2
  run init

toMaybe : (() -> {Abort | e} a) -> {e} Maybe a
toMaybe prog =
  handle prog () with
    | return x      -> Just x
    | abort u => k  -> Nothing

-- The sum of some of the numbers, chosen one by one.
someSum : List Nat -> {Choose} Nat
someSum Nil         = 0
someSum (Cons x xs) =
  let rest = someSum xs
  if choose () then x + rest else rest

export
subsetSums : List Nat -> List Nat
subsetSums xs = allResults (\u -> someSum xs)

tick : Nat -> {State Nat} ()
tick 0        = ()
tick (Succ n) =
  put (get () + 1)
  tick n

export
countUp : Nat -> Nat
countUp n = sndOf (runState 0 (\u -> tick n))

safeDiv : Nat -> Nat -> {Abort} Nat
safeDiv n d = if h : d != 0 then n / d else fromEmpty (abort ())

orZero : Maybe Nat -> Nat
orZero Nothing  = 0
orZero (Just x) = x

export
divideOrZero : Nat -> Nat -> Nat
divideOrZero n d = orZero (toMaybe (\u -> safeDiv n d))
