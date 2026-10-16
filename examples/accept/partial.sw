-- Partial definitions (docs/proposals/partial.md): code that might not
-- finish says `Partial` in its type, and so does everything that runs it.
-- Only `stitchwort run` and the playground run it; these are checked, and
-- crates/driver/tests/partial.rs runs them and counts their ticks.

-- Not recursive: an ordinary definition whose result is partial.
immediate : Nat -> {Partial} Nat
immediate n = n + 1

-- Calls to partial functions run in order, in partial code.
twice : Nat -> {Partial} Nat
twice n =
  let a = immediate n
  immediate a

-- Recursion with no visible bound.
collatzSteps : Nat -> {Partial} Nat
collatzSteps 1 = 0
collatzSteps n = 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

-- A search that loops forever if nothing satisfies `p`.
firstFrom : (Nat -> Bool) -> Nat -> {Partial} Nat
firstFrom p n = if p n then n else firstFrom p (n + 1)

-- Would pass the termination checker, but says `Partial`, so it's
-- translated like the others.
sumTo : Nat -> {Partial} Nat
sumTo 0 = 0
sumTo n = n + sumTo (n - 1)

-- Two recursive calls, one after the other.
fib : Nat -> {Partial} Nat
fib n = if leq n 1 then n else fib (n - 1) + fib (n - 2)

-- Recursion that never finishes.
spin : Nat -> {Partial} Nat
spin n = spin (n + 1)

-- Mutual recursion: one group, one loop.
isEven : Nat -> {Partial} Bool
isEven 0 = True
isEven n = isOdd (n - 1)

isOdd : Nat -> {Partial} Bool
isOdd 0 = False
isOdd n = isEven (n - 1)

-- Hofstadter's female and male sequences: nested mutual calls.
hofF : Nat -> {Partial} Nat
hofF 0 = 1
hofF n = n - hofM (hofF (n - 1))

hofM : Nat -> {Partial} Nat
hofM 0 = 0
hofM n = n - hofF (hofM (n - 1))

-- A recursive function passed to a helper: the helper must be polymorphic
-- in the rest of its row (`| e`), so the recursive calls can make requests.
useP : (Nat -> {Partial | e} Nat) -> Nat -> {Partial | e} Nat
useP k n = k n

viaHelper : Nat -> {Partial} Nat
viaHelper 0 = 1
viaHelper n = useP viaHelper (n - 1)

-- The callback under a lambda, called twice at each level.
twiceWith : (Nat -> {Partial | e} Nat) -> Nat -> {Partial | e} Nat
twiceWith k n = k n + k n

tree : Nat -> {Partial} Nat
tree 0 = 1
tree n = twiceWith (\x -> tree x) (n - 1)

-- A partial application of a member, inside the group.
addThen : Nat -> Nat -> {Partial} Nat
addThen 0 m = m
addThen n m = useP (addThen (n - 1)) (m + 1)

-- Callbacks kept in a record that's used inside the definition.
type Handlers (e : Sig) : Type =
  | MkHandlers (onStep : Nat -> {Partial | e} Nat) (onDone : Nat -> {Partial | e} Nat)

drive : [e : Sig] -> Handlers e -> Nat -> {Partial | e} Nat
drive (MkHandlers onStep onDone) 0 = onDone 0
drive (MkHandlers onStep onDone) n = onStep n

stepper : Nat -> {Partial} Nat
stepper n = drive (MkHandlers (\m -> stepper (m - 1)) (\m -> m)) n

-- A closure over a partial function that's already defined can be returned.
retryWith : Nat -> {Partial} (Nat -> {Partial} Nat)
retryWith n = \x -> collatzSteps (x + n)

-- Type parameters are fixed: each recursive call passes them on.
mapP : (a -> {Partial | e} b) -> List a -> {Partial | e} (List b)
mapP f Nil         = Nil
mapP f (Cons x xs) = Cons (f x) (mapP f xs)

-- A total function is passed where a partial one is expected.
incrementAll : List Nat -> {Partial} (List Nat)
incrementAll xs = mapP (\x -> x + 1) xs

stepsOfAll : List Nat -> {Partial} (List Nat)
stepsOfAll xs = mapP collatzSteps xs

-- Partial code may perform abilities, and handlers' clauses may run partial
-- code (the computation a handler handles must be total).
ability Log where
  say : Nat -> {Log} ()

logged : Nat -> {Log} Nat
logged n =
  say n
  n

countLogged : Nat -> {Partial} Nat
countLogged n =
  handle logged n with
    | return x   -> x
    | say m => k -> collatzSteps m + k ()

-- Partial code with IO.
countdown : Nat -> {IO, Partial} ()
countdown 0 = print "liftoff"
countdown n =
  print (natToText n)
  countdown (n - 1)

-- Total code can mention partial functions, store them and pass them on:
-- only running one needs `Partial`.
discard : (Nat -> {Partial} Nat) -> Nat
discard f = 0

kept : Pair Nat (Nat -> {Partial} Nat)
kept = MkPair 1 collatzSteps

later : () -> {Partial} Nat
later = \u -> spin 0

test "mentioning partial functions is total" = discard collatzSteps + fst kept == 1

main : () -> {IO, Partial} ()
main u =
  print (natToText (collatzSteps 27))
  print (natToText (firstFrom (\n -> leq 100 (n * n)) 0))
  print (natToText (fib 10))
  print (if isEven 10 then "even" else "odd")
  print (natToText (hofF 10))
  print (natToText (viaHelper 5))
  print (natToText (tree 3))
  print (natToText (addThen 3 4))
  print (natToText (stepper 4))
  print (natToText (retryWith 0 27))
  print (natToText (length (incrementAll [1, 2, 3])))
  print (natToText (sumTo 100))
  print (natToText (countLogged 6))
  countdown 3
