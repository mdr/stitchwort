-- Partial definitions (docs/proposals/partial.md): code that might not
-- finish says `Partial` in its type, and so does everything that runs it.
-- Only `stitchwort run` and the playground run it; these are checked, and
-- crates/driver/tests/partial.rs runs them and counts their ticks.

-- Not recursive: an ordinary definition whose result is partial.
import Std.Effect (Sig)
import Std (List, Nat, Pair)

def immediate (n: Nat): {Partial} Nat := n + 1

-- Calls to partial functions run in order, in partial code.
def twice (n: Nat): {Partial} Nat :=
  let a := immediate n
  immediate a

-- Recursion with no visible bound.
def collatzSteps: Nat -> {Partial} Nat
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

-- A search that loops forever if nothing satisfies `p`.
def firstFrom (p: Nat -> Bool) (n: Nat): {Partial} Nat := if p n then n else firstFrom p (n + 1)

-- Would pass the termination checker, but says `Partial`, so it's
-- translated like the others.
def sumTo: Nat -> {Partial} Nat
  | 0 => 0
  | n => n + sumTo (n - 1)

-- Two recursive calls, one after the other.
def fib (n: Nat): {Partial} Nat := if Nat.leq n 1 then n else fib (n - 1) + fib (n - 2)

-- Recursion that never finishes.
def spin (n: Nat): {Partial} Nat := spin (n + 1)

-- Mutual recursion: one group, one loop.
def isEven: Nat -> {Partial} Bool
  | 0 => True
  | n => isOdd (n - 1)

def isOdd: Nat -> {Partial} Bool
  | 0 => False
  | n => isEven (n - 1)

-- Hofstadter's female and male sequences: nested mutual calls.
def hofF: Nat -> {Partial} Nat
  | 0 => 1
  | n => n - hofM (hofF (n - 1))

def hofM: Nat -> {Partial} Nat
  | 0 => 0
  | n => n - hofF (hofM (n - 1))

-- A recursive function passed to a helper: the helper must be polymorphic
-- in the rest of its row (`| e`), so the recursive calls can make requests.
def useP (k: Nat -> {Partial | e} Nat) (n: Nat): {Partial | e} Nat := k n

def viaHelper: Nat -> {Partial} Nat
  | 0 => 1
  | n => useP viaHelper (n - 1)

-- The callback under a lambda, called twice at each level.
def twiceWith (k: Nat -> {Partial | e} Nat) (n: Nat): {Partial | e} Nat := k n + k n

def tree: Nat -> {Partial} Nat
  | 0 => 1
  | n => twiceWith (x => tree x) (n - 1)

-- A partial application of a member, inside the group.
def addThen: Nat -> Nat -> {Partial} Nat
  | 0, m => m
  | n, m => useP (addThen (n - 1)) (m + 1)

-- Callbacks kept in a record that's used inside the definition.
type Handlers (e: Sig): Type =
  | MkHandlers (onStep: Nat -> {Partial | e} Nat) (onDone: Nat -> {Partial | e} Nat)

def drive: [e: Sig] -> Handlers e -> Nat -> {Partial | e} Nat
  | MkHandlers onStep onDone, 0 => onDone 0
  | MkHandlers onStep onDone, n => onStep n

def stepper (n: Nat): {Partial} Nat := drive (MkHandlers (m => stepper (m - 1)) (m => m)) n

-- A closure over a partial function that's already defined can be returned.
def retryWith (n: Nat): {Partial} (Nat -> {Partial} Nat) := x => collatzSteps (x + n)

-- Type parameters are fixed: each recursive call passes them on.
def mapP (f: a -> {Partial | e} b): List a -> {Partial | e} (List b)
  | Nil       => Nil
  | Cons x xs => Cons (f x) (mapP f xs)

-- A total function is passed where a partial one is expected.
def incrementAll (xs: List Nat): {Partial} (List Nat) := mapP (x => x + 1) xs

def stepsOfAll (xs: List Nat): {Partial} (List Nat) := mapP collatzSteps xs

-- Partial code may perform abilities, and handlers' clauses may run partial
-- code (the computation a handler handles must be total).
ability Log where
  say: Nat -> {Log} ()

def logged (n: Nat): {Log} Nat :=
  say n
  n

def countLogged (n: Nat): {Partial} Nat :=
  handle logged n with
    | return x   => x
    | say m, k => collatzSteps m + k()

-- Partial code with IO.
def countdown: Nat -> {IO, Partial} ()
  | 0 => IO.print "liftoff"
  | n =>
    IO.print (Nat.toText n)
    countdown (n - 1)

-- Total code can mention partial functions, store them and pass them on:
-- only running one needs `Partial`.
def discard (f: Nat -> {Partial} Nat): Nat := 0

def kept: Pair Nat (Nat -> {Partial} Nat) := MkPair 1 collatzSteps

def later: () -> {Partial} Nat := u => spin 0

test "mentioning partial functions is total" := discard collatzSteps + Pair.fst kept == 1

def main(): {IO, Partial} () :=
  IO.print (Nat.toText (collatzSteps 27))
  IO.print (Nat.toText (firstFrom (n => Nat.leq 100 (n * n)) 0))
  IO.print (Nat.toText (fib 10))
  IO.print (if isEven 10 then "even" else "odd")
  IO.print (Nat.toText (hofF 10))
  IO.print (Nat.toText (viaHelper 5))
  IO.print (Nat.toText (tree 3))
  IO.print (Nat.toText (addThen 3 4))
  IO.print (Nat.toText (stepper 4))
  IO.print (Nat.toText (retryWith 0 27))
  IO.print (Nat.toText (List.length (incrementAll [1, 2, 3])))
  IO.print (Nat.toText (sumTo 100))
  IO.print (Nat.toText (countLogged 6))
  countdown 3
