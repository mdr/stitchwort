# 7. Recursion and termination

Stitchwort has no loops; repetition is recursion, and the library's functions (`map`, `foldLeft`, `sum`, …) cover the common cases. Every function must finish, unless its type says it may not. The compiler checks this, because a proof is only meaningful if the functions it talks about return: a "proof" that loops forever would prove anything.

Most recursion is checked without any help. When it isn't, you say why the function finishes, or mark it `Partial`.

## Structural recursion

A recursive call on a part of an argument, such as the tail of a list or the `n` in `Succ n`, is accepted as it is. Each call gets a smaller piece, and the pieces run out:

<!-- snippet: recursion.sw#structural -->
```stitchwort
def length: List a → Nat
  | [] => 0
  | Cons _ rest => 1 + length rest

def factorial: Nat → Nat
  | 0 => 1
  | Succ n => Succ n * factorial n

test "structural" := length [1, 2, 3] == 3 ∧ factorial 5 == 120
```

`Succ n` is the pattern for a number that is one more than `n`, so it matches any `Nat` but 0. (`Zero` and `Succ` are `Nat`'s two constructors; number literals stand for them.)

Extra parameters can change freely, as long as one argument shrinks. An accumulator is the usual case:

<!-- snippet: recursion.sw#accumulator -->
```stitchwort
def reverseOnto (done: List a): List a → List a
  | [] => done
  | Cons x rest => reverseOnto (Cons x done) rest

test "an accumulator" := reverseOnto [] [1, 2, 3] == [3, 2, 1]
```

Trees work the same way: `left` and `right` are parts of the `Node`.

<!-- snippet: recursion.sw#trees -->
```stitchwort
type Tree =
  | Leaf
  | Node (left: Tree) (value: Nat) (right: Tree)

def Tree.insert (tree: Tree) (value: Nat): Tree :=
  match tree with
    | Leaf => Node Leaf value Leaf
    | Node left here right =>
      if value < here then Node (left.insert value) here right
      else Node left here (right.insert value)

def Tree.toList: Tree → List Nat
  | Leaf => []
  | Node left value right => left.toList ++ [value] ++ right.toList

def treeSort (values: List Nat): List Nat := (values.foldLeft Leaf (tree value => tree.insert value)).toList

test "tree sort" := treeSort [5, 2, 8, 1] == [1, 2, 5, 8]
```

## When the argument isn't a part: `decreasing`

Halving a number isn't recursion on a part of it, so the compiler can't see that it finishes:

<!-- snippet: errors/termination.sw -->
```stitchwort
def halvings (n: Nat): Nat :=
  if n ≤ 1 then 0 else 1 + halvings (n / 2)
```

<!-- output: check errors/termination.sw -->
```text
[E-TERMINATION] Error: can't show that `halvings` terminates
   ╭─[ errors/termination.sw:2:28 ]
   │
 2 │   if n ≤ 1 then 0 else 1 + halvings (n / 2)
   │                            ───────┬───────
   │                                   ╰───────── this recursive call might not terminate: no argument is known to be smaller
   │
   │ Note 1: however the recursive calls are repeated, some argument must get smaller (a part of a pattern-matched constructor); an argument passed on unchanged, or rebuilt from its own pattern, is no smaller
   │
   │ Note 2: non-terminating definitions are rejected unless they're partial: `{Partial}` in the result type
───╯
```

`decreasing e` after the result type names a number `e`, made from the parameters, that gets smaller at every recursive call. Each call then needs a proof that it does. The compiler looks for one itself, from the facts in scope, and tries `omega` ([chapter 10](10-proofs.md)), which proves most arithmetic facts. Here the `else` branch knows `n` isn't below 10, which is enough for `n / 10 < n`:

<!-- snippet: recursion.sw#decreasing -->
```stitchwort
def digits (n: Nat): List Nat
    decreasing n
:=
  if n < 10 then [n] else digits (n / 10) ++ [n % 10]

test "decreasing" := digits 2025 == [2, 0, 2, 5]
```

When the compiler can't find a proof, it says which fact it needs. Here `n - step < n` is false when `step` is 0:

<!-- snippet: errors/decreasing.sw -->
```stitchwort
def countDown (n: Nat) (step: Nat): Nat
    decreasing n
:=
  if n ≤ 0 then 0 else 1 + countDown (n - step) step
```

<!-- output: check errors/decreasing.sw -->
```text
[E-DECREASING] Error: can't show `n - step < n` here, which `decreasing n` needs for this call
   ╭─[ errors/decreasing.sw:4:28 ]
   │
 4 │   if n ≤ 0 then 0 else 1 + countDown (n - step) step
   │                            ────────────┬────────────
   │                                        ╰────────────── this recursive call
   │
   │ Note: give a proof with `[decreasing := …]`, or test it with `if h: n - step < n then … else …`
───╯
```

The message shows the fact as you wrote it. The note gives the usual fix: test the fact with `if h: … then … else …`. In the `then` branch the fact is in scope, and the call finds it. Euclid's algorithm needs this, since `omega` doesn't reason about `%` by a variable: `a % b < b` holds once `b != 0`, and the test puts it in scope:

<!-- snippet: recursion.sw#gcd -->
```stitchwort
def gcd (a: Nat) (b: Nat): Nat
    decreasing b
:=
  if nonzero: b ≠ 0 then
    if smaller: a % b < b then gcd b (a % b) else a
  else a

test "gcd" := gcd 84 36 == 12
```

Here `a % b < b` always holds, so the inner `else` never runs; the test is there to give the compiler the fact. A proof can also be given directly, as `[decreasing := proof]` after the call. With a pair of measures, `decreasing (m, n)`, each call makes `m` smaller, or keeps `m` and makes `n` smaller, as in Ackermann's function, whose calls `omega` proves:

<!-- snippet: recursion.sw#lexicographic -->
```stitchwort
def ackermann (m: Nat) (n: Nat): Nat
    decreasing (m, n)
:=
  match m, n with
    | Zero, n => n + 1
    | Succ k, Zero => ackermann k 1
    | Succ k, Succ j => ackermann k (ackermann (Succ k) j)

test "ackermann" := ackermann 2 3 == 9
```

A function with `decreasing` runs and tests like any other. For proofs about it, the compiler generates `f.unfold`, the equation that unfolds one step ([syntax.md, `decreasing`](../syntax.md#decreasing)).

## Mutual recursion

Definitions can call each other, in any order in the file. Their termination is checked together:

<!-- snippet: recursion.sw#mutual -->
```stitchwort
def isEven: Nat → Bool
  | 0 => True
  | Succ n => isOdd n

def isOdd: Nat → Bool
  | 0 => False
  | Succ n => isEven n

test "mutual recursion" := isEven 10 ∧ isOdd 7
```

## `Partial`: functions that may not finish

Some functions have no known reason to finish, such as the Collatz sequence. Mark them `Partial`. `Partial` is written in the type like an ability ([chapter 8](08-abilities.md)), and everything that calls a partial function must say `Partial` too:

<!-- snippet: partial.sw -->
```stitchwort
-- Chapter 7: a function that may not finish says so with `Partial`.
import Std (IO, Nat)

def collatzSteps: Nat → {Partial} Nat
  | 0 => 0
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

def main(): {IO, Partial} () := IO.print "27 takes ${collatzSteps 27} steps"
```

<!-- output: run partial.sw -->
```text
27 takes 111 steps
```

Only `stitchwort run`, `stitchwort test` and the playground run partial code; the type checker never does. A test can call `collatzSteps` like any other function, with nothing extra to write:

<!-- snippet: partial-test.sw -->
```stitchwort
def collatzSteps: Nat → {Partial} Nat
  | 0 => 0
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

test "27 takes 111 steps" := collatzSteps 27 == 111
```

<!-- output: test partial-test.sw -->
```text
  ✓ 27 takes 111 steps  ran
1 test(s): 1 passed, 0 failed (0 from the cache)
```

Tests are runtime checks ([chapter 9](09-testing.md)), so `stitchwort test` runs this one as `stitchwort run` runs a partial `main`. If a test like this never finished, that would be a bug in the test or the code, and you'd stop it as you'd stop a program that hangs.

Library functions that take a callback can be given a partial one. `List.map` is partial exactly when its callback is, so the caller says `Partial` and nothing else changes; there's no separate partial `map` to write:

<!-- snippet: partial-map.sw -->
```stitchwort
-- Chapter 7: `List.map` with a partial callback is partial too.
import Std (IO, List, Nat)

def collatzSteps: Nat → {Partial} Nat
  | 0 => 0
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

def stepsOfAll (numbers: List Nat): {Partial} (List Nat) := List.map numbers collatzSteps

def main(): {IO, Partial} () := IO.print "steps: ${stepsOfAll [3, 7, 27]}"
```

<!-- output: run partial-map.sw -->
```text
steps: [7, 16, 111]
```

A caller whose type doesn't say `Partial` gets `E-PARTIAL`, which names the callback. `List.filter`, `List.find`, `List.any`, the folds and the other list functions whose callback type has an `{e}` take partial callbacks in the same way. A callback whose type has no `{e}`, such as `List.sortBy`'s comparison, must finish, and giving it a partial one is a type mismatch that says so.

`Partial` keeps the rest of the program honest: a function whose type doesn't say `Partial` is known to finish, which is what proofs about it rely on.

More: [syntax.md, `decreasing`](../syntax.md#decreasing), [`Partial`](../syntax.md#partial), and the design notes [well-founded-recursion.md](../proposals/well-founded-recursion.md), [mutual-recursion.md](../proposals/mutual-recursion.md) and [partial.md](../proposals/partial.md).
