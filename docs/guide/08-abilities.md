# 8. Abilities

A function's type says what it may do besides returning a value. `Nat -> Nat` is pure: it computes a number and nothing else. `Nat -> {IO} Nat` may also read input and print. The things in braces are **abilities**: sets of operations, such as printing, failing, logging or choosing. A function can only perform what its type lists:

<!-- snippet: errors/ability.sw -->
```stitchwort
import Std (IO)

def total (prices: List Nat): Nat :=
  IO.print "adding up ${prices.length} prices"
  prices.sum
```

<!-- output: check errors/ability.sw -->
```text
[E-ABILITY] Error: this may perform `IO`, which isn't allowed here
   ╭─[ errors/ability.sw:4:3 ]
   │
 4 │ ╭─▶   IO.print "adding up ${prices.length} prices"
 5 │ ├─▶   prices.sum
   │ │
   │ ╰────────────────── `IO` isn't in the abilities of the enclosing function or handler
   │
   │     Note: add `IO` to the function's type (`-> {IO …} …`), or handle it
───╯
```

Abilities are Stitchwort's version of algebraic effects, the design behind Unison's abilities and Koka's effects. The code that performs operations is plain, direct-style code: no monads, no `await`. What the operations *mean* is decided separately, by a **handler**. The same code can print its log in one place and collect it into a list in a test.

## Declaring an ability

An ability lists its operations. Each takes one argument (use `()` for none) and has a result:

<!-- snippet: abilities.sw#declare -->
```stitchwort
ability Log where
  say: Text -> {Log} ()

def checkout (items: Nat): {Log} Nat :=
  say "checking out ${items} items"
  let price := items * 5
  say "the price is ${price}"
  price
```

`checkout` performs `say` twice. Each line of the block runs in order, and `let` lines run when they're reached.

## Handling it

A handler runs a computation and says what each operation does. `handle prog() with` takes a `return` clause, for when the computation finishes with a value, and a clause per operation. In `| say message, resume =>`, `message` is the operation's argument and `resume` is the rest of the computation from that point: call it with the operation's result to carry on.

This handler collects the messages in a list. Each clause returns a function that takes the messages said so far, which is how a handler keeps state:

<!-- snippet: abilities.sw#handle -->
```stitchwort
def collectLog (prog: () -> {Log | e} a): {e} (a, List Text) :=
  let run: List Text -> {e} (a, List Text) :=
    handle prog() with
      | return result => said => (result, said)
      | say message, resume => said => resume () (said ++ [message])
  run []

test "collected" := collectLog (() => checkout 3) == (15, ["checking out 3 items", "the price is 15"])
```

A few things to notice:

- **The computation is a thunk.** `collectLog` takes `prog: () -> {Log | e} a`, a function of no arguments, and the caller writes `() => checkout 3`. Passing `checkout 3` itself would run it at the call, before the handler is in place.
- **`{Log | e}` is "`Log`, plus whatever `e` stands for".** `e` is a row variable: the handler removes `Log` and passes every other ability through to its own type, `{e}`. So `collectLog` works around code that also prints, or fails.
- **The handler stays in place.** `resume` continues under the same handler, so later `say`s are caught too.

A handler that ignores the operation just resumes:

<!-- snippet: abilities.sw#ignore -->
```stitchwort
def quietly (prog: () -> {Log | e} a): {e} a :=
  handle prog() with
    | return result => result
    | say _, resume => resume ()

test "ignored" := quietly (() => checkout 2) == 10
```

And one that prints performs `IO` in its clause, so its own type says `{IO | e}`:

<!-- snippet: abilities.sw#print -->
```stitchwort
def printLog (prog: () -> {Log, IO | e} a): {IO | e} a :=
  handle prog() with
    | return result => result
    | say message, resume =>
      IO.print "log: ${message}"
      resume ()

def main(): {IO} () :=
  let price := printLog (() => checkout 4)
  IO.print "total: ${price}"
```

<!-- output: run abilities.sw -->
```text
log: checking out 4 items
log: the price is 20
total: 20
```

An operation's result can be anything the handler chooses. Here `next()` asks the handler for a number, and the handler threads a counter through, as a mutable variable would in another language:

<!-- snippet: abilities.sw#state -->
```stitchwort
ability Counter where
  next: () -> {Counter} Nat

def label (names: List Text): {Counter} (List Text) := names.mapIn (name => "${next()}. ${name}")

def counting (start: Nat) (prog: () -> {Counter | e} a): {e} a :=
  let run: Nat -> {e} a :=
    handle prog() with
      | return result => _ => result
      | next (), resume => count => resume count (count + 1)
  run start

test "numbered" := counting 1 (() => label ["tea", "milk"]) == ["1. tea", "2. milk"]
```

## Effect polymorphism: `{e}`

A function that takes a callback can be polymorphic in the callback's abilities. `applyTwice` says its result performs whatever `f` performs, so it works for pure functions and effectful ones alike:

<!-- snippet: abilities.sw#polymorphic -->
```stitchwort
def applyTwice (f: a -> {e} a) (x: a): {e} a := f (f x)

test "pure" := applyTwice (n => n + 1) 0 == 2
def loggedStep (n: Nat): {Log} Nat :=
  say "at ${n}"
  n + 1

test "with an ability" := collectLog (() => applyTwice loggedStep 0) == (2, ["at 0", "at 1"])
```

With a pure callback, `e` is empty and `applyTwice` is an ordinary pure function. This is how `List.mapIn` works: `xs.mapIn f` is `map` for an `f` that may perform abilities, such as reading or failing.

A data type can carry callbacks with abilities too. Give it a parameter of type `Effects` (from `Std.Effect`), and use it as the row of its fields:

<!-- snippet: abilities.sw#effects-parameter -->
```stitchwort
type Hooks (e: Effects) = {
  before: Nat -> {e} (),
  after: Nat -> {e} ()
}

def withHooks (hooks: Hooks e) (step: Nat -> Nat) (n: Nat): {e} Nat :=
  hooks.before n
  let result := step n
  hooks.after result
  result

def doubled (n: Nat): {Log} Nat :=
  withHooks { before = m => say "before ${m}", after = m => say "after ${m}" } (m => m * 2) n

test "hooks" := collectLog (() => doubled 5) == (10, ["before 5", "after 10"])
```

The row is worked out where the value is used; there's no syntax yet for writing a particular row, such as `Hooks {Log}`, as a type argument.

## Failing: `Fail` and `Abort`

`Fail` is the library's ability for operations that can fail with a message, like exceptions, but visible in the type. `need` takes the value out of an `Option` or fails with a message, `ensure` fails when a condition is false, and `fail` fails wherever a value of any type is expected. `toResult` handles it, turning the computation into a `Result`:

<!-- snippet: abilities.sw#fail -->
```stitchwort
type Turn = { left: Bool, distance: Nat }

def Turn.read (text: Text): {Fail} Turn :=
  let (direction, rest) := need text.uncons "expected a turn, got nothing"
  ensure (direction == 'L' || direction == 'R') "expected L or R, got '${text}'"
  { left = direction == 'L', distance = rest.toNatOrFail }

def readTurns (lines: List Text): {Fail} (List Turn) := lines.mapIn Turn.read

test "a turn" := toResult (() => Turn.read "L68") == Ok ({ left = True, distance = 68 })
test "a bad turn" := toResult (() => readTurns ["L1", "X2"]) == Err "expected L or R, got 'X2'"
test "context" := toResult (() => Fail.context "line 2" (() => Turn.read "R")) == Err "line 2: expected a whole number, got ''"
```

`Fail.context` puts a label in front of a failure's message. Other handlers: `Fail.toOption`, `Fail.orElse` (a default) and `Fail.recover` (a function of the message). `Option.orFail` and `Text.toNatOrFail` are dot-notation forms.

`Abort` is the same without a message, for code where the reason doesn't matter:

<!-- snippet: abilities.sw#abort -->
```stitchwort
def halfOf (n: Nat): {Abort} Nat :=
  Abort.ensure (n % 2 == 0)
  n / 2

test "abort" := Abort.toOption (() => halfOf 6) == Some 3 && Abort.toOption (() => halfOf 7) == None
```

## Searching: `Each`

`Each` runs the rest of a computation once for each element of a list, and collects every result, like nested loops with a filter, or a Scala `for`/`yield`:

<!-- snippet: abilities.sw#each -->
```stitchwort
def triples (n: Nat): List (Nat, Nat, Nat) := Each.collect (() =>
  let a := Each.each (List.between 1 n)
  let b := Each.each (List.between a n)
  let c := Each.each (List.between b n)
  Each.require (a * a + b * b == c * c)
  (a, b, c))

test "pythagorean triples" := triples 13 == [(3, 4, 5), (5, 12, 13), (6, 8, 10)]
```

## `IO` and `main`

`IO` has three operations: `IO.print` (writes a line), `IO.readLine()` (the next line, or `None` at the end of the input) and `IO.readAll()` (the rest of the input). `IO.readAllLines()` is the input as a list of lines.

`main` has the type `{IO} ()`, and may also be `{IO, Fail} ()`: a failure that reaches the top is printed to standard error as `error: …`, after whatever was printed before it, and the exit status is 1. The shop from [chapter 6](06-namespaces-and-library.md), on an order it can't read:

<!-- output: run --project project Shop.Report.main < project/bad-orders.txt -->
```text
error: expected a quantity, got 'two'
```

`main` can also be `Partial` ([chapter 7](07-recursion.md)), but not yet both `Fail` and `Partial`.

To test code that performs `IO`, handle it: `IO.simulate` runs a computation against a list of input lines and returns what it printed ([chapter 9](09-testing.md)).

## How it runs

Before the kernel sees a program, a computation with abilities is translated into ordinary data: a tree of operations, each with the rest of the computation as a function ([core.md, Abilities](../core.md#abilities)). A handler is a fold over that tree, so the kernel's usual termination check is what shows that handlers finish. A use of an effect-polymorphic function with a pure callback is plain pure code. A pure function stays pure: a handler used inside it doesn't show in its type, so `collectLog` can be called from a test.

More: [syntax.md, Abilities](../syntax.md#abilities), [`Abort`](../syntax.md#abort), [`Fail` and `Result`](../syntax.md#fail-and-result), [`Each`](../syntax.md#each), and the design notes [abilities.md](../proposals/abilities.md), [effect-polymorphism.md](../proposals/effect-polymorphism.md) and [errors.md](../proposals/errors.md).
