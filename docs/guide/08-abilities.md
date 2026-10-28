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
  say: Text → {Log} ()

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
def collectLog (prog: () → {Log | e} a): {e} (a, List Text) :=
  let run: List Text → {e} (a, List Text) :=
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
def quietly (prog: () → {Log | e} a): {e} a :=
  handle prog() with
    | return result => result
    | say _, resume => resume ()

test "ignored" := quietly (() => checkout 2) == 10
```

And one that prints performs `IO` in its clause, so its own type says `{IO | e}`:

<!-- snippet: abilities.sw#print -->
```stitchwort
def printLog (prog: () → {Log, IO | e} a): {IO | e} a :=
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
  next: () → {Counter} Nat

def label (names: List Text): {Counter} (List Text) := names.map (name => "${next()}. ${name}")

def counting (start: Nat) (prog: () → {Counter | e} a): {e} a :=
  let run: Nat → {e} a :=
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
def applyTwice (f: a → {e} a) (x: a): {e} a := f (f x)

test "pure" := applyTwice (n => n + 1) 0 == 2
def loggedStep (n: Nat): {Log} Nat :=
  say "at ${n}"
  n + 1

test "with an ability" := collectLog (() => applyTwice loggedStep 0) == (2, ["at 0", "at 1"])
```

With a pure callback, `e` is empty and `applyTwice` is an ordinary pure function. This is how `List.map`, `List.filter`, the folds and the other list functions work: `xs.map f` takes an `f` that may perform abilities, such as reading or failing, and with a pure `f` it is the ordinary pure `map`. The effects run in list order, each element's once, and `any`, `all`, `find` and `takeWhile` stop calling `f` once the answer is decided.

A data type can carry callbacks with abilities too. Give it a parameter of type `Effects` (from `Std.Effect`), and use it as the row of its fields:

<!-- snippet: abilities.sw#effects-parameter -->
```stitchwort
type Hooks (e: Effects) = {
  before: Nat → {e} (),
  after: Nat → {e} ()
}

def withHooks (hooks: Hooks e) (step: Nat → Nat) (n: Nat): {e} Nat :=
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

def Turn.parse (text: Text): {Fail} Turn :=
  let (direction, rest) := need text.uncons "expected a turn, got nothing"
  ensure (direction == 'L' ∨ direction == 'R') "expected L or R, got '${text}'"
  { left = direction == 'L', distance = rest.toNatOrFail }

def parseTurns (lines: List Text): {Fail} (List Turn) := lines.map Turn.parse

test "a turn" := toResult (() => Turn.parse "L68") == Ok ({ left = True, distance = 68 })
test "a bad turn" := toResult (() => parseTurns ["L1", "X2"]) == Err "expected L or R, got 'X2'"
test "context" := toResult (() => Fail.context "line 2" (() => Turn.parse "R")) == Err "line 2: expected a whole number, got ''"
```

`Fail.context` puts a label in front of a failure's message. Other handlers: `Fail.toOption`, `Fail.orElse` (a default) and `Fail.recover` (a function of the message). `Option.orFail` and `Text.toNatOrFail` are dot-notation forms.

`Abort` is the same without a message, for code where the reason doesn't matter:

<!-- snippet: abilities.sw#abort -->
```stitchwort
def halfOf (n: Nat): {Abort} Nat :=
  Abort.ensure (n % 2 == 0)
  n / 2

test "abort" := Abort.toOption (() => halfOf 6) == Some 3 ∧ Abort.toOption (() => halfOf 7) == None
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

## Parsing: `Parse`

A parser from `Std.Parse` is direct-style code with the `Parse` ability. It reads tokens with `nat()`, `char ','`, `text "p="` and the like, and chooses with `oneOf`, `optional` and `many`. A runner gives it the input: `Parse.eachLine` parses each line on its own (the one to reach for when there's a record per line), and `Parse.all` parses the whole input, for input with sections. Either turns a failure into a `Fail` that names the line and column:

<!-- snippet: abilities.sw#parse -->
```stitchwort
type Box = { x: Nat, y: Nat, z: Nat }

def box(): {Parse} Box :=
  let x := nat()
  char ','
  let y := nat()
  char ','
  let z := nat()
  { x, y, z }

def parseBoxes (input: Text): {Fail} (List Box) := Parse.eachLine input box

test "boxes" := toResult (() => parseBoxes "162,817,812\n57,618,57\n") == Ok [{ x = 162, y = 817, z = 812 }, { x = 57, y = 618, z = 57 }]
test "a bad box" := toResult (() => parseBoxes "162,817,812\n57,6x8,57\n") == Err "line 2, column 5: expected ','"
```

A choice always backs up: when one alternative fails, the next starts from the same place. An error names the furthest point any alternative reached, and everything expected there. A parser fails with `Parse.fail`, `Parse.ensure` or `Parse.need`, and `Parse.fromFail (() => word.toNatOrFail)` runs a `Fail` helper inside a parser. `examples/accept/parse-basics.sw` shows the rest: keyword tables, grids, nested input.

Input in sections of one kind is `sections (() => lines nat)`. When the sections hold different things, as rules then updates, read each with `section` (its lines, then the blank line) and the last with `lines`: `let rules := section rule`, then `let updates := lines update` (`examples/accept/parse-aoc-day05.sw`). A bad line in a section is reported with what the line expected and "or a blank line before this line", since a missing blank line looks the same. `Parse.all` allows any number of line breaks at the end of the input.

For matches scattered through noise, `findAll parser` gives the value of every match, left to right, as Python's `re.findall` does; it tries `parser` at each character, so it's right for any parser. When a match can only start at certain characters, `findAllStarting (char => char == 'm') parser` skips the others in one step, which is several times faster on large input. `natDigits 1 3` reads a number of one to three digits, `repeat 2 4 parser` reads two to four of something, and `Parse.ensureAt start ok message` reports a failed check where `start` was marked rather than where the parse has got to.

## `IO` and `main`

`IO` has three operations: `IO.print` (writes a line), `IO.readLine()` (the next line, or `None` at the end of the input) and `IO.readAll()` (the rest of the input). `IO.readAllLines()` is the input as a list of lines.

`main` has the type `{IO} ()`, and may also be `{IO, Fail} ()`: a failure that reaches the top is printed to standard error as `error: …`, after whatever was printed before it, and the exit status is 1. The shop from [chapter 6](06-namespaces-and-library.md), on an order it can't parse:

<!-- output: run --project project Shop.Report.main < project/bad-orders.txt -->
```text
error: expected a quantity, got 'two'
```

`main` can also be `Partial` ([chapter 7](07-recursion.md)), and it can be both `Fail` and `Partial`. This loop reads numbers until the end of its input and fails on a line that isn't one:

<!-- snippet: sum-lines.sw@sumLines,main -->
```stitchwort
def sumLines (total: Nat): {IO, Fail, Partial} Nat :=
  match IO.readLine() with
    | None => total
    | Some line =>
      let number := line.toNatOrFail
      IO.print "total so far ${total + number}"
      sumLines (total + number)

def main(): {IO, Fail, Partial} () := IO.print "sum ${sumLines 0}"
```

<!-- output: run sum-lines.sw < sum-lines.input -->
```text
total so far 1
total so far 3
error: expected a whole number, got 'x'
```

A handler still can't go around partial code, so `Fail.toResult` can't catch a failure from inside `sumLines`: only `main` can leave it unhandled.

To test code that performs `IO`, handle it: `IO.simulate` runs a computation against a list of input lines and returns what it printed ([chapter 9](09-testing.md)).

## How it runs

Before the kernel sees a program, a computation with abilities is translated into ordinary data: a tree of operations, each with the rest of the computation as a function ([core.md, Abilities](../core.md#abilities)). A handler is a fold over that tree, so the kernel's usual termination check is what shows that handlers finish. A use of an effect-polymorphic function with a pure callback is plain pure code. A pure function stays pure: a handler used inside it doesn't show in its type, so `collectLog` can be called from a test.

More: [syntax.md, Abilities](../syntax.md#abilities), [`Abort`](../syntax.md#abort), [`Fail` and `Result`](../syntax.md#fail-and-result), [`Each`](../syntax.md#each), and the design notes [abilities.md](../proposals/abilities.md), [effect-polymorphism.md](../proposals/effect-polymorphism.md), [errors.md](../proposals/errors.md) and [parser-combinators.md](../proposals/parser-combinators.md).
