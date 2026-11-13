# 4. Functions

## Lambdas and partial application

A lambda is written `x => body`, and one with several parameters `a b => body`. Functions are curried, as in Haskell or OCaml: `add 10` is a function waiting for the second number. A constructor is a function too.

<!-- snippet: functions.sw#lambdas -->
```stitchwort
def increment: Nat → Nat := n => n + 1

def add: Nat → Nat → Nat := a b => a + b

def addTen: Nat → Nat := add 10

test "lambdas" := [1, 2, 3].map (n => n * n) == [1, 4, 9]
test "partial application" := addTen 5 == 15
test "a constructor is a function" := [1, 2].map Some == [Some 1, Some 2]
```

`A -> B` is the type of functions from `A` to `B`, and `->` groups to the right: `Nat -> Nat -> Nat` is `Nat -> (Nat -> Nat)`.

A lambda passed as an argument needs brackets: `map (n => n * n) xs`. Without them, `map n => …` would be a lambda with two parameters, the first called `map`. The compiler warns about this (`W-LAMBDA-SHADOW`) when the first parameter hides a function in scope.

A lambda's parameter types come from where it is passed or, for one bound by `let`, from its body and how it is used afterwards: `let step := x => x + 1` needs no annotation, and in `let nameOf := person => person.name` followed by `people.map nameOf`, `person` is a `Person` because of the `map`. Looking something up with `.` waits until the type is known. If nothing ever says what it is, as here where `nameOf` is never used, it can't be looked up:

<!-- snippet: errors/unknown-receiver.sw -->
```stitchwort
type Person = { name: Text, age: Nat }

def headcount (people: List Person): Nat :=
  let nameOf := person => person.name
  people.length
```

<!-- output: check errors/unknown-receiver.sw -->
```text
[E-CANNOT-INFER] Error: can't tell what `person` is, so can't look up `.name`
   ╭─[ errors/unknown-receiver.sw:4:27 ]
   │
 4 │   let nameOf := person => person.name
   │                           ─────┬─────
   │                                ╰─────── its type isn't known yet here
   │
   │ Note: `.name` is looked up in the namespace of the value's type, so that type must be known where it's used: annotate it, as in `(p: Person) => p.name`, or write the function's full name
───╯
1 error: in `headcount`
```

Annotating it, `let nameOf := (person: Person) => person.name`, always works.

A lambda bound by `let` with no type written may perform abilities ([chapter 8](08-abilities.md)): its body works out which. `let next := () => ask() + n` has type `() -> {Ask} Nat`, and each call `next()` asks again, so it can be called only where `Ask` is allowed.

## Type parameters

A lowercase name in a signature that isn't declared anywhere, like `a` here, is a type parameter: the function works for any type. You don't declare it; the compiler adds it, and works out what it is at each call:

<!-- snippet: functions.sw#generics -->
```stitchwort
def twice (f: a → a) (x: a): a := f (f x)

def firstOr (fallback: a): List a → a
  | [] => fallback
  | [x, .._] => x

test "twice" := twice increment 5 == 7
test "a is Text here" := firstOr "none" ["tea", "milk"] == "tea"
```

Type parameters are **implicit**: they're filled in by the compiler, not passed. Written out, they go in square brackets, and you can pass one by name when the compiler can't work it out, or to be explicit:

<!-- snippet: functions.sw#implicit -->
```stitchwort
def pairUp [a: Type] [b: Type] (x: a) (y: b): (a, b) := (x, y)

test "implicit arguments are inferred" := pairUp 1 "one" == (1, "one")
test "or given by name" := pairUp [b := Text] 1 "one" == (1, "one")
```

The same applies to values that types depend on, such as the length `n` in `Vec a n` ([chapter 10](10-proofs.md)): a lowercase name used as a type's argument is bound for you.

A lambda can take implicit parameters too, written the same way, so that its body can name them. Without them, `x => x` still checks against `[a: Type] -> a -> a`: the compiler introduces the implicit parameter for it, unnamed. `[auto h: P] => …` takes an `auto` parameter ([chapter 5](05-interfaces.md)) likewise.

<!-- snippet: functions.sw#implicit-lambda -->
```stitchwort
def pairUpLambda: [a: Type] → [b: Type] → a → b → (a, b) :=
  [a: Type] [b: Type] (x: a) (y: b) => (x, y)

test "a lambda with implicit parameters" :=
  let flip := [a: Type] [b: Type] (x: a) (y: b) => (y, x)
  flip 1 "one" == ("one", 1) ∧ pairUpLambda 1 "one" == (1, "one")
```

## Named arguments

Any parameter can be passed by name, `(name := value)`, in any order. A call that names arguments is the same call as the positional one. Leaving explicit parameters out makes a function of the ones left:

<!-- snippet: functions.sw#named -->
```stitchwort
def clamp (low: Nat) (high: Nat) (value: Nat): Nat :=
  if value < low then low else if value > high then high else value

test "by position" := clamp 0 10 50 == 10
test "by name, in any order" := clamp (value := 50) (high := 10) (low := 0) == 10
test "leaving some out" := [1, 50, 200].map (clamp (low := 5) (high := 100)) == [5, 50, 100]
```

Implicit parameters are named with square brackets, `[b := Text]`, as above. The language server completes parameter names after `(` and `[`.

A constructor's fields are named the same way, and so are its type's parameters, by the names in the type's header: they are implicit in the constructor, so they take square brackets. `Nil [a := Int]` is the empty list of integers, where nothing else says what its items are:

<!-- snippet: functions.sw#named-constructors -->
```stitchwort
type Pair (a: Type) (b: Type) =
  | MkPair (first: a) (second: b)

test "an empty list of integers" := (Nil [a := Int]).length == 0
test "the type's parameters by name" := MkPair [b := Text] [a := Int] 1 "one" == MkPair (1: Int) "one"
```

## Default values

An explicit parameter may have a default, written after `:=`, as a record field may ([chapter 3](03-data.md#default-values)). A call that leaves it out gets the default. Defaults are given by name, so a positional argument never lands on a defaulted parameter, and adding a default to a function never changes what existing calls mean:

<!-- snippet: functions.sw#param-defaults -->
```stitchwort
def price (base: Nat) (quantity: Nat := 1) (discount: Nat := 0): Nat := base * quantity - discount

test "defaults" := price 5 == 5
test "some by name" := price 5 (quantity := 3) == 15
test "any order" := price 5 (discount := 2) (quantity := 3) == 13
test "a call that leaves them out is a function of the rest" := [5, 8].map price == [5, 8]
```

A default may use the parameters before it. Every way of writing a call fills the defaults it doesn't name, so `price` is the function `base => price base 1 0` when passed as a value, as in the last test. A positional argument that would land on a defaulted parameter, `price 5 3`, is `E-DEFAULT-POSITIONAL`, which says to write `(quantity := 3)`. An `export def` can't have defaults yet ([chapter 11](11-running-and-shipping.md)).

## Dot notation

`x.f args` calls the function `f` in the namespace of `x`'s type, with `x` as its **first** argument. So a function declared as `def Point.shift (point: Point) …` reads like a method:

<!-- snippet: functions.sw#dot -->
```stitchwort
type Point = { x: Int, y: Int }

def Point.shift (point: Point) (dx: Int) (dy: Int): Point := { x = point.x + dx, y = point.y + dy }

def Point.manhattan (point: Point): Nat := point.x.natAbs + point.y.natAbs

def origin: Point := { x = 0, y = 0 }

test "dot notation" := (origin.shift 3 (-4)).manhattan == 7
test "the same call, in full" := Point.manhattan (Point.shift origin 3 (-4)) == 7
```

`origin.shift 3 (-4)` is `Point.shift origin 3 (-4)`. There are no classes and no methods: dot notation is only a way of writing calls. It works for the library's types too (`xs.map f` is `List.map xs f`), and needs no import: the value's type picks the namespace. Nothing is searched for: if `f`'s first explicit parameter isn't a `Point`, `origin.f` is `E-DOT-NO-RECEIVER`, so a function meant to be called with a dot takes its main value first. A function in `Point`'s namespace that takes a `Point` but not first gets the warning `W-RECEIVER-NOT-FIRST`.

A constructor is a value, but `Key.valid` is the name of a function, and `BirthYear.valid` isn't. The compiler reads `BirthYear.valid` as the name `valid` in a namespace `BirthYear`, and says what to write instead:

<!-- snippet: errors/constructor-dot.sw -->
```stitchwort
type Key =
  | BirthYear
  | IssueYear

def Key.valid (key: Key) (text: Text): Bool := match key with
  | BirthYear => text.length == 4
  | IssueYear => text.length == 4

def check: Bool := BirthYear.valid "2002"
```

<!-- output: check errors/constructor-dot.sw -->
```text
[E-UNKNOWN-NAME] Error: unknown name `BirthYear.valid`
   ╭─[ errors/constructor-dot.sw:9:20 ]
   │
 9 │ def check: Bool := BirthYear.valid "2002"
   │                    ───────┬───────
   │                           ╰───────── not in scope
   │
   │ Note: `BirthYear` is a `Key`: write `Key.valid BirthYear` or `BirthYear |> .valid`
───╯
1 error: in `check`
```

A negative number as an argument needs no brackets when the `-` has a space before it and none after it: `f -4` is `f (-4)` and `f -x` is `f (-x)`. `n - 4`, `n-4` and `n- 4` are subtractions, so `n -4` for a number `n` is an error with a note saying so.

## Pipes

`x |> f a` is `f x a`: the value on the left becomes the **first** argument, as it does for dot notation. The library puts the main argument first for this reason (`List.map xs f`), so `x |> f a` and `x.f a` agree. A pipe whose right side starts with a dot is dot notation, so `|> .split ' '` calls `Text.split` on the value with `' '` as the separator:

<!-- snippet: functions.sw#pipes -->
```stitchwort
def wordLengths (line: Text): List Nat :=
  line
    |> .split ' '
    |> .filter (word => word ≠ "")
    |> .map .length

test "pipes" := wordLengths "the  quick fox" == [3, 5, 3]
```

A line may start with `|>` to continue the expression on the line above.

`|>` binds tighter than comparisons, `∧` and `∨`, and looser than `++`, arithmetic and application, as in Elixir and Gleam. So a comparison after a pipeline compares its result, and a pipe after `∧` takes only its own side:

<!-- snippet: functions.sw#pipe-precedence -->
```stitchwort
test "compare a pipeline" := [1, 2, 3, 4] |> List.filter (n => n % 2 == 0) == [2, 4]
test "a pipe after ∧" := wordLengths "" == [] ∧ ["a", "b"] |> .length == 2
```

The second test is `(wordLengths "" == []) ∧ ((["a", "b"] |> .length) == 2)`. To pipe the result of a comparison, bracket it: `(a == b) |> f`.

## Sections

`.name args` with nothing before the dot is a short function: `.manhattan` is `p => p.manhattan`, and `.split ','` is `t => t.split ','`, which is `t => Text.split t ','`. As an argument, a section with arguments needs brackets:

<!-- snippet: functions.sw#sections -->
```stitchwort
def distances (points: List Point): List Nat := points.map .manhattan

test "a section is a function" := distances [origin, { x = 1, y = -2 }] == [0, 3]
test "with arguments" := ["a,b", "c"].map (.split ',') == [["a", "b"], ["c"]]
test "a section runs to the end of the expression" := ["ab", "", "c"].filter (.length > 1) == ["ab"]
test "an operator section" := [1, 5, 2, 8].filter (> 3) == [5, 8]
test "the argument on the right" := [1, 2].map (10 +) == [11, 12]
test "a bare operator" := [1, 2, 3].foldLeft 0 (+) == 6
```

A section that starts an expression takes the whole expression: `(.length > 1)` is `s => s.length > 1`, and `people.find (.id == id)` is `people.find (p => p.id == id)`. After a pipe, `xs |> .sum == 6` is `xs.sum == 6`. A section's argument is used once, at the start; to use it twice, write the lambda.

An operator with one operand left out is a function of that operand: `(== 'S')` is `c => c == 'S'`, `(> 3)` is `n => n > 3`, and `(10 +)` is `n => 10 + n`. This works for `+ * / % ++ = != == < <= > >= && || in !in <->`, not for `-`: `(- 1)` is the number negative one, so write `(.sub 1)` or `(n => n - 1)`. With no operand at all, an operator is a function of two arguments: `(+)` is `a b => a + b`, and `(&&)` is `a b => a && b`. There is no placeholder for an argument in the middle of an expression: write the lambda.

## Local definitions

A `def` can stand in a block, wherever a `let` can. It sees the variables above it, and can be recursive. It is lifted to a top-level definition named after its owner, so tests and proofs can refer to it from outside:

<!-- snippet: functions.sw#local -->
```stitchwort
def sumOfSquares (n: Nat): Nat :=
  def go: Nat → Nat → Nat
    | 0, total => total
    | Succ k, total => go k (total + Succ k * Succ k)
  go n 0

test "local definition" := sumOfSquares 3 == 14
test "named from outside" := sumOfSquares.go 2 0 == 5
```

There is no `where` clause; write local definitions before the line that uses them.

## Taking a value apart in a lambda

A lambda that does nothing but `match` on its parameter can be written as the cases alone: `match | Valid value => value | _ => 0` is `x => match x with | Valid value => value | _ => 0`. Written as a definition's whole body (`:= match` and the cases on the lines below), it is the same as writing the cases under the signature.

Two variations are for the commonest uses of a lambda like this. `match some` is for picking out the values of one shape, as Scala's `collect` does: each result is wrapped in `Some`, and the values no case matches give `None`, so it fits `filterMap`, `findMap` and any other function that takes an `a -> Option b`. `matches` is for testing: it gives `True` for the values a case matches (a case may leave out its `=> result`, which means `True`) and `False` for the rest.

<!-- snippet: functions.sw#clauses -->
```stitchwort
type Reading =
  | Valid (value: Nat)
  | Garbled (text: Text)
  | Missing

def Reading.score: Reading → Nat := match
  | Valid value => value
  | Garbled text => text.length
  | Missing => 0

def valid: Reading → Option Nat := match some
  | Valid value => value

def isMissing: Reading → Bool := matches | Missing

def sample: List Reading := [Valid 4, Garbled "xx", Missing, Valid 9]

test "a lambda written as its cases" := sample.map (match | Valid value => value | _ => 0) == [4, 0, 0, 9]
test "a definition written as cases" := sample.map Reading.score == [4, 2, 0, 9]
test "keeping what matches" := sample.filterMap valid == [4, 9]
test "inline" := sample.filterMap (match some | Garbled text => text.length) == [2]
test "the first match" := sample.findMap (match some | Valid value => value * 10) == Some 40
test "testing a value" := sample.filter (matches | Valid _ | Missing) == [Valid 4, Missing, Valid 9]
test "a name is tested" := sample.count isMissing == 1

def bigValue: Reading → Option Nat := match some
  | Valid value if value > 5 => value

test "a condition on a case" := sample.filterMap bigValue == [9]

def isBig: Reading → Bool := matches | Valid value if value > 5

test "a condition alone" := sample.filter isBig == [Valid 9]
```

A plain `match` still has to cover every case; the `some` and `matches` are what say that the values left out are dropped or false. If the cases you write already cover every value, the compiler warns (`W-MATCH-TOTAL`), since a `match` says that better. The words `some` and `matches` are special only in these places, so a variable of that name works anywhere else. On one line, a `|` before `=>` joins patterns, so put cases that give different results on lines of their own.

A case may carry a condition, `| Valid value if value > 5 => value`: it applies only when the condition holds, and when it doesn't, the cases below it are tried. [Chapter 3](03-data.md#conditions-on-cases) explains conditions on cases in every kind of `match`; they work the same in these three forms. In `match some` and `matches` a value no case accepts is dropped or false, as one no pattern matches is. In `matches`, a case with a condition and no `=>` is true when the condition holds. In a plain `match`, a case with a condition covers nothing, so there must still be a case without one for the same values.

## Functions as values

Functions can be stored in lists and records, passed and returned like any other value:

<!-- snippet: functions.sw#higher-order -->
```stitchwort
def applyAll (functions: List (Nat → Nat)) (start: Nat): Nat := functions.foldLeft start (value f => f value)

test "functions are values" := applyAll [increment, add 10, n => n * 2] 1 == 24
```

More: [syntax.md, Definitions in detail](../syntax.md#definitions-in-detail), [Named arguments](../syntax.md#named-arguments), [Pipe forward](../syntax.md#pipe-forward-), [Method sections](../syntax.md#method-sections), [Local definitions](../syntax.md#local-definitions).
