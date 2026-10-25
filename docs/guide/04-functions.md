# 4. Functions

## Lambdas and partial application

A lambda is written `x => body`, and one with several parameters `a b => body`. Functions are curried, as in Haskell or OCaml: `add 10` is a function waiting for the second number. A constructor is a function too.

<!-- snippet: functions.sw#lambdas -->
```stitchwort
def increment: Nat -> Nat := n => n + 1

def add: Nat -> Nat -> Nat := a b => a + b

def addTen: Nat -> Nat := add 10

test "lambdas" := [1, 2, 3].map (n => n * n) == [1, 4, 9]
test "partial application" := addTen 5 == 15
test "a constructor is a function" := [1, 2].map Some == [Some 1, Some 2]
```

`A -> B` is the type of functions from `A` to `B`, and `->` groups to the right: `Nat -> Nat -> Nat` is `Nat -> (Nat -> Nat)`.

A lambda passed as an argument needs brackets: `map (n => n * n) xs`. Without them, `map n => …` would be a lambda with two parameters, the first called `map`. The compiler warns about this (`W-LAMBDA-SHADOW`) when the first parameter hides a function in scope.

A lambda's parameter types usually come from where it is used. When nothing says what they are, annotate the parameter:

<!-- snippet: errors/unknown-receiver.sw -->
```stitchwort
type Person = { name: Text, age: Nat }

def names (people: List Person): List Text :=
  let nameOf := person => person.name
  people.map nameOf
```

<!-- output: check errors/unknown-receiver.sw -->
```text
[E-CANNOT-INFER] Error: can't work out the type of this function
   ╭─[ errors/unknown-receiver.sw:4:17 ]
   │
 4 │   let nameOf := person => person.name
   │                 ──────────┬──────────
   │                           ╰──────────── add a type annotation: `(…: T)`
───╯
```

`let nameOf := (person: Person) => person.name` works, and so does `people.map (person => person.name)`, where the type comes from `people`.

## Type parameters

A lowercase name in a signature that isn't declared anywhere, like `a` here, is a type parameter: the function works for any type. You don't declare it; the compiler adds it, and works out what it is at each call:

<!-- snippet: functions.sw#generics -->
```stitchwort
def twice (f: a -> a) (x: a): a := f (f x)

def firstOr (fallback: a): List a -> a
  | [] => fallback
  | Cons x _ => x

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
def pairUpLambda: [a: Type] -> [b: Type] -> a -> b -> (a, b) :=
  [a: Type] [b: Type] (x: a) (y: b) => (x, y)

test "a lambda with implicit parameters" :=
  let flip := [a: Type] [b: Type] (x: a) (y: b) => (y, x)
  flip 1 "one" == ("one", 1) && pairUpLambda 1 "one" == (1, "one")
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

A negative literal as an argument needs brackets: `f -4` is `f - 4`.

## Pipes

`x |> f a` is `f x a`: the value on the left becomes the **first** argument, as it does for dot notation. The library puts the main argument first for this reason (`List.map xs f`), so `x |> f a` and `x.f a` agree. A pipe whose right side starts with a dot is dot notation, so `|> .split ' '` calls `Text.split` on the value with `' '` as the separator:

<!-- snippet: functions.sw#pipes -->
```stitchwort
def wordLengths (line: Text): List Nat :=
  line
    |> .split ' '
    |> .filter (word => word != "")
    |> .map (.length)

test "pipes" := wordLengths "the  quick fox" == [3, 5, 3]
```

A line may start with `|>` to continue the expression on the line above.

`|>` binds more loosely than everything except `->`, including `==`. This catches everyone at least once:

<!-- snippet: errors/pipe-precedence.sw -->
```stitchwort
import Std (List)

test "evens" := [1, 2, 3, 4] |> List.filter (n => n % 2 == 0) == [2, 4]
```

<!-- output: check errors/pipe-precedence.sw -->
```text
[E-TYPE-MISMATCH] Error: type mismatch
   ╭─[ errors/pipe-precedence.sw:3:46 ]
   │
 3 │ test "evens" := [1, 2, 3, 4] |> List.filter (n => n % 2 == 0) == [2, 4]
   │                                              ───────┬───────
   │                                                     ╰───────── this is a function, but the expected type is `List ?0`
   │
   │ Note: `|>` binds looser than `==`, so `x |> f == y` pipes `x` into the whole comparison `f == y`; to compare the result of the pipe, write brackets: `(x |> f) == y`
───╯
```

The test reads as `[1, 2, 3, 4] |> (List.filter (…) == [2, 4])`. Bracket the pipeline, `([1, 2, 3, 4] |> List.filter (…)) == [2, 4]`, or use dot notation, `[1, 2, 3, 4].filter (…) == [2, 4]`. A pipe into a [section](#sections) is the exception: `[1, 2, 3, 4] |> .filter (…) == [2, 4]` means `[1, 2, 3, 4].filter (…) == [2, 4]`, since a section takes the rest of its expression.

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
  def go: Nat -> Nat -> Nat
    | 0, total => total
    | Succ k, total => go k (total + Succ k * Succ k)
  go n 0

test "local definition" := sumOfSquares 3 == 14
test "named from outside" := sumOfSquares.go 2 0 == 5
```

There is no `where` clause; write local definitions before the line that uses them.

## Functions as values

Functions can be stored in lists and records, passed and returned like any other value:

<!-- snippet: functions.sw#higher-order -->
```stitchwort
def applyAll (functions: List (Nat -> Nat)) (start: Nat): Nat := functions.foldLeft start (value f => f value)

test "functions are values" := applyAll [increment, add 10, n => n * 2] 1 == 24
```

More: [syntax.md, Definitions in detail](../syntax.md#definitions-in-detail), [Named arguments](../syntax.md#named-arguments), [Pipe forward](../syntax.md#pipe-forward-), [Method sections](../syntax.md#method-sections), [Local definitions](../syntax.md#local-definitions).
