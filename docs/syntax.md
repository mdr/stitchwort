# Surface syntax (implemented subset)

**Status:** describes `crates/syntax` as of 16 October 2026. DESIGN.md §4 shows the intended language. Not yet implemented: anonymous record types and functions over any record with a field (records stages 3 and 4) and a `case` expression.

## Layout

Interim rule, until the full layout specification (DESIGN.md §14):

- A declaration starts at column 0.
- Every following line that's indented continues it.
- A line containing only `export` belongs to the declaration after it.
- Tabs aren't allowed. `--` starts a comment that runs to the end of the line.
- **Blocks.** An expression that starts on a new line is a block: each line at that line's column is a statement, and lines indented further continue it. A statement is `let x = e` (or `let x : T = e`), binding `x` for the following lines, or an expression run for its effects. The last line is the result. A line at the block's column straight after a line ending in an operator (such as `->`) continues that line.
- **`if` across lines.** `then` and `else` may start a line, even at the block's own column (where any other token would start a new statement), as long as they're indented at least as far as the line the `if` is on. So `if c then a` / `else if d then b` / `else e` on separate lines, all lined up, is one expression. A nested `if` takes the closest `else`. An `else` further left than its `if`'s line is an error that says so.

## Declarations

```
-- Data type. The universe defaults to `Type`.
type List (a : Type) : Type =
  | Nil
  | Cons (head : a) (tail : List a)

type False : Prop            -- no constructors

-- Definition: a signature, then equations. `a` is only used as a type, so
-- it's bound automatically as an implicit parameter: `[a : Type] -> …`.
length : List a -> Nat
length Nil         = 0
length (Cons x xs) = Succ (length xs)

-- Implicit parameters can also be written out, and are in scope by name.
theorem cong : (f : a -> b) -> [x y : a] -> x = y -> f x = f y
cong f p = J (\y' p' -> f x = f y') rfl p

-- A theorem's type must be a proposition
theorem zeroPlus : (n : Nat) -> 0 + n = n
zeroPlus n = rfl

-- A test: a `Bool` that `stitchwort test` checks is `True`
test "lengths add up" = Nat.leq (length (List.append [1] [2, 3])) 3

-- Exported to JavaScript by `stitchwort build --js`
export
total : List Nat -> Nat
total Nil         = 0
total (Cons x xs) = x + total xs
```

Definitions may be named in either case: `length`, or `Not` for a function returning a type.

Patterns are variables, `_`, numbers, constructors applied to patterns (nested to any depth, as in `half (Succ (Succ n))`), record patterns ([Records](#records)), or `()`. A number pattern tests for that number, of any size. In an equation with a variable or `_` where others have numbers, nothing is known about the argument: not even that it's a different number, and not that it's a `Succ` (so with `make : (n : Nat) -> ResultType n`, `make 0 = …; make n = …` checks the second equation knowing nothing about `n`). To use the shape of a number, match on `Zero` and `Succ` instead; a number pattern in a column that also has `Zero` or `Succ` patterns counts down like `Succ`s. On an `Int`, number patterns can be negative, `(-1)`: a match on `Int` numbers splits on the sign (`OfNat` or `NegSucc`) first, so an equation with a variable or `_` knows the sign of the argument in the branch where it is all that matches, but still nothing about its size. Equations are tried from top to bottom. `()` with a right-hand side matches the unit value; without one, it says the argument's type has no values, and the equation needs no right-hand side:

```
absurd : Void -> a
absurd ()
```

Implicit and auto parameters are in scope by name in every equation, wherever they appear in the signature:

```
get : (xs : List a) -> (i : Nat) -> [auto ok : i < List.length xs] -> a
get Nil i = Void.absurd (Bool.falseNotTrue ok)    -- ok : i < 0, which computes to False = True
…
```

### Declaration order

Declarations can be written in any order: every top-level name (definitions, data types and their constructors, abilities and their operations) is visible throughout its module. So `main` can come first and its helpers below it. The compiler checks each declaration after the ones it refers to, and otherwise in source order; errors are reported, and tests run, in source order. Definitions that refer to each other are checked together, and their termination is decided together (docs/proposals/mutual-recursion.md):

```
isEven : Nat -> Bool
isEven 0        = True
isEven (Succ n) = isOdd n

isOdd : Nat -> Bool
isOdd 0        = False
isOdd (Succ n) = isEven n
```

- **A type can't mention a definition it's checked together with** (`E-MUTUAL-SIGNATURE`): the definitions in a cycle are finished all at once, and a type may only use what's finished. A proof about `isEven` belongs outside the cycle, where its type computes.
- **Inside a cycle, a definition must be given all its arguments** wherever it's used, so the termination checker sees what each call passes: `map isOdd xs` inside `isEven` is refused, `map (\n -> isOdd n) xs` isn't. Outside the cycle, anything goes.
- **Data types that refer to each other are checked together**, like a tree whose children are a forest:

  ```
  type Tree : Type =
    | Node (label : Nat) (kids : Forest)

  type Forest : Type =
    | FNil
    | FCons (first : Tree) (rest : Forest)
  ```

  They must have the same parameters, with the same names, and the same universe (`E-MUTUAL-PARAMETERS`), and their parameters can't mention each other (`E-MUTUAL-SIGNATURE`). Their fields can mention any of the types, but not their constructors (`E-MUTUAL-CONSTRUCTOR`): `(ok : kids = FNil)` in `Tree` is refused. None of them may occur to the left of an arrow in any of their fields (`E-POSITIVITY`), or inside another type (`List Tree`). Propositions defined together can only be matched on to produce other proofs (`E-PROP-ELIM`). Functions over them are ordinary definitions that call each other: `size (Node n kids) = Succ (sizeForest kids)` is a smaller call, since `kids` is part of the tree.
- **A data type can't be in a cycle with a definition, and an ability can't be in a cycle at all** (`E-MUTUAL-KIND`): that would be induction-recursion, or Landin's knot.
- **A name in the module takes priority over a type variable.** In `length : List a -> Nat`, `a` is a type variable only if nothing in the module (or an import) is called `a`; otherwise it means that declaration, wherever it is, with a warning (`W-MODULE-NAME`) pointing at both. Write `[a : Type] -> List a -> Nat` to make it a type variable regardless.
- **`auto` only uses decision procedures that are already checked and written above the use.** One written above that's still waiting for something below to be checked isn't available yet; `E-AUTO-NONE` says which case applies. Passing the procedure explicitly makes it an ordinary dependency, checked first.

## Namespaces and imports

Names are grouped into namespaces (docs/proposals/namespaces.md). The library is `Std`, and a program sees only its core types, their constructors, the operators and `not` without asking: `Nat`, `Bool`, `List`, `Maybe`, `Pair`, `Char`, `Text`, `Ordering`, `Decidable`, `Void`, `Unit`, `Not`, `IO` (with `print` and `readLine`), and their constructors. Everything else is written with its namespace, or imported:

```
import Text (split, join)

words : Text -> List Text
words line = split ' ' line

count : List Nat -> Nat
count xs = List.length xs
```

- **A qualified name** is written without spaces: `List.length`, `Std.List.Cons`. Its first component is found like any name, or as a namespace (the file's own, then the library's); `Std.…` always means the library.
- **A type owns a namespace** holding its constructors (`Shape.Square`), and so does an ability, holding its operations (`State.get`). Anything declared with a qualified name goes in that namespace: `Shape.area : Shape -> Nat`. A qualifier that names nothing makes a namespace of the file's own (`Geometry.double`). The library's namespaces can't be added to (`E-STD-NAMESPACE`), however they're written: `List.sum` and `Std.List.sum` are both refused.
- **`import N (a, b)`** goes at the top of the file and makes `a` and `b` from namespace `N` usable without `N.`. Importing a type brings its constructors (or an ability its operations). An unknown namespace or name is `E-IMPORT-UNKNOWN`; importing a name the file also declares is `E-IMPORT-CLASH`.
- **A short name** means, in order: a local variable, the file's own declaration (or a constructor or operation of the file's own type or ability), an import, or the default. The first that has it decides, so a file can define its own `length` or `Maybe`; hiding `Maybe` hides its `Just` and `Nothing` too (they're still `Std.Maybe.Just`). Two different things at the same level are an error only where the name is used (`E-AMBIGUOUS`): write the full name.
- **Syntax always means the library's**: `+`, `==`, `++`, `if`, literals and `()` don't depend on what names a file declares.

## Records

A record declaration makes a new type with named fields (docs/proposals/records.md, stage 1). Two record types with the same fields are different types. An alias is an ordinary definition instead.

```
type Person = { name : Text, age : Nat }

-- Parameters, universes and dependent fields as for data types: a field's
-- type may mention earlier fields. Proof fields are erased.
type Sized (a : Type) =
  { items : List a
  , size : Nat
  , ok : List.length items = size
  }

alice : Person
alice = { name = "Alice", age = 30 }       -- every field once, in any order

newborn : Text -> Person
newborn name = { age = 0, name }           -- `name` alone is `name = name`

birthday : Person -> Person
birthday p = { p | age = p.age + 1 }       -- update: a new record

describe : Person -> Text
describe { name, age } = name ++ " is " ++ Nat.toText age

nameOf : Person -> Text
nameOf { name, .. } = name                 -- `..` ignores the other fields
```

- **A literal needs an expected type**: a signature, an argument's type, or an annotation, `({ x = 0, y = 0 } : Point)`. Nothing is guessed from the field names (`E-CANNOT-INFER`).
- **`e.name`** reads a field, or calls a function by dot notation: it looks `name` up in the namespace of `e`'s type `T`, finding the field or `T.name`, and puts `e` in the place of `T.name`'s first parameter of type `T`, whatever its position (`line.split ','` is `Text.split ',' line`; `t.split` alone is `\c -> Text.split c t`). A nickname's namespace is tried before what it stands for (`p : Price` tries `Price.show`, then `Nat.show`), and `p.sym` on an equation finds `Eq.sym`. It's written without spaces around the `.`, binds tighter than application (`f p.name` is `f (p.name)`), and chains (`t.lead.name`, `(f x).age`). The receiver runs first, then the arguments as written. `e`'s type must be known where it's used: `\p -> p.name` needs `\(p : Person) -> p.name` unless the function's type is known from elsewhere (`people.map (\p -> p.name)` works, since `people` is checked first). See docs/proposals/namespaces.md §4.8.
- **An update** `{ e | f = …, … }` replaces some fields. A later field whose type mentions a replaced one must be replaced too (`E-RECORD-UPDATE`): `{ s | items = xs }` isn't allowed for `s : Sized a`, `{ s | items = xs, size = n, ok = proof }` is.
- **Record patterns** `{ f = p, g, .. }` work wherever patterns do, nested in constructors and other records, when the type of what they match is known (a parameter's from the signature, or a field's from the constructor around it). After `=`, a constructor pattern takes its arguments without parentheses: `{ items = Cons x xs, .. }`.
- **Order of effects**: in a computation, field expressions run in the order written, then the record is built; an update's base runs once, first.
- **`==`** works on a record without parameters whose fields are all data, none depending on another, each with a decision procedure for `=`. Otherwise it's `E-AUTO-NONE`, with a note saying why; write a decision procedure (a function returning `Decidable (r = s)`) instead.
- **After an arrow**, `{` starts an ability row, so a record literal in a function type's result needs parentheses: `(p : Person) -> ({ p | age = p.age } = p)`.
- At the JS boundary a record is a plain object with its fields as keys, in declared order, and no `tag` (DESIGN.md §12).

## Abilities

```
-- An ability and its operations. Each operation takes one argument and
-- performs only its own ability.
ability State (s : Type) where
  get : () -> {State s} s
  put : s -> {State s} ()

-- A function type may list the abilities calling it performs, and a row
-- variable `e` (bound automatically, like a type variable) for "whatever
-- else". `{e}` alone is just the variable. `A -> B` is pure and total.
tick : () -> {State Nat} Nat
tick u =
  let n = get ()
  put (n + 1)
  n

-- A handler removes one ability. Clauses run outside the handler: `k`
-- resumes the computation (with the handler still in place) and may be
-- called any number of times. A `return` clause and a clause for every
-- operation are required.
allResults : (() -> {Choose | e} a) -> {e} List a
allResults prog =
  handle prog () with
    | return x       -> [x]
    | choose u => k  -> List.append (k True) (k False)
```

Effectful code is written in direct style. Arguments are evaluated left to right, and the lines of a block in order. A handler's clauses on their own lines must line up: a `|` at another column belongs to an enclosing handler. An operation on its own (`choose`) is a function, `\x -> choose x`. A signature can be a computation that isn't a function: `current : {State Nat} Nat`. A pure function can use a handler inside; what it handles doesn't appear in its type. How this is translated into ordinary data is described in `docs/core.md`, under "Abilities".

## `Partial`

A function that might not finish says `Partial` in its row, and so does
everything that runs it (docs/proposals/partial.md, stage 1). It's written
like an ability, but it has no operations and can't be handled; `Partial`
is reserved.

```
collatzSteps : Nat -> {Partial} Nat
collatzSteps 1 = 0
collatzSteps n = 1 + collatzSteps (next n)     -- no termination check

main : () -> {IO, Partial} ()                    -- run by `stitchwort run`
main u = print (Nat.toText (collatzSteps 27))

-- A helper that's given a recursive function must be polymorphic in the
-- rest of its row (`| e`): the recursive calls are requests that only the
-- recursive definition can answer.
useP : (Nat -> {Partial | e} Nat) -> Nat -> {Partial | e} Nat
useP k n = k n

loop : Nat -> {Partial} Nat
loop 0 = 0
loop n = useP loop (n - 1)
```

- Calling a partial function in code whose type doesn't say `Partial` is
  `E-PARTIAL`. Mentioning one is fine: `\u -> collatzSteps 3` is a total
  value, and partial functions can be passed around and stored.
- A total function fits where a partial one is expected; not the other way
  round. A row variable never stands for `Partial`, so a handler can't run
  a partial computation (`E-PARTIAL`), though its clauses may.
- Definitions that call each other must be all partial or all total
  (`E-PARTIAL-MIXED`). A partial one is partial once it has the parameters
  its equations name: `mk : Nat -> (Nat -> {Partial} Nat)` with
  `mk n = …` is total, returning a partial function.
- Inside its definition, a partial recursive function as a value can't be
  passed to a helper with a fixed row (`E-PARTIAL-CALLBACK`) or returned
  (`E-PARTIAL-ESCAPE`); its type parameters come first and every recursive
  call passes them on unchanged (`E-PARTIAL-NONUNIFORM`).
- Only `stitchwort run` and the playground run partial code. Tests can't;
  the checker never does.

## Expressions

Loosest-binding first:

| Syntax | Meaning |
|---|---|
| `\x y -> e` | Function |
| `(x y : A) -> B` | Dependent function type |
| `[x y : A] -> B` | Function type with implicit parameters, filled in by the compiler |
| `[auto x : P] -> B` | An implicit proof of `P`, found from hypotheses in scope or a decision procedure |
| `if c then a else b` | On a `Bool` |
| `if h : P then a else b` | Decides `P` (at runtime if need be). `h : P` in `a`, `h : Not P` in `b` |
| `A -> B` | Function type |
| `A -> {E, F \| e} B` | Function type whose calls may perform abilities `E` and `F`, plus whatever `e` stands for |
| `handle e with \| return x -> … \| op x => k -> …` | Runs `e`, handling one ability |
| `()` | The unit value, and its type |
| `(A, B)`, `(a, b)`, `(p, q)` | Tuples: `Pair A B`, `MkPair a b` and the pattern `MkPair p q`, by identity (a user's own `Pair` doesn't change it). Three or more nest to the right: `(a, b, c)` is `(a, (b, c))`. Where a type is expected (a function's domain, a definition of type `Type`) it's the type; otherwise it's the type if its first component's type is a universe. `(e)` is grouping, there is no one-element tuple, and an annotation inside needs brackets: `(a, (b : T))` or `((a, b) : T)`. Components are in `Type` (not `Prop`), as `Pair`'s are |
| `a = b`, `a != b` | Equality and inequality (propositions). Not associative |
| `a == b` | Whether `a = b`, as a `Bool`, using the decision procedure for `a = b` (as `if h :` does). Works for `Nat`, `Bool`, and any type with a decision procedure for `=` |
| `a < b`, `a <= b` | Comparisons on `Nat` and `Int` (propositions, decided by computation) |
| `a ++ b` | Joins two texts (`Text.append`) or two lists (`List.append`). Binds more loosely than `+`, and groups to the right |
| `a + b`, `a - b` | Addition, and subtraction (stopping at zero on `Nat`). Left-associative |
| `a * b`, `a / b`, `a % b` | Bind tighter than `+`. `/` and `%` need a proof that `b != 0` |
| `-e` | Prefix minus; it makes its arithmetic `Int` ([Numbers](#numbers)). Binds tighter than `*` `/` `%` and looser than application and dots: `-x.abs` is `-(x.abs)`, `-18 % 100` is `(-18) % 100`. Not an argument: `f -5` is `f - 5`; write `f (-5)`. May repeat, and `a - -b` needs the space (`--` starts a comment) |
| `(-k)` | In a pattern: a negative `Int` number, in brackets (or as a tuple component, `(-1, 0)`), numerals only |
| `f a b` | Application |
| `f [x := e]` | Supplying the implicit parameter `x` by name |
| `_` | A hole the compiler fills in |
| `x`, `Nat`, `Succ` | Names. Constructors and data types start with an uppercase letter |
| `0`, `42`, `-5` | Numeric literals: a `Nat`, or an `Int` where one is expected (`Nat` by default); `-5` is always an `Int`. See [Numbers](#numbers) |
| `'a'`, `'\n'`, `'\u{1F600}'` | `Char` literals: one Unicode scalar value. Escapes are `\n`, `\t`, `\r`, `\\`, `\"`, `\'` and `\u{…}` with 1–6 hex digits; `\u{…}` must name a scalar value, so `'\u{D800}'` is an error. Text literals take the same escapes |
| `"héllo"` | `Text` literal: a sequence of Unicode scalar values (see [text-and-io.md](proposals/text-and-io.md)) |
| `Type`, `Type 1`, `Prop` | Universes |
| `(e : T)` | Type annotation |
| `[a, b, c]` | `List` literal. In an expression, `[x := e]` supplies an implicit argument and every other `[…]` is a list |
| `{ name = e, age }`, `{ p \| age = e }` | Record literal (with an expected type) and update ([Records](#records)). After an arrow, `{` starts an ability row instead |
| `e.name` | A field, or dot notation: `T.name e …` for `e : T`. No spaces around the `.`; binds tighter than application |
| `rfl` | Proof of `a = a` |
| `J (\y p -> P) base proof` | Transport along an equality |

A partially applied constructor is a function: `Succ` on its own means `\n -> Succ n`.

### Numbers

A numeric literal is a `Nat` or an `Int`, depending on what's expected (`Nat` if nothing says). An arithmetic expression or comparison has one number type for all its operands, chosen by the first of these that applies: the expected type; a prefix minus (which forces `Int`); an operand with no literal in it; any other operand; else `Nat`. So `3 - 5 = -2` is on `Int`, and `x + 1` follows `x`. A `let` binding keeps its own type: `let m = 3 - 5` is a `Nat`, and `m + i` with `i : Int` is an error.

There is no implicit conversion between `Nat` and `Int`: use `n.toInt`, `Int.toNat` (negatives become 0) or `Int.toNatChecked`.

A literal argument of a generic function takes its type from the expected result when that is known: with `i : Int`, `chooseFirst 5 i` checked against `Int` works, because the result type is used before the arguments are checked ([syntax-conveniences.md](proposals/syntax-conveniences.md) section 7). Known limit: where nothing says what the result is, such as `let v = chooseFirst 5 i`, the `5` is still checked as a `Nat` first and fails; write `chooseFirst (5 : Int) i`. Design: [integers.md](proposals/integers.md); examples: `examples/accept/int-literals.sw`, `examples/accept/int-choose-first.sw`, `examples/accept/expected-types.sw`.
