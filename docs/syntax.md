# Surface syntax (implemented subset)

**Status:** describes `crates/syntax` as of 16 October 2026. DESIGN.md §4 shows the intended language. Not yet implemented: anonymous record types and functions over any record with a field (records stages 3 and 4), `Partial` and a `case` expression.

## Layout

Interim rule, until the full layout specification (DESIGN.md §14):

- A declaration starts at column 0.
- Every following line that's indented continues it.
- A line containing only `export` belongs to the declaration after it.
- Tabs aren't allowed. `--` starts a comment that runs to the end of the line.
- **Blocks.** An expression that starts on a new line is a block: each line at that line's column is a statement, and lines indented further continue it. A statement is `let x = e` (or `let x : T = e`), binding `x` for the following lines, or an expression run for its effects. The last line is the result. A line at the block's column straight after a line ending in an operator (such as `->`) continues that line.

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
test "lengths add up" = leq (length (append [1] [2, 3])) 3

-- Exported to JavaScript by `stitchwort build --js`
export
total : List Nat -> Nat
total Nil         = 0
total (Cons x xs) = x + total xs
```

Definitions may be named in either case: `length`, or `Not` for a function returning a type.

Patterns are variables, `_`, numbers, constructors applied to patterns (nested to any depth, as in `half (Succ (Succ n))`), record patterns ([Records](#records)), or `()`. A number pattern tests for that number, of any size. In an equation with a variable or `_` where others have numbers, nothing is known about the argument: not even that it's a different number, and not that it's a `Succ` (so with `make : (n : Nat) -> ResultType n`, `make 0 = …; make n = …` checks the second equation knowing nothing about `n`). To use the shape of a number, match on `Zero` and `Succ` instead; a number pattern in a column that also has `Zero` or `Succ` patterns counts down like `Succ`s. Equations are tried from top to bottom. `()` with a right-hand side matches the unit value; without one, it says the argument's type has no values, and the equation needs no right-hand side:

```
absurd : Void -> a
absurd ()
```

Implicit and auto parameters are in scope by name in every equation, wherever they appear in the signature:

```
get : (xs : List a) -> (i : Nat) -> [auto ok : i < length xs] -> a
get Nil i = absurd (falseNotTrue ok)    -- ok : i < 0, which computes to False = True
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
- **A name in the module takes priority over a type variable.** In `length : List a -> Nat`, `a` is a type variable only if nothing in the module is called `a`; otherwise it means that declaration, wherever it is, with a warning (`W-MODULE-NAME`) pointing at both. Write `[a : Type] -> List a -> Nat` to make it a type variable regardless.
- **`auto` only uses decision procedures that are already checked and written above the use.** One written above that's still waiting for something below to be checked isn't available yet; `E-AUTO-NONE` says which case applies. Passing the procedure explicitly makes it an ordinary dependency, checked first.

## Records

A record declaration makes a new type with named fields (docs/proposals/records.md, stage 1). Two record types with the same fields are different types. An alias is an ordinary definition instead.

```
type Person = { name : Text, age : Nat }

-- Parameters, universes and dependent fields as for data types: a field's
-- type may mention earlier fields. Proof fields are erased.
type Sized (a : Type) =
  { items : List a
  , size : Nat
  , ok : length items = size
  }

alice : Person
alice = { name = "Alice", age = 30 }       -- every field once, in any order

newborn : Text -> Person
newborn name = { age = 0, name }           -- `name` alone is `name = name`

birthday : Person -> Person
birthday p = { p | age = p.age + 1 }       -- update: a new record

describe : Person -> Text
describe { name, age } = name ++ " is " ++ natToText age

nameOf : Person -> Text
nameOf { name, .. } = name                 -- `..` ignores the other fields
```

- **A literal needs an expected type**: a signature, an argument's type, or an annotation, `({ x = 0, y = 0 } : Point)`. Nothing is guessed from the field names (`E-CANNOT-INFER`).
- **`e.name`** reads a field. It's written without spaces around the `.`, binds tighter than application (`f p.name` is `f (p.name)`), and chains (`t.lead.name`, `(f x).age`). `e`'s type must be known where it's used: `\p -> p.name` needs `\(p : Person) -> p.name` unless the function's type is known from elsewhere.
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
    | choose u => k  -> append (k True) (k False)
```

Effectful code is written in direct style. Arguments are evaluated left to right, and the lines of a block in order. A handler's clauses on their own lines must line up: a `|` at another column belongs to an enclosing handler. An operation on its own (`choose`) is a function, `\x -> choose x`. A signature can be a computation that isn't a function: `current : {State Nat} Nat`. A pure function can use a handler inside; what it handles doesn't appear in its type. How this is translated into ordinary data is described in `docs/core.md`, under "Abilities".

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
| `a = b`, `a != b` | Equality and inequality (propositions). Not associative |
| `a == b` | Whether `a = b`, as a `Bool`, using the decision procedure for `a = b` (as `if h :` does). Works for `Nat`, `Bool`, and any type with a decision procedure for `=` |
| `a < b`, `a <= b` | Comparisons on `Nat` (propositions, decided by computation) |
| `a ++ b` | Joins two texts (`textAppend`) or two lists (`append`). Binds more loosely than `+`, and groups to the right |
| `a + b`, `a - b` | Addition, and subtraction stopping at zero. Left-associative |
| `a * b`, `a / b`, `a % b` | Bind tighter than `+`. `/` and `%` need a proof that `b != 0` |
| `f a b` | Application |
| `f [x := e]` | Supplying the implicit parameter `x` by name |
| `_` | A hole the compiler fills in |
| `x`, `Nat`, `Succ` | Names. Constructors and data types start with an uppercase letter |
| `0`, `42` | `Nat` literals |
| `'a'`, `'\n'`, `'\u{1F600}'` | `Char` literals: one Unicode scalar value. Escapes are `\n`, `\t`, `\r`, `\\`, `\"`, `\'` and `\u{…}` with 1–6 hex digits; `\u{…}` must name a scalar value, so `'\u{D800}'` is an error. Text literals take the same escapes |
| `"héllo"` | `Text` literal: a sequence of Unicode scalar values (see [text-and-io.md](proposals/text-and-io.md)) |
| `Type`, `Type 1`, `Prop` | Universes |
| `(e : T)` | Type annotation |
| `[a, b, c]` | `List` literal. In an expression, `[x := e]` supplies an implicit argument and every other `[…]` is a list |
| `{ name = e, age }`, `{ p \| age = e }` | Record literal (with an expected type) and update ([Records](#records)). After an arrow, `{` starts an ability row instead |
| `e.name` | A record's field. No spaces around the `.`; binds tighter than application |
| `rfl` | Proof of `a = a` |
| `J (\y p -> P) base proof` | Transport along an equality |

A partially applied constructor is a function: `Succ` on its own means `\n -> Succ n`.
