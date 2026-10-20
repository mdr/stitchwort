# Surface syntax (implemented subset)

**Status:** describes `crates/syntax` as of 16 October 2026. DESIGN.md §4 shows the intended language. Not yet implemented: anonymous record types and functions over any record with a field (records stages 3 and 4) and a `case` expression.

## Layout

Interim rule, until the full layout specification (DESIGN.md §14):

- A declaration starts at column 0.
- Every following line that's indented continues it.
- Tabs aren't allowed. `--` starts a comment that runs to the end of the line.
- Names are ASCII: letters, digits, `_` and `'`, starting with a letter or `_`. Other characters are fine in text, characters and comments, but `def café` is an error ("unexpected character").
- **Blocks.** An expression that starts on a new line is a block: each line at that line's column is a statement, and lines indented further continue it. A statement is `let x := e` (or `let x: T := e`), binding `x` for the following lines, or an expression run for its effects. The last line is the result. A `let` may hold a proof as well as data, and later lines know its value: after `let p := n`, `p` *is* `n` to the checker, so `Nat.leAddRight p 1` proves `n <= n + 1` ([proposals/let.md](proposals/let.md)). A `match` or local definition after a `let` knows it too, and a recursive call on `let r := rest` is as small as `rest`. The value is computed once when the program runs, before the lines after it; a proof or a type isn't computed at all (as for a proof parameter). Messages may show the value where you wrote the name. A `let` performs only what its right-hand side does: binding an effectful function performs nothing until it's called. A `let` whose right-hand side performs an operation (`let k := ask()`) is opaque: its value isn't known until the program runs. A line at the block's column straight after a line ending in an operator (such as `->`) continues that line.
- **`if` across lines.** `then` and `else` may start a line, even at the block's own column (where any other token would start a new statement), as long as they're indented at least as far as the line the `if` is on. So `if c then a` / `else if d then b` / `else e` on separate lines, all lined up, is one expression. A nested `if` takes the closest `else`. An `else` further left than its `if`'s line is an error that says so.

## Style

Whitespace around `:` doesn't matter to the parser: `(n : Nat)`, `(n: Nat)` and `(n:Nat)` are the same binder. The house style is `x: T`, with no space before the colon and one after, as in Scala and TypeScript: `(n: Nat)`, `[a: Type]`, `{ lo: Nat }`, `def f (n: Nat): Nat`, `def x: Nat := 1`, `let x: T := e`, `(e: T)`, `match h: e with`, `if h: P then …`. `:=` has a space on both sides. A call with no arguments is written `f()`; that style is decided too, and the examples will be restyled to follow separately. The compiler's messages and printed types use the house style.

## Declarations

```
-- Data type. The universe defaults to `Type`.
type List (a: Type): Type =
  | Nil
  | Cons (head: a) (tail: List a)

type False: Prop            -- no constructors

-- Definition: a header, then a `:=` body or arms. `a` is only used as a
-- type, so it's bound automatically as an implicit parameter: `[a: Type] -> …`.
def length: List a -> Nat
  | Nil       => 0
  | Cons x xs => Succ (length xs)

-- Implicit parameters can also be written out, and are in scope by name.
theorem cong (f: a -> b) [x y: a] (p: x = y): f x = f y := J (\y' p' => f x = f y') rfl p

-- A theorem's type must be a proposition
theorem zeroPlus (n: Nat): 0 + n = n := rfl

-- A test: a `Bool` (or a decidable proposition, as `if` takes) that `stitchwort test` checks is `True`
test "lengths add up" := Nat.leq (length (List.append [1] [2, 3])) 3

-- Exported to JavaScript by `stitchwort build --js`
export def total: List Nat -> Nat
  | Nil       => 0
  | Cons x xs => x + total xs
```

Definitions may be named in either case: `length`, or `Not` for a function returning a type.

**Automatic implicits.** An unknown lowercase name in a signature (the whole signature, header parameters included) is bound as an implicit parameter at the front if every use of it is either where a type is expected (`List a`, `a -> b`, `[x: a]`) or the whole argument of a type for a parameter that's a value (Idris's way). So with `type Dial (highest: Nat) = …`, `def part1 (start: Dial highest) (turns: List Turn): Nat` means `def part1 [highest: Nat] (start: Dial highest) …`: its type is the parameter's. "A type" here is a data type, an ability, or a definition whose result is a type (`def Below (n: Nat): Type`). Several are bound in the order of their first uses, and one may depend on another (`(t: Tagged a x)` for `type Tagged (a: Type) (tag: a)` binds `[a: Type] [x: a]`). Uses needing different types are `E-TYPE-MISMATCH` at the later one, with a note. Any other use keeps it an unknown name, so a misspelling doesn't quietly become a parameter: `Dial (highest + 1)` or `… <= highest` in the signature needs `[highest: Nat]` written out. Bound names are in scope by name in the body, as written-out implicits are.

Patterns are variables, `_`, numbers, constructors applied to patterns (nested to any depth, as in `half (Succ (Succ n))`), record patterns ([Records](#records)), or `()`. A number pattern tests for that number, of any size. A character pattern `'L'` is `MkChar 76 _` (the code as a number pattern, the proof as `_`), so it groups and falls through like numbers, and can be nested in other patterns. In an arm with a variable or `_` where other arms have numbers, nothing is known about the argument: not even that it's a different number, and not that it's a `Succ` (so with `def make: (n: Nat) -> ResultType n`, the arms `| 0 => …` and `| n => …` check the second arm knowing nothing about `n`). To use the shape of a number, match on `Zero` and `Succ` instead; a number pattern in a column that also has `Zero` or `Succ` patterns counts down like `Succ`s. On an `Int`, number patterns can be negative, `(-1)`: a match on `Int` numbers splits on the sign (`OfNat` or `NegSucc`) first, so an arm with a variable or `_` knows the sign of the argument in the branch where it is all that matches, but still nothing about its size. Arms are tried from top to bottom. `()` with a right-hand side matches the unit value; without one, it says the argument's type has no values, and the arm needs no right-hand side:

```
def absurd: Void -> a
  | ()
```

Implicit and auto parameters are in scope by name in every arm, wherever they appear in the signature:

```
def get: (xs: List a) -> (i: Nat) -> [auto ok: i < List.length xs] -> a
  | Nil, i => Void.absurd (Bool.falseNotTrue ok)    -- ok: i < 0, which computes to False = True
…
```

List patterns: `[]` is `Nil`, and `[p, q, r]` is `Cons p (Cons q (Cons r Nil))`, by identity with the library's `List` (a user's own `Cons` doesn't change it), wherever a pattern is allowed (arms, `match`, `let`, lambdas). Each element is a pattern; a constructor element takes its arguments without brackets (`[Just a, Nothing]`), and `(-k)` works as in tuples. A list pattern may end in a rest: `[x, y, ..rest]` is `Cons x (Cons y rest)`, where `rest` is any pattern (`..rest`, `.._`); `..` must be last and appears once, and `[..p]` is just `p` (`examples/accept/list-rest-patterns.sw`). There is no `x :: xs` form, and list expressions have no `..` spread (use `++` or `Cons`). A list pattern is refutable like `Cons`, so in `let` the pattern must still cover the type (`let [a, b] := xs` is `E-LET-REFUTABLE`). A missing case is reported as the constructor that lacks it (see `examples/reject/list-pattern-missing-longer.sw`).

### Declaration order

Declarations can be written in any order: every top-level name (definitions, data types and their constructors, abilities and their operations) is visible throughout its module. So `main` can come first and its helpers below it. The compiler checks each declaration after the ones it refers to, and otherwise in source order; errors are reported, and tests run, in source order. Definitions that refer to each other are checked together, and their termination is decided together (docs/proposals/mutual-recursion.md):

```
def isEven: Nat -> Bool
  | 0      => True
  | Succ n => isOdd n

def isOdd: Nat -> Bool
  | 0      => False
  | Succ n => isEven n
```

- **A type can't mention a definition it's checked together with** (`E-MUTUAL-SIGNATURE`): the definitions in a cycle are finished all at once, and a type may only use what's finished. A proof about `isEven` belongs outside the cycle, where its type computes.
- **Inside a cycle, a definition must be given all its arguments** wherever it's used, so the termination checker sees what each call passes: `map isOdd xs` inside `isEven` is refused, `map (\n => isOdd n) xs` isn't. Outside the cycle, anything goes.
- **Data types that refer to each other are checked together**, like a tree whose children are a forest:

  ```
  type Tree: Type =
    | Node (label: Nat) (kids: Forest)

  type Forest: Type =
    | FNil
    | FCons (first: Tree) (rest: Forest)
  ```

  They must have the same parameters, with the same names, and the same universe (`E-MUTUAL-PARAMETERS`), and their parameters can't mention each other (`E-MUTUAL-SIGNATURE`). Their fields can mention any of the types, but not their constructors (`E-MUTUAL-CONSTRUCTOR`): `(ok: kids = FNil)` in `Tree` is refused. None of them may occur to the left of an arrow in any of their fields (`E-POSITIVITY`), or inside another type (`List Tree`). Propositions defined together can only be matched on to produce other proofs (`E-PROP-ELIM`). Functions over them are ordinary definitions that call each other: `size (Node n kids) = Succ (sizeForest kids)` is a smaller call, since `kids` is part of the tree.
- **A data type can't be in a cycle with a definition, and an ability can't be in a cycle at all** (`E-MUTUAL-KIND`): that would be induction-recursion, or Landin's knot.
- **A name in the module takes priority over a type variable.** In `def length: List a -> Nat`, `a` is a type variable only if nothing in the module (or an import) is called `a`; otherwise it means that declaration, wherever it is, with a warning (`W-MODULE-NAME`) pointing at both. Write `[a: Type] -> List a -> Nat` to make it a type variable regardless.
- **`auto` only uses decision procedures that are already checked and written above the use.** One written above that's still waiting for something below to be checked isn't available yet; `E-AUTO-NONE` says which case applies. Passing the procedure explicitly makes it an ordinary dependency, checked first.

## Definitions in detail

The design is in [the proposal](proposals/declaration-syntax.md). Until 18 October 2026 definitions were a signature line followed by equations (`length : List a -> Nat`, then `length Nil = 0` …), with `->` in lambdas and arms and `let x = e`; that syntax is gone, and a declaration starting with a name is `E-OLD-DECLARATION`. Some older documents still use it. A header with no body (`def f : T`) is allowed only for the prelude's primitives; anywhere else it is `E-MISSING-DEFINITION`.

```
definition ::= "export"? ("def" | "theorem") name binder* ":" type body
body       ::= ":=" expr | arm+
arm        ::= "|" pattern ("," pattern)* ("=>" expr)?
binder     ::= "(" name+ ":" type ")" | "[" name+ ":" type "]"
             | "[" "auto" name ":" type "]" | "(" ")"
test       ::= "test" string ":=" expr
```

```
def total (k: Nat) (lines: List Text): Nat := (lines.map (joltage k)).sum

def length: List a -> Nat          -- arms: one pattern per argument after the colon
  | Nil       => 0
  | Cons x xs => Succ (length xs)

def total (k: Nat): List Text -> Nat    -- named parameters, then arms
  | Nil       => 0
  | Cons l ls => joltage k l + total k ls

def main(): {IO} () := report (solve (IO.readAllLines()))

test "parse" := parseBank "102" == [1, 0, 2]
export def identityNat (n: Nat): Nat := n

let x := 1 + 2                       -- in a block
\x => x + 1                          -- a lambda
match xs with
  | Nil => 0
  | Cons x _ => x
handle prog() with
  | return x    => [x]
  | choose u, k => List.append (k True) (k False)
```

- `->` is only the function type. `=>` separates a pattern or parameter from what follows (arms, `match`, handlers, lambdas). `=` is only equality; `:=` gives a body or a `let` its value. Using `=` there is `E-DEF-EQUALS`.
- Parameters before the colon have the same name in every arm and can't be matched. Parameters after the colon are matched by the arms. `()` before the colon is an unused unit parameter (it becomes `_`).
- A handler clause is `| op x, k => body`: the operation's argument, then the continuation's name. The argument is one atomic pattern, so bracket a tuple: `| op (a, b), k => …`.

**Layout.** Let *D* be the column of the declaration's `def`, `theorem` or `export`.

1. Comments and blank lines never matter for layout.
2. The header may continue on later lines, each indented more than *D*.
3. A `:=` body is on the header's line, or a block on the next line indented more than *D*.
4. Arms start on their own lines, not on the header's line. Each arm's `|` starts a line, and all of them are at one column *A*, more than *D*. A `|` between *D* and *A* is an error.
5. An arm's body can continue on lines indented more than *A*. A line at column *A* or less ends the arm. So a `match` or `handle` inside an arm must indent its own `|`s more than *A*; a `|` at column *A* is always the definition's next arm.
6. The definition ends at the first line at column *D* or less. Any other token at column *A*, or between *D* and *A*, is an error.
7. Inside `( )`, `[ ]` and `{ }`, layout ends nothing. A `|` in `{State s | e} B` belongs to the row.

### Local definitions

A `def` or `theorem` may stand in a block wherever a `let` may (the body of a definition, an arm, a `match` alternative, a lambda body, a `test`). It has the same form as at top level, arms and all:

```
def sumTo (n: Nat): Nat :=
  let start := 0
  def go: Nat -> Nat -> Nat
    | Zero, acc => acc
    | Succ k, acc => go k (acc + Succ k)
  go n start
```

- **Scope is top-down.** A local definition sees the parameters, pattern variables and earlier `let`s above it, and is visible to the lines below it. A later local definition or `let` of the same name shadows it, as a `let` does.
- **Consecutive local definitions form a group**: each may use the others in the group (and itself), so `isEven` and `isOdd` can be written one after the other.
- **Each is lifted** to a top-level definition `sumTo.go`. It takes as leading parameters the outer variables it uses, and the ones their types mention (a proof `ok: i < 5` is captured together with `i`). A captured implicit or auto parameter stays implicit or auto. A local definition and its owner may call each other, and termination is checked on the lifted program, as for any definitions that call each other.
- **Naming from outside:** `sumTo.go`, and `f.go.inner` for a definition inside `go`. Names are unique within one top-level definition (`E-DUPLICATE`), even if a later one shadows an earlier one, because the lifted names are all `f.name`.
- **Lemmas:** a local `theorem goZero (a: Nat): go 0 a = a := rfl` about a local function works when that function doesn't call its owner (it must be finished for the lemma's type to compute). If the function calls its owner, it isn't finished while the owner is checked: a proof that needs it to compute fails (with a note suggesting a top-level theorem about `f.go`), and a lemma whose type mentions it is `E-MUTUAL-SIGNATURE`.
- **Limits:** a recursive local definition can't be `{Partial}` (`E-LOCAL-DEFINITION`; define it at top level). A local definition in a cycle with its owner can't be passed unapplied (`E-TERMINATION`): write `\x => go x`. A block must end with an expression (`E-PARSE`).
- There is no `where` clause: after a body or the last arm it is `E-WHERE`, which points to local definitions.

Examples: `examples/accept/local-defs.sw`, `examples/accept/local-defs-effects.sw`, `examples/extract/local-defs.sw`. Design: [syntax-conveniences.md](proposals/syntax-conveniences.md) section 3.

**Exact arity.** Every arm has exactly one pattern for each explicit argument after the colon. These are counted after unfolding definitions, up to the first thing that isn't a function type (such as an ability row). So `def f: Nat -> Nat -> Nat` needs `| Zero, y => y`, not `| Zero => \y => y`. Fewer patterns is `E-ARITY`, as is a different number in different arms. A `:=` body has no arity rule. Implicit and auto arguments after the colon aren't matched; they're in scope by name.

**`E-DUPLICATE-PARAMETER`.** The names of the header's parameters, and of the implicit and auto parameters after the colon, must all be different.

## Namespaces and imports

Names are grouped into namespaces (docs/proposals/namespaces.md). The library is `Std`, and a program sees only its core types, their constructors, the operators and `not` without asking: `Nat`, `Bool`, `List`, `Maybe`, `Pair`, `Char`, `Text`, `Ordering`, `Decidable`, `Void`, `Unit`, `Not`, `And`, `Or`, `IO` (its operations are written `IO.print`, `IO.readLine` and `IO.readAll`, or imported), and their constructors. Everything else is written with its namespace, or imported:

```
import Text (split, join)

def words (line: Text): List Text := split ' ' line

def count (xs: List Nat): Nat := List.length xs
```

- **`namespace Day05`** is the first line of a file (only comments may come before it). It puts everything the file declares in the namespace `Day05`: `Day05.main`, `Day05.Range.size`, and the file is checked and run as that namespace (`stitchwort run` runs `Day05.main`). A file has at most one namespace line, and `Std` and the library's namespaces (`List`, `Text`, …) can't be used for it (`E-STD-NAMESPACE`, `E-NAMESPACE-RESERVED`). Without a namespace line, names have no prefix, as before. Design: [multi-file.md](proposals/multi-file.md).
- **A qualified name** is written without spaces: `List.length`, `Std.List.Cons`. Its first component is found like any name, or as a namespace (the file's own, then the library's); `Std.…` always means the library.
- **A type owns a namespace** holding its constructors (`Shape.Square`), and so does an ability, holding its operations (`State.get`). Anything declared with a qualified name goes in that namespace: `Shape.area: Shape -> Nat`. A qualifier that names nothing makes a namespace of the file's own (`Geometry.double`). The library's namespaces can't be added to (`E-STD-NAMESPACE`), however they're written: `List.sum` and `Std.List.sum` are both refused.
- **`import N (a, b)`** goes at the top of the file and makes `a` and `b` from namespace `N` usable without `N.`. Importing a type brings its constructors (or an ability its operations). An unknown namespace or name is `E-IMPORT-UNKNOWN`; importing a name the file also declares is `E-IMPORT-CLASH`. `import N (..)` brings every name declared directly in `N`, below the names imported by name (`import List (..)`, then `map`, `filter`, …); it can't name the file's own namespace, `Std` itself, or a type of a project namespace (`E-IMPORT-WILDCARD`). An import's namespace is found without looking at the other imports.
- **A short name** means, in order: a local variable, the file's own declaration (or a constructor or operation of the file's own type or ability), an import by name, a name from an `import N (..)`, or the default. The first that has it decides, so a file can define its own `length` or `Maybe`; hiding `Maybe` hides its `Just` and `Nothing` too (they're still `Std.Maybe.Just`). Two different things at the same level are an error only where the name is used (`E-AMBIGUOUS`): write the full name.
- **A project** is a folder with a `stitchwort.yaml` (empty is fine; `sources: [src, lib]` lists the folders to read, default `src`). Every `.sw` file under them starts with a `namespace` line, and files with the same namespace are one module: their declarations are all visible to each other, in any order, but each file has its own imports. Namespaces use each other by `import` or by writing the name in full (`Lib.Range.size`, no import needed); a cycle between namespaces is `E-NAMESPACE-CYCLE`. `stitchwort check`, `test` and `run NAME` look for the project from the current folder up (or take `--project DIR`); a file given by path (`stitchwort run hello.sw`) is checked on its own, using only the library.
- **Syntax always means the library's**: `+`, `==`, `++`, `if`, literals and `()` don't depend on what names a file declares.

## Type synonyms and bracket layout

**Type synonyms.** `type Grid = List (List Nat)` is `def Grid: Type := List (List Nat)`: a transparent name, interchangeable with what it stands for, with its own namespace (`def Grid.rolls (g: Grid) …`, then `g.rolls`). Parameters are written as binders, `type Matrix (a: Type) = List (List a)`, and the type can be a tuple, `type Point = (Nat, Nat)`. After `=`, `{` starts a record and `|` a sum type's constructors (each constructor starts with its own `|`, even a single one: `type T = | Foo (x: Nat)`); anything else is the type. `type T = A | B` and `type T = Foo (x: Nat)` look like sums without their `|`, so they're `E-PARSE` with a note saying so (`examples/accept/type-synonyms.sw`, `examples/reject/type-synonym-*.sw`). A synonym can't be recursive: `type A = B` with `type B = A` leaves neither with a type to stand for (`E-SYNONYM-CYCLE`, `examples/reject/synonym-*.sw`).

**Brackets continue lines.** Inside `[ ]`, `( )` and `{ }`, a line starting with `,` or a closing bracket continues the bracket however far left it starts, so a list can be laid out with leading commas (`examples/accept/list-literal-layout.sw`). A trailing comma is allowed in list, tuple and record expressions and patterns, and in a record declaration's fields.

## Records

A record declaration makes a new type with named fields (docs/proposals/records.md, stage 1). Two record types with the same fields are different types. An alias is a type synonym instead (above).

```
type Person = { name: Text, age: Nat }

-- Parameters, universes and dependent fields as for data types: a field's
-- type may mention earlier fields. Proof fields are erased.
type Sized (a: Type) =
  { items: List a
  , size: Nat
  , ok: List.length items = size
  }

def alice: Person := { name = "Alice", age = 30 }       -- every field once, in any order

def newborn (name: Text): Person := { age = 0, name }           -- `name` alone is `name = name`

def birthday (p: Person): Person := { p | age = p.age + 1 }       -- update: a new record

def describe: Person -> Text
  | { name, age } => name ++ " is " ++ Nat.toText age

def nameOf: Person -> Text
  | { name, .. } => name                 -- `..` ignores the other fields
```

- **A literal needs an expected type**: a signature, an argument's type, or an annotation, `({ x = 0, y = 0 }: Point)`. Nothing is guessed from the field names (`E-CANNOT-INFER`).
- **`e.name`** reads a field, or calls a function by dot notation: it looks `name` up in the namespace of `e`'s type `T`, finding the field or `T.name`, and puts `e` in the place of `T.name`'s first parameter of type `T`, whatever its position (`line.split ','` is `Text.split ',' line`; `t.split` alone is `\c => Text.split c t`). A nickname's namespace is tried before what it stands for (`p: Price` tries `Price.show`, then `Nat.show`), and `p.sym` on an equation finds `Eq.sym`. It's written without spaces around the `.`, binds tighter than application (`f p.name` is `f (p.name)`), and chains (`t.lead.name`, `(f x).age`). The receiver runs first, then the arguments as written. `e`'s type must be known where it's used: `\p => p.name` needs `\(p: Person) => p.name` unless the function's type is known from elsewhere (`people.map (\p => p.name)` works, since `people` is checked first; so does `List.map (\p => p.name) people`: in an application, a lambda whose parameter type isn't known yet, and that can't be checked without it, is checked after the later arguments, unless a later argument's type depends on it. Only the checking order changes, not the order arguments are passed or run in). `f p .name`, with a space, is a method section instead ([Method sections](#method-sections)). See docs/proposals/namespaces.md §4.8.
- **An update** `{ e | f = …, … }` replaces some fields. A later field whose type mentions a replaced one must be replaced too (`E-RECORD-UPDATE`): `{ s | items = xs }` isn't allowed for `s: Sized a`, `{ s | items = xs, size = n, ok = proof }` is.
- **Record patterns** `{ f = p, g, .. }` work wherever patterns do, nested in constructors and other records, when the type of what they match is known (a parameter's from the signature, or a field's from the constructor around it). After `=`, a constructor pattern takes its arguments without parentheses: `{ items = Cons x xs, .. }`.
- **Order of effects**: in a computation, field expressions run in the order written, then the record is built; an update's base runs once, first.
- **`==`** works on a record without parameters whose fields are all data, none depending on another, each with a decision procedure for `=`. (Other declared data types get `==` too, see the operator table.) Otherwise it's `E-AUTO-NONE`, with a note saying why; write a decision procedure (a function returning `Decidable (r = s)`) instead.
- **After an arrow**, `{` starts an ability row, so a record literal in a function type's result needs parentheses: `(p: Person) -> ({ p | age = p.age } = p)`.
- At the JS boundary a record is a plain object with its fields as keys, in declared order, and no `tag` (DESIGN.md §12).

## Abilities

```
-- An ability and its operations. Each operation takes one argument and
-- performs only its own ability.
ability State (s: Type) where
  get: () -> {State s} s
  put: s -> {State s} ()

-- A function type may list the abilities calling it performs, and a row
-- variable `e` (bound automatically, like a type variable) for "whatever
-- else". `{e}` alone is just the variable. `A -> B` is pure and total.
def tick(): {State Nat} Nat :=
  let n := get()
  put (n + 1)
  n

-- A handler removes one ability. Clauses run outside the handler: `k`
-- resumes the computation (with the handler still in place) and may be
-- called any number of times. A `return` clause and a clause for every
-- operation are required.
def allResults (prog: () -> {Choose | e} a): {e} List a :=
  handle prog() with
    | return x       => [x]
    | choose u, k    => List.append (k True) (k False)
```

Effectful code is written in direct style. Arguments are evaluated left to right, and the lines of a block in order. A handler's clauses on their own lines must line up: a `|` at another column belongs to an enclosing handler. An operation on its own (`choose`) is a function, `\x => choose x`. A signature can be a computation that isn't a function: `current: {State Nat} Nat`. A pure function can use a handler inside; what it handles doesn't appear in its type. How this is translated into ordinary data is described in `docs/core.md`, under "Abilities".

## `IO`

`IO` is an ability with `print: Text -> {IO} ()`, `readLine: () -> {IO} (Maybe Text)` and `readAll: () -> {IO} Text` (also `IO.print`, `IO.readLine`, `IO.readAll`). `IO.simulate lines prog` runs `prog` against scripted input and records what it prints.

- `IO.readLine()` gives the next line without its LF (and a CR just before it), `Nothing` once nothing remains.
- `IO.readAll()` gives everything that remains, verbatim, line endings included; `""` once nothing remains. After it, `IO.readLine()` is `Nothing`; after some `IO.readLine`s it gives the rest. Under `IO.simulate` it gives the remaining scripted lines, each followed by LF.
- `Text.lines: Text -> List Text` follows Rust's `str::lines`: split on LF, drop a CR right before an LF, and the last line's ending is optional. `"a\nb"` and `"a\nb\n"` both give `["a", "b"]`; `""` gives `[]`; `"\n"` gives `[""]`; `"a\r\nb"` gives `["a", "b"]`. A CR anywhere else stays, including a final one.
- `IO.readAllLines(): {IO} (List Text)` is `(readAll()).lines`. It is total.

## `Partial`

A function that might not finish says `Partial` in its row, and so does
everything that runs it (docs/proposals/partial.md, stage 1). It's written
like an ability, but it has no operations and can't be handled; `Partial`
is reserved.

```
def collatzSteps: Nat -> {Partial} Nat
  | 1 => 0
  | n => 1 + collatzSteps (next n)     -- no termination check

-- run by `stitchwort run`
def main(): {IO, Partial} () := IO.print (Nat.toText (collatzSteps 27))

-- A helper that's given a recursive function must be polymorphic in the
-- rest of its row (`| e`): the recursive calls are requests that only the
-- recursive definition can answer.
def useP (k: Nat -> {Partial | e} Nat) (n: Nat): {Partial | e} Nat := k n

def loop: Nat -> {Partial} Nat
  | 0 => 0
  | n => useP loop (n - 1)
```

- Calling a partial function in code whose type doesn't say `Partial` is
  `E-PARTIAL`. Mentioning one is fine: `\u => collatzSteps 3` is a total
  value, and partial functions can be passed around and stored.
- A total function fits where a partial one is expected; not the other way
  round. A row variable never stands for `Partial`, so a handler can't run
  a partial computation (`E-PARTIAL`), though its clauses may.
- Definitions that call each other must be all partial or all total
  (`E-PARTIAL-MIXED`). A partial one is partial once it has the parameters
  its arms or parameters name: `def mk (n: Nat): Nat -> {Partial} Nat :=
  …` is total, returning a partial function.
- Inside its definition, a partial recursive function as a value can't be
  passed to a helper with a fixed row (`E-PARTIAL-CALLBACK`) or returned
  (`E-PARTIAL-ESCAPE`); its type parameters come first and every recursive
  call passes them on unchanged (`E-PARTIAL-NONUNIFORM`).
- Only `stitchwort run` (with or without `--js`) and the playground run
  partial code. Tests can't;
  the checker never does.

## Expressions

Loosest-binding first:

| Syntax | Meaning |
|---|---|
| `\x y => e` | Function |
| `(x y: A) -> B` | Dependent function type |
| `[x y: A] -> B` | Function type with implicit parameters, filled in by the compiler |
| `[auto x: P] -> B` | An implicit proof of `P`, found from hypotheses in scope or a decision procedure |
| `if c then a else b` | On a `Bool`, or on a proposition with a decision procedure, as `if _: c then a else b` (Lean's way): `if x < y`, `if n <= hi`, `if d != 0` work on `Nat` and `Int`. `c` is tried as a `Bool` first, exactly as before, so a `Bool` condition (`if xs == ys`) means what it always has; only if that fails is `c` tried as a proposition, with everything the first try did undone. A proposition nothing decides is `E-AUTO-NONE` at the condition (`if f = g` on functions); a condition that's neither is the `Bool` error. So do `&&`, `\|\|` and `not` on comparisons: `if x < y && y < z`, `if not (x < y)`. A condition that performs operations must be a `Bool` |
| `if h: P then a else b` | Decides `P` (at runtime if need be). `h: P` in `a`, `h: Not P` in `b` |
| `A -> B` | Function type |
| `A -> {E, F \| e} B` | Function type whose calls may perform abilities `E` and `F`, plus whatever `e` stands for |
| `handle e with \| return x => … \| op x, k => …` | Runs `e`, handling one ability |
| `match e with \| p => a \| q => b` | Takes apart `e` by patterns; `match h: e with` also names an equation ([`match`](#match)) |
| `()` | The unit value, and its type |
| `(A, B)`, `(a, b)`, `(p, q)` | Tuples: `Pair A B`, `MkPair a b` and the pattern `MkPair p q`, by identity (a user's own `Pair` doesn't change it). Three or more nest to the right: `(a, b, c)` is `(a, (b, c))`. Where a type is expected (a function's domain, a definition of type `Type`) it's the type; otherwise it's the type if its first component's type is a universe. `(e)` is grouping, there is no one-element tuple, and an annotation inside needs brackets: `(a, (b: T))` or `((a, b): T)`. Components are in `Type` (not `Prop`), as `Pair`'s are |
| `x \|> f a b` | Pipe forward: `f a b x`, the value becoming the last argument. The loosest operator except `->`; left-associative. See [Pipe forward](#pipe-forward-) |
| `a \|\| b` | Or. On `Bool`s it's `if a then True else b`: `b` is evaluated, and its operations performed, only if `a` is `False`. Where a proposition is expected (a type, or `if h: …`) it's `Or a b` (constructors `Inl`, `Inr`), decided by `Decidable.or`. Looser than `&&`; groups to the right. See below |
| `a && b` | And. On `Bool`s it's `if a then b else False`: `b` is evaluated only if `a` is `True`. Where a proposition is expected it's `And a b` (constructor `Both`), decided by `Decidable.and`. Looser than `=`, `==` and `<`; groups to the right. See below |
| `a = b`, `a != b` | Equality and inequality (propositions). Not associative |
| `a == b` | Whether `a = b`, as a `Bool`, using the decision procedure for `a = b` (as `if h:` does). Works for `Nat`, `Int`, `Bool`, `Char`, `Text`, any type with a decision procedure for `=`, and lists, tuples and `Maybe` of those (`[(1, "a")] == [(1, "a")]`): a decision procedure taking one for the elements (`List.decEq`, `Pair.decEq`, `Maybe.decEq`) is given one found the same way. So does a record with such fields (`{ ids: List Nat, delta: Maybe Int }`), and a declared data type whose fields can all be compared, derived automatically when it's declared (`type Dir = | L | R`, recursive types, `Tree Nat` for `type Tree (a: Type): Type = …`: parameters must be `Type`). `List (Nat -> Nat)` is `E-AUTO-NONE`, with a note naming the element type that has none; so is a type with a function field, a proof or type field, or defined together with others (mutual), with a note saying why |
| `a < b`, `a <= b` | Comparisons on `Nat` and `Int` (propositions, decided by computation) |
| `a ++ b` | Joins two texts (`Text.append`) or two lists (`List.append`). Binds more loosely than `+`, and groups to the right |
| `a + b`, `a - b` | Addition, and subtraction (stopping at zero on `Nat`). Left-associative |
| `a * b`, `a / b`, `a % b` | Bind tighter than `+`. `/` and `%` need a proof that `b != 0` |
| `-e` | Prefix minus; it makes its arithmetic `Int` ([Numbers](#numbers)). Binds tighter than `*` `/` `%` and looser than application and dots: `-x.abs` is `-(x.abs)`, `-18 % 100` is `(-18) % 100`. Not an argument: `f -5` is `f - 5`; write `f (-5)`. May repeat, and `a - -b` needs the space (`--` starts a comment) |
| `(-k)` | In a pattern: a negative `Int` number, in brackets (or as a tuple component, `(-1, 0)`), numerals only |
| `f a b` | Application |
| `not a` | `Bool.not a`; where a proposition is expected, `Not a`. Only when `not` is the library's (a local `not` is an ordinary function) and has one argument: `List.map not bs` is `Bool.not` as a function. See below |
| `f [x := e]` | Supplying the implicit parameter `x` by name |
| `_` | A hole the compiler fills in |
| `x`, `Nat`, `Succ` | Names. Constructors and data types start with an uppercase letter |
| `0`, `42`, `-5` | Numeric literals: a `Nat`, or an `Int` where one is expected (`Nat` by default); `-5` is always an `Int`. See [Numbers](#numbers) |
| `'a'`, `'\n'`, `'\u{1F600}'` | `Char` literals: one Unicode scalar value. Escapes are `\n`, `\t`, `\r`, `\\`, `\"`, `\'`, `\$` and `\u{…}` with 1–6 hex digits; `\u{…}` must name a scalar value, so `'\u{D800}'` is an error. Text literals take the same escapes |
| `"héllo"` | `Text` literal: a sequence of Unicode scalar values (see [text-and-io.md](proposals/text-and-io.md)) |
| `Type`, `Type 1`, `Prop` | Universes |
| `(e: T)` | Type annotation |
| `[a, b, c]` | `List` literal. In an expression, `[x := e]` supplies an implicit argument and every other `[…]` is a list |
| `{ name = e, age }`, `{ p \| age = e }` | Record literal (with an expected type) and update ([Records](#records)). After an arrow, `{` starts an ability row instead |
| `e.name` | A field, or dot notation: `T.name e …` for `e: T`. No spaces around the `.`; binds tighter than application |
| `.name`, `.drop 1` | Method section: `\x => x.name`, `\x => x.drop 1`. A space before the `.` (or a bracket or line start). See [Method sections](#method-sections) |
| `rfl` | Proof of `a = a` |
| `J (\y p => P) base proof` | Transport along an equality |

**Interpolation.** Inside a text literal, `${e}` inserts `e` converted with `.toText`: `"Part 1: ${solvePart1 turns}"` is `"Part 1: " ++ (solvePart1 turns).toText`, and `"n = ${2 + 3}"` is `"n = 5"`. The expression may contain braces and nested text literals, as in `"${f "x"}"`. A `$` not followed by `{` is an ordinary character; write `\$` for a literal dollar sign: `"cost: \$5"`.

A partially applied constructor is a function: `Succ` on its own means `\n => Succ n`.

### `&&`, `||` and `not`

Each has two readings, chosen by what's expected, the way `if c` chooses:

- **Where a proposition is expected** (a type: a signature, `if h: …`, an `auto` argument) they're the propositions `And a b`, `Or a b` and `Not a`, and both operands must be propositions. A `Bool` operand is an error (`E-NOT-A-TYPE`) with a note: for a `Bool` `b`, the proposition is `b = True`. `if h: x < y && y < z` gives `h: x < y && y < z` in the `then` branch and `h: Not (x < y && y < z)` in the `else` branch. The library's `Decidable.and`, `Decidable.or` and `Decidable.not` decide them from decisions of each side; both sides are decided before these run, so `if h: p && q` decides `q` even when `p` is false. `And.left`, `And.right` and `Or.neither` take them apart.
- **Otherwise** (a `Bool` expected, as in a `def …: Bool`, a test or `if c`, or nothing known, as in `let`) it's a `Bool`, and **each operand is a condition, as `if` takes one**: a `Bool`, or failing that a proposition with a decision procedure, decided. So `x < y && y < z`, `flag && x < 3` and `not (x < y)` are all `Bool`s, and a `Bool` operand means what it always has. `a && b` is `if a then b else False` and `a \|\| b` is `if a then True else b`: `b` isn't evaluated when `a` decides the answer, and when `b` performs operations, they're performed only if `b` is evaluated. Operations in `a` are performed first. With nothing expected, if the `Bool` reading fails, the proposition reading is tried, with everything the first try did undone; if that fails too, the `Bool` reading's error is reported (`E-AUTO-NONE` at an operand nothing decides, as for `if`).

Precedence, loosest first: `->`, then `\|>`, then `\|\|`, then `&&`, then `=` `!=` `==` `<` `<=`. So `a \|\| b && c` is `a \|\| (b && c)`, `x < y && y < z` needs no brackets, and `p && q -> r` is `(p && q) -> r`. `not` is a function, so `not x < y` is `(not x) < y`: write `not (x < y)`. The printer shows `And p q` and `Or p q` as `p && q` and `p \|\| q`. A single `&` is still an error.

A test (`test "…" := e`) takes `e` as a condition too: a `Bool`, or a proposition with a decision procedure, so `test "ordered" := 1 < 2 && 2 < 3` and `test "small" := 3 < 5` work.

**Anywhere a `Bool` is expected**, a proposition with a decision procedure is decided, as Lean's `decide` coercion does: `List.filter (\n => k * n <= size) xs`, `List.all (\x => x < 10) xs`, `def le (a b: Nat): Bool := a <= b`. The expression is elaborated as usual; only if it turns out to be a proposition (its type is `Prop`) and the expected type is the library's `Bool` is it replaced by `Decidable.toBool` of its decision. A proposition nothing decides is `E-AUTO-NONE` at the expression, saying a `Bool` is expected (`List.filter (\g => g = f) gs` on functions). Where a proposition is expected nothing changes, and conditions (`if c`, `&&`, `||`, `not`, `test`) still try the `Bool` reading first and then the proposition, as above.

### Pipe forward `|>`

`x |> f` is `f x`, and `x |> f a b` is `f a b x`: the value on the left becomes the **last** argument. That's why the library puts the main argument last (`List.map f xs`, `List.sum xs`), so a pipeline reads in the order things happen:

```
def total: Nat :=
  people
    |> List.map (\p => p.age)
    |> List.sum
```

**Library convention:** in a function that takes a main value (the collection, optional or text being operated on) plus other arguments, the main value comes last, so pipes read naturally; dot notation (`m.andThen f`) works regardless of where the main value sits.

It is the loosest operator except `->`, and groups to the left: `x |> f |> g` is `(x |> f) |> g`, `a + b |> f` is `(a + b) |> f`, and `x |> f -> T` is `(x |> f) -> T`. Because it's looser than `=`, `xs |> List.sum = 6` is `xs |> (List.sum = 6)`; write `(xs |> List.sum) = 6`.

- **Layout.** A line may start with `|>` to continue the expression, if it's indented at least as far as the line the expression starts on, even at the enclosing block's own column (as `then` and `else` may). `|>` is its own token, so it never clashes with the `|` of arms and alternatives. After a `match`, a `|>` line at or right of the last alternative's `|` continues that alternative's body (the last alternative takes what follows, as with any operator); one further left, but at least at the `match` line's column, pipes the whole `match`.
- **A lambda on the right** takes the rest of the pipeline: `x |> \y => f y |> g` is `x |> \y => (f y |> g)`, which means the same as `(x |> \y => f y) |> g`.
- **The left side is checked first**, and its type is unified with the function's last parameter before the other arguments are checked. So `people |> List.map (\p => p.name)` knows `p: Person` when it reaches the lambda (`List.map (\p => p.name) people` works too, by checking the lambda last; see [`e.name`](#records)). A value of the wrong type is `E-TYPE-MISMATCH`, pointing at the function: "this takes `List Nat` as its last argument, but the value before `|>` has type `Text`".
- **The left side runs first** when it performs operations, then the right side's arguments, then the call: `say "left" 1 |> add (say "right" 2)` prints `left`, then `right`.
- **A number literal on the left** is just `f 5`: it takes its type from `f`, as an argument would.

Implicit and `auto` arguments, `[x := e]` and constructors work on the right as in a normal call.

### Method sections

`.f args` is `\x => x.f args`: dot notation with the receiver left out.

```
people.map .name                    -- people.map (\p => p.name)
people |> .map .age |> .sum         -- (people.map (\p => p.age)).sum
ls.map (.split ',')                 -- ls.map (\l => l.split ',')
```

- **Chains and arguments.** `.name.length` is `\x => x.name.length`. Arguments after the head section belong to it: `.drop 1` is `\x => x.drop 1`. As an argument a section takes none, so bracket it: `List.map .name people`, `people.map (.greet "Hi")`. Like `e.name`, the receiver goes in whatever position of the function it fits (`.split ','` is `\t => Text.split ',' t`).
- **The space rule.** A section follows a space (or a bracket, or starts the expression): `f p .name` is `f p (.name)`, while `p.name` is still a field access. `p. name` is still an error, and so are `.Name` and `.1`.
- **Pipe.** `xs |> .drop 1` is rewritten by the parser to exactly `xs.drop 1`, with no lambda, so `xs |> .drop 1 |> .sum` is `(xs.drop 1).sum`.
- **Layout.** A section can't start a continuation line as an argument: in `foo xs` followed by an indented `.map f`, the `.map f` would read as another argument of `foo`, so it's a parse error ("a line can't start with a method section"), with a note pointing to `|> .map f` or `(.map f)`. A line starting `|> .map f` is fine.
- **Checking.** A section is a lambda, so it's checked like one: its receiver's type must be known from the expected function type (`people.map .name`, `apply .length "abc"` for `apply (f: Text -> Nat)`), from a pipe's left side, or from an annotation (`(.drop 1: List Nat -> List Nat)`). In an application, a section whose parameter type isn't known yet is checked after the other arguments, so `List.map .name people` works (as `List.map (\p => p.name) people` does; a plain lambda is checked in place first and waits only if that fails).
- **Unknown receiver.** `let g := .drop 1` or `(.length) "abcd"` is `E-CANNOT-INFER` ("can't tell what `.drop` is applied to"), with a note suggesting a pipe, passing it where a function type is known, or an annotation.
- **No such function.** The ordinary dot-notation error: `xs |> .dorp 1` is `E-UNKNOWN-FIELD`, "`List` has no field or function `dorp`", with a "did you mean `drop`?" note.
- **Effects.** It follows lambda rules: `IO.readAllLines() |> .map (.split ',') |> .length` works in a `{IO}` function.

Examples: `examples/accept/method-sections.sw`, `examples/reject/section-unknown-receiver.sw`, `examples/reject/section-no-such-function.sw`, `examples/reject/section-on-next-line.sw`.

### `match`

`match` takes apart one or more values in an expression, with the same patterns as arms:

```
def describe (xs: List Nat): Text :=
  match xs with
    | Nil        => "empty"
    | Cons x Nil => "one"
    | _          => "many"

def zipLen (xs: List Nat) (ys: List Nat): Nat := 1 + match xs, ys with
  | Cons _ a, Cons _ b => zipLen a b
  | _, _ => 0
```

The alternatives start with `|`, lined up one under another and further right than the line the `match` starts on. A `match` may also be written on one line: `match n with | Zero => 0 | Succ k => k`. Several scrutinees are separated by commas, and each alternative has one pattern for each. Branches may be several lines, as in a `handle`. Alternatives are tried from top to bottom, and together they must cover every case (`E-NONEXHAUSTIVE`).

Patterns are those of arms: variables, `_`, numbers, constructors, tuples, record patterns and `()`. A `match` can also be used in a signature (`def Pick (b: Bool): Type := match b with | True => Nat | False => Text`), and may be nested in a branch.

There are two translations. If the `match` is the whole right-hand side of a definition, and every scrutinee is an unnamed parameter that its patterns haven't already taken apart, the `match` becomes part of the definition's case tree, as if you had written more arms. Any other `match` becomes a generated definition, named after the definition it is in (shown as `owner.%match1`, though error messages say "this `match`"), which takes the values it needs from the surrounding code and is called where the `match` was. A scrutinee that is a variable is refined in the branches, and so is everything whose type mentions it. A scrutinee that is any other expression is generalised: wherever it appears in the expected type, it's replaced by the pattern of the branch.

`match h: e with` gives each branch an equation `h` about the original expression, such as `h: length xs = Zero` in the `Zero` branch. The expression is also generalised in the expected type, even when `e` is a variable. A `match` with a name is always generated as a definition.

This is how a proof splits on an `if`: matching on the condition replaces it in the goal, and `h` is the evidence for the branch. No motive is written by hand (`Bool.inspect` asks for one).

```
theorem pickGe: (w: Nat) -> (xs: List Nat) -> (c: Nat) -> (after: List Nat) -> c <= Pair.fst (Bank.best.pick w xs c after)
  | Succ w, Cons x more, c, after =>
    match e: Nat.leq (Succ c) x with
      | True  => Nat.leTrans c x (Pair.fst (Bank.best.pick w more x more)) (Nat.lessLe c x e) (pickGe w more x more)
      | False => pickGe w more c after
```

Write the condition as `Nat.leq …` (`Bool` values), not `a <= b`: that form is the `Decidable` test the `if` elaborates to, and generalising it can be `E-MATCH-MOTIVE`. Hypotheses whose types mention the condition (`h: Nat.leq a b = False -> …`) are generalised too, and a branch's goal has already computed one step further, so a branch may need less than the same proof under `Bool.inspect` did. Real proofs: `aoc/src/day03/day03.sw` (`pickGe`, `pickLen`, `pickSub`, `pickBestStep`) and `aoc/src/day02/day02.sw` (`window`, `gaussPick`).

A scrutinee that performs abilities runs once, in order from left to right, before any branch is chosen. Branches may perform abilities too, if the ability row of the definition allows them.

The first version has limits. Each one is `E-MATCH-MOTIVE`, and the message says how to get round it:

- the same variable is matched twice (`match n, n with …`);
- one scrutinee is part of another (`match n, Succ n with …`);
- the type of one expression scrutinee mentions another expression scrutinee;
- generalising a scrutinee makes the type of something else ill-formed.

The way round all of them is a top-level helper with a written signature. `E-MATCH-EQUATION` is for an equality `h` that can't be formed because the scrutinee and the expression have different types. This version doesn't report it.

JavaScript: a `match` that is part of the case tree, with a tail call to its own definition in a branch, becomes a loop like any self tail call. A generated definition doesn't: a `match` that is lifted, in tail position, whose branch calls the owner, is a pair of mutual tail calls, and those aren't loops yet. Deep recursion through it can hit the JS stack limit, which is reported as the boundary's out-of-resources error. A tail `match` on a parameter (the whole right-hand side) isn't affected. Examples: `examples/accept/match.sw`, `examples/extract/match.sw`. Design: [syntax-conveniences.md](proposals/syntax-conveniences.md) section 4.

### `calc`

`calc` writes a proof as a chain of steps, one per line. Each step is `_ R e`, where `R` is `=`, `<=` or `<`, followed by `:= proof`:

```
theorem mixed (a: Nat) (b: Nat) (h1: a = b) (h2: b <= 3): a < 5 :=
  calc a
    _ = b := h1
    _ <= 3 := h2
    _ < 5
```

The steps line up, one column further right than the line `calc` is on, and each starts with `_` (so inside a `calc`, a line starting with `_` is the next step, not an argument of the line before). `calc` is a keyword; the relation always goes on a step line, so `calc a = b := p` is a syntax error. `calc` is an expression, usable wherever a proof is.

- **Steps.** `e0` is inferred, and each later expression is checked at its type. Step `i` is the proposition `e(i-1) R e(i)`, and its proof is checked against that. A proof that proves something else is `E-CALC-STEP`, pointing at the proof and saying what the line says.
- **A step with no proof** is closed by `rfl`, checked against the step's proposition: the step holds if that proposition computes to true. For `=` that means the two sides compute to the same value. For `<=` and `<` it is about the order proposition, not the ends: `_ <= n` after `0` needs no proof (`Nat.leq 0 n` computes to `True`), but `calc n` then `_ < n` is rejected even though both ends are `n`. Otherwise it is `E-CALC-STEP` ("this step has no proof, and `rfl` doesn't prove it").
- **Relations.** `=` works at any type. `<=` and `<` are on `Nat` only for now (`E-CALC-RELATION`), and `=`, `<=`, `<` can be mixed freely. Other relations (`!=`, `>`, …) aren't chained; `!=` is a syntax error.
- **The conclusion.** The chain proves `e0 R e(n)`, where `R` comes from folding the steps' relations left to right: `=` with `R` is `R`, `<=` with `<=` is `<=`, and any `<` makes it `<`. The steps are joined with the proofs people write by hand: `Eq.trans`, `J` with `Eq.sym` for `=` next to an order, `Nat.leTrans` and `Nat.lessTrans`, and the kernel re-checks the result as usual.
- **With a goal.** Where the type is known, the chain is checked against it by computation: its first and last expressions only have to compute to the goal's sides, and its relation must be the goal's (`<` is not weakened to `<=`; `Nat.lessLe` does that). Otherwise it is `E-CALC-GOAL`, naming the end that differs. With no goal (`let h := calc …`), the chain has the type `e0 R e(n)`.

| steps so far, next step | result | term |
|---|---|---|
| `=`, `=` | `=` | `Eq.trans p q` |
| `=`, `R` | `R` | `J (\w _ => w R c) q (Eq.sym p)` |
| `R`, `=` | `R` | `J (\w _ => a R w) p q` |
| `<=`, `<=` | `<=` | `Nat.leTrans a b c p q` |
| `<`, `<=` | `<` | `Nat.leTrans (Succ a) b c p q` |
| `<=`, `<` | `<` | `Nat.leTrans (Succ a) (Succ b) c p q` |
| `<`, `<` | `<` | `Nat.lessTrans a b c p q` |

(`p` proves `a R1 b` and `q` proves `b R2 c`.) Examples: `examples/accept/calc.sw`, `examples/reject/calc-*.sw`. Design: [calc-rewrite.md](proposals/calc-rewrite.md) section 5.

### `rewrite`

`rewrite p in t` proves the goal from `t` by replacing, in the goal, the left side of the equation `p: a = b` by its right side. It spares you the motive: where `Eq.cong (\x => (x + n) / d) p` spells out the expression around the change, `rewrite p` looks for `a` in the goal and works the motive out itself.

```
theorem stepZero (highest: Nat) (n: Nat):
    Bool.toNat (0 == 0) + ((Succ highest - 0) % Succ highest + n) / Succ highest
      = ((Succ highest - 1) % Succ highest + Succ n) / Succ highest :=
  rewrite Nat.modSelf (Succ highest), Nat.modSmall highest (Succ highest) (Nat.leRefl highest), Nat.addSucc highest n
    in Eq.sym (Nat.addDivSelf (Succ highest) n)
```

| form | meaning |
|---|---|
| `rewrite p in t` | `t` proves the goal with `a` replaced by `b` |
| `rewrite p` | the same as `rewrite p in rfl`, against the whole goal |
| `rewrite p, q in t` | `p`, then `q` on what is left, then `t`: `rewrite p in (rewrite q in t)` |
| `rewrite <- p in t` | right to left: `b` is replaced by `a` |

`rewrite` is a keyword. `in` is not: it is only special where a rule can end (outside brackets, inside a rule), so a variable called `in` is an ordinary name, and a rule that passes it as an argument puts it in parentheses, `rewrite f (in) in t`. The result is a `J` term, which the kernel re-checks; the kernel is unchanged.

- **The goal must be known.** `rewrite` is checked against a goal: a definition's body, an argument whose type is fixed, a `calc` step, a `let` with a type. With none (`let h := rewrite p in t`), it is `E-REWRITE-NO-GOAL`; give the type with an ascription, `(rewrite p in t: a = b)`. In a `calc` step, `rewrite p` is checked against the step's line, `e(i-1) R e(i)`, and may rewrite either side.
- **The rule** is any proof of an equation, with its implicit arguments left open if nothing fixes them (`[n: Nat] -> f n = g n` used as `rewrite h`). The equation's *left side* needs a function, constructor or variable at its head; an unknown function (`?g x`) is `E-REWRITE-RULE`, as is a proof that isn't an equation (a lemma still waiting for its arguments).
- **Finding occurrences.** The goal is searched in pre-order, outermost first, left to right, and the search never looks inside an occurrence it has chosen. A subterm is an occurrence if it has the same head and number of arguments as `a`, is the same term or has the same type and *computes* to it. Matching the rule's open arguments is one-way: only the rule's own can be solved, and a candidate that fails leaves nothing solved. Every occurrence is replaced, then `t` is checked against the result. If there are none, it is `E-REWRITE-NOTHING`.
- **Binders.** An occurrence that mentions a variable the goal binds (`f y` in `(y: Nat) -> f y = g y`) is skipped: `J` can't rewrite inside a function without function extensionality. One that doesn't mention it (`f 1`) is rewritten normally. If that leaves nothing, the message points at a pointwise lemma like `List.mapCongr`.
- **Cost.** All the comparisons of one `rewrite` share a budget of evaluation steps. Running out is `E-REWRITE-BUDGET`, never "no match": it says the comparison was too expensive, not that the occurrence is absent. State the step with `calc`, or rewrite with a more specific equation. `STITCHWORT_REWRITE_METRICS=1` prints, per `rewrite`, how many subterms were looked at, how many had the right head, how many comparisons ran and the steps they took.
- **The motive.** After the occurrences are replaced by a variable, the goal must still be a valid proposition (`E-REWRITE-MOTIVE`: the usual cause is an `auto` proof, such as the `d != 0` of `x % d`, that is about the term being replaced; rewrite a larger term that contains it, or use `calc`), and putting the left side back must compute to the original goal. That second check fails only where comparison ignores something it shouldn't have, and is also `E-REWRITE-MOTIVE`.
- **What will surprise you.**
  - `rewrite p` in a `calc` step rewrites the whole step proposition, both sides, not just the expression on the line before. `<-` is therefore needed less often, but it is the only way to replace the right side by the left.
  - Every matching occurrence is replaced. There is no way to pick one; use `calc` to say exactly which form you want.
  - An occurrence can match without being there textually, because a term that computes to the left side matches. And the goal searched is the elaborated goal, which keeps definitions folded only until they can compute: a goal written `Succ m + n` is `Succ (m + n)` by then, and `x % d` has unfolded into `x - x / d * d` (so error messages may show `Nat.leq a b = True` for `a <= b`). A rule's left side is read the same way, so the two still agree.
  - The first match fixes the rule's open arguments. With `f n = g n` and a goal `f 1 + f 2`, only `f 1` is rewritten; `f 2` is a different instance. The search order is what picks the instance, and a chosen occurrence isn't searched inside: in `f (f 1)` with `n := f 1`, the inner `f 1` stays.
  - An occurrence found by being the same term can be of the wrong type: two copies of `\x => x`, one for `Bool` and one for `Nat`, are the same term to the search, and a rule about the `Nat` one meets the `Bool` one first (`E-REWRITE-MOTIVE`: the goal with it replaced is ill typed).
  - `E-REWRITE-BUDGET` is about cost, not truth.
  - If a proof-irrelevant comparison arrives ([proof-irrelevance.md](proposals/proof-irrelevance.md)), a candidate that equals the left side only by ignoring a proof field can match and then fail the round trip, as `E-REWRITE-MOTIVE`.

Examples: `examples/accept/rewrite.sw`, `examples/reject/rewrite-*.sw`. Design: [calc-rewrite.md](proposals/calc-rewrite.md) section 6; as built, its "As built" note.

#### Patterns in `let` and lambdas

`let` and a lambda's parameters take patterns too:

```
let (q, r) := (n / 7, n % 7)
let MkPair a b := p                -- a constructor's arguments need no brackets
let { name, .. } := p
let (a, b): (Nat, Nat) := e       -- the right-hand side is checked against the type
let _ := e
\(a, b) => a + b
\acc (k, v) => acc + v
\{ name, .. } => name
```

`let p := e` followed by the rest of the block means `match e with | p => rest`, and a lambda's pattern parameters are matched against its arguments in the same way. `let x := e` and `let (x) := e` are the ordinary `let`.

A pattern made only of tuples, records, variables and `_` is instead projections, outside a proof: `let (a, b) := e` is `let a := e.fst` and `let b := e.snd`, with `e` computed once (in a hidden `let`, unless it's a variable). So a function using one computes even when `e` is unknown: after `def sw (p: (A, B)): (B, A) := let (a, b) := p; (b, a)`, `sw p` is `(p.snd, p.fst)` by `rfl`. Where the expected type is a proposition (a proof), it stays the `match`, which splits `e` into a pair and so refines the goal ([proposals/let.md](proposals/let.md) §7, §A.7).

The one-alternative `match` must cover every value of the type, or the `let` is `E-LET-REFUTABLE`: coverage is by the type, not the value, so `let Just x = Just 3` is rejected by design. Use `match` to say what happens otherwise. Elimination of proofs still applies (`E-PROP-ELIM`). In a block with abilities, the right-hand side runs once, in order, before the rest.

Limits:

- a record pattern in a lambda needs its type known where the lambda is checked, as `p.name` does;
- a lambda's parameter can't be annotated: `\(x: T) => …` is an error, so annotate the lambda, `((\x => …): A -> B)`;
- a pattern `let` that isn't the whole right-hand side is lifted like a `match`, so it isn't available in `partial` functions, data or ability declarations, or the REPL.

Examples: `examples/accept/let-patterns.sw`. Design: [syntax-conveniences.md](proposals/syntax-conveniences.md) section 5.

### Numbers

A non-negative numeric literal is a `Nat` or an `Int`, depending on what's expected (`Nat` if nothing says); a negative literal such as `-5` is always an `Int`, and `-0` is `0`. An arithmetic expression or comparison has one number type for all its operands, chosen by the first of these that applies: the expected type; a prefix minus (which forces `Int`); an operand with no literal in it; any other operand; else `Nat`. So `3 - 5 = -2` is on `Int`, and `x + 1` follows `x`. A `let` binding keeps its own type: `let m := 3 - 5` is a `Nat`, and `m + i` with `i: Int` is an error.

There is no implicit conversion between `Nat` and `Int`: use `n.toInt`, `Int.toNat` (negatives become 0) or `Int.toNatChecked`.

A literal argument of a generic function takes its type from the expected result when that is known: with `i: Int`, `chooseFirst 5 i` checked against `Int` works, because the result type is used before the arguments are checked ([syntax-conveniences.md](proposals/syntax-conveniences.md) section 7). Known limit: where nothing says what the result is, such as `let v = chooseFirst 5 i`, the `5` is still checked as a `Nat` first and fails; write `chooseFirst (5: Int) i`. Design: [integers.md](proposals/integers.md); examples: `examples/accept/int-literals.sw`, `examples/accept/int-choose-first.sw`, `examples/accept/expected-types.sw`.
