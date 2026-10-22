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

Whitespace around `:` doesn't matter to the parser: `(n : Nat)`, `(n: Nat)` and `(n:Nat)` are the same binder. The house style is `x: T`, with no space before the colon and one after, as in Scala and TypeScript: `(n: Nat)`, `[a: Type]`, `{ lo: Nat }`, `def f (n: Nat): Nat`, `def x: Nat := 1`, `let x: T := e`, `(e: T)`, `match h: e with`, `if h: P then …`. `:=` has a space on both sides. A call with no arguments is written `f()`, with no space before the `()`. **`name()` with no space is a call**, and it is a single atom, so it is one argument: `parseTurns IO.readAllLines()` is `parseTurns (IO.readAllLines())`, `f x()` is `f (x())`, and `f().x` is `(f()).x`: dot notation applies to the result of the call (`IO.readAll().lines`, `f().g y`). With a space, `f ()` is the ordinary application to the unit, so `f x ()` is `f x ()` and `f ().x` is `f (().x)`. The compiler's messages and printed types use the house style.

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
theorem cong (f: a -> b) [x y: a] (p: x = y): f x = f y := J (y' p' => f x = f y') rfl p

-- A theorem's type must be a proposition
theorem zeroPlus (n: Nat): 0 + n = n := rfl

-- A test: a `Bool` (or a decidable proposition, as `if` takes) that `stitchwort test` checks is `True`
test "lengths add up" := Nat.leq (length (List.append [1] [2, 3])) 3

-- Exported to JavaScript by `stitchwort build --js`
export def total: List Nat -> Nat
  | Nil       => 0
  | Cons x xs => x + total xs
```

When a test whose whole body is a comparison (`==`, `!=`, `=`, `<`, `<=`, `>`, `>=`) fails, `stitchwort test` and the playground's Tests tab show the values of its two sides, in the order written:

```
  ✗ part 1 on the example  ran  (`==` is False)
      left:  2
      right: 3
```

The sides are evaluated again only when the test fails (also when the failure comes from the cache, which keeps just the outcome), so a passing test costs nothing extra. A value is cut off with `…` after about 200 characters, and one too large to quote is shown as `… (too large to show)`. A test that isn't a bare comparison (`a == b && c`) just reports `evaluated to False`.

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

List patterns: `[]` is `Nil`, and `[p, q, r]` is `Cons p (Cons q (Cons r Nil))`, by identity with the library's `List` (a user's own `Cons` doesn't change it), wherever a pattern is allowed (arms, `match`, `let`, lambdas). Each element is a pattern; a constructor element takes its arguments without brackets (`[Some a, None]`), and `(-k)` works as in tuples. A list pattern may end in a rest: `[x, y, ..rest]` is `Cons x (Cons y rest)`, where `rest` is any pattern (`..rest`, `.._`); `..` must be last and appears once, and `[..p]` is just `p` (`examples/accept/list-rest-patterns.sw`). There is no `x :: xs` form, and list expressions have no `..` spread (use `++` or `Cons`). A list pattern is refutable like `Cons`, so in `let` the pattern must still cover the type (`let [a, b] := xs` is `E-LET-REFUTABLE`). A missing case is reported as the constructor that lacks it (see `examples/reject/list-pattern-missing-longer.sw`).

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
- **Inside a cycle, a definition must be given all its arguments** wherever it's used, so the termination checker sees what each call passes: `map isOdd xs` inside `isEven` is refused, `map (n => isOdd n) xs` isn't. Outside the cycle, anything goes.
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
- **`auto` only uses decision procedures (definitions marked `instance` returning `Decidable …`) that are already checked and written above the use.** One written above that's still waiting for something below to be checked isn't available yet; `E-AUTO-NONE` says which case applies. Passing the procedure explicitly makes it an ordinary dependency, checked first.

## Definitions in detail

The design is in [the proposal](proposals/declaration-syntax.md). Until 18 October 2026 definitions were a signature line followed by equations (`length : List a -> Nat`, then `length Nil = 0` …), with `->` in lambdas and arms and `let x = e`; that syntax is gone. Some older documents still use it. A header with no body (`def f : T`) is allowed only for the prelude's primitives; anywhere else it is `E-MISSING-DEFINITION`.

```
definition ::= "export"? ("def" | "theorem" | "instance") name binder* ":" type body
body       ::= ":=" expr | arm+
arm        ::= "|" pattern ("," pattern)* ("=>" expr)?
binder     ::= "(" name+ ":" type ")" | "[" name+ ":" type "]"
             | "[" "auto" name ":" type "]" | "[" "auto" type "]" | "(" ")"
interface  ::= "interface" Name binder ("=" "{" fields "}")
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

def main(): {IO} () := report (solve IO.readAllLines())

test "parse" := parseBank "102" == [1, 0, 2]
export def identityNat (n: Nat): Nat := n

let x := 1 + 2                       -- in a block
x => x + 1                          -- a lambda
(x: Nat) (y: Nat) => x + y          -- a lambda with typed parameters
match xs with
  | Nil => 0
  | Cons x _ => x
handle prog() with
  | return x    => [x]
  | choose u, k => List.append (k True) (k False)
```

- `->` is only the function type. `=>` separates a pattern or parameter from what follows (arms, `match`, handlers, lambdas). `=` is only equality; `:=` gives a body or a `let` its value. Using `=` there is `E-DEF-EQUALS`.
- Parameters before the colon have the same name in every arm and can't be matched. Parameters after the colon are matched by the arms. `()` before the colon is an unused unit parameter (it becomes `_`).
- A lambda's parameters are names, patterns, or typed parameters written as a definition's are: `(x: Nat) => …`, `(x y: Nat) => …`, mixed freely (`x (y: Nat) => …`). A typed parameter takes its type from the annotation, which in a checked lambda must agree with the expected parameter type (else `E-TYPE-MISMATCH`, pointing at the annotation), and which lets a lambda with no expected type be inferred: `(p: Person) => p.name` has type `Person -> Text`. A typed parameter can't also be a pattern, and `[x: T]` (implicit) parameters aren't allowed. Examples: `examples/accept/lambda-annotations.sw`.
- A lambda is a run of parameters followed by `=>`: `x => e`, `x y => e` (curried), `_ => e`. A parameter is a lower-case name, `_`, a typed group, or a pattern in brackets (`(a, b)`, `(MkPair a b)`, `{ name, .. }`); `(a, b) => e` is one pair taken apart, not two parameters (for two, write `a b => e`). A constructor or number parameter needs brackets too: `(Trivial) => …`. A lambda is a whole expression only: after `:=`, `=>`, `then`, `else`, `|>`, an opening bracket or a comma, a record field's `=`, or at the start of a block line. As an argument or an operand it needs brackets. There is no backslash form.

> **Lambdas used as arguments need brackets:** `map (x => x + 1) xs`. Without them, `map x => …` is a two-parameter lambda whose first parameter is named `map`. A lambda with two or more parameters whose first parameter hides a function in scope gets the warning `W-LAMBDA-SHADOW`, and an error inside it gets a note saying to bracket the lambda. Example: `examples/accept/lambda-shadow.sw`, `examples/reject/lambda-forgotten-brackets.sw`.

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
- **Parameter order.** The captured variables come in the order they are written: the header's parameters (before the colon), then the arm's pattern variables from left to right, then `let`s and earlier local definitions, each moved later only when a type needs a variable that comes after it. So in `| Cons line rest, c, Succ k, d => def left: Nat -> Bool | …` a `left` that uses `rest`, `k` and `d` is `reach.left rest k d`, then its own argument (`reach.left rest k d c`), whatever order the compiler splits the arguments in. Lifted `match`es take their variables in the same order. A call with a wrong argument shows the definition's whole signature (`examples/reject/local-def-wrong-order.sw`). Examples: `examples/accept/local-def-capture-order.sw`.
- **Naming from outside:** `sumTo.go`, and `f.go.inner` for a definition inside `go`. Names are unique within one top-level definition (`E-DUPLICATE`), even if a later one shadows an earlier one, because the lifted names are all `f.name`.
- **Lemmas:** a local `theorem goZero (a: Nat): go 0 a = a := rfl` about a local function works when that function doesn't call its owner (it must be finished for the lemma's type to compute). If the function calls its owner, it isn't finished while the owner is checked: a proof that needs it to compute fails (with a note suggesting a top-level theorem about `f.go`), and a lemma whose type mentions it is `E-MUTUAL-SIGNATURE`.
- **Limits:** a recursive local definition can't be `{Partial}` (`E-LOCAL-DEFINITION`; define it at top level). A local definition in a cycle with its owner can't be passed unapplied (`E-TERMINATION`): write `x => go x`. A block must end with an expression (`E-PARSE`).
- There is no `where` clause: after a body or the last arm it is `E-WHERE`, which points to local definitions.

Examples: `examples/accept/local-defs.sw`, `examples/accept/local-defs-effects.sw`, `examples/extract/local-defs.sw`. Design: [syntax-conveniences.md](proposals/syntax-conveniences.md) section 3.

**Exact arity.** Every arm has exactly one pattern for each explicit argument after the colon. These are counted after unfolding definitions, up to the first thing that isn't a function type (such as an ability row). So `def f: Nat -> Nat -> Nat` needs `| Zero, y => y`, not `| Zero => y => y`. Fewer patterns is `E-ARITY`, as is a different number in different arms. A `:=` body has no arity rule. Implicit and auto arguments after the colon aren't matched; they're in scope by name.

**`E-DUPLICATE-PARAMETER`.** The names of the header's parameters, and of the implicit and auto parameters after the colon, must all be different.

## Namespaces and imports

Names are grouped into namespaces (docs/proposals/namespaces.md). The library is `Std`. A program sees its **prelude** without asking (docs/proposals/prelude-slim.md §3): the types built-in syntax needs, `Nat`, `Int`, `Bool`, `Char`, `Text`, `List`, `Pair`, `Unit`, `Void`, `Not`, `And`, `Or`, `Decidable`, plus `Option` and `Ordering`; the interfaces `DecEq`, `Ord`, `Add`, `Mul` and `Show`; the ability `IO`; and `not`. A prelude type comes with its own declaration: its constructors (`Cons`, `List.Cons`), its record fields, an ability's operations (`IO.print`, `IO.readLine`, `IO.readAll`) and an interface's methods (`Ord.compare`). **The rest of its namespace needs an import**: `List.map`, `Nat.addComm` and `IO.readAllLines` need `import Std (List, Nat, IO)`, and without it the error says so ("`List.map` needs `import Std (List)`"). `Std.List.map`, written in full, always works. **Dot notation and pipes need no import**: in `xs.map f` and `xs |> .map f` the value's type picks the namespace. Other library types (`Map`, `Set`, `Vec`, `Fin`) aren't in the prelude: even the type's name needs `import Std (Map)`. `auto` and instance search see the whole library, whatever is imported.

```
import Std (List)
import Text (split, join)

def words (line: Text): List Text := split ' ' line

def count (xs: List Nat): Nat := List.length xs     -- needs `import Std (List)`

def total (xs: List Nat): Nat := xs.sum              -- needs nothing
```

- **`namespace Day05`** is the first line of a file (only comments may come before it). It puts everything the file declares in the namespace `Day05`: `Day05.main`, `Day05.Range.size`, and the file is checked and run as that namespace (`stitchwort run` runs `Day05.main`). A file has at most one namespace line, and `Std` and the library's namespaces (`List`, `Text`, …) can't be used for it (`E-STD-NAMESPACE`, `E-NAMESPACE-RESERVED`). Without a namespace line, names have no prefix, as before. Design: [multi-file.md](proposals/multi-file.md).
- **A qualified name** is written without spaces: `List.length`, `Std.List.Cons`. Its first component is found like any name, or as a namespace (the file's own, then an imported library namespace); `Std.…` always means the library. A prelude type used as a qualifier without an import reaches only its own declaration (`List.Cons`, `IO.print`); anything else in a library namespace (`List.map`, `Eq.sym`, `Map.insert`) needs `import Std (List)`, `import Std (Eq)` and so on, or the full `Std.Eq.sym`; dot notation (`p.sym`) needs neither.
- **A type owns a namespace** holding its constructors (`Shape.Square`), and so does an ability, holding its operations (`State.get`). Anything declared with a qualified name goes in that namespace: `Shape.area: Shape -> Nat`. A qualifier that names nothing makes a namespace of the file's own (`Geometry.double`). The library's namespaces can't be added to (`E-STD-NAMESPACE`), however they're written: `List.sum` and `Std.List.sum` are both refused.
- **`import N (a, b)`** goes at the top of the file and makes `a` and `b` from namespace `N` usable without `N.`. Importing a type brings its constructors (or an ability its operations). An item may be any sub-namespace, including one that declares no name of its own (`import Std (Eq)`, then `Eq.sym`). An unknown namespace or name is `E-IMPORT-UNKNOWN`; importing a name the file also declares is `E-IMPORT-CLASH`. `import N (..)` brings every name declared directly in `N`, below the names imported by name (`import List (..)`, then `map`, `filter`, …); it can't name the file's own namespace, `Std` itself, or a type of a project namespace (`E-IMPORT-WILDCARD`). An import's namespace is found without looking at the other imports, so a library namespace whose name isn't in the prelude is written in full: `import Std.Effect (Comp)`, `import Std.Map (insert)` (while `import List (map)` works, `List` being a prelude name). `import Std (List)` is how a file asks for a prelude type's namespace; it isn't a duplicate of the prelude.
- **A short name** means, in order: a local variable, the file's own declaration (or a constructor or operation of the file's own type or ability), an import by name, a name from an `import N (..)`, or the default. The first that has it decides, so a file can define its own `length` or `Option`; hiding `Option` hides its `Some` and `None` too (they're still `Std.Option.Some`). Two different things at the same level are an error only where the name is used (`E-AMBIGUOUS`): write the full name.
- **A project** is a folder with a `stitchwort.yaml` (empty is fine; `sources: [src, lib]` lists the folders to read, default `src`). Every `.sw` file under them starts with a `namespace` line, and files with the same namespace are one module: their declarations are all visible to each other, in any order, but each file has its own imports. Namespaces use each other by `import` or by writing the name in full (`Lib.Range.size`, no import needed); a cycle between namespaces is `E-NAMESPACE-CYCLE`. `stitchwort check`, `test` and `run NAME` look for the project from the current folder up (or take `--project DIR`); a file given by path (`stitchwort run hello.sw`) is checked on its own, using only the library.
- **Syntax always means the library's**: `+`, `==`, `++`, `if`, literals and `()` don't depend on what names a file declares.

## Type synonyms and bracket layout

**Type synonyms.** `type Grid = List (List Nat)` is `def Grid: Type := List (List Nat)`: a transparent name, interchangeable with what it stands for, with its own namespace (`def Grid.rolls (g: Grid) …`, then `g.rolls`). Parameters are written as binders, `type Matrix (a: Type) = List (List a)`, and the type can be a tuple, `type Point = (Nat, Nat)`. After `=`, `{` starts a record and `|` a sum type's constructors (each constructor starts with its own `|`, even a single one: `type T = | Foo (x: Nat)`); anything else is the type. `type T = A | B` and `type T = Foo (x: Nat)` look like sums without their `|`, so they're `E-PARSE` with a note saying so (`examples/accept/type-synonyms.sw`, `examples/reject/type-synonym-*.sw`). A synonym can't be recursive: `type A = B` with `type B = A` leaves neither with a type to stand for (`E-SYNONYM-CYCLE`, `examples/reject/synonym-*.sw`).

**Brackets continue lines.** Inside `[ ]`, `( )` and `{ }`, a line starting with `,` or a closing bracket continues the bracket however far left it starts, so a list can be laid out with leading commas (`examples/accept/list-literal-layout.sw`). A trailing comma is allowed in list, tuple and record expressions and patterns, and in a record declaration's fields.

## Indexed data types

docs/proposals/indexed-families.md §7; `examples/accept/indexed-families.sw`.

- **Indices go after the header's colon**, parameters before it: `type Vec (a: Type): Nat -> Type =`. They can be named, `(len: Nat) -> Type`, and a later one's type can mention an earlier one, `(n: Nat) -> Fin n -> Type`. An index's type must fit in the type's universe, as a field's must, so a type indexed by types is written `Ty: Type -> Type 1` (`E-UNIVERSE` otherwise). Records and synonyms have no indices (`E-RECORD-INDICES`, `E-PARSE`).
- **Each constructor states its result type** after `:`, the type applied to its parameters exactly as declared, then indices: `| VCons (x: a) (xs: Vec a n): Vec a (Succ n)`. `Vec Nat 0` in `Vec (a: Type)` is `E-TYPE-MISMATCH`. Without indices the result type is optional.
- **Implicit fields.** `[n: Nat]` among a constructor's fields is an implicit field. In a constructor of a type with indices, an undeclared lowercase name (`n` above) becomes an automatic implicit field, as in a signature; a use in an index counts (`FZero: Fin (Succ n)` binds `n: Nat`). Automatic fields go first, ordered by their dependencies; one whose type would mention a written field must be written out, after it (`E-IMPLICIT-FIELD`). Implicit fields are filled in by unification when building a value, or named: `VCons [n := k] x xs`.
- **Write `Succ n` (or `1 + n`), not `n + 1`, in an index**: `+` counts down its first argument, so `n + 1` doesn't compute while `n` is unknown.
- **In a signature**, a name used in an index is bound automatically even where it's also used as a value: `def head: Vec a (Succ n) -> a`, `theorem leToLeq: Le m n -> m <= n`.
- **Matching** needs no new syntax. Implicit fields are skipped in patterns, or matched by name, `VCons [n := k] _ _` (positional `[k]` isn't allowed). An arm may be left out only when its constructor can't be there (`head` has no `VNil` arm), or when another argument then has no possible constructor (`get: Vec a n -> Fin n -> a` has no `VNil` arm: there, `i: Fin 0`). A left-out arm that can be there is `E-NONEXHAUSTIVE`. When the compiler can't tell (an index like `n + m` with `n` unknown, or a type to take apart), it's `E-INDEX-STUCK`: match on `n` first, or use a variable index. `()` works for a family with no possible constructor (`Even 1`). An arm that can never match is the warning `W-UNREACHABLE`, and isn't checked.
- **Running and exporting.** A family's values run like any data type's; its forced fields are stored, and its proof fields are erased. An `export` can't have a family anywhere in its inputs or result, directly, through a synonym, in a container or in a record field (`E-EXPORT`); a function may use one inside (`examples/extract/vec-inside.sw`).

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
- **`e.name`** reads a field, or calls a function by dot notation: it looks `name` up in the namespace of `e`'s type `T`, finding the field or `T.name`, and puts `e` in the place of `T.name`'s first parameter of type `T`, whatever its position (`line.split ','` is `Text.split ',' line`; `t.split` alone is `c => Text.split c t`). A nickname's namespace is tried before what it stands for (`p: Price` tries `Price.show`, then `Nat.show`), and `p.sym` on an equation finds `Eq.sym`. It's written without spaces around the `.`, binds tighter than application (`f p.name` is `f (p.name)`), and chains (`t.lead.name`, `(f x).age`). `e.f a` is elaborated as the prefix call `T.f a e` is: where nothing needs to run first, the call's result is compared with the expected type before `e` is checked in its parameter's place, so `def c: List Int := [1, 2].map (x => x)` checks, as `List.map (x => x) [1, 2]` does, and a literal receiver takes its type from the call. Dot notation needs `e`'s type only for the head that names the namespace (`List` for a list literal, whatever its elements), found by inferring `e` once and undoing that; the exceptions, which keep the dot reading (receiver first, its type fixed before the arguments are checked), are a receiver that can't be inferred on its own (`[1, 2].map (x => x).map f`: its lambda needs the expected type), a call that leaves out parameters before the receiver (`t.split`), a named argument, a call that performs operations (the receiver runs first, then the arguments as written), and `x |> .f`. `e`'s type must be known where it's used: `p => p.name` needs `(p: Person) => p.name` unless the function's type is known from elsewhere (`people.map (p => p.name)` works, since `people` is checked first; so does `List.map (p => p.name) people`: in an application, a lambda whose parameter type isn't known yet, and that can't be checked without it, is checked after the later arguments, unless a later argument's type depends on it. Only the checking order changes, not the order arguments are passed or run in). `name()` with no space is a call (see the call style above), and the dot applies to its result: `IO.readAll().lines` is `(IO.readAll()).lines`, and `f().g y` is `(f()).g y`. `f p .name`, with a space, is a method section instead ([Method sections](#method-sections)). See docs/proposals/namespaces.md §4.8.
- **An update** `{ e | f = …, … }` replaces some fields. A later field whose type mentions a replaced one must be replaced too (`E-RECORD-UPDATE`): `{ s | items = xs }` isn't allowed for `s: Sized a`, `{ s | items = xs, size = n, ok = proof }` is.
- **Record patterns** `{ f = p, g, .. }` work wherever patterns do, nested in constructors and other records, when the type of what they match is known (a parameter's from the signature, or a field's from the constructor around it). After `=`, a constructor pattern takes its arguments without parentheses: `{ items = Cons x xs, .. }`.
- **Order of effects**: in a computation, field expressions run in the order written, then the record is built; an update's base runs once, first.
- **`==`** works on a record whose fields are all data with `DecEq` (none depending on another), or proofs of equations in types with `DecEq` (left out of the comparison: `type Dial (highest: Nat) = { position: Nat, inRange: position <= highest }` gets `==`). A `DecEq` instance is derived when the record is declared, as for other data types (see the operator table). Otherwise it's `E-INSTANCE-NONE`, with a note saying why; declare an instance (`instance T.instDecEq: DecEq T := { decide = … }`) instead.
- **`T.ext`** is generated for a record, as a checked theorem: two values are equal when their data fields are. `theorem Dial.ext [highest: _] (x: Dial highest) (y: Dial highest) (positionEq: x.position = y.position): x = y`, with one hypothesis `fEq: x.f = y.f` for each data field `f` and none for proof fields (any two proofs of an equation in a type with `DecEq` are equal). It's there when the data fields don't depend on earlier fields (functions are fine), and each proof field proves an equation in a type with `DecEq` that doesn't mention the record or a type parameter; otherwise `T.ext` is an unknown name. A record with no data fields gets `T.ext x y: x = y`. Interfaces, propositions, records defined together with other types and indexed ones get none. The library's records (`Mod`, `Set`) have none generated; `Mod.ext` is written by hand. A `theorem T.ext` of your own in the same module is used instead, with no error (`examples/accept/record-ext.sw`).
- **After an arrow**, `{` starts an ability row, so a record literal in a function type's result needs parentheses: `(p: Person) -> ({ p | age = p.age } = p)`.
- At the JS boundary a record is a plain object with its fields as keys, in declared order, and no `tag` (DESIGN.md §12).

## Interfaces

An interface describes what a type supports; an instance says how one type supports it; `auto` finds the instance by type (docs/proposals/interfaces.md, stages 1 to 5; `examples/accept/interfaces*.sw`, `examples/accept/eqeq-*.sw`, `examples/accept/operators.sw`).

```
-- A record of operations (and laws: proof fields), with one parameter, a type.
interface Pretty (a: Type) =
  { pretty: a -> Text }

-- An instance: a definition of the interface for one type, marked `instance`.
instance Item.instPretty: Pretty Item :=
  { pretty = i => "item" }

-- It may ask for instances of its type's variables.
instance Pretty.instList [auto p: Pretty a]: Pretty (List a) :=
  { pretty = xs => Text.join ',' (xs.map Pretty.pretty) }

-- Asking for one, by `auto`, named or not.
def shout [auto p: Pretty a] (x: a): Text := Pretty.pretty x ++ "!"
def whisper [auto Pretty a] (x: a): Text := Pretty.pretty x

-- A named alternative: a plain `def` of the interface's type, never found
-- by `auto`, passed by name.
def loud: Pretty Item := { pretty = i => "ITEM" }

test "by name" := shout [p := loud] MkItem == "ITEM!"
```

The library has five interfaces so far. `Ord` is a total order: `compare`, the relations `lessThan` and `lessEq` with their decisions `decLessThan` and `decLessEq`, and laws (`equal`, `flip`, `trans`, and four tying the relations to `compare`), with `DecEq` as its superclass `eq`. It has instances for `Nat` and `Int` (whose relations are `<` and `<=` themselves), `Char`, `Text`, `Bool`, `Ordering`, lists and `Vec` (lexicographic), `Option` (`None` first) and pairs; `List.sort`, `List.maximum` and `List.minimum` use it (`List.sort [ord := descending] xs` for another order), and `Ord.fromCompare` (a comparison and its three laws) and `Ord.byKey` (a key that tells values apart; its `<` and `<=` are the key's own, so `c < x` on a `Fin` is `Fin.toNat c < Fin.toNat x`) build one. A declared data type or record gets one derived: constructors in the order they're declared, then the fields left to right, proof fields left out (`Dial` by its `position`), wherever it gets a derived `==` and its data fields have `Ord`; a module's own `instance T.instOrd: Ord T` replaces it (`examples/accept/derive-ord-*.sw`). `<` and `<=` are its relations, for every type ([Numbers](#numbers)). `Add` (`zero`, `add`, and the laws `zeroAdd`, `assoc`, `comm`: things you add in any order) and `Mul` (`one`, `mul`, and `oneMul`, `mulOne`, `assoc`: not commutative) are `+` and `*`, with instances for `Nat` and `Int`; `List.sum`, `List.sumBy` and `List.product` use them, so `[(3: Int), -5, 1].sum` is `-1` and a list of a user's points adds up with its `Add` instance. `DecEq` (`decide: (x: a) -> (y: a) -> Decidable (x = y)`) is the one `==`, `!=`, `if h: x = y` and `auto` use to decide equations, with `DecEq.uniqueEq` (any two proofs of an equation in a type with `DecEq` are equal) and `DecEq.sound`. Decision procedures for anything else are instances too, but of `Decidable …` (`instance decToken: Decidable Token := …`): none of the rules below apply to them, and `auto` keeps its search for them (first fit, above the use).

`Show` is the fifth: `toText` (what `${e}` inserts) and `toSource` (a source-like form, used for the elements of containers: text in quotes with escapes, `'a'` for a character; not promised to parse back). They agree except for `Text` and `Char`. The library has instances for `Nat`, `Int`, `Bool`, `Char`, `Text`, `Ordering`, lists, `Option`, tuples, `Vec`, `Fin`, `Map` and `Set`; a declared data type or record gets one derived (`Dot`, `Rect 3 4`, `Node Leaf (-1) Leaf`, `{ name = "tea", price = 3 }`; proof fields left out), unless a field is a function, a type, or depends on an earlier field, or the type is used inside another type of its own fields. A module's own `instance T.instShow: Show T` replaces it, and `Show.fromText f` builds one from a single function: `instance Point.instShow: Show Point := Show.fromText Point.toText`. A type with none is `E-INSTANCE-NONE` at the `${…}` (`examples/accept/show.sw`).

**`Mod n`** (`import Std (Mod)`; `examples/accept/mod-arith.sw`, docs/proposals/fin-arithmetic.md) is the numbers 0 to n - 1, where `+` and `*` wrap around, as on a clock: it has `Add` and `Mul` instances (with their laws proved for every `n`), `DecEq`, `Ord` (by value) and `Show` (the number). `Fin n` stays the type of positions in a `Vec`, with no arithmetic, so that `i + 1` at the last position can't silently wrap; `Fin.toMod` and `Mod.toFin` convert. A value is `{ value: Nat, isLt: … }` and runs as a plain number. There are no `Mod` literals: `Mod.ofNat` and `Mod.ofInt` make values, and wrap (`(Mod.ofNat 150: Mod 100)` is 50, `(Mod.ofInt (-1): Mod 100)` is 99, by the Euclidean remainder). There is no `-`: `i.sub j` and `i.neg` are named functions that wrap (`Mod.sub 5 7` is 98 in `Mod 100`). `Mod 0` has one value, 0, so that every `Mod n` has a zero. A dial: `turns.scanLeft (p t => p + Mod.ofInt t) (Mod.ofNat 50: Mod 100)`.

- **An interface is a record** (`type I (a: Type) = { … }`, [Records](#records)) that the compiler finds values of. It has exactly one parameter, a type, and is in `Type` (`E-INTERFACE-SHAPE`). Its fields are its operations; a field whose type is a proposition is a law, erased at runtime.
- **Methods.** Each field `f` of `I` gives `I.f: [a: Type] -> [auto i: I a] -> …`, which takes the field from the dictionary it's given: `Pretty.pretty x`. `i` is the interface's name with a lower-case first letter (`pretty`, `decEq`), so `Pretty.pretty [pretty := loud] x` passes one by name. Methods are in the interface's namespace and can be imported: `import Pretty (pretty)`. On a dictionary `d`, `d.pretty` is its field, by dot notation.
- **Instances** are definitions marked `instance`, always named; `T.instI` or `I.instT` by convention (the name can't be in a namespace of the library: `Pretty.instNat`, not `Nat.instPretty`). The type must be the interface applied to a type name and distinct variables: `Pretty Nat`, `Pretty (List a)`, `Pretty (a, b)`, `Size (Vec a n)`, after unfolding synonyms (`E-INSTANCE-HEAD`: not `Pretty (List Nat)`, not `Pretty a`, not a non-interface). Its parameters may only be those variables (implicit, usually bound automatically) and `auto` parameters asking for an interface of one of them (`E-INSTANCE-PARAMETER`, `E-INSTANCE-CONTEXT`). The body is any expression of the interface type.
- **One instance per interface and type name** (`E-INSTANCE-OVERLAP`), declared in the module that declares the interface or the type (`E-INSTANCE-ORPHAN`): in a project the namespace, in a single file the file. A synonym owns nothing: `type LocalNat = Nat` doesn't make its module an owner of `Nat`. Another choice for a type is a named alternative.
- **Finding one.** For `[auto i: I T]`: if unification already fixed it, that; otherwise the dictionaries in scope (parameters and `let`s of interface type, and the superclasses inside them), then the one instance for `T`'s type name, whose own `auto` parameters are found the same way. A dictionary in scope wins over the instance: inside `shout [p := loud]`, every `Pretty Item` is `loud`. Two different ones in scope is `E-INSTANCE-AMBIGUOUS` (pass one by name); none is `E-INSTANCE-NONE`. Nothing is guessed: while what's needed, or whether a dictionary in scope fits, depends on something not yet worked out, it waits until the rest of the declaration is, and is then `E-INSTANCE-UNKNOWN-TYPE` (annotate) or `E-INSTANCE-STUCK`. There's no depth limit, only a large step budget (`E-INSTANCE-BUDGET`, which means resolution stopped, not that there's no instance).
- **Superclasses.** A field whose type is another interface on the same parameter is a superclass: `interface Child (a: Type) = { base: Base a, law: … }`. The superclasses can't form a cycle (`E-INTERFACE-CYCLE`). A literal of an interface type may leave a superclass out: it's found like an `auto` argument, before the later fields are checked (so `law`'s type can compute with it). A dictionary in scope gives its superclasses too (`[auto c: Child a]` gives a `Base a`, `c.base`). An instance's superclass must be the instance the compiler finds for it (`E-INSTANCE-SUPER`). Asking for an interface and its own superclass on one type is `E-INSTANCE-REDUNDANT`.
- **Order.** As elsewhere, declarations can be in any order: the rest of the module is checked after its instances, and an instance after the instances of its superclasses and of the interfaces it mentions. An instance needed where it can't be checked first (it depends on the declaration that needs it) is `E-INSTANCE-NONE`, with a note saying so.
- **`auto` parameters on types.** A data type, record or synonym may have `auto` parameters among its parameters, always named: `type Map (k: Type) (v: Type) [auto ord: Ordered k] = { … }` (docs/proposals/interfaces.md §7.5; `examples/accept/data-auto.sw`). Wherever the type is written, the parameter is found as a function's `auto` argument is: `Map Text Nat` is `Map Text Nat [ord := Ordered.instText]`, and inside a function with `[auto ord: Ordered k]`, `Map k v` is the map with that `ord`. Another one is given by name, in its place: `Map Nat Nat [ord := descending]`. The dictionary is part of the type, so maps built with different ones have different types (`E-TYPE-MISMATCH`, with a note); an operation on an existing map takes the ordering from the map's type, whatever else is in scope. A variable for it, `(m: Map k v [ord := o])`, is bound automatically like a type variable, and covers maps with any ordering. In an instance's type it must be written that way, `instance Map.instPretty: Pretty (Map k v [ord := o])` (`E-INSTANCE-HEAD` otherwise): where the instance is used, `o` is the one in the type, not found again. It must ask for an interface (`E-DATA-AUTO`), and types defined together must have the same `auto` parameters. The kernel sees an ordinary parameter, and the value has no field for it.
- `[auto` followed by an uppercase name in a type is a binder: `[auto Pretty a] -> Text`. A list literal starting with a variable called `auto` applied to a constructor would need brackets.

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

Effectful code is written in direct style. Arguments are evaluated left to right, and the lines of a block in order. A handler's clauses on their own lines must line up: a `|` at another column belongs to an enclosing handler. An operation on its own (`choose`) is a function, `x => choose x`. A dot call to an effectful function is a call like any other and runs where it's written, also with no further arguments and at the end of a chain of pure calls (`1 + w.toNat.orAbort`). A signature can be a computation that isn't a function: `current: {State Nat} Nat`. Naming or calling a computation where a plain value is expected runs it there, so it's allowed only if it may perform nothing: a function over any row `{e}` used at the empty row, or a `Std.Effect.Comp NoOp NoRes a`, gives its `a` ([proposals/let.md](proposals/let.md) §8). The types stay different: a function returning a computation isn't a function returning a value. A row written `{}` is no row: `{} Nat` is `Nat`. A pure function can use a handler inside; what it handles doesn't appear in its type. How this is translated into ordinary data is described in `docs/core.md`, under "Abilities".

## `IO`

`IO` is an ability with `print: Text -> {IO} ()`, `readLine: () -> {IO} (Option Text)` and `readAll: () -> {IO} Text` (also `IO.print`, `IO.readLine`, `IO.readAll`). `IO.simulate lines prog` runs `prog` against scripted input and records what it prints.

- `IO.readLine()` gives the next line without its LF (and a CR just before it), `None` once nothing remains.
- `IO.readAll()` gives everything that remains, verbatim, line endings included; `""` once nothing remains. After it, `IO.readLine()` is `None`; after some `IO.readLine`s it gives the rest. Under `IO.simulate` it gives the remaining scripted lines, each followed by LF.
- `Text.lines: Text -> List Text` follows Rust's `str::lines`: split on LF, drop a CR right before an LF, and the last line's ending is optional. `"a\nb"` and `"a\nb\n"` both give `["a", "b"]`; `""` gives `[]`; `"\n"` gives `[""]`; `"a\r\nb"` gives `["a", "b"]`. A CR anywhere else stays, including a final one.
- `IO.readAllLines(): {IO} (List Text)` is `(readAll()).lines`. It is total.

## `Text` helpers

Characters are Unicode scalar values, as for `Text.length`. The text comes last.

- `Text.take n t`, `Text.drop n t`: the first `n` characters, and the rest (all of `t`, or `""`, if it is shorter).
- `Text.startsWith p t`, `Text.endsWith s t`, `Text.contains p t`: `Bool`s. The empty text starts, ends and occurs in every text.
- `Text.stripPrefix p t`, `Text.stripSuffix s t`: `Some` of `t` without `p` (or `s`), or `None`.
- `Text.splitOn sep t`: splits at each whole occurrence of `sep`, left to right without overlaps: `"a, b" |> Text.splitOn ", "` is `["a", "b"]`, `"aaa"` on `"aa"` is `["", "a"]`. There is always at least one piece. An empty `sep` doesn't split: the result is `[t]` (as Lean's `String.splitOn`). `Text.split` splits on one `Char`.
- Dot notation puts the receiver in the first `Text` parameter, which is the prefix, suffix or separator here: `"L68".stripPrefix "L"` is `Text.stripPrefix "L68" "L"`, so write `line |> Text.stripPrefix "L"`. `t.take 1` and `t.drop 1` read as usual, since their first `Text` parameter is `t`.

Proved: `Text.stripPrefix p (p ++ t) = Some t`, `Text.startsWith p (p ++ t) = True`, `Text.take n t ++ Text.drop n t = t`.

## Grid helpers

For puzzles over a grid of rows. A row of a known width is a `Vec a width`. The fill or pad value is the first parameter, so dot notation reads `row.shiftRight 0`.

- `Vec.shiftRight fill v`: element i moves to i + 1, the last element drops off and `fill` comes in at the front (`[1, 2, 3]` gives `[0, 1, 2]`). `Vec.shiftLeft fill v` is the other way round (`[2, 3, 0]`).
- `Vec.around pad f v`: `f left x right` for each element and its two neighbours, with `pad` past either end. It is `Vec.zipWith3 f (v.shiftRight pad) v (v.shiftLeft pad)` (`Vec.aroundShifts`), in one pass.
- `Vec.tabulate n f`: `[f 0, …, f (n - 1)]`, where `f` takes a `Fin n` (as `Vec.get` does).
- `List.transposeFill fill rows`: pads every row with `fill` to the longest row's length (`List.maxLength rows`), then transposes, so no column loses a cell. `List.transpose` keeps only as many columns as the first row is long.
- These are in `std/Vec/Grid.sw` and `std/List/Grid.sw` (`tabulate` is in `Vec.sw`). A program loads those files only if it uses one of these names.

The lemmas read a result one index at a time with `List.getOr`, which is the form a proof about one column rewrites with. `i < n` is the row's width. The left neighbour is written `List.getOr pad i (Cons pad row)`: at `Succ c` it computes to `getOr pad c row`, and at 0 it is `pad`.

- `Vec.getOrShiftRight d fill v i (h: i < n)`: index i of `v.shiftRight fill` is `List.getOr d i (Cons fill v.toList)`.
- `Vec.getOrShiftLeft fill v i`: index i of `v.shiftLeft fill` is index `Succ i` of `v`, with `fill` as the default, at every i. `Vec.getOrShiftLeftLt` takes any default and needs `i < n`.
- `Vec.getOrAround d pad f v i (h: i < n)`: index i is `f` of indices i - 1, i and `Succ i`, read with default `pad`.
- `Vec.getTabulate` (`Vec.get (Vec.tabulate n f) i = f i`) and `Vec.getOrTabulate d n f i h` (`= f (Fin.ofNatLt n i h)`).
- `Vec.getOrZipWith` and `Vec.getOrZipWith3`: index i is `f` of index i of each input, when `f` maps the defaults to the default. `Vec.getOrPast`: past the end, `getOr` gives the default.
- `List.transposeFillCell fill rows c r`: row r of column c is `List.getOr fill c` of row r, with no bounds on r or c (cells past the ends are `fill` on both sides). `List.transposeFillColumns` states the whole result as columns read by index. `List.getOrTransposeFill` gives column c as a list. `List.lengthTransposeFill`, `List.lengthColumnTransposeFill` and `List.lengthLeMaxLength` give the lengths.

## `Abort`

`Std.Abort` (`crates/elab/src/std/Abort/Abort.sw`) is an ability for giving up, as `do` over `Option` in Lean or `?` in Roc: code that may give up says `{Abort}`, reads each step's `Option` with `need`, and a handler decides what giving up means.

```
import Std.Abort (need, ensure, abort, toOption)

def turn (t: Text): {Abort} Int :=
  let (c, rest) := need t.uncons     -- a `None` stops the whole computation
  ensure (c == 'L' || c == 'R')
  let n := rest.toInt.orAbort        -- `need`, by dot notation
  if c == 'L' then -n else n

def parse (t: Text): Option Int := toOption (() => turn t)
```

- `Abort.need: Option a -> {Abort} a`, and `Option.orAbort` for dot notation (`o.orAbort`). `Abort.ensure: Bool -> {Abort} ()` gives up on `False`. `Abort.abort(): {Abort} a` gives up wherever a value of any type is expected.
- `Abort.toOption: (() -> {Abort | e} a) -> {e} Option a` and `Abort.orElse: a -> (() -> {Abort | e} a) -> {e} a` are the handlers. Other abilities pass through, so `{IO, Abort}` code works: what was printed before giving up stays printed (`examples/accept/abort.sw`).
- The operation is `Abort.stop: () -> {Abort} Empty`, for handlers of your own. Its result is `Std.Empty`, a `Type` with no values (`Empty.absurd: Empty -> a`), so no handler can resume it. (`Void` is a proposition, and an operation's result must be a type.) `abort()` is `Empty.absurd (stop())`.
- `Abort.toOption (() => need o) = o` and `Abort.orElse d (() => need o) = o.getOrElse d` hold for every `o`, by `rfl` on each case (`Abort.toOptionNeed`, `Abort.orElseNeed`).

## `decreasing`

A definition (or theorem) whose recursion isn't on a piece of an argument
says why it ends: `decreasing e` after the result type, before `:=` or the
arms, where `e` is a `Nat` of the parameters named in the header
(docs/proposals/well-founded-recursion.md, stage 1). Every recursive call
needs a proof that `e` is smaller there: `auto` finds one in scope, or the
call gives it as `[decreasing := proof]`.

```
def digitsOnto (n: Nat) (acc: List Nat): List Nat
  decreasing n
:=
  if big: Nat.leq n 9 = False
  then digitsOnto (n / 10) (Cons (n % 10) acc) [decreasing := Nat.divTenLess n big]
  else Cons n acc

-- The guard style: the `if` puts the proof in scope, and `auto` finds it.
def halvings (n: Nat) (count: Nat): Nat
  decreasing n
:=
  let next := n / 2
  if h: next < n then halvings next (count + 1) else count

-- A theorem recursing on the same measure; `evens.unfold n` is `evens n`'s
-- own equation.
theorem evensShort (n: Nat): List.length (evens n) <= n
  decreasing n
:=
  rewrite evens.unfold n in
  match n with …
```

- `:=` may start a line of its own after `decreasing e`, at the
  declaration's column. On one line: `def f (n: Nat): Nat decreasing n := …`.
- `f.unfold: (x…) -> f x… = <the body, with f in its recursive calls>` is
  generated for every `def` with `decreasing` (not for a theorem). `f x`
  doesn't unfold by itself on an argument that isn't known; `rewrite
  f.unfold x in` takes one step. On known arguments it computes: tests and
  `rfl` work as for any definition.
- A recursive call may be inside a function passed to another, when that
  one has a **congruence lemma** (stage 3a): `List.sumBy (d => if h: d < n
  then weight d else 0) xs` needs the proof of `d < n` like any recursive
  call (here `h`), and the compiler's own proofs use `List.sumByCong`. The
  lemma is found by name, the function's own name and `Cong`, beside it, and
  must say: given the function's parameters in order, each function
  parameter twice (`f1`, `f2`), and then `(x…) -> f1 x… = f2 x…` for each,
  the two calls are equal. `std` has `List.mapCong`, `List.foldLeftCong`,
  `List.sumByCong`, `List.filterMapCong` and `List.occurrencesCong`; your
  own functions can have them too:

  ```
  theorem List.sumByCong [auto add: Add b] (f1: a -> b) (f2: a -> b) (xs: List a) (ef: (x: a) -> f1 x = f2 x):
      List.sumBy f1 xs = List.sumBy f2 xs
  ```

  The function may be in a `let`, take several arguments (`List.foldLeft
  (acc x => …)`), `match` on its argument, and sit inside another such
  function; a `theorem` with `decreasing` may recurse inside any function
  (it needs no lemma).
- Refused, with `E-DECREASING`: a recursive call `auto` can't prove smaller
  (the message shows the goal and the hypotheses in scope); one inside a
  function passed to a function with no congruence lemma, or one of the
  wrong shape (the message says which and why); one inside a function
  stored in data, passed to a local variable, or returning a function
  (comparing functions would need function extensionality); a measure that
  uses no header parameter, definitions that call each other, a recursive
  call in an `if`'s condition or with another recursive call in its
  arguments, and a body that returns a function. A measure that isn't a
  `Nat` is `E-TYPE-MISMATCH`. A definition that never calls itself gets
  `W-DECREASING-UNUSED`.
- A recursive call written with a dot (`rest.total`) works when `auto`
  finds the proof; one that gives `[decreasing := …]` is written in prefix
  form.
- `decreasing` is a keyword.

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
  `E-PARTIAL`. Mentioning one is fine: `u => collatzSteps 3` is a total
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
- Only `stitchwort run` (on either runtime, or with `--js`) and the playground run
  partial code. Tests can't;
  the checker never does.

## Expressions

Loosest-binding first:

| Syntax | Meaning |
|---|---|
| `x y => e` | Function |
| `(x y: A) -> B` | Dependent function type |
| `[x y: A] -> B` | Function type with implicit parameters, filled in by the compiler |
| `[auto x: P] -> B` | An implicit proof of `P`, found from hypotheses in scope or a decision procedure (an `instance` returning `Decidable …`; an equation is decided by its type's `DecEq`); or, for an interface `P` (`[auto ord: Ord a]`), an instance ([Interfaces](#interfaces)) |
| `[auto P] -> B` | The same without a name, for an interface (`[auto Pretty a]`): it can't be referred to or passed by name |
| `if c then a else b` | On a `Bool`, or on a proposition with a decision procedure, as `if _: c then a else b` (Lean's way): `if x < y`, `if n <= hi`, `if d != 0` work on `Nat` and `Int`. `c` is tried as a `Bool` first, exactly as before, so a `Bool` condition (`if xs == ys`) means what it always has; only if that fails is `c` tried as a proposition, with everything the first try did undone. A proposition nothing decides is `E-AUTO-NONE` at the condition (`E-INSTANCE-NONE` for an equation in a type without `DecEq`, as `if f = g` on functions); a condition that's neither is the `Bool` error. So do `&&`, `\|\|` and `not` on comparisons: `if x < y && y < z`, `if not (x < y)`. A condition that performs operations must be a `Bool` |
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
| `a == b` | Whether `a = b`, as a `Bool`, from the type's `DecEq` instance ([Interfaces](#interfaces)), as `if h:` and `!=` do. The library has instances for `Nat`, `Int`, `Bool`, `Char`, `Text`, `Ordering`, and for lists, tuples, `Option` and `Vec` of types with one (`[(1, "a")] == [(1, "a")]`). A declared data type or record gets one derived when it's declared, if its fields can all be compared: data with `DecEq`, the type itself, or proofs of equations in types with `DecEq` (`type Dir = | L | R`, recursive types, `Tree Nat` for `type Tree (a: Type): Type = …`, value parameters). A module's own `instance T.instDecEq: DecEq T` replaces the derived one. `List (Nat -> Nat)` is `E-INSTANCE-NONE`, naming the element type that has none; so is a type with a function field, another proof field or a type field, or defined together with others (mutual), with a note saying why |
| `a < b`, `a <= b` | Comparisons on `Nat` and `Int` (propositions, decided by computation), and through `Ord` on every other type with one. Not associative |
| `a > b`, `a >= b` | `b < a` and `b <= a`: the same terms, so goals, messages and the printer show `<` and `<=`. No interface, no laws of their own. Same level as `<`, not associative. Since `a > b` is `b < a`, `b` is the left operand and is evaluated first (the language is pure, so only the order of effects in an operand could show it). Usable wherever `<` is: `if x > 0`, conditions, tests, theorem statements (`theorem t (h: b < a): a > b := h`) and `calc` chains. `>>` isn't an operator |
| `a ++ b` | Joins two texts (`Text.append`) or two lists (`List.append`). Binds more loosely than `+`, and groups to the right |
| `a + b`, `a - b` | Addition, and subtraction (stopping at zero on `Nat`). Left-associative |
| `a * b`, `a / b`, `a % b` | Bind tighter than `+`. `/` and `%` need a proof that `b != 0` |
| `-e` | Prefix minus; it makes its arithmetic `Int` ([Numbers](#numbers)). Binds tighter than `*` `/` `%` and looser than application and dots: `-x.abs` is `-(x.abs)`, `-18 % 100` is `(-18) % 100`. Not an argument: `f -5` is `f - 5`; write `f (-5)`. May repeat, and `a - -b` needs the space (`--` starts a comment) |
| `(-k)` | In a pattern: a negative `Int` number, in brackets (or as a tuple component, `(-1, 0)`), numerals only |
| `f a b` | Application |
| `!a` | `not a`: prefix "not", written as `-` is. Binds tighter than `*` `/` `%`, `<`, `&&` and the rest, and looser than application and dots: `!xs.isEmpty` is `!(xs.isEmpty)`, `!f x` is `!(f x)`, `!a && b` is `(!a) && b`, `!x > y` is `y < (!x)`. May repeat (`!!a`); not an argument (`f !x` is a syntax error: write `f (!x)`). Like `not`, it's `Bool.not` on a `Bool` and `Not` where a proposition is expected, and `a != b` is unaffected |
| `not a` | `Bool.not a`; where a proposition is expected, `Not a`. Only when `not` is the library's (a local `not` is an ordinary function) and has one argument: `List.map not bs` is `Bool.not` as a function. See below |
| `f [x := e]` | Supplying the implicit parameter `x` by name |
| `_` | A hole the compiler fills in |
| `x`, `Nat`, `Succ` | Names. Constructors and data types start with an uppercase letter |
| `0`, `42`, `-5` | Numeric literals: a `Nat`, or an `Int` where one is expected (`Nat` by default); `-5` is always an `Int`. See [Numbers](#numbers) |
| `'a'`, `'\n'`, `'\u{1F600}'` | `Char` literals: one Unicode scalar value. Escapes are `\n`, `\t`, `\r`, `\\`, `\"`, `\'`, `\$` and `\u{…}` with 1–6 hex digits; `\u{…}` must name a scalar value, so `'\u{D800}'` is an error. Text literals take the same escapes |
| `"héllo"` | `Text` literal: a sequence of Unicode scalar values (see [text-and-io.md](proposals/text-and-io.md)) |
| `"""` … `"""` | `Text` literal over several lines. See "Text blocks" below |
| `include "inputs/day04.txt"` | The `Text` in a file, read when the program is checked. See [`include`](#include) |
| `Type`, `Type 1`, `Prop` | Universes |
| `(e: T)` | Type annotation |
| `[a, b, c]` | `List` literal. In an expression, `[x := e]` supplies an implicit argument and every other `[…]` is a list |
| `{ name = e, age }`, `{ p \| age = e }` | Record literal (with an expected type) and update ([Records](#records)). After an arrow, `{` starts an ability row instead |
| `e.name` | A field, or dot notation: `T.name e …` for `e: T`. No spaces around the `.`; binds tighter than application; `f().x` is `(f()).x` (`name()` with no space is a call) |
| `.name`, `.drop 1` | Method section: `x => x.name`, `x => x.drop 1`. A space before the `.` (or a bracket or line start). See [Method sections](#method-sections) |
| `rfl` | Proof of `a = a` |
| `J (y p => P) base proof` | Transport along an equality |

**Interpolation.** Inside a text literal, `${e}` inserts `e` converted by its type's `Show` instance ([Interfaces](#interfaces)): `"Part 1: ${solvePart1 turns}"` is `"Part 1: " ++ Show.toText (solvePart1 turns)`, and `"n = ${2 + 3}"` is `"n = 5"`. Text and characters are inserted as they are (`"${"tea"}"` is `tea`), and quoted inside lists, tuples, records and constructors (`"${["a", "b"]}"` is `["a", "b"]`). The expression may contain braces and nested text literals, as in `"${f "x"}"`. A `$` not followed by `{` is an ordinary character; write `\$` for a literal dollar sign: `"cost: \$5"`.

**Text blocks.** A text literal over several lines is written between `"""` and `"""`, as Java's text blocks, Swift's and Scala's multi-line strings are, for a puzzle's example input in a test:

```
def example: Text := """
  L68
  L30
    R48
  """
-- is "L68\nL30\n  R48\n"
```

- **The text starts on the line after the opening `"""`**, which holds nothing else (spaces aside); `"""x"""` is `E-PARSE`. One rule, as in Java, and a one-line text is `"x"`, so nothing is lost. The newline after the opening `"""` isn't part of the text.
- **The common indentation is removed**: the fewest leading spaces among the lines with something on them and the closing line, when `"""` is alone on it (Java's rule). So the literal can be indented with the code around it, and a closing `"""` indented less than the text keeps the difference: `"""⏎····a⏎··"""` is `"··a\n"`. Lines of only spaces don't count and become empty; spaces at the end of other lines stay. A tab in the indentation is `E-PARSE` (as in code); tabs elsewhere in a line are ordinary characters.
- **The closing `"""` decides the ending.** Alone on its own line, the text ends with a newline after its last line (`Text.lines` ignores it, so `example.lines` is the ten lines above and nothing more). Right after the last character, there is none: `"""⏎  a⏎  b"""` is `"a\nb"`. `"""⏎"""` is `""`.
- **Escapes and `${…}` are as in `"…"`**, read after the indentation is removed: `\n`, `\t`, `\u{…}`, `\$`, `\"`. A `"` or `""` needs no escape; three in a row do (`\"""`; `\"\"\"` also works). A `${…}` stays on one line (`E-PARSE` otherwise).
- **Line endings are read as `\n`**: a CR before an LF is dropped.
- **It is an ordinary text literal**: the same term as the `"…\n…"` it stands for, with the same hash (`crates/driver/tests/compact_text.rs`), and still compact. Examples: `examples/accept/text-block.sw`.

A partially applied constructor is a function: `Succ` on its own means `n => Succ n`.

### `include`

`include "path"` is a `Text` with the contents of a file, read when the program is checked: `(include "../../../../inputs/day04.txt").lines` is the lines of a puzzle input. The path is a literal in quotes, written like an argument (put it in brackets before a `.`, as above).

- **Relative to the file that has the `include`**, with `/` between names, `..` for the folder above, whatever folder `stitchwort` runs from. It must stay inside the project folder (for a file run on its own, the file's folder); a path above it, or an absolute one, is `E-INCLUDE-OUTSIDE`.
- **The contents are what is hashed, not the path.** The text becomes a literal in the definition, so editing the file reruns exactly the tests that use it, and moving or renaming it, with the same text, changes nothing. Tests in `aoc/src/Aoc/DayNN/Tests/Input.sw` use it to check each day's answers on the committed puzzle input.
- **Errors.** `E-INCLUDE-MISSING` names the file tried (from the project folder); `E-INCLUDE-NOT-TEXT` is a file that isn't UTF-8; `E-INCLUDE-OUTSIDE` includes a path that leaves the project folder, by `..` or through a symlink; `E-INCLUDE-UNAVAILABLE` is anywhere there are no files to read: a single file in the playground (its projects read the bundled files).
- The text is one compact literal like any other, so a 20 KB input costs no more to check or hash than a 20 KB string.

### `&&`, `||` and `not`

Each has two readings, chosen by what's expected, the way `if c` chooses:

- **Where a proposition is expected** (a type: a signature, `if h: …`, an `auto` argument) they're the propositions `And a b`, `Or a b` and `Not a`, and both operands must be propositions. A `Bool` operand is an error (`E-NOT-A-TYPE`) with a note: for a `Bool` `b`, the proposition is `b = True`. `if h: x < y && y < z` gives `h: x < y && y < z` in the `then` branch and `h: Not (x < y && y < z)` in the `else` branch. The library's `Decidable.and`, `Decidable.or` and `Decidable.not` decide them from decisions of each side; both sides are decided before these run, so `if h: p && q` decides `q` even when `p` is false. `And.left`, `And.right` and `Or.neither` take them apart.
- **Otherwise** (a `Bool` expected, as in a `def …: Bool`, a test or `if c`, or nothing known, as in `let`) it's a `Bool`, and **each operand is a condition, as `if` takes one**: a `Bool`, or failing that a proposition with a decision procedure, decided. So `x < y && y < z`, `flag && x < 3` and `not (x < y)` are all `Bool`s, and a `Bool` operand means what it always has. `a && b` is `if a then b else False` and `a \|\| b` is `if a then True else b`: `b` isn't evaluated when `a` decides the answer, and when `b` performs operations, they're performed only if `b` is evaluated. Operations in `a` are performed first. With nothing expected, if the `Bool` reading fails, the proposition reading is tried, with everything the first try did undone; if that fails too, the `Bool` reading's error is reported (`E-AUTO-NONE` at an operand nothing decides, as for `if`).
- **The right side knows the left side**, as in `if a then b else False`: when `a` is a proposition (`n != 0`, `x < y`), `b` is checked knowing that `a` holds in `a && b`, and that it doesn't (`Not a`) in `a || b`, so an `auto` argument in `b` can use it. `n != 0 && len % n == 0` works (the `%` needs a proof of `n != 0`), as does `n = 0 || total / n > 2`; in a chain `a && b && c`, `c` knows both `a` and `b`. A `Bool` left side (`n == 0`, `xs.isEmpty`) says nothing about `b`, just as `if n == 0` doesn't: write `n != 0` or `n = 0` for the fact. When `b` needs no proof, `a && b` is the plain `if a then b else False` on the decision's `Bool`, so the library's lemmas about `&&` and `||` on `Bool`s apply to it; when it does, it's `if _: a then b else False` (`Decidable.elim`), as that `if` makes it.

Precedence, loosest first: `->`, then `\|>`, then `\|\|`, then `&&`, then `=` `!=` `==` `<` `<=` `>` `>=`. So `a \|\| b && c` is `a \|\| (b && c)`, `x < y && y < z` needs no brackets, and `p && q -> r` is `(p && q) -> r`. `not` is a function, so `not x < y` is `(not x) < y`: write `not (x < y)`; prefix `!` binds the same way, tighter than every binary operator (`!x < y` is `(!x) < y`). The printer shows `And p q` and `Or p q` as `p && q` and `p \|\| q`. A single `&` is still an error.

A test (`test "…" := e`) takes `e` as a condition too: a `Bool`, or a proposition with a decision procedure, so `test "ordered" := 1 < 2 && 2 < 3` and `test "small" := 3 < 5` work.

**Anywhere a `Bool` is expected**, a proposition with a decision procedure is decided, as Lean's `decide` coercion does: `List.filter (n => k * n <= size) xs`, `List.all (x => x < 10) xs`, `def le (a b: Nat): Bool := a <= b`. The expression is elaborated as usual; only if it turns out to be a proposition (its type is `Prop`) and the expected type is the library's `Bool` is it replaced by `Decidable.toBool` of its decision. A proposition nothing decides is `E-AUTO-NONE` at the expression, saying a `Bool` is expected (`List.filter (g => g = f) gs` on functions). Where a proposition is expected nothing changes, and conditions (`if c`, `&&`, `||`, `not`, `test`) still try the `Bool` reading first and then the proposition, as above.

### Pipe forward `|>`

`x |> f` is `f x`, and `x |> f a b` is `f a b x`: the value on the left becomes the **last** argument. That's why the library puts the main argument last (`List.map f xs`, `List.sum xs`), so a pipeline reads in the order things happen:

```
def total: Nat :=
  people
    |> List.map (p => p.age)
    |> List.sum
```

**Library convention:** in a function that takes a main value (the collection, optional or text being operated on) plus other arguments, the main value comes last, so pipes read naturally; dot notation (`m.flatMap f`) works regardless of where the main value sits.

It is the loosest operator except `->`, and groups to the left: `x |> f |> g` is `(x |> f) |> g`, `a + b |> f` is `(a + b) |> f`, and `x |> f -> T` is `(x |> f) -> T`. Because it's looser than `=`, `xs |> List.sum = 6` is `xs |> (List.sum = 6)`; write `(xs |> List.sum) = 6`.

- **Layout.** A line may start with `|>` to continue the expression, if it's indented at least as far as the line the expression starts on, even at the enclosing block's own column (as `then` and `else` may). `|>` is its own token, so it never clashes with the `|` of arms and alternatives. After a `match`, a `|>` line at or right of the last alternative's `|` continues that alternative's body (the last alternative takes what follows, as with any operator); one further left, but at least at the `match` line's column, pipes the whole `match`.
- **A lambda on the right** takes the rest of the pipeline: `x |> y => f y |> g` is `x |> y => (f y |> g)`, which means the same as `(x |> y => f y) |> g`.
- **The left side is checked first**, and its type is unified with the function's last parameter before the other arguments are checked. So `people |> List.map (p => p.name)` knows `p: Person` when it reaches the lambda (`List.map (p => p.name) people` works too, by checking the lambda last; see [`e.name`](#records)). A value of the wrong type is `E-TYPE-MISMATCH`, pointing at the function: "this takes `List Nat` as its last argument, but the value before `|>` has type `Text`".
- **The left side runs first** when it performs operations, then the right side's arguments, then the call: `say "left" 1 |> add (say "right" 2)` prints `left`, then `right`.
- **A number literal on the left** is just `f 5`: it takes its type from `f`, as an argument would.

Implicit and `auto` arguments, `[x := e]` and constructors work on the right as in a normal call.

### Method sections

`.f args` is `x => x.f args`: dot notation with the receiver left out.

```
people.map .name                    -- people.map (p => p.name)
people |> .map .age |> .sum         -- (people.map (p => p.age)).sum
ls.map (.split ',')                 -- ls.map (l => l.split ',')
```

- **Chains and arguments.** `.name.length` is `x => x.name.length`. Arguments after the head section belong to it: `.drop 1` is `x => x.drop 1`. As an argument a section takes none, so bracket it: `List.map .name people`, `people.map (.greet "Hi")`. Like `e.name`, the receiver goes in whatever position of the function it fits (`.split ','` is `t => Text.split ',' t`).
- **The space rule.** A section follows a space (or a bracket, or starts the expression): `f p .name` is `f p (.name)`, while `p.name` is still a field access. `p. name` is still an error, and so are `.Name` and `.1`.
- **Pipe.** `xs |> .drop 1` is rewritten by the parser to exactly `xs.drop 1`, with no lambda, so `xs |> .drop 1 |> .sum` is `(xs.drop 1).sum`.
- **Layout.** A section can't start a continuation line as an argument: in `foo xs` followed by an indented `.map f`, the `.map f` would read as another argument of `foo`, so it's a parse error ("a line can't start with a method section"), with a note pointing to `|> .map f` or `(.map f)`. A line starting `|> .map f` is fine.
- **Checking.** A section is a lambda, so it's checked like one: its receiver's type must be known from the expected function type (`people.map .name`, `apply .length "abc"` for `apply (f: Text -> Nat)`), from a pipe's left side, or from an annotation (`(.drop 1: List Nat -> List Nat)`). In an application, a section whose parameter type isn't known yet is checked after the other arguments, so `List.map .name people` works (as `List.map (p => p.name) people` does; a plain lambda is checked in place first and waits only if that fails).
- **The partial application.** Where the receiver lands in the function's last explicit parameter, the section is not a lambda but the partial application `T.f a…` itself: `.snd` is exactly `Pair.snd` and `.isZero` is `Dial.isZero`, so `xs.any .snd` and `xs.any Pair.snd` are the same term, and a proof that restates a program's expression with the qualified name (`match e: Vec.any Pair.snd next with`) still finds it. Where the receiver isn't last, the section stays a lambda: `.sub 3` is `x => Nat.sub x 3`, `.addNat 3` is `x => Mod.addNat x 3`. Implicit arguments are inserted as for the qualified name. A section with chained fields (`.name.length`), or whose arguments don't fit until the receiver's type is fixed, is a lambda too.
- **`_.name`.** `_` is a hole, not a parameter, so `.count _.isZero` is `E-CANNOT-INFER`, with a note to write the section `.isZero`.
- **Unknown receiver.** `let g := .drop 1` or `(.length) "abcd"` is `E-CANNOT-INFER` ("can't tell what `.drop` is applied to"), with a note suggesting a pipe, passing it where a function type is known, or an annotation.
- **No such function.** The ordinary dot-notation error: `xs |> .dorp 1` is `E-UNKNOWN-FIELD`, "`List` has no field or function `dorp`", with a "did you mean `drop`?" note.
- **Effects.** It follows lambda rules: `IO.readAllLines() |> .map (.split ',') |> .length` works in a `{IO}` function.

Examples: `examples/accept/method-sections.sw`, `examples/reject/section-unknown-receiver.sw`, `examples/reject/section-no-such-function.sw`, `examples/reject/section-on-next-line.sw`, `examples/accept/method-section-partial.sw`, `examples/reject/section-underscore.sw`. Design: [method-sections.md](proposals/method-sections.md).

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

What a generalised `match` (an expression scrutinee, or any named one) replaces:

- **The goal.** Every occurrence of the scrutinee in the expected type is replaced by the pattern of the branch. An occurrence is found by shape: the same term, ignoring source positions and binder names. No definition is unfolded to look for it and no metavariable is solved, so `Ord.compare y x` is not an occurrence of `Ord.compare x y`, and `a <= b` (the `Decidable` test) is not `Nat.leq a b`.
- **The goal as it stands.** The expected type is searched in its computed form, not as you wrote it. A definition applied to the scrutinee that can already take a step is searched as what it unfolded to, and once the branch's pattern is put in, the goal computes further. A definition that can't take a step stays a call, and the scrutinee among its arguments is replaced.
- **Hypotheses.** Variables in scope whose types mention the scrutinee (`h: Nat.leq a b = False -> …`), and the variables whose types mention those, are copied: in each branch they have the replaced type. Variables whose types don't mention it are left alone. A `let`-bound variable is copied like a parameter, as an opaque hypothesis: in the branches it has the replaced type, but its value is forgotten (it's no longer definitionally the value it was bound to; the value is passed in from outside, so nothing is lost for the code after the `match`). So after `let small := halfSmall n`, `match e: half n with …` lets a branch match on `small` at its refined type (`examples/accept/match-let-hypothesis.sw`).
- **The equation.** `match h: e with` adds `h: e = pattern`, about the original expression.
- **`auto` arguments.** A scrutinee that is an application with an `auto` argument is searched as elaborated: `match e: Ord.compare x y with` replaces `Ord.compare x y` in the goal and in `h: Ord.compare x y = Less` without `[ord := ord]` (SW-188; an application's dictionary is found as soon as its arguments fix its type, before the goal is searched).

Nothing else changes. The definitions and lemmas you call keep their statements, so a lemma stated about the folded form (`accessible grid s r c`) fails with a type mismatch against a branch's goal that is a step further along. This was the main surprise in the day 4 proofs ([aoc-2025.md](aoc-2025.md), pain point 1), and it is predictable once known. To avoid it, give the lemma the matched value as an argument (`sweepRowCases` on the marks, `ifFloorRoll` on the condition), or state it about the computed form.

This is how a proof splits on an `if`: matching on the condition replaces it in the goal, and `h` is the evidence for the branch. No motive is written by hand (`Bool.inspect` asks for one).

```
theorem pickGe: (w: Nat) -> (xs: List Nat) -> (c: Nat) -> (after: List Nat) -> c <= Pair.fst (Bank.best.pick w xs c after)
  | Succ w, Cons x more, c, after =>
    match e: Nat.leq (Succ c) x with
      | True  => Nat.leTrans c x (Pair.fst (Bank.best.pick w more x more)) (Nat.lessLe c x e) (pickGe w more x more)
      | False => pickGe w more c after
```

Write the condition as `Nat.leq …` (`Bool` values), not `a <= b`: that form is the `Decidable` test the `if` elaborates to, and generalising it can be `E-MATCH-MOTIVE`. Hypotheses whose types mention the condition (`h: Nat.leq a b = False -> …`) are generalised too, and a branch's goal has already computed one step further, so a branch may need less than the same proof under `Bool.inspect` did. Real proofs: `aoc/src/day03/day03.sw` (`pickGe`, `pickLen`, `pickSub`, `pickBestStep`) and `aoc/src/day02/day02.sw` (`window`, `gaussPick`).

**Proving things about a definition with an inner `match`.** A `match` inside an arm that isn't the whole right-hand side (an operand of `||`, say) becomes a generated function whose name source can't write, so a lemma can't mention it. A proof doesn't need to:

- *Arms compute.* A call with constructors where the definition splits is already its right-hand side, so `reach (Cons line rest) c (Succ k) d` is an `if` on `charAt line c == '^'` without any lemma, and any equation of that kind is `rfl`.
- *Match on the condition.* `match e: cond with` refines a hypothesis about the call (a parameter, a lambda's variable or a `let`), because the condition is there once the call has unfolded.
- *Leave the inner `match`'s part as `_`.* Arguments you write out inside a branch (`reach (Cons line rest) c (Succ k) d`) are elaborated afresh and aren't refined, only the goal and the variables in scope are. A `_` is solved by unification from the hypothesis, so the generated function is filled in and never written. The type mismatch note for a written-out argument suggests this.
- *Split its scrutinee to make it compute.* The generated function unfolds once its own scrutinee is a constructor, so `match c with | Zero => … | Succ b => …` turns the hidden operand into `False` or `reach rest b k d`.
- *To state something about it, name it.* Writing the same `match` in a lemma makes a second generated function, which is a different definition (two generated functions are never equal while their scrutinee is unknown). Make the `match` a local `def` in the arm and refer to it from outside as `owner.name` ([Local definitions](#local-definitions)).

Example: `examples/accept/match-inner-match-proof.sw`; a real proof is `fallKeeps` in `aoc/src/Aoc/Day07/Proofs/Part1.sw`. Design: [proposals/equation-lemmas.md](proposals/equation-lemmas.md).

A scrutinee that performs abilities runs once, in order from left to right, before any branch is chosen. Branches may perform abilities too, if the ability row of the definition allows them.

The first version has limits. Each one is `E-MATCH-MOTIVE`, and the message says how to get round it:

- the same variable is matched twice (`match n, n with …`);
- one scrutinee is part of another (`match n, Succ n with …`);
- the type of one expression scrutinee mentions another expression scrutinee;
- generalising a scrutinee makes the type of something else ill-formed.

The way round all of them is a top-level helper with a written signature. `E-MATCH-EQUATION` is for an equality `h` that can't be formed because the scrutinee and the expression have different types. This version doesn't report it.

JavaScript: a `match` that is part of the case tree, with a tail call to its own definition in a branch, becomes a loop like any self tail call. A generated definition doesn't: a `match` that is lifted, in tail position, whose branch calls the owner, is a pair of mutual tail calls, and those aren't loops yet. Deep recursion through it can hit the JS stack limit, which is reported as the boundary's out-of-resources error. A tail `match` on a parameter (the whole right-hand side) isn't affected. Examples: `examples/accept/match.sw`, `examples/extract/match.sw`. Design: [syntax-conveniences.md](proposals/syntax-conveniences.md) section 4.

### `calc`

`calc` writes a proof as a chain of steps, one per line. Each step is `_ R e`, where `R` is `=`, `<=`, `<`, `>=` or `>`, followed by `:= proof`:

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
- **Relations.** `=` works at any type. `<=` and `<` are on `Nat` only for now (`E-CALC-RELATION`), and `=`, `<=`, `<` can be mixed freely. `>=` and `>` chain the other way round: a chain whose steps are `=`, `>=` and `>` is read from its last expression back, so `calc a` / `_ > b := p` / `_ >= c := q` is `calc c` / `_ <= b := q` / `_ < a := p` and proves `c < a` (which is what `a > c` means); the proofs are those of the flipped steps (`p: b < a`), and an `=` step's proof is used flipped, with `Eq.sym`. `<`/`<=` and `>`/`>=` can't be mixed in one chain (`E-CALC-RELATION`). Other relations (`!=`, …) aren't chained; `!=` is a syntax error.
- **The conclusion.** The chain proves `e0 R e(n)`, where `R` comes from folding the steps' relations left to right: `=` with `R` is `R`, `<=` with `<=` is `<=`, and any `<` makes it `<`. The steps are joined with the proofs people write by hand: `Eq.trans`, `J` with `Eq.sym` for `=` next to an order, `Nat.leTrans` and `Nat.lessTrans`, and the kernel re-checks the result as usual.
- **With a goal.** Where the type is known, the chain is checked against it by computation: its first and last expressions only have to compute to the goal's sides, and its relation must be the goal's or compute to it — for example, a `<` chain ending at `Succ b` proves `a <= b`, since `a < Succ b` computes to `a <= b`; `<` is not otherwise weakened to `<=` (`Nat.lessLe` does that). Otherwise it is `E-CALC-GOAL`, naming the end that differs. With no goal (`let h := calc …`), the chain has the type `e0 R e(n)`.

| steps so far, next step | result | term |
|---|---|---|
| `=`, `=` | `=` | `Eq.trans p q` |
| `=`, `R` | `R` | `J (w _ => w R c) q (Eq.sym p)` |
| `R`, `=` | `R` | `J (w _ => a R w) p q` |
| `<=`, `<=` | `<=` | `Nat.leTrans a b c p q` |
| `<`, `<=` | `<` | `Nat.leTrans (Succ a) b c p q` |
| `<=`, `<` | `<` | `Nat.leTrans (Succ a) (Succ b) c p q` |
| `<`, `<` | `<` | `Nat.lessTrans a b c p q` |

(`p` proves `a R1 b` and `q` proves `b R2 c`.) Examples: `examples/accept/calc.sw`, `examples/reject/calc-*.sw`. Design: [calc-rewrite.md](proposals/calc-rewrite.md) section 5.

### `rewrite`

`rewrite p in t` proves the goal from `t` by replacing, in the goal, the left side of the equation `p: a = b` by its right side. It spares you the motive: where `Eq.cong (x => (x + n) / d) p` spells out the expression around the change, `rewrite p` looks for `a` in the goal and works the motive out itself.

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
| `rewrite p at h in t` | in `t`, the hypothesis `h` has its type with `a` replaced by `b` |
| `rewrite p at h` | the rewritten `h` itself, as a term |
| `rewrite p, q at h` | `p`, then `q` on what is left, in `h`'s type |
| `rewrite p at f x y` | the term `f x y` with its type rewritten (no `in`: there is no name to rebind) |

`rewrite` is a keyword. `in` and `at` are not: they are only special where a rule can end (outside brackets, inside a rule, and not as a field `r.at`), and `in` also where the target after `at` can end. So a variable called `in` or `at` is an ordinary name, a rule may start with one (`rewrite at b h in t`, with `at` a lemma), and a rule that passes one as an argument puts it in parentheses, `rewrite f (in) in t`, `rewrite f (at) at h`. The result is a `J` term, which the kernel re-checks; the kernel is unchanged.

- **The goal must be known**, without `at`. `rewrite` is checked against a goal: a definition's body, an argument whose type is fixed, a `calc` step, a `let` with a type. With none (`let h := rewrite p in t`), it is `E-REWRITE-NO-GOAL`; give the type with an ascription, `(rewrite p in t: a = b)`, or rewrite a fact's type instead with `at`. In a `calc` step, `rewrite p` is checked against the step's line, `e(i-1) R e(i)`, and may rewrite either side.
- **`at`: rewriting a hypothesis.** `rewrite p at h` searches the type of `h` instead of the goal, by the same rules (below), and is `h` carried along `p`: a fact about `b` where `h` was about `a`. It never needs a goal, so it works in an untyped `let`, under `Eq.sym`, or where the goal has computed past what you'd rewrite: in `d != 0` from `h: 1 <= d`, the goal after `e: d = 0` is `False = True`, with no `0` left in it, but `e => Bool.falseNotTrue (rewrite e at h)` rewrites `h` to `1 <= 0`, which computes to `False = True`. With `in t`, `h` is rebound for `t` (a `let`, so the old `h` is shadowed; a hypothesis whose type mentions the old `h` isn't changed). `in` needs a local name after `at` (`E-REWRITE-TARGET` otherwise); without `in`, any expression may follow `at`, such as a lemma applied to its arguments. To rewrite the goal too, nest: `rewrite p at h in rewrite p in t`. The errors are the goal's, about "the type of `h`". Examples: `examples/accept/rewrite-at.sw`, `examples/reject/rewrite-at-*.sw`; design: [rewrite-hypothesis.md](proposals/rewrite-hypothesis.md).
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
  - An occurrence found by being the same term can be of the wrong type: two copies of `x => x`, one for `Bool` and one for `Nat`, are the same term to the search, and a rule about the `Nat` one meets the `Bool` one first (`E-REWRITE-MOTIVE`: the goal with it replaced is ill typed).
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
(a, b) => a + b
acc (k, v) => acc + v
{ name, .. } => name
```

`let p := e` followed by the rest of the block means `match e with | p => rest`, and a lambda's pattern parameters are matched against its arguments in the same way. `let x := e` and `let (x) := e` are the ordinary `let`.

A pattern made only of tuples, records, variables and `_` is instead projections, outside a proof: `let (a, b) := e` is `let a := e.fst` and `let b := e.snd`, with `e` computed once (in a hidden `let`, unless it's a variable). So a function using one computes even when `e` is unknown: after `def sw (p: (A, B)): (B, A) := let (a, b) := p; (b, a)`, `sw p` is `(p.snd, p.fst)` by `rfl`. Where the expected type is a proposition (a proof), it stays the `match`, which splits `e` into a pair and so refines the goal ([proposals/let.md](proposals/let.md) §7, §A.7).

The one-alternative `match` must cover every value of the type, or the `let` is `E-LET-REFUTABLE`: coverage is by the type, not the value, so `let Some x = Some 3` is rejected by design. Use `match` to say what happens otherwise. Elimination of proofs still applies (`E-PROP-ELIM`). In a block with abilities, the right-hand side runs once, in order, before the rest.

Limits:

- a record pattern in a lambda needs its type known where the lambda is checked, as `p.name` does;
- a pattern `let` that isn't the whole right-hand side is lifted like a `match`, so it isn't available in `partial` functions, data or ability declarations, or the REPL.

Examples: `examples/accept/let-patterns.sw`. Design: [syntax-conveniences.md](proposals/syntax-conveniences.md) section 5.

### Numbers

A non-negative numeric literal is a `Nat` or an `Int`, depending on what's expected (`Nat` if nothing says); a negative literal such as `-5` is always an `Int`, and `-0` is `0`. An arithmetic expression or comparison has one number type for all its operands, chosen by the first of these that applies: the expected type; a prefix minus (which forces `Int`); an operand with no literal in it; any other operand; else `Nat`. So `3 - 5 = -2` is on `Int`, and `x + 1` follows `x`. A `let` binding keeps its own type: `let m := 3 - 5` is a `Nat`, and `m + i` with `i: Int` is an error.

There is no implicit conversion between `Nat` and `Int`: use `n.toInt`, `Int.toNat` (negatives become 0) or `Int.toNatChecked`.

`+`, `*`, `<` and `<=` work on any type with the instance they need ([Interfaces](#interfaces); docs/proposals/interfaces.md §5.13): `x + y` is `Add.add x y`, `x * y` is `Mul.mul x y`, and `x < y` and `x <= y` are `Ord`'s `lessThan` and `lessEq`, with the dictionary found as for any `auto` argument, so a dictionary in scope is used (`[auto ord: Ord Nat]` makes `<` on `Nat` its order). On `Nat` and `Int` with no other dictionary in scope that's the library's instances, whose fields are the built-in operations, and the term is the operation itself (`Nat.add x y`), as it always was. `if x < y` decides with the decider in the same dictionary (`Ord.decLessThan`), also through a definition that unfolds to it. The operand type is chosen as above; an expression with `-`, `/`, `%` or a prefix minus is still on `Nat` or `Int` only, and so are literals: generic code writes `Add.zero` and `Mul.one` (`E-TYPE-MISMATCH` otherwise, with a note). Missing an instance is `E-INSTANCE-NONE` (`+` on `Bool`, `<` on functions).

A literal argument of a generic function takes its type from the expected result when that is known: with `i: Int`, `chooseFirst 5 i` checked against `Int` works, because the result type is used before the arguments are checked ([syntax-conveniences.md](proposals/syntax-conveniences.md) section 7). Known limit: where nothing says what the result is, such as `let v = chooseFirst 5 i`, the `5` is still checked as a `Nat` first and fails; write `chooseFirst (5: Int) i`. Design: [integers.md](proposals/integers.md); examples: `examples/accept/int-literals.sw`, `examples/accept/int-choose-first.sw`, `examples/accept/expected-types.sw`.
