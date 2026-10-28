# Surface syntax (implemented subset)

**Status:** describes `crates/syntax` as of 16 October 2026. DESIGN.md §4 shows the intended language. Not yet implemented: anonymous record types and functions over any record with a field (records stages 3 and 4) and a `case` expression.

## Layout

Interim rule, until the full layout specification (DESIGN.md §14):

- A declaration starts at column 0.
- Every following line that's indented continues it.
- Tabs aren't allowed. `--` starts a comment that runs to the end of the line.
- Names are ASCII: letters, digits, `_` and `'`, starting with a letter or `_`. Other characters are fine in text, characters and comments, but `def café` is an error ("unexpected character").
- **ASCII is the base syntax, with a fixed set of Unicode spellings of operators** (D1200): `∈` `∉` `→` `↔` `∧` `∨` `¬` `≤` `≥` `≠` `∃` for `in` `!in` `->` `<->` `&&` `||` `!` `<=` `>=` `!=` `exists`. Each is exactly the token its ASCII form is, so meaning, precedence, errors and hashes are the same either way, and the two mix freely. Any other symbol from logic or mathematics (`∀`, `⊆`, `∪`, `≡`, `λ`, `⇒` …) is an error saying what to write instead, or that it isn't supported. See [Logic notation](#logic-notation-in--and-exists).
- **Blocks.** An expression that starts on a new line is a block: each line at that line's column is a statement, and lines indented further continue it. A statement is `let x := e` (or `let x: T := e`), binding `x` for the following lines, or an expression run for its effects. The last line is the result. A `let` may hold a proof as well as data, and later lines know its value: after `let p := n`, `p` *is* `n` to the checker, so `Nat.leAddRight p 1` proves `n <= n + 1` ([proposals/let.md](proposals/let.md)). A `match` or local definition after a `let` knows it too, and a recursive call on `let r := rest` is as small as `rest`. The value is computed once when the program runs, before the lines after it; a proof or a type isn't computed at all (as for a proof parameter). Messages may show the value where you wrote the name. A `let` performs only what its right-hand side does: binding an effectful function performs nothing until it's called. A `let` whose right-hand side performs an operation (`let k := ask()`) is opaque: its value isn't known until the program runs. A line at the block's column straight after a line ending in an operator (such as `->`) continues that line.
- **An expression `let`** (D1425, D1453). `(let x := e; body)` binds `x` for `body` where a block's line would be awkward: inside brackets, as an argument, or in a one-line definition. It is `let x := e` followed by `body`, with the same tree as the block form, so everything above applies unchanged: later parts know the value, it may bind a proof, `let x: T := e` and patterns work, and a refutable pattern is `E-LET-REFUTABLE`. The `;` ends the value and is required; `in` can't be the separator because it is membership, so in `(let found := x in xs; found)` the value is `x in xs`. A `let` is a whole expression, like a lambda: after `:=`, `=>`, `then`, `else`, an opening bracket or a comma, or at the start of a block line (where `let x := e; body` on one line is the same as two lines). As an argument, an operand or a `|>` stage it needs brackets, and its body runs as far as an expression can, so `(let x := 1; x) + 2` needs the brackets. `;` has no other use. A missing `;` or body is `E-PARSE` (`examples/accept/let-expression.sw`, `examples/reject/let-expression-missing-*.sw`).
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

-- A test: a runtime check, run by `stitchwort test`, that a `Bool` (or a decidable proposition, as `if` takes) is `True`; it may call `Partial` code
test "lengths add up" := Nat.leq (length (List.append [1] [2, 3])) 3

-- Exported to JavaScript by `stitchwort build --js`
export def total: List Nat -> Nat
  | Nil       => 0
  | Cons x xs => x + total xs
```

When a test fails, `stitchwort test` and the playground's Tests tab say why, as far as they can (D601). If the test is a comparison (`==`, `!=`, `=`, `<`, `<=`, `>`, `>=`), they show the values of its two sides, in the order written; for two lists or two texts that aren't equal, also where they first differ (counting from 0):

```
  ✗ parses the example  ran  (`==` is False)
      left:  [1, 2, 4]
      right: [1, 2, 3]
      first difference at [2]: 4 vs 3
```

The comparison can be the last line of a block of `let`s, or an operand of `&&`: the first operand that is false is the one shown, with its text and where it is:

```
  ✗ both parts  ran  (`==` is False)
      left:  3
      right: 4
      in: part1 2 == 4  (day1.sw:14:31)
```

A false operand that isn't a comparison (`isSorted xs`) is named with `in:` alone. The sides are evaluated again only when the test fails (also when the failure comes from the cache, which keeps just the outcome), so a passing test never pays for it, and nothing here changes whether a test passes: the run found `False` first. A value is cut off with `…` after about 200 characters, and one too large to quote is shown as `… (too large to show)`. A test that is neither (`List.all p xs`, `a || b`, `not (a == b)`) reports `evaluated to False`.

Definitions may be named in either case: `length`, or `Not` for a function returning a type.

**Automatic implicits.** An unknown lowercase name in a signature (the whole signature, header parameters included) is bound as an implicit parameter at the front if every use of it is either where a type is expected (`List a`, `a -> b`, `[x: a]`) or the whole argument of a type for a parameter that's a value (Idris's way). So with `type Dial (highest: Nat) = …`, `def part1 (start: Dial highest) (turns: List Turn): Nat` means `def part1 [highest: Nat] (start: Dial highest) …`: its type is the parameter's. "A type" here is a data type, an ability, or a definition whose result is a type (`def Below (n: Nat): Type`). Several are bound in the order of their first uses, and one may depend on another (`(t: Tagged a x)` for `type Tagged (a: Type) (tag: a)` binds `[a: Type] [x: a]`). Uses needing different types are `E-TYPE-MISMATCH` at the later one, with a note. Any other use keeps it an unknown name, so a misspelling doesn't quietly become a parameter: `Dial (highest + 1)` or `… <= highest` in the signature needs `[highest: Nat]` written out. Bound names are in scope by name in the body, as written-out implicits are.

Patterns are variables, `_`, numbers, constructors applied to patterns (nested to any depth, as in `half (Succ (Succ n))`), record patterns ([Records](#records)), or `()`. A number pattern tests for that number, of any size. A character pattern `'L'` is `MkChar 76 _` (the code as a number pattern, the proof as `_`), so it groups and falls through like numbers, and can be nested in other patterns. In an arm with a variable or `_` where other arms have numbers, the argument is known to be none of those numbers, and nothing more: not that it's a `Succ` (so with `def make: (n: Nat) -> ResultType n`, where `ResultType` matches `Zero` and `Succ`, the arms `| 0 => …` and `| n => …` check the second arm with `ResultType n` not computing). What it is known not to be is used where another match on the same numbers (or some of them) meets it: that match takes its own catch-all arm (docs/proposals/literal-match-facts.md). So a proof by the same `match` as a program's reaches the program's `_` arm in its own: with `commandOf` matching `'k'`, `'j'` and `_ => None`, a theorem that only `'k'` and `'j'` are commands is `match char with | 'k' => … | 'j' => … | _ => …`, and in the last arm `commandOf char` is `None` (`examples/accept/literal-match-facts.sw`). From hypotheses `n ≠ 3` and `n ≠ 7`, match `n` on `3`, `7` and `_`, rule out the first two with the hypotheses, and the `_` arm knows the rest. This works for `Nat`, `Char` and `Int` patterns (on an `Int`, for the size within each sign), and through `k +` (`f (Succ (Succ n))` takes `f`'s catch-all when `n` is known to be none of `f`'s numbers less 2), but not through other arithmetic, and the facts aren't hypotheses with names: a proof that needs `n ≠ 3` as a value proves it as usual. To use the shape of a number, match on `Zero` and `Succ` instead; a number pattern in a column that also has `Zero` or `Succ` patterns counts down like `Succ`s. On an `Int`, number patterns can be negative, `(-1)`: a match on `Int` numbers splits on the sign (`OfNat` or `NegSucc`) first, so an arm with a variable or `_` knows the sign of the argument in the branch where it is all that matches, but still nothing about its size. On a `Fin n`, a number pattern is `FZero` or `FSucc` around the one below (`2` is `FSucc (FSucc FZero)`), so it mixes with those patterns and a match on `0`, `1` and `2` of a `Fin 3` is complete (leave out `1` and the error names it: "no arm matches 1"); one not below a known n is `E-FIN-LITERAL` ([`Fin` literals](#fin-literals)). Arms are tried from top to bottom. `()` with a right-hand side matches the unit value; without one, it says the argument's type has no values, and the arm needs no right-hand side:

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
- **`auto` limits how deeply decision procedures depend on each other.** A procedure that needs other decisions (`Decidable.or` needs one for each side) uses one level of depth for each, and the search stops after eight (`E-AUTO-NONE`). A decision of a smaller part of the same proposition costs only a fraction of a level, so a long chain of them is not limited by the eight: `n ∈ [1, 2, …]` unfolds to `1 = n ∨ 2 = n ∨ …`, and `auto` proves it for a literal list of 100 elements as quickly as for 9, and says `E-AUTO-FALSE` when `n` isn't in it. The chain is bounded at a couple of thousand steps. Examples: `examples/accept/auto-membership-long-list.sw`, `examples/reject/auto-membership-absent.sw`.

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
(let x := 1 + 2; x * x)              -- an expression
x => x + 1                          -- a lambda
(x: Nat) (y: Nat) => x + y          -- a lambda with typed parameters
[a: Type] (x: a) => x               -- a lambda with an implicit parameter
match xs with
  | Nil => 0
  | Cons x _ => x
handle prog() with
  | return x    => [x]
  | choose u, k => List.append (k True) (k False)
```

- `->` is only the function type. `=>` separates a pattern or parameter from what follows (arms, `match`, handlers, lambdas). `=` is only equality; `:=` gives a body or a `let` its value. Using `=` there is `E-DEF-EQUALS`.
- Parameters before the colon have the same name in every arm and can't be matched. Parameters after the colon are matched by the arms. `()` before the colon is an unused unit parameter (it becomes `_`).
- A lambda's parameters are names, patterns, or typed parameters written as a definition's are: `(x: Nat) => …`, `(x y: Nat) => …`, mixed freely (`x (y: Nat) => …`). A typed parameter takes its type from the annotation, which in a checked lambda must agree with the expected parameter type (else `E-TYPE-MISMATCH`, pointing at the annotation), and which lets a lambda with no expected type be inferred: `(p: Person) => p.name` has type `Person -> Text`. A typed parameter can't also be a pattern. Examples: `examples/accept/lambda-annotations.sw`.
- A lambda may bind implicit and `auto` parameters, written as a header writes them: `[a: Type] (x: a) => x`, `[a b: Type] => …`, `[auto h: Ord a] => …`, `[auto Ord a] => …` (docs/proposals/lambda-syntax.md §4.3, D91). Each parameter has a mode, explicit, implicit or auto, matching the three kinds of function type. Checked against a function type, a `[a: T]` parameter takes the type's leading implicit parameter (an `[auto h: P]` one its leading auto parameter), binding it by its own name so the body can use it; the written type must agree with the expected one. It never has a parameter introduced in front of it: against anything else (an explicit function type, an auto parameter where an implicit one is written or the reverse, a type that isn't a function) it's `E-TYPE-MISMATCH`, "this lambda takes an implicit parameter first, but the expected type `Nat -> Nat` takes an explicit one". Inferred with no expected type, it has an implicit (or auto) function type: `let pick := [a: Type] (x: a) (y: a) => x` is `[a: Type] -> a -> a -> a`, and each use of `pick` fills in `a`; such a lambda isn't applied to an unknown where it's written, only where it's called. As a definition's whole right-hand side (every arm's), it takes the signature's implicit parameters after the last pattern itself, rather than the signature putting them in scope: `def idf: [a: Type] -> a -> a := [a: Type] => (x: a) => x`. A lambda without `[…]` parameters is unchanged: checked against `[a: Type] -> a -> a`, `x => x` has the implicit parameter introduced for it, under a name it can't use. `[a] => …` (no type) is `E-PARSE`, "a parameter needs a type". Examples: `examples/accept/lambda-implicit-parameters.sw`, `examples/reject/lambda-implicit-mode-mismatch.sw`, `examples/reject/lambda-auto-mode-mismatch.sw`.
- A lambda is a run of parameters followed by `=>`: `x => e`, `x y => e` (curried), `_ => e`. A parameter is a lower-case name, `_`, a typed group (`(x: A)`, or `[a: A]`, `[auto h: P]`), or a pattern in brackets (`(a, b)`, `(MkPair a b)`, `{ name, .. }`); `(a, b) => e` is one pair taken apart, not two parameters (for two, write `a b => e`). A constructor or number parameter needs brackets too: `(Trivial) => …`. A lambda is a whole expression only: after `:=`, `=>`, `then`, `else`, `|>`, an opening bracket or a comma, a record field's `=`, or at the start of a block line. As an argument or an operand it needs brackets. There is no backslash form.

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

Names are grouped into namespaces (docs/proposals/namespaces.md). The library is `Std`. A program sees its **prelude** without asking (docs/proposals/prelude-slim.md §3): the types built-in syntax needs, `Nat`, `Int`, `Bool`, `Char`, `Text`, `List`, `Pair`, `Unit`, `Void`, `Not`, `And`, `Or`, `Decidable`, plus `Option`, `Result` and `Ordering`; the interfaces `DecEq`, `Ord`, `Add`, `Mul` and `Show`; the ability `IO`; and `not`. A prelude type comes with its own declaration: its constructors (`Cons`, `List.Cons`), its record fields, an ability's operations (`IO.print`, `IO.readLine`, `IO.readAll`) and an interface's methods (`Ord.compare`). **The rest of its namespace needs an import**: `List.map`, `Nat.addComm` and `IO.readAllLines` need `import Std (List, Nat, IO)`, and without it the error says so ("`List.map` needs `import Std (List)`"). `Std.List.map`, written in full, always works. **Dot notation and pipes need no import**: in `xs.map f` and `xs |> .map f` the value's type picks the namespace. Other library types (`Map`, `Set`, `Vec`, `Fin`) aren't in the prelude: even the type's name needs `import Std (Map)`. `auto` and instance search see the whole library, whatever is imported.

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

**Brackets continue lines.** Inside `[ ]`, `( )` and `{ }`, a line starting with `,` or a closing bracket continues the bracket however far left it starts, so a list can be laid out with leading commas (`examples/accept/list-literal-layout.sw`). A trailing comma is allowed in list, tuple and record expressions and patterns, and in a record declaration's fields. Even in column 0, such a `,` or closer continues the bracket rather than starting a declaration; a declaration keyword (`def`, `type`, …) in column 0 still starts one, so a missing closer is reported where it should be. The house style for a bracket that spans lines is a comma at the end of each line, no trailing comma after the last item, and the closer on its own line in column 0:

```
type Person = {
  name: Text,
  age: Nat
}
```

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
- **`e.name`** reads a field, or calls a function by dot notation: it looks `name` up in the namespace of `e`'s type `T`, finding the field or `T.name`, and passes `e` as `T.name`'s **first explicit argument** (`line.split ','` is `Text.split line ','`; `t.split` alone is `Text.split t`, plain partial application). Nothing is searched: if `T.name`'s first explicit parameter isn't a `T`, the call is `E-DOT-NO-RECEIVER` ("`Nat.firstFrom` doesn't take a `Nat` first, so `n.firstFrom` can't put `n` there"), with a note to call it in full. So a function meant for dot notation takes its main value first (see the [library convention](#pipe-forward-)). The definition of a function in `T`'s namespace that takes a `T`, but not first, gets the warning `W-RECEIVER-NOT-FIRST` (in a library file it is an error); `@[noReceiver]` before the `def` opts a helper out, for a function not meant to be called with `.` or `|>`. Implicit and `auto` parameters before the first explicit one are inserted as usual. A nickname's namespace is tried before what it stands for (`p: Price` tries `Price.show`, then `Nat.show`), also when the receiver is a call whose declared result type is the nickname (`(mk n).double` with `mk: Nat -> Meters` tries `Meters.double` first), and `p.sym` on an equation finds `Eq.sym`. It's written without spaces around the `.`, binds tighter than application (`f p.name` is `f (p.name)`), and chains (`t.lead.name`, `(f x).age`). `e.f a` is elaborated as the prefix call `T.f e a` is: where nothing needs to run first, the call's result is compared with the expected type before `e` is checked in its parameter's place, so `def c: List Int := [1, 2].map (x => x)` checks, as `List.map [1, 2] (x => x)` does, and a literal receiver takes its type from the call. Dot notation needs `e`'s type only for the head that names the namespace (`List` for a list literal, whatever its elements), found by inferring `e` once and undoing that; the exceptions, which keep the dot reading (receiver first, its type fixed before the arguments are checked), are a receiver that can't be inferred on its own (`[1, 2].map (x => x).map f`: its lambda needs the expected type), a named argument, a call that performs operations (the receiver runs first, then the arguments as written), and `x |> .f`. `e`'s type must be known where it's used: `p => p.name` needs `(p: Person) => p.name` unless the function's type is known from elsewhere (`people.map (p => p.name)` works, since `people` is checked first; so does `List.map people (p => p.name)`, which checks `people` first. In an application, a lambda written before the argument that gives its parameter type, and that can't be checked without it, is checked after the later arguments, unless a later argument's type depends on it; the library puts function arguments last, so this rarely matters. Only the checking order changes, not the order arguments are passed or run in). `name()` with no space is a call (see the call style above), and the dot applies to its result: `IO.readAll().lines` is `(IO.readAll()).lines`, and `f().g y` is `(f()).g y`. `f p .name`, with a space, is a method section instead ([Method sections](#method-sections)). See docs/proposals/namespaces.md §4.8.
- **An update** `{ e | f = …, … }` replaces some fields. A later field whose type mentions a replaced one must be replaced too (`E-RECORD-UPDATE`): `{ s | items = xs }` isn't allowed for `s: Sized a`, `{ s | items = xs, size = n, ok = proof }` is. An update may also change the record's type parameters, as Haskell's does: a parameter can change only if every field whose type mentions it is replaced. With `type Timed (a: Type) = { start: a, end: a, label: Text }`, `{ t | start = Int.toNat t.start, end = Int.toNat t.end }` turns a `Timed Int` into a `Timed Nat`, while replacing `start` alone is `E-RECORD-UPDATE`, naming the kept field `end` that fixes `a`. Where the update's type is inferred (a `let`), the update is first checked as written, so `{ t | start = 5 }` stays a `Timed Int`; only if that fails does a parameter only the new fields mention become a new unknown. A parameter that no replaced field mentions never changes (`examples/accept/record-update-type-change.sw`).
- **Record patterns** `{ f = p, g, .. }` work wherever patterns do, nested in constructors and other records, when the type of what they match is known (a parameter's from the signature, or a field's from the constructor around it). After `=`, a constructor pattern takes its arguments without parentheses: `{ items = Cons x xs, .. }`. As a constructor's argument a record pattern is written in brackets, `Cons ({ name, .. }) rest`: braces right after a constructor name its own fields (next).
- **Named-field constructor patterns** `C { f = p, g, .. }` match a `C`, naming its fields as a record pattern names a record's: `| Circle { id, .. } => id`, `| Circle { text = t, start = 0, .. } => t`, `| Dot { ref, id, start } => …`, `| Polygon { .. } => …` (docs/proposals/variant-fields.md §4). A field alone binds a variable of its name; fields come in any order, each once; without `..` every explicit field is named (`E-RECORD-FIELD`); a name `C` doesn't have is `E-UNKNOWN-FIELD`, listing its fields. It's the positional pattern with `_` for the fields left out, so it works wherever a pattern does (arms, `match`, `let`, bracketed lambda parameters, nested in other patterns) and coverage is the positional pattern's. Braces right after a constructor always name its fields, whatever its arity, and take no further arguments (`C { … } p` is `E-PARSE`); a record as the constructor's argument is `W ({ name, .. })`, or by field, `W { person = { name, .. }, .. }`. Implicit fields aren't named in braces (match them positionally, `VCons [n := k] _ _`). When a one-field constructor's field holds a record that has the field names given too (`Some { value = n, .. }` on an `Option Item` whose `Item` has a `value`), the pattern still names the constructor's field, with the warning `W-RECORD-ARGUMENT`. In expressions, braces after a constructor name its fields too (next bullet). Examples: `examples/accept/ctor-field-patterns.sw`, `examples/reject/ctor-fields-*.sw`.
- **Named construction** `C { f = e, g }` builds a `C` by its fields, wherever an expression goes (`Circle { ref = 1, id = "a", text = "t" }`, `Dot { id, ref = 2 }`; docs/proposals/variant-fields.md §4.5). Fields come in any order, a bare `f` is `f = f`, and every explicit field is given once: an unknown name is `E-UNKNOWN-FIELD` (listing the constructor's fields), a missing one `E-RECORD-FIELD` ("this `Circle` is missing `text`"), one given twice `E-RECORD-FIELD`. It is the positional application with the explicit fields in declaration order (`Circle 1 "a" "t"`), so the term and its hash are the same. Implicit fields are filled by unification as in a positional application (`VCons { x = 1, xs = VNil }`); naming one is `E-UNKNOWN-FIELD` with a note to write `VCons [n := e] …`. A proof field is an explicit field and is given (`MkPos { n = 3, ok = omega }`). Braces right after a constructor always name its fields, so a record as the constructor's argument is `Some ({ name = "tea", price = 3 })`, or by field, `Some { value = { name = "tea", price = 3 } }`; `Some { name = "tea", price = 3 }` is `E-UNKNOWN-FIELD` with a note to bracket. Braces take no further arguments (`C { … } x` is `E-PARSE`), as an argument they need brackets (`f Circle { … }` is `E-PARSE`; write `f (Circle { … })`), and an update isn't a construction (`Some { r | a = 1 }` is `E-PARSE`). A record type's own name isn't a constructor (`Item { … }` is `E-NOT-A-CONSTRUCTOR`; a record literal is written without its name). A type or function that isn't a constructor keeps the old meaning: braces are a record literal argument (`AtR { q = …, n = 0 }`). In a computation the field expressions run in the order written, as for record literals. `show` prints a record inside a constructor in brackets, `Some ({ name = "tea", price = 3 })`, so its output is valid source. Examples: `examples/accept/ctor-field-construction.sw`, `examples/reject/ctor-construction-*.sw`.
- **Shared fields**: a field name `f` is shared by a data type `T` when every constructor has an explicit field `f` of the same type, a type that mentions only `T`'s parameters and other shared fields (syntactically, on the declared type; an implicit field never counts). `T.f : [params] [indices] -> T … -> F` is then generated (one `case`, a branch per constructor) in `T`'s namespace, so `a.f`, `.f` sections (`xs.map .id`), pipes (`a |> .id`), `T.f a` written in full and proofs (`(Circle 1 "a").id = "a" := rfl`, or by cases) all work. It applies to every non-record data type, one-constructor ones and indexed families included (`Pair.fst`, `And.left`, `Char.code`). A written `def T.f` when `f` is shared is `E-DUPLICATE` (the note says to delete it and use the field); when `f` isn't shared it's allowed, and dot notation finds it. When `f` isn't shared, `a.f` is `E-UNKNOWN-FIELD` ("`Shape` has no shared field `text`") with a note saying why: only some constructors have it (match on `a` to read it, `| Circle { text, .. } => …`), its type differs (`id` is `Text` in `Dot` but `Nat` in `Polygon`), its type mentions a field only some constructors have, two fields' order is cyclic across constructors, it's implicit, or (in a proposition) its type mentions data that can't be taken out of a proof. Examples: `examples/accept/shared-fields.sw`, `examples/reject/shared-field-*.sw`; docs/proposals/variant-fields.md §5.
- **Shared-field update**: `{ c | id = x }` on a value of a non-record data type (any number of constructors) rebuilds whichever constructor `c` is, with the named fields replaced. Every named field must be shared; several may be given, in any written order. New values are checked in the shared fields' dependency order; in a computation the base runs first, then the replacements in the order written. In every constructor, a field (explicit or implicit, data or proof) whose type mentions a replaced field must be named too: if it's shared, that's `E-RECORD-UPDATE` ("updating `n` needs `xs` updated too"); if it's implicit or one constructor's own, `E-RECORD-UPDATE` ("`n` can't be updated on every `Labelled`", with a note naming the constructor and field). A field that isn't shared is `E-UNKNOWN-FIELD` ("`Shape` has no shared field `text`"), one no constructor has is "`Shape` has no field `colour`", and one given twice is `E-RECORD-FIELD`. Indexed families are refused (`E-RECORD-UPDATE`). It's elaborated as `let`s and a `match` on the base, so `{ a | xs = ys }` with `ys: Vec Nat (Sized.n a)` checks, and the base may be any expression. Record updates are unchanged. In a theorem's statement, bracket the update (`({ c | id = x }).id = x`), since `{` there starts an effect row. Examples: `examples/accept/shared-field-update.sw`, `examples/reject/shared-field-update-*.sw`; docs/proposals/variant-fields.md §6.
- **Update lemmas.** On an unknown value an update doesn't compute (it's a `match` on the value), so `({ c | id = x }).id = x` isn't `rfl`. Instead, each shared field `f` that an update can replace gets, for each shared field `g`, the theorem `T.f.update.g`, reading `g` after `f` is updated: with `type Shape = | Dot (ref: Nat) (id: Text) | Circle (ref: Nat) (id: Text) (text: Text)`,

  ```
  theorem Shape.ref.update.ref (x: Shape) (ref: Nat): ({ x | ref = ref }).ref = ref
  theorem Shape.ref.update.id (x: Shape) (ref: Nat): ({ x | ref = ref }).id = x.id
  ```

  and likewise `Shape.id.update.ref` and `Shape.id.update.id`; a type's parameters are implicit (`[a: Type] → (x: Tagged a) → (tag: a) → …`). `rewrite Shape.ref.update.id in rfl` proves `({ s | ref = s.ref + 1 }).id = s.id`, finding any update of `ref` written anywhere (two updates of the same fields are equal, docs/proposals/variant-fields.md §6.5), and nested updates `{ { s | ref = 0 } | id = t }` take one lemma each. An update of several fields at once, `{ s | ref = 0, id = t }`, is a different term, which these don't match (`E-REWRITE-NOTHING`); split on the value (`cases`) there. When updating `f` forces other shared fields (`xs: Vec Nat n` for `n`), `T.n.update.g` updates them all, `({ x | n = n, xs = xs }).g`. Only a data field whose type mentions no field is read back: after `{ x | xs = ys }`, `xs` has type `Vec Nat ({ x | xs = ys }).n`, not `Vec Nat x.n`, so there's no `T.xs.update.xs`; a proof field, which isn't unfolded, isn't read either. There are none when updating `f` would need an implicit field or one constructor's own field replaced, nor for records (`({ p | x = 1 }).x = 1` is `rfl`), indexed families (which can't be updated) or propositions. They're generated with the type, checked by the kernel like any theorem, and hover shows them; the names can't be written as declarations (`theorem Shape.ref.update.id` is `E-PARSE`). Example: `examples/accept/shared-field-update-lemmas.sw`; docs/proposals/variant-fields.md §6.6.
- **Order of effects**: in a computation, field expressions run in the order written, then the record is built; an update's base runs once, first.
- **`==`** works on a record whose fields are all data with `DecEq` (none depending on another), or proofs of equations in types with `DecEq` (left out of the comparison: `type Dial (highest: Nat) = { position: Nat, inRange: position <= highest }` gets `==`). A `DecEq` instance is derived when the record is declared, as for other data types (see the operator table). Otherwise it's `E-INSTANCE-NONE`, with a note saying why; declare an instance (`instance T.instDecEq: DecEq T := { decide = … }`) instead.
- **`T.ext`** is generated for a record, as a checked theorem: two values are equal when their data fields are. `theorem Dial.ext [highest: _] (x: Dial highest) (y: Dial highest) (positionEq: x.position = y.position): x = y`, with one hypothesis `fEq: x.f = y.f` for each data field `f` and none for proof fields (any two proofs of an equation in a type with `DecEq` are equal). It's there when the data fields don't depend on earlier fields (functions are fine), and each proof field proves an equation in a type with `DecEq` that doesn't mention the record or a type parameter; otherwise `T.ext` is an unknown name. A record with no data fields gets `T.ext x y: x = y`. Interfaces, propositions, records defined together with other types and indexed ones get none. The library's records (`Mod`, `Set`) have none generated; `Mod.ext` is written by hand. A `theorem T.ext` of your own in the same module is used instead, with no error (`examples/accept/record-ext.sw`).
- **After an arrow**, `{` starts an ability row, so a record literal in a function type's result needs parentheses: `(p: Person) -> ({ p | age = p.age } = p)`.
- At the JS boundary a record is a plain object with its fields as keys, in declared order, and no `tag` (DESIGN.md §12); a one-field record with `@[js.unboxed]` is its field's value instead (Microtypes).

### Field defaults

A record's field, or a constructor's explicit field, may have a default value, written after `:=` (docs/proposals/named-arguments.md §5.1). A record literal or a named construction may then leave that field out.

```
type RangeOptions = {
  start: Nat := 0,
  stop: Nat,
  step: Nat := 1
}

def small: RangeOptions := { stop = 10 }                   -- start = 0, step = 1
def evens: RangeOptions := { stop = 10, step = 2 }

type Sized = {
  size: Nat := 8,
  cells: Vec Bool size := Vec.replicate size False         -- uses the actual `size`
}

type Shape =
  | Circle (radius: Nat) (id: Text := "anonymous")
  | Square (side: Nat)

Circle { radius = 1 }      -- a Shape: id is "anonymous"
Circle 1 "a"               -- positional: every field, as before
Circle (radius := 1)       -- named arguments: a function still waiting for `id`
```

- **What may be left out.** Only a field with a default; leaving out any other is `E-RECORD-FIELD`, with a note naming the fields that have defaults. `{}` is a literal of a record whose fields all have defaults, and `C {}` a construction. Positional application and named arguments ([Named arguments](#named-arguments)) still give every explicit field, so no existing call changes meaning. An update `{ r | a = 5 }` keeps the other fields' values (a default is how a value is built, not a computed property), and patterns are unchanged: without `..` they name every field.
- **What a default may use**: the type's parameters, the fields before it (implicit ones too), and anything in scope at the declaration. A later field is `E-UNKNOWN-NAME`, with a note. It must be pure, and so finish: an operation is `E-ABILITY`, and calling something `Partial` is `E-PARTIAL`. So when a default is computed, and how often, can't be seen. A default may still be a function that performs operations when called (`onDone: Nat -> {IO} () := n => IO.print "done"`).
- **Checked for any earlier values.** A default is checked once, at the declaration, for every value of the fields before it, since a literal may give them: `ok: size = 8 := rfl` after `size: Nat := 8` is `E-REFL`. A later field's type may mention a defaulted field, and the default computes there: `{ cells = Vec.replicate 8 False }` checks for `Sized`.
- **Leaving a field out commits to its default.** Nothing is inferred from the other fields: with `size: Nat := 0`, `{ cells = threeCells }` is `E-TYPE-MISMATCH`, with a note that `size` is left out and is `0`.
- **Run order.** In a computation, the fields given run once, in the order written, then the record is built, and the defaults use their results: with `type Twice = { x: Nat, twice: Nat := x + x }`, `{ x = readNat() }` reads once. In pure code, a given field that a default uses is bound by a `let` first (unless it's a variable or a literal), so it isn't computed twice.
- **Identity.** Each default is a generated definition, `RangeOptions.step.default` (for a constructor's field, `Shape.Circle.id.default`), taking the parameters and earlier fields it needs. A literal that leaves a field out calls it, so `{ stop = 10 }` equals `{ start = 0, stop = 10, step = 1 }` (`rfl` proves it), but the two have different hashes. Defaults aren't part of the type's hash: changing one changes the hashes (and reruns the tests) of exactly the literals that leave that field out. A literal that gives every field is the same term, with the same hash, as before the type had defaults. These names can't be written in source.
- **Where defaults can't go.** A function type's parameter (`(f: (step: Nat := 1) -> Nat)`), a lambda's, or an implicit or `auto` parameter is `E-PARSE` ("only a definition's parameter or a field can have a default value"); an implicit constructor field can't have one; an interface's methods can't (`E-FIELD-DEFAULT`). A definition's explicit parameters can: see [Parameter defaults](#parameter-defaults).
- **A default that names a definition of its module** makes the type depend on it, so that definition can't mention the type (`E-MUTUAL-KIND`, as for any cycle between a data type and a definition).
- **At the JS boundary**, an export's parameter may leave a defaulted field out, and the decoder fills it by running the default, in field order, from the fields before it (given or defaulted). A result always has every field. So the TypeScript declarations have two shapes (D1101): `RangeOptions`, complete, for results, and `RangeOptionsInput`, with the defaulted fields optional, for parameters. Every type that holds one, anywhere in its fields, has an input shape too (`type Job = { name: Text, options: RangeOptions }` gives `JobInput`, with `options: RangeOptionsInput`), and a type argument is written with its input shape (`BoxInput<RangeOptionsInput>`):

  ```ts
  export type RangeOptions = { readonly start: bigint; readonly stop: bigint; readonly step: bigint };
  export type RangeOptionsInput = { readonly start?: bigint; readonly stop: bigint; readonly step?: bigint };
  export declare function widen(options: RangeOptionsInput): RangeOptions;
  ```

  Only a *missing* own property asks for the default. A property that is present is decoded as given, `undefined` included: for a field that isn't an `Option`, `undefined` is refused like any wrong value (`options.step: expected a non-negative bigint`), and an inherited property is refused as for any field. A defaulted `Option` field has three meanings (D1114): with `colour: Option Text := Some "blue"`, `{}` is the default, `{ colour: undefined }` is `None`, and `{ colour: "red" }` is `Some "red"` (`null` is still refused). Its input type is `colour?: string | undefined`, and on output it is always present, `colour: string | undefined`, `None` as `undefined`, so a value passed back in keeps its `None`. An `Option` field without a default keeps the encoding below: a missing property and `undefined` are both `None`, and `None` is no property. `@[js.optional]` on a field with a default is `E-ATTRIBUTE`. An input shape's name must be free: another type at the boundary called `RangeOptionsInput` is `E-EXPORT`. A `@[js.unboxed]` record is its field's value at the boundary, so its own default never applies there.

Examples: `examples/accept/field-defaults.sw`, `examples/reject/field-default-*.sw`, `examples/extract/field-defaults.sw`. Design: [named-arguments.md](proposals/named-arguments.md) §5.1 to §5.3.

### Parameter defaults

An explicit parameter of a `def` or `theorem` header, top-level or local, may have a default value, written after `:=` (docs/proposals/signature-defaults.md):

```
def makeBooking (id: Text)
    (start: Float := 0.0)
    (duration: Float := 60.0)
    (room: Option Text := None): Booking :=
  { id, start, duration, room }

test "a short booking" := makeBooking "a" (duration := 30.0) |> .duration == 30.0
test "every booking" := ["a", "b"].map makeBooking |> .length == 2
```

- **Given by name only.** Positional arguments skip a defaulted parameter, so adding a default never moves a positional argument: `makeBooking "a" (duration := 30.0)`. A positional argument written after the header's parameters ran out, in a call that left a default out, is `E-DEFAULT-POSITIONAL` (`scaler 5 3` with `def scaler (base: Nat) (factor: Nat := 1): Nat -> Nat`), with both fixes: `scaler 5 (factor := 3)`, or `(scaler 5) 3`, whose brackets finish the call before `3` is applied.
- **Every written call fills the defaults it doesn't name**, at the end of the call: a bare name (`makeBooking` is `id => makeBooking id 0.0 60.0 None`, so `.map makeBooking` works), dot notation (`clip.trimmed`), a method section (`.trimmed`) and a pipe (`clip |> Clip.trimmed`). A required parameter left out before the last given or defaulted one makes the call a function of it, with its name (`range 0` is `stop => range 0 stop 1`); one after it stays to currying. A function's type is still the full arrow, defaults included; to pass the function with a default open, write the lambda (`start stop step => range start stop (step := step)`).
- **What a default may use**, and when it is checked, are as for fields: the parameters before it (a later one is `E-UNKNOWN-NAME`, with a note), checked once at the declaration for any values of those (`(ok: size = 8 := rfl)` after `(size: Nat := 8)` is `E-REFL`), and pure (`E-ABILITY`, `E-PARTIAL`). It can't use the definition, or one defined together with it (`E-MUTUAL-SIGNATURE`).
- **Leaving a parameter out commits to its default** before the arguments are checked: with `def sized (n: Nat := 3) (xs: Vec Nat n)`, `sized two` (`two: Vec Nat 2`) is `E-TYPE-MISMATCH`, with a note that `n` is left out and is `3`; `sized (n := 2) two` checks. A written argument a default uses is computed once: bound by a `let` first unless it's a variable, a name or a number.
- **Identity.** Each default is a generated definition, `range.step%default`, taking the earlier parameters it needs; a call that leaves the parameter out calls it, so `range 0 10` equals `range 0 10 (step := 1)` (`rfl` proves it) with a different hash. Defaults aren't part of the definition's hash: changing one changes the hashes of exactly the calls that leave it out, and a call that names every default is the term it was before the defaults were added.
- **Not yet**: an `export def` with a default is `E-EXPORT` (JS callers will get an options object), and a constructor application doesn't fill field defaults.
- **Editor.** Hover shows the header as written, defaults included, and completing a parameter's name shows its default (`step := 1`).

Examples: `examples/accept/param-defaults.sw`, `examples/projects/accept/param-defaults-across-namespaces`, `examples/reject/param-default-*.sw`.

## Numbers in an `export`

An exported `Nat` or `Int` crosses the JS boundary as a `bigint`. To take or return a plain JS `number`, use the library's `SafeNat` or `SafeInt` (`std/Int/Safe.sw`, SW-337) as the parameter or result type:

```
import Std (Option, SafeNat)

export def addSafe (a: SafeNat) (b: SafeNat): Option SafeNat := SafeNat.ofNat (a.value + b.value)
```

```ts
export declare function addSafe(a: number, b: number): number | undefined;
```

- **They are records.** `type SafeNat = { value: Nat, fits: value <= 9007199254740991 }` and `type SafeInt = { value: Int, fits: Int.natAbs value <= 9007199254740991 }`: a number and a proof that it's at most 2^53 - 1 in magnitude, the largest whole number a JS `number` holds exactly (`Number.MAX_SAFE_INTEGER`). In Stitchwort they're ordinary records, so `n.value` is the `Nat` or `Int`; `SafeNat.ofNat` and `SafeInt.ofInt` give `Some` when a number is within the bounds, and the `fits` proof is what a function builds by comparing, as above.
- **Numerals.** A numeral checked against `SafeNat` or `SafeInt` is the record with that value, its bound checked by computing it, so no proof is written: `{ bytes = 10, offset = -3 }` for `{ bytes: SafeNat, offset: SafeInt }`, and `(10: SafeNat)` is `{ value = 10, fits = rfl }` (SW-354). A negative numeral is a `SafeInt` as it is an `Int`. One beyond 2^53 - 1 in magnitude (`9007199254740992`), or a negative `SafeNat`, is `E-SAFE-LITERAL`. Only an expected `SafeNat` or `SafeInt` makes a numeral one; in a comparison beside one, the numeral takes its type. They have no arithmetic: compute on `.value`. In JS such a value is a plain `number`. Examples: `examples/accept/safe-literals.sw`, `examples/reject/safe-literal-*.sw`.
- **Decoding is checked.** A JS argument must be a `number` that is a whole number from 0 to 2^53 - 1 (`SafeNat`) or from -(2^53 - 1) to 2^53 - 1 (`SafeInt`). A `bigint`, a string, `NaN`, an infinity, a fraction and a whole number out of range are refused with `StitchwortInputError`: `a: expected a number`, `a: expected a whole number`, `a: expected a whole number from 0 to 9007199254740991`. A whole `number` beyond 2^53 - 1 may have been rounded already, so it's out of range, not repaired. `-0` is read as 0.
- **Encoding is exact**, because the type bounds every value of it, so a function can't return a number a JS `number` can't hold: it has to show (`fits`) that it fits, or return `None`.
- **Everywhere a type goes**: inside lists, `Option`, data types and records, with the path to the problem as for any input. `Nat` and `Int` are unchanged and remain `bigint`.
- **Only the library's types.** A program's own record called `SafeNat` is an ordinary record. The JS codec is used only for the library's exact declarations, by content hash.

Example: `examples/extract/safe-numbers.sw`. See DESIGN.md §12.

A `Float` crosses as a `number`, any `number`: `NaN`, the infinities and `-0` included, and a `bigint` or a string is refused (D685). It needs no wrapper, since every double is a `Float`. A program that needs finite input checks it on its own types (`if h: ...`); a proof field in a record checks nothing at run time (D702). Example: `examples/extract/floats.sw`.

## `Option` in an `export`

An `Option T` crosses the JS boundary as `T | undefined` (D582):

```
import Std (Nat, Option, Text)

type Profile = { name: Text, nick: Option Text }

export def withNick (p: Profile) (n: Option Text): Profile := { p | nick = n }
export def halve: Option Nat -> Option Nat
  | None   => None
  | Some n => Some (Nat.div n 2)
```

```ts
export type Profile = { readonly name: string; readonly nick?: string };
export declare function withNick(p: Profile, n: string | undefined): Profile;
export declare function halve(arg0: bigint | undefined): bigint | undefined;
```

- **Decoding.** `undefined` is `None`; any other value is decoded as a `T` and is `Some` of it. `null` is refused (`n: expected a value or undefined, not null`), not read as `None`.
- **In a record's field** the property is optional, `nick?: string`: a missing property is `None` too. Encoding `None` leaves the property out, not set to `undefined`, so the declarations type-check under `exactOptionalPropertyTypes` as well as `--strict`. A record's other fields are still required, and an inherited property is still refused.
- **Everywhere else**, in arguments, results, list elements (`(bigint | undefined)[]`), a constructor's fields and the arguments of parameterised types, it is `T | undefined`.
- **Nested.** Only the outermost `Option` is `T | undefined`: `Option (Option Nat)` is `Option<bigint> | undefined`, where the inner `Option<bigint>` is the tagged object `{ $tag: "None" }` or `{ $tag: "Some", value }`, so `Some None` and `None` stay distinguishable.
- **Inside `Option`**, a `SafeNat` is a `number` (`number | undefined`), and a record's proof fields about an optional field are checked after it's decoded.

Example: `examples/extract/options.sw`. See DESIGN.md §12.

## `Map Text V` in an `export`

A `Map Text V` crosses the JS boundary as a plain object, a dictionary from string keys to `V` (D651, D665):

```
import Std (List, Map, Nat, Text)

type Person = { name: Text, age: Nat }

export def ages (people: Map Text Person): Map Text Nat := people.map (p => p.age)
export def bump (scores: Map Text Nat) (who: Text): Map Text Nat := scores.insertWith who 1 Nat.add
```

```ts
export type Person = { readonly name: string; readonly age: bigint };
export declare function ages(people: { readonly [k: string]: Person }): { [k: string]: bigint };
export declare function bump(scores: { readonly [k: string]: bigint }, who: string): { [k: string]: bigint };
```

- **Decoding** reads the object's own enumerable string keys (`Object.keys`) and decodes each value with `V`'s codec; the map is built with the library's own `Map.fromList`, so its keys are in order as in any map. Symbol keys, inherited properties and non-enumerable ones are not entries. A key that is a lone surrogate is refused, like any `Text`.
- **A plain object is required.** `null`, a primitive, an array, a JS `Map`, a `Date` or a class instance is refused (`scores: expected a plain object, not a Map, a class instance or another kind of object`), since reading no keys from it would silently give an empty map. An object made by `{}`, `JSON.parse` or `Object.create(null)` is plain; so is one from another realm (a `vm` context, an iframe).
- **Awkward keys are data.** `__proto__`, `constructor`, `toString` and the empty string are entries like any other, on input (an own `__proto__` property, as `JSON.parse` makes) and on output. Encoding defines each key as an ordinary data property on a fresh `{}`, so no prototype is set and no setter runs.
- **Encoding** gives a plain object (prototype `Object.prototype`) with the entries in key order, which is `Text`'s order, by code point. JS lists keys that are array indices (`"9"`, `"10"`) first, in numeric order.
- **In TypeScript** the type is an index signature, `{ readonly [k: string]: V }` as a function's parameter and `{ [k: string]: V }` in a result and inside a data type's declaration (like lists: `readonly` only where it helps a caller; `readonly` on an index signature never affects assignability, but a list inside it would), the same as `Record<string, V>`, so an app's `Record<SpeakerId, V>` (a flavoured or branded string key) is accepted as an argument and a result assigns back to it. An `interface` with known keys isn't an index signature in TypeScript; a `type` alias is.
- **Nesting**: `V` can be a record, a list, an `Option` (`{ readonly [k: string]: bigint | undefined }`) or another `Map Text _`.
- **Only `Text` keys**, ordered by `Text`'s own order, or a microtype's (a `@[js.unboxed]` record over `Text`, see Microtypes) in its derived order, which is the same. Any other `Map` in an export is `E-EXPORT`: "only maps from `Text`, or from a `js.unboxed` record over `Text`, cross, as plain objects".

Example: `examples/extract/dictionary.sw`. See DESIGN.md §12.

## Attributes

An exported data type crosses to JavaScript as `{ $tag: "Ctor", …fields }`: the property `$tag` holds the constructor's name, and each field's key is its name, with each `'` as `$`. Attributes, written `@[name "argument", …]`, set another form where the type is declared, to match a wire format an app already has (docs/proposals/attributes.md):

```
@[js.tag "type"]
type Shape =
  | @[js.name "DOT"] Dot
  | @[js.name "CIRCLE"] Circle (radius: Nat) (@[js.name "center_x"] centerX: Nat)

type Drawing = { @[js.name "type"] kind: Text, shapes: List Shape }
```

```ts
export type Shape =
  | { readonly type: "DOT" }
  | { readonly type: "CIRCLE"; readonly radius: bigint; readonly center_x: bigint };
export type Drawing = { readonly type: string; readonly shapes: Shape[] };
```

| Attribute | On | Meaning |
|---|---|---|
| `js.tag "KEY"` | a data type (not a record) | the key of the property that says which constructor an object is, instead of `$tag` |
| `js.name "NAME"` | a constructor | its tag value, instead of its name |
| `js.name "NAME"` | a constructor's or a record's field | its key, instead of its name |
| `js.optional` (no argument) | a constructor's field of type `Option T` | an optional property `f?: T`, instead of `f: T \| undefined` |
| `js.enum` (no argument) | a data type whose constructors have no fields | a plain string, one per constructor (its name, or its `js.name`), instead of an object |
| `noReceiver` (no argument) | a definition | in a type's namespace, a function that isn't called with `.` or `|>`, so it may take the type's value after another parameter without the warning `W-RECEIVER-NOT-FIRST` |
| `js.unboxed` (no argument) | a record without parameters with exactly one field that has a property | its field's own JS form (`string` for a `Text`), instead of an object; in TypeScript, `type T = string` (see Microtypes) |

- **Where they go.** Before a declaration (on the line or lines before `type`, or on the same line), after a constructor's `|`, and inside a field's brackets or before a record field's name. Several are written `@[a "x", b "y"]` or `@[a "x"] @[b "y"]`; order doesn't matter. A group may span lines, and its `]` may be at the start of a line. An attribute group always belongs to the next declaration, whatever it is.
- **Arguments** are plain strings (no `${…}`), used exactly: no `$` for primes, nothing added. Any non-empty string works, `"0"`, `"a-b"` and `"__proto__"` as a tag value included; quotes and other characters are escaped correctly in the JS and the `.d.ts`.
- **Checked.** Tag values must differ, and a constructor's keys must differ from each other and from the tag key; no key may be `__proto__` (assigning it sets an object's prototype): `E-JS-NAME-CLASH`. A type with attributes is checked where it's declared. One without is checked when an export reaches it, so a field called `__proto__` needs a `js.name` only in a type that crosses. A field called `tag` keeps the key `tag`.
- **Optional properties.** `@[js.optional]` on a constructor's field written with the type `Option T` makes it `readonly f?: T`, as a record's `Option` fields already are: a missing key or `undefined` is `None`, a present value is `Some`, `null` is refused, and an encoded `None` leaves the key out. It is `E-ATTRIBUTE` on a field of any other type (including a type parameter that is an `Option` somewhere), on a record's field (those are optional already), on a field with a default (a missing key is already its default, see [Field defaults](#field-defaults)), on a proof or type field, on a constructor, a type or anywhere else, written twice, or with an argument.
- **String unions.** `@[js.enum]` on a data type whose constructors have no fields makes it cross as a string, not an object; `@[js.name "…"]` on a constructor chooses its string (without it, the constructor's name):

  ```
  @[js.enum]
  type Label =
    | @[js.name "IMPORTANT"] Important
    | @[js.name "SLIDE_TEXT"] SlideText
  ```

  ```ts
  export type Label = "IMPORTANT" | "SLIDE_TEXT";
  ```

  Decoding accepts exactly the listed strings: any other string, a non-string, or the old object form `{ $tag: … }` is refused (`label: expected "IMPORTANT" or "SLIDE_TEXT", not "important"`). It works in every position: a record's field, inside `Option` (`f?: Label`), a list, a map, a constructor's field (with `js.optional`), a function's argument or result. Fields that have no property in JS (a proof, a type) and a type's parameters don't count. It is `E-ATTRIBUTE` on a record, on a type with no constructors, on a type with a constructor that has a field, together with `js.tag` (a string has no tag key), on a constructor or a field, with an argument, or written twice; two constructors with the same string, by name or by `js.name`, is `E-JS-NAME-CLASH`, and `@[js.name ""]` is `E-ATTRIBUTE`. **Against a TypeScript `enum`:** an app's `enum Label { IMPORTANT = "IMPORTANT", … }` member is assignable to the string union (so the app's values go straight into the exported functions), but a string, and so the generated union, is *not* assignable to the enum (tsc 7.0.2, `TS2322`: a result can't be assigned to a variable of the enum's type, and a generated record isn't assignable to the app's record whose fields are the enum). `` `${Label}` ``, the enum's template-literal type, is exactly the generated union, assignable both ways, so an app's type test compares against that (or maps its enum with it); `result as Label` is a cast that compiles.
- **Lists are mutable in declarations.** Every list in a data type's declaration is `T[]`, so an app's `{ xs: T[] }` and the generated type are assignable both ways (`readonly T[]` isn't assignable to `T[]`), and a function's list parameter is `readonly T[]`, which takes either kind. The codec copies arrays in and out, so the caller owns what it gets.
- **Only data fields have keys.** A proof field or a type field has no property in JS, so an attribute on one is `E-ATTRIBUTE`; so is one on a binder naming several fields, `(@[…] x y: Nat)`. The same logical field may have a different key in each constructor.
- **Nowhere else.** An unknown attribute is `E-ATTRIBUTE-UNKNOWN` (with a suggestion), and a known one anywhere else (a theorem, a `def`, an export, an instance, an interface, a type synonym, a test, an ability, a function's or a type's parameter, a lambda, a local definition, a namespace line), twice on one target, without its argument, or on a type with a built-in JS form (`Nat`, `Int`, `SafeNat`, `SafeInt`, `Bool`, `Text`, `Char`, `List`, `Option`) is `E-ATTRIBUTE`. A number or a second string as the argument is `E-PARSE`. Nothing is silently ignored.
- **Nothing changes inside Stitchwort.** Patterns, field access, `show`, `==` and proofs use the Stitchwort names, and attributes aren't part of content hashes, so changing one reruns no test.

Examples: `examples/extract/attributes.sw`, `examples/extract/app-types.sw`, `examples/extract/string-enums.sw`, `examples/extract/microtypes.sw`. See DESIGN.md §12.

## Microtypes

A *microtype* is a type of its own around one value, so that ids of different kinds can't be mixed up: a one-field record is a different type from any other, with the same fields or not, and `@[js.unboxed]` makes it cross to JavaScript as the value itself (docs/proposals/microtypes.md):

```
import Std (Map, Option, Show, Text)

@[js.unboxed]
type UserId = { value: Text }

@[js.unboxed]
type OrderId = { value: Text }

instance UserId.instShow: Show UserId := Show.fromText (u => u.value)

export def ownerOf (orders: Map OrderId UserId) (o: OrderId): Option UserId := orders.get o
```

```ts
export type UserId = string;
export type OrderId = string;
export declare function ownerOf(orders: { readonly [k: OrderId]: UserId }, o: OrderId): UserId | undefined;
```

- **Inside Stitchwort it is a record.** Build one with `{ value = t }` (where its type is known), read it with `u.value`; passing an `OrderId` where a `UserId` is expected is `E-TYPE-MISMATCH`. `==`, `<` and `${…}` are derived as for any record; the derived `Show` prints `{ value = "u1" }`, so the one-line instance above makes `"${u}"` print `u1`. `UserId.ext` proves two equal from their `value`s. Converting a list is `ids.map (u => u.value)`: there is no `coerce` (D1069). At run time a record with one field is stored as that field (D866), so a microtype costs nothing.
- **At the boundary it is its field.** `js.unboxed` is allowed on a record without parameters that has exactly one field with a property (a proof field, like `valid: Email.isValid value = True`, doesn't count and is checked on the way in, as for any record). It crosses as the field's own JS form, both ways, everywhere a type can appear: a function's argument or result, a record's or a constructor's field, an `Option`, a list, a map's value. The old object form `{ value: "u1" }` is refused (`u: expected a string`).
- **In TypeScript it is a plain alias**, `export type UserId = string;` (or the field's type: `bigint`, `string[]`, …), used by name at every use (D1066). The alias doesn't keep `UserId` and `OrderId` apart in TypeScript; an app passes its plain strings straight in.
- **Map keys.** `Map UserId V` crosses as a plain object, `{ readonly [k: UserId]: V }`, when the record is `@[js.unboxed]` over `Text` and the map uses its derived order, which compares the field by `Text`'s and so sorts the keys as `Map Text V` does (D1068). A key's proof fields are checked. A microtype key in an order the program wrote (its own `Ord` instance, or `[ord := …]`) is `E-EXPORT`, as is a key that is a record without the attribute or a microtype over anything but `Text`.
- **Refused** (`E-ATTRIBUTE`): on a data type with constructors, a constructor or a field; on a record with type parameters, with no field with a property, or with two; on a record whose field is an `Option` (an `Option` of it couldn't tell `None` from `Some { value = None }`; an `Option` behind a synonym is `E-EXPORT` when an export reaches it); alongside `js.name` on its field; with an argument, or twice.

**The recipe**, as `examples/extract/microtype-orders.sw` does it:

1. *Declare.* `@[js.unboxed] type UserId = { value: Text }`, one per kind of id. Give it a one-line `Show` if `${u}` should print the text: `instance UserId.instShow: Show UserId := Show.fromText (u => u.value)` (the derived one prints `{ value = "u1" }`).
2. *Validate.* Put the rule in a proof field, `type Email = { value: Text, valid: Email.isValid value = True }`, so no invalid `Email` exists, and write the one way to make one from arbitrary text, a smart constructor:

   ```
   def Email.parse (t: Text): Option Email :=
     if h: Email.isValid t = True then Some ({ value = t, valid = h }) else None
   ```

   Code that may fail says `{Fail}` instead and uses `Email.parse t |> .orFail "not an email address: ${t}"`. An export that returns `Option Email` gives JavaScript `string | undefined`; one that takes an `Email` refuses a string that fails the rule (`e: proof field `valid` ... doesn't hold`).
3. *Use as a `Map` key.* `Map OrderId UserId` needs nothing more: the derived order compares the field, so `Map.get`, `Map.insert` and the lemmas work as for `Text` keys. Keep the derived `Ord`; a key in another order can't cross (above).
4. *Export.* `export def ownerOf (owners: Map OrderId UserId) (o: OrderId): Option UserId`. In TypeScript the app passes `{ o1: "u1" }` and `"o1"`.

Examples: `examples/extract/microtypes.sw` (every position), `examples/extract/microtype-orders.sw` (the recipe).

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

The library has five interfaces so far. `Ord` is a total order: `compare`, the relations `lessThan` and `lessEq` with their decisions `decLessThan` and `decLessEq`, and laws (`equal`, `flip`, `trans`, and four tying the relations to `compare`), with `DecEq` as its superclass `eq`. It has instances for `Nat` and `Int` (whose relations are `<` and `<=` themselves), `Float` (IEEE 754's total order, [Numbers](#float)), `Char`, `Text`, `Bool`, `Ordering`, lists and `Vec` (lexicographic), `Option` (`None` first) and pairs; `List.sort`, `List.maximum` and `List.minimum` use it (`List.sort [ord := descending] xs` for another order), and `Ord.fromCompare` (a comparison and its three laws) and `Ord.byKey` (a key that tells values apart; its `<` and `<=` are the key's own, so `c < x` on a `Fin` is `Fin.toNat c < Fin.toNat x`) build one. A declared data type or record gets one derived: constructors in the order they're declared, then the fields left to right, proof fields left out (`Dial` by its `position`), wherever it gets a derived `==` and its data fields have `Ord`; a module's own `instance T.instOrd: Ord T` replaces it (`examples/accept/derive-ord-*.sw`). `<` and `<=` are its relations, for every type ([Numbers](#numbers)). `Add` (`zero`, `add`, and the laws `zeroAdd`, `assoc`, `comm`: things you add in any order) and `Mul` (`one`, `mul`, and `oneMul`, `mulOne`, `assoc`: not commutative) are `+` and `*`, with instances for `Nat` and `Int`; `List.sum`, `List.sumBy` and `List.product` use them, so `[(3: Int), -5, 1].sum` is `-1` and a list of a user's points adds up with its `Add` instance. `DecEq` (`decide: (x: a) -> (y: a) -> Decidable (x = y)`) is the one `==`, `!=`, `if h: x = y` and `auto` use to decide equations, with `DecEq.uniqueEq` (any two proofs of an equation in a type with `DecEq` are equal) and `DecEq.sound`. Decision procedures for anything else are instances too, but of `Decidable …` (`instance decToken: Decidable Token := …`): none of the rules below apply to them, and `auto` keeps its search for them (first fit, above the use).

`Show` is the fifth: `toText` (what `${e}` inserts) and `toSource` (a source-like form, used for the elements of containers: text in quotes with escapes, `'a'` for a character; not promised to parse back). They agree except for `Text`, `Char` and `Float` (`3` and `3.0`, [Numbers](#float)). The library has instances for `Nat`, `Int`, `Float`, `Bool`, `Char`, `Text`, `Ordering`, lists, `Option`, tuples, `Vec`, `Fin`, `Map` and `Set`; a declared data type or record gets one derived (`Dot`, `Rect 3 4`, `Node Leaf (-1) Leaf`, `{ name = "tea", price = 3 }`; proof fields left out), unless a field is a function, a type, or depends on an earlier field, or the type is used inside another type of its own fields. A module's own `instance T.instShow: Show T` replaces it, and `Show.fromText f` builds one from a single function: `instance Point.instShow: Show Point := Show.fromText Point.toText`. A type with none is `E-INSTANCE-NONE` at the `${…}` (`examples/accept/show.sw`).

**`Mod n`** (`import Std (Mod)`; `examples/accept/mod-arith.sw`, docs/proposals/fin-arithmetic.md) is the numbers 0 to n - 1, where `+` and `*` wrap around, as on a clock: it has `Add` and `Mul` instances (with their laws proved for every `n`), `DecEq`, `Ord` (by value) and `Show` (the number). `Fin n` stays the type of positions in a `Vec`, with no arithmetic, so that `i + 1` at the last position can't silently wrap; `Fin.toMod` and `Mod.toFin` convert. A value is `{ value: Nat, isLt: … }` and runs as a plain number. There are no `Mod` literals: `Mod.ofNat` and `Mod.ofInt` make values, and wrap (`(Mod.ofNat 150: Mod 100)` is 50, `(Mod.ofInt (-1): Mod 100)` is 99, by the Euclidean remainder). There is no `-`: `i.sub j` and `i.neg` are named functions that wrap (`Mod.sub 5 7` is 98 in `Mod 100`). Moving by a `Nat`, `i.addNat k` and `i.subNat k` (which go through `Mod.ofInt`), has its laws: `addNatZero`, `subNatZero`, `addNatAddNat` (`(i.addNat j).addNat k = i.addNat (j + k)`), `subNatSubNat`, `addNatSubNat` and `subNatAddNat` (there and back is `i`); with `negZero`, `negNeg`, and the mirror laws `negSubNat` (`Mod.neg (i.subNat k) = (Mod.neg i).addNat k`) and `negAddNat`. `Mod.negOfInt` and `Mod.ofIntAdd` are the steps they are proved by. `Mod 0` has one value, 0, so that every `Mod n` has a zero. A dial: `turns.scanLeft (p t => p + Mod.ofInt t) (Mod.ofNat 50: Mod 100)`.

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
-- else". `{e}` alone is just the variable (an effect-row parameter: code
-- abstract over it can't construct, inspect or branch on it). `A -> B` is pure
-- and total.
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

Effectful code is written in direct style. Arguments are evaluated left to right, named ones where they are written ([Named arguments](#named-arguments)), and the lines of a block in order. A handler's clauses on their own lines must line up: a `|` at another column belongs to an enclosing handler. An operation on its own (`choose`) is a function, `x => choose x`. A dot call to an effectful function is a call like any other and runs where it's written, also with no further arguments and at the end of a chain of pure calls (`1 + w.toNat.orAbort`). A signature can be a computation that isn't a function: `current: {State Nat} Nat`. Naming or calling a computation where a plain value is expected runs it there, so it's allowed only if it may perform nothing: a function over any row `{e}` used at the empty row, or a `Std.Effect.Comp NoOp NoRes a`, gives its `a` ([proposals/let.md](proposals/let.md) §8). Where a computation is expected (a parameter, constructor field, list item or tuple part of type `Std.Effect.Comp …`), a computation is passed as it is and not run: `isDone c` sees `c` itself, and `Effect.runPure (Done 3)` is `3` ([proposals/effect-polymorphism.md](proposals/effect-polymorphism.md), stage 0). The types stay different: a function returning a computation isn't a function returning a value. A row written `{}` is no row: `{} Nat` is `Nat`. Messages print the empty-row computation type in full, `Comp NoOp NoRes Nat`, so it is not mistaken for `Nat`. A pure function can use a handler inside; what it handles doesn't appear in its type. How this is translated into ordinary data is described in `docs/core.md`, under "Abilities".

`Effects` (`import Std.Effect (Effects)`) is the type of an effect-row parameter, so a data type can be parameterised by effects as it is by types, and the row goes inside the type's functions: `type Handlers (e: Effects): Type = | MkHandlers (onStep: Nat -> {Partial | e} Nat) (onDone: Nat -> {Partial | e} Nat)`, and `def drive: [e: Effects] -> Handlers e -> Nat -> {Partial | e} Nat`, where `{e}` and `{A | e}` stand for that row (`examples/accept/partial.sw`). Rows are abstract indices: a program can declare an `Effects` parameter and pass it on, but cannot build, compare or inspect one ([proposals/effect-polymorphism.md](proposals/effect-polymorphism.md) §7, D1142, D1143).

### `IO`

`IO` is an ability with `print: Text -> {IO} ()`, `readLine: () -> {IO} (Option Text)` and `readAll: () -> {IO} Text` (also `IO.print`, `IO.readLine`, `IO.readAll`). `IO.simulate lines prog` runs `prog` against scripted input and records what it prints; `IO.simulateWith seed lines prog` does the same with `IO.randomSeed` giving `seed` (0 under `IO.simulate`).

- `IO.readLine()` gives the next line without its LF (and a CR just before it), `None` once nothing remains.
- `IO.readAll()` gives everything that remains, verbatim, line endings included; `""` once nothing remains. After it, `IO.readLine()` is `None`; after some `IO.readLine`s it gives the rest. Under `IO.simulate` it gives the remaining scripted lines, each followed by LF.
- `Text.lines: Text -> List Text` follows Rust's `str::lines`: split on LF, drop a CR right before an LF, and the last line's ending is optional. `"a\nb"` and `"a\nb\n"` both give `["a", "b"]`; `""` gives `[]`; `"\n"` gives `[""]`; `"a\r\nb"` gives `["a", "b"]`. A CR anywhere else stays, including a final one.
- `IO.readAllLines(): {IO} (List Text)` is `(readAll()).lines`. It is total.
- Four lower-level operations are what a terminal handler is built on ([proposals/terminal-io.md](proposals/terminal-io.md) §4): `console: () -> {IO} Console` says whether standard input and output are terminals, and the size (`Console` is `{ inputIsTerminal: Bool, outputIsTerminal: Bool, columns: Nat, rows: Nat }`, 0 by 0 when the size isn't known); `keysMode: Bool -> {IO} ()` enters or leaves keys mode (on a terminal: no line editing or echo, Ctrl-C still stops the program; the alternate screen, cursor hidden, no wrapping; put back however the program ends); `readBytes: () -> {IO} (Option (List Nat))` gives the bytes of one read, `None` at the end; `write: Text -> {IO} ()` writes the text with no line ending, then flushes. `print`, `readLine` and `readAll` leave keys mode first. Without a terminal (pipes, the playground, `run --js` for now) `console` says so and keys mode changes nothing. Under `IO.simulate`, `console` says there's no terminal, `keysMode` does nothing, `readBytes` gives the remaining scripted lines as UTF-8 (`Char.utf8`), each followed by LF, in one read, and `write` records its text as a payload (`examples/accept/terminal-ops.sw`).

### `Abort`

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

#### Proofs about a block that gave `Some`

A proof that knows `h: toOption (block) = Some v` (or `parse t = Some v`, for a `parse` defined as one) reads off what each step gave with one lemma per step, each continuing from the last one's `rest` (`examples/accept/abort-inversion.sw`):

```
def pickOrder (warehouse: Warehouse) (order: Order): Option Pick :=
  toOption (() =>
    let onHand := warehouse.stock.get order.item |> .orAbort
    let label := warehouse.locations.get order.item |> .orAbort
    let bin := warehouse.bins.get label |> .orAbort
    ensure (order.quantity <= onHand)
    { item = order.item, bin, quantity = order.quantity, left = onHand - order.quantity })

theorem pickStock (warehouse: Warehouse) (order: Order) (pick: Pick) (h: pickOrder warehouse order = Some pick):
    warehouse.stock.get order.item = Some (pick.quantity + pick.left) :=
  Abort.needEqSome h (onHand foundStock rest =>
    Abort.needEqSome rest (label foundLabel rest =>
      Abort.needEqSome rest (bin foundBin rest =>
        Abort.ensureEqSome rest (enough picked =>
          rewrite foundStock, <- Option.someInjective _ _ picked in
            rewrite (omega: order.quantity + (onHand - order.quantity) = onHand) in rfl))))
```

- `Abort.needEqSome h use`: the block starts with `need x` (or `x.orAbort`). `use` gets the value `u`, `x = Some u`, and `toOption` of the rest of the block (with `u` for the step) `= Some v`.
- `Abort.ensureEqSome h use`: the block starts with `ensure ok`. `use` gets `ok = True` and the rest.
- `Abort.thenEqSome (() => t) h use`: the block starts with any `{Abort}` computation `t`, such as a call to a function of your own. `use` gets its value `u`, `toOption (() => t) = Some u` and the rest. `t` must be given: it can't be found from `h` (`E-TYPE-MISMATCH`).
- Each is stated with `[goal: Prop]`, as `Option.flatMapEqSome` is, and the rest of the block is found from `h`'s type by unification, so nothing about the program is written twice. Pure `let`s between steps have already been substituted. The last step of a block has no rest: `rewrite Abort.toOptionNeed at rest` turns `toOption (() => need x) = Some v` into `x = Some v`, and a block that ends in a value leaves `Some e = Some v`, for `Option.someInjective`.
- The other way, every step succeeding gives the result by computing: with the steps' equations, `rewrite foundStock, foundLabel, foundBin, enough in rfl` proves `pickOrder warehouse order = Some …`.
- [`cases`](#cases) takes a block apart too (`h: parseSmallOption s t = Some v`), when it can close every case by itself; these lemmas name what each step gave, for a proof that goes on from there.
- For `Fail.toResult (block) = Ok v`, the same with `Fail.needEqOk` (`need x msg`, `x.orFail msg`), `Fail.ensureEqOk`, `Fail.orFailEqOk` (`r.orFail`, for a `Result`: `r = Ok u`) and `Fail.thenEqOk`, closing with `Result.okInjective`. `Fail.toOption` is `toResult` with the message dropped (`Fail.toOptionToResult`).

### `Fail` and `Result`

`Std.Fail` (`crates/elab/src/std/Fail/Fail.sw`) is `Abort` with a message: code that may fail says `{Fail}`, and a failure says why ([proposals/errors.md](proposals/errors.md)). `Result a e = Ok (value: a) | Err (error: e)` is in the prelude, next to `Option`, so `Ok` and `Err` need no import, and results compare with `==`.

```
import Std (Fail)
import Std.Fail (fail, need, ensure, toResult)

def turn (t: Text): {Fail} Int :=
  let (c, rest) := need t.uncons "expected a turn, got nothing"
  ensure (c == 'L' || c == 'R') "expected L or R, got '${t}'"
  let n := rest.toIntOrFail          -- "expected a whole number, got '…'"
  if c == 'L' then -n else n

def parse (t: Text): Result Int Text := toResult (() => turn t)
```

- `Fail.fail: Text -> {Fail} a` fails wherever a value of any type is expected. `Fail.need: Option a -> Text -> {Fail} a`, and `Option.orFail` for dot notation (`o.orFail "msg"`). `Fail.ensure: Bool -> Text -> {Fail} ()` fails on `False`. `Result.orFail: Result a Text -> {Fail} a` fails with the error.
- The handlers: `Fail.toResult: (() -> {Fail | e} a) -> {e} Result a Text`, `Fail.toOption` (drops the message), `Fail.orElse: a -> (() -> {Fail | e} a) -> {e} a` and `Fail.recover: (Text -> {e} a) -> (() -> {Fail | e} a) -> {e} a`. Other abilities pass through, so `{IO, Fail}` code works: what was printed before the failure stays printed (`examples/accept/fail.sw`).
- `Fail.context label prog` puts `label: ` in front of a failure's message, and is itself `{Fail | e}`: `context "line 3" (() => turn l)` fails with `line 3: expected L or R, got 'X1'`. The `fail` in its clause goes to the next handler out, as a clause's operations do.
- With `Abort`: `Abort.orFail msg prog` turns giving up into failing with `msg`, and `Fail.toAbort prog` turns failing into giving up (the message is dropped).
- `List.map: List a -> (a -> {e} b) -> {e} List b` takes a function that may perform abilities, such as `Fail`: `t.split ',' |> .map Range.parse` fails at the first piece that isn't a range. With a pure function the row is empty and it is the plain `map`.
- `Text.toNatOrFail` and `Text.toIntOrFail` trim the text, read it, and otherwise fail with `expected a whole number, got 't'`, quoting the text as given. Messages start in lowercase, say what was expected and then what was found, and quote the found text in single quotes, which shows stray spaces.
- On `Result` (`import Std (Result)`, or by dot notation): `map`, `mapError`, `flatMap`, `toOption`, `getOrElse`, `isOk` and `traverse` (each element through a function, stopping at the first `Err`), and `Option.toResult o err`. Lemmas: `Result.okInjective`, `Result.flatMapEqOk` (`r` held some `u`, passed to a continuation that gives the goal). A `Result` crosses to JavaScript as `{ $tag: "Ok"; value } | { $tag: "Err"; error }` (`examples/extract/results.sw`).
- The operation is `Fail.stop: Text -> {Fail} Empty`, for handlers of your own; `fail msg` is `Empty.absurd (stop msg)`.
- **`main` may leave `Fail` unhandled:** `def main(): {IO, Fail} () := …` (or `{Fail} ()`, or `{IO, Fail, Partial} ()`) runs under `stitchwort run`, `run --reference`, `run --js` and in the playground. The runner performs `Fail.stop` itself, as it performs `IO.print`: what was printed before stays, `error: <message>` goes to standard error (the playground shows it below the output), and the exit status is 1. Runtime errors (`E-IO`, `E-RESOURCE`) exit with 2. A handler still can't go around partial code, so only `main` can leave a partial computation's `Fail` unhandled (`examples/accept/main-fail.sw`, `main-fail-partial.sw`).
- Proofs, each by `rfl` on each case: `Fail.toResultPure` (`toResult (() => v) = Ok v`), `Fail.toResultFail` (`Err msg`), `Fail.toResultNeed` (`toResult (() => need o msg) = Option.toResult o msg`), `Fail.toResultEnsure`, `Fail.toResultOrFail` (`toResult (() => r.orFail) = r`), `Fail.toOptionNeed` and `Abort.orFailNeed`. About any computation, each by `match reify` ([Proofs about effectful code](#proofs-about-effectful-code)): `Fail.toResultThen t k` (`toResult (() => k (t ())) = Result.flatMap (toResult t) (x => toResult (() => k x))`), `Fail.toOptionThen` (the same with `toOption` and `Option.flatMap`), `Fail.toOptionToResult t` (`toOption t = (toResult t).toOption`), `Abort.toOptionThen`, and `Fail.toResultMap f xs` (`toResult (() => xs.map f) = Result.traverse xs (x => toResult (() => f x))`).

### `Each`

`Std.Each` (`crates/elab/src/std/Each/Each.sw`) runs the rest of a computation once for each element of a list and collects every result, as Scala's `for`/`yield` or Haskell's list monad do ([proposals/each-ability.md](proposals/each-ability.md)).

```
import Std (Each)
import Std.Each (each, require)

def pairs (n: Nat): List (Pair Nat Nat) := Each.collect (() =>
  let a := each (List.between 1 n)
  let b := each (List.between a n)    -- may depend on `a`
  require (a + b == n)                -- drops this choice unless it holds
  (a, b))
```

- `Each.each: List a -> {Each} a` and `Each.require: Bool -> {Each} ()`.
- `Each.collect: (() -> {Each} a) -> List a` gives the results in order, the first choice varying slowest. `Each.collectIn: (() -> {Each | e} a) -> {e} List a` is the same with other abilities passing through; the handler outside decides, so `Abort` outside `Each` gives up on everything, and inside it gives up on one choice.
- The operations are `Each.fork: () -> {Each} Bool` (both answers) and `Each.stop: () -> {Each} Empty` (none); `each` is a loop of `fork`s. An operation can't be polymorphic, so there is no `each` operation of its own.
- Proofs: `Each.collectEach k xs` (`collect (() => k (each xs)) = xs.flatMap (x => collect (() => k x))`, by induction), `Each.collectRequire k ok` (`collect` of `require ok` then `k()` is `if ok then collect k else []`, by `rfl` on each case), `Each.collectPure v` (`[v]`, by `rfl`) and `Each.collectEachSelf xs` (`xs`).

### Proofs about effectful code

A handler applied to a computation whose shape is known computes, so a proof about `Fail.toResult (() => need o msg)` splits on `o` and is `rfl` in each case. A law about *any* computation `t: () -> {Fail} a` needs to split on what `t` does. `match reify t with` does that, with clauses written as a handler's ([proposals/proof-reification.md](proposals/proof-reification.md)):

```
theorem Fail.toResultThen (t: () -> {Fail} a) (k: a -> {Fail} b):
    Fail.toResult (() => k (t ())) = Result.flatMap (Fail.toResult t) (x => Fail.toResult (() => k x)) :=
  match reify t with
    | return x => rfl          -- `t` finished with `x`
    | Fail.stop msg, _ => rfl  -- `t` failed with `msg`
```

- In each clause, `t ()` in the goal (and in the types of the variables in scope) is replaced by what it did, as a `match` on an expression generalises it ([`match`](#match)), so the handlers in the goal compute. The second name in an operation's clause (`_` here) is the rest of the computation, a function from what the operation returns: `| State.get (), rest =>` has `rest: s -> {State s} a`.
- The thunk is a function `() -> {A, B} t` or written in place, `match reify (() => f x) with`. Its row must list its abilities and be closed: `{Fail}` or `{State Nat, Fail}`, not `{Fail | e}` or `{e}`, and not `Partial` (`E-REIFY`). There must be a `return` clause and one clause for each operation of the row (`E-NONEXHAUSTIVE`); an operation of an ability not in the row is `E-ABILITY`.
- It splits once: the first thing the computation does. Laws about computations that resume (`State`) by induction on everything they do aren't supported yet.
- **Proofs only.** `reify` may be used only in a declaration whose result is erased: a `theorem`, or a `def` whose type ends in `Prop` or a type (`def Finished (t: () -> {State s} a): Prop := match reify t with …`), including the local definitions and `match`es inside it. Anywhere else (a `def` that computes data, a `test`, an `instance`, an `export`) it is `E-PROOF-ONLY`: what it gives depends on how a computation is represented, so it must never run. To act on a failure at run time, use a handler.
- **Programs can't take a computation apart either.** `Effect.Comp`'s constructors (`Done`, `Call`) and the definitions that match on it (`Effect.foldComp`, `Effect.bind`, `Effect.translate`, `Effect.runPure`) may be named only in a declaration whose result is erased (the same test), or in a signature or a type. In a `def` that computes data, a `test` or an expression it is `E-PROOF-ONLY`; the standard library is exempt. A program can still pass a computation as a thunk, run it, and give it to a handler: that is all it can do with one. A hand-written tree is only for proofs, and a predicate about one is a `Prop`:

  ```
  def IsDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Prop
    | Done value => Unit
    | Call () rest
  ```
- `reify` is a keyword only right after `match`; elsewhere it's an ordinary name. `match h: reify t` is refused: the equation would be between computations, whose type has no spelling.
- `examples/accept/reify-fail.sw` has the laws, `Fail.toResultMap` (by induction on the list, with a split on `f x` and then on the rest), and one-step splits of a user's `State` computation.

## `Text` helpers

Characters are Unicode scalar values, as for `Text.length`. The text comes last.

- `Text.take t n`, `Text.drop t n`: the first `n` characters, and the rest (all of `t`, or `""`, if it is shorter).
- `Text.startsWith t p`, `Text.endsWith t s`, `Text.contains t p`: `Bool`s. The empty text starts, ends and occurs in every text.
- `Text.stripPrefix t p`, `Text.stripSuffix t s`: `Some` of `t` without `p` (or `s`), or `None`.
- `Text.splitOn t sep`: splits at each whole occurrence of `sep`, left to right without overlaps: `"a, b".splitOn ", "` is `["a", "b"]`, `"aaa"` on `"aa"` is `["", "a"]`. There is always at least one piece. An empty `sep` doesn't split: the result is `[t]` (as Lean's `String.splitOn`). `Text.split` splits on one `Char`.
- These take the text being examined first and the pattern second, so `line.stripPrefix "L"`, `line |> Text.stripPrefix "L"` and `Text.stripPrefix line "L"` all say the same: `Some` of `line` without a leading `"L"`. Read `t.startsWith p` as "`t` starts with `p`"; `p.startsWith t` is the other way round and type-checks, since both are `Text`, so mind which one is the subject.

Proved: `Text.stripPrefix (p ++ t) p = Some t`, `Text.startsWith (p ++ t) p = True`, `Text.take t n ++ Text.drop t n = t`.

## `Option` helpers

`Std.Option` (`crates/elab/src/std/Option/Option.sw`) has the helpers that save a nested `match` on an `Option`. All are reached by dot notation or a pipe (`x |> .filter p`), and each is defined by matching on its options, so a proof can `match e:` on them.

- `Option.map x f`, `Option.flatMap x f`, `Option.getOrElse x d`: the value changed, changed to an option, or the default. `Option.fold x none some` is `none` for `None` and `some v` for `Some v`.
- `Option.isSome x`, `Option.isNone x`: `Bool`s. `Option.any x p` is `False` for `None`, `Option.all x p` is `True`, and both are `p v` for `Some v`. `Option.filter x p` keeps `Some v` only when `p v`.
- `x.orElse y` is the first `Some` of the two. `x.merge both y` (same type) and `x.alignWith left right both y` (two types) combine two options: a lone value stays (through `left` or `right` for `alignWith`), two values go through `both`, and neither gives `None`.
- Lemmas: `Option.someInjective`, `Option.orElseEqSome` (`x.orElse y = Some v` means `x = Some v`, or `x = None` and `y = Some v`), `Option.mapEqSome`, `Option.flatMapEqSome` (`x` held some `u`, passed to a continuation that gives the goal) and `Option.filterEqSome` (`x = Some v` and `p v = True`), with `Option.orElseNone`, `Option.orElseSome` and `Option.noneOrElse` for computing.

## Grid helpers

For puzzles over a grid of rows. A row of a known width is a `Vec a width`. The row comes first and the fill or pad value after it, so dot notation reads `row.shiftRight 0`.

- `Vec.shiftRight v fill`: element i moves to i + 1, the last element drops off and `fill` comes in at the front (`[1, 2, 3]` gives `[0, 1, 2]`). `Vec.shiftLeft v fill` is the other way round (`[2, 3, 0]`).
- `Vec.around v pad f`: `f left x right` for each element and its two neighbours, with `pad` past either end. It is `Vec.zipWith3 (v.shiftRight pad) v (v.shiftLeft pad) f` (`Vec.aroundShifts`), in one pass.
- `Vec.tabulate n f`: `[f 0, …, f (n - 1)]`, where `f` takes a `Fin n` (as `Vec.get` does).
- `List.transposeFill rows fill`: pads every row with `fill` to the longest row's length (`List.maxLength rows`), then transposes, so no column loses a cell. `List.transpose` keeps only as many columns as the first row is long.
- These are in `std/Vec/Grid.sw` and `std/List/Grid.sw` (`tabulate` is in `Vec.sw`). A program loads those files only if it uses one of these names.

The lemmas read a result one index at a time with `Vec.getOr v d i` (element i, or `d` past the end; it is `List.getOr v.toList d i`), which is the form a proof about one column rewrites with. `i < n` is the row's width. The left neighbour is written `Vec.getOr (VCons pad row) pad i`: at `Succ c` it computes to `getOr pad c row`, and at 0 it is `pad`.

- `Vec.getOrShiftRight v d fill i (h: i < n)`: index i of `v.shiftRight fill` is `Vec.getOr (VCons fill v) d i`.
- `Vec.getOrShiftLeft v fill i`: index i of `v.shiftLeft fill` is index `Succ i` of `v`, with `fill` as the default, at every i. `Vec.getOrShiftLeftLt` takes any default and needs `i < n`.
- `Vec.getOrAround v d pad i (h: i < n) f`: index i is `f` of indices i - 1, i and `Succ i`, read with default `pad`.
- `Vec.getTabulate` (`Vec.get (Vec.tabulate n f) i = f i`) and `Vec.getOrTabulate d n f i h` (`= f (Fin.ofNatLt n i h)`).
- `Vec.getOrZipWith` and `Vec.getOrZipWith3`: index i is `f` of index i of each input, when `f` maps the defaults to the default; `Vec.getOrMap` the same for `map` (default `f d`). `Vec.getOrReplicate`: copies of x read with default x are x. `Vec.getOrPast`: past the end, `getOr` gives the default. `Vec.getOrGet`: in range it is `Vec.get`. `Vec.headOrGetOr`: `headOr d v` is index 0.
- `Vec.extGetOr u d v h`: vectors equal at every index are equal. `Vec.sumByGetOr v d f`: `v.sumBy f` is the sum of `f` of index i over `List.range n`.
- `List.transposeFillCell rows fill c r`: row r of column c is `List.getOr row fill c` of row r, with no bounds on r or c (cells past the ends are `fill` on both sides). `List.transposeFillColumns` states the whole result as columns read by index. `List.getOrTransposeFill` gives column c as a list. `List.lengthTransposeFill`, `List.lengthColumnTransposeFill` and `List.lengthLeMaxLength` give the lengths.

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
- **A pair of measures**, `decreasing (m1, m2)`, is lexicographic (stage
  3d): every recursive call makes `m1` smaller (and `m2` may then be
  anything), or keeps `m1` the same and makes `m2` smaller. A call's proof
  is a `Nat.LexLess (m1 new) (m2 new) (m1 old) (m2 old)`, written
  `Nat.LexLess.First h` (with `h: m1 new < m1 old`) or `Nat.LexLess.Second
  rfl h` (with `h: m2 new < m2 old`, the first the same), or found:
  `[decreasing := omega]` tries the first and then the second from the
  arithmetic facts in scope, and `auto` (no proof given) does the same from
  the hypotheses in scope, so a guard works as for one measure. A recursive
  call may sit in another's arguments, as in Ackermann's function:

  ```
  def ack (m: Nat) (n: Nat): Nat
    decreasing (m, n)
  :=
    match m, n with
      | Zero, n => n + 1
      | Succ k, Zero => ack k 1 [decreasing := omega]
      | Succ k, Succ j => ack k (ack (Succ k) j [decreasing := omega]) [decreasing := omega]

  -- Two counters, guard style: `auto` builds each call's proof from the `if`.
  def minutesLeft (hours: Nat) (minutes: Nat): Nat
    decreasing (hours, minutes)
  :=
    let earlierMinute := minutes - 1
    let earlierHour := hours - 1
    if fewerMinutes: earlierMinute < minutes then 1 + minutesLeft hours earlierMinute
    else if fewerHours: earlierHour < hours then 1 + minutesLeft earlierHour 59
    else 0
  ```

  Both parts are `Nat`s of the header's parameters; a longer tuple isn't
  supported yet. Write a proof with the constructors rather than a lemma
  that takes the numbers as arguments: `stitchwort test` computes a lemma's
  number arguments, and with a nested call one of them is the inner call's
  result, computed again at every level (`examples/accept/decreasing-lex.sw`).
- `f.unfold: (x…) -> f x… = <the body, with f in its recursive calls>` is
  generated for every `def` with `decreasing` (not for a theorem). `f x`
  doesn't unfold by itself on an argument that isn't known; `rewrite
  f.unfold x in` takes one step. On known arguments it computes: tests and
  `rfl` work as for any definition.
- A recursive call may be inside a function passed to another, when that
  one has a **congruence lemma** (stage 3a): `List.sumBy xs (d => if h: d < n
  then weight d else 0)` needs the proof of `d < n` like any recursive
  call (here `h`), and the compiler's own proofs use `List.sumByCong`. The
  lemma is found by name, the function's own name and `Cong`, beside it, and
  must say: given the function's parameters in order, each function
  parameter twice (`f1`, `f2`), and then `(x…) -> f1 x… = f2 x…` for each,
  the two calls are equal. `std` has `List.mapCong`, `List.foldLeftCong`,
  `List.sumByCong`, `List.filterMapCong` and `List.occurrencesCong`; your
  own functions can have them too:

  ```
  theorem List.sumByCong [auto add: Add b] (xs: List a) (f1: a -> b) (f2: a -> b) (ef: (x: a) -> f1 x = f2 x):
      List.sumBy xs f1 = List.sumBy xs f2
  ```

  The function may be in a `let`, take several arguments (`List.foldLeft
  (acc x => …)`), `match` on its argument, and sit inside another such
  function; a `theorem` with `decreasing` may recurse inside any function
  (it needs no lemma).
- When there's no cheap guard to test, `List.attach` (stage 3b) gives the
  function its proof instead: `xs.attach` is the elements of `xs`, each a
  `List.Member a xs`, a record of the element (`value`) and the proof that
  it's in `xs` (`isIn: List.Mem value xs`). A fact about membership turns
  `isIn` into the decrease, written in the call:

  ```
  List.range n |> .attach |> .sumBy (({ value = d, isIn }) =>
    if Nat.divides d n then f d [decreasing := And.right (List.memRangeFrom d n 0 isIn)] else 0)
  ```

  `List.Mem x xs` is `List.Any (y => y = x) xs`, so on a written-out list
  it computes to a chain of `Or`s. The facts: `List.memRangeFrom` (`s <=
  x` and `x < s + c` in `List.rangeFrom c s`), `List.memBetween` (`lo <= x`
  and `x <= hi`, its numbers implicit), `List.memFilter`, `List.memMap`,
  `List.memMapAny` and `List.memAppend`. Once the call is made the proofs
  can be dropped: `List.attachValues`, `List.sumByAttach` and
  `List.mapAttach` say that mapping or summing over `e.value` is the same
  as over `xs`. At run time `attach` builds the list of records (returning
  `xs` itself is a later optimisation).
- Refused, with `E-DECREASING`: a recursive call `auto` can't prove smaller
  (the message shows the goal and the hypotheses in scope); one inside a
  function passed to a function with no congruence lemma, or one of the
  wrong shape (the message says which and why); one inside a function
  stored in data, passed to a local variable, or returning a function
  (comparing functions would need function extensionality); a measure that
  uses no header parameter, definitions that call each other, a recursive
  call in an `if`'s condition, a measure with more than two parts, and a
  body that returns a function. A measure that isn't a
  `Nat` is `E-TYPE-MISMATCH`. A definition that never calls itself gets
  `W-DECREASING-UNUSED`.
- A recursive call written with a dot (`rest.total`) works when `auto`
  finds the proof; one that gives `[decreasing := …]` is written in prefix
  form.
- `decreasing` is a keyword.

## Opaque definitions

An **opaque** definition is checked like any other (its body against its
type, its termination, its effects) and runs like any other, but while other
declarations are checked it has a type and no body: no comparison, `rfl`,
`match` or `rewrite` looks inside it (docs/proposals/opaque-definitions.md).
A call of it is compared with another call of it by the arguments, as a
function variable's would be. It's opaque *to the checker*, not private: the
body is in the source, and `f.unfold` states it. The checker's kernel
enforces it too, and it's part of the definition's hash.

```
opaque def generateLevel (depth: Nat): {Random} Plan :=
  …

-- A declaration that needs the body says so after its type.
theorem generateLevelDepth (depth: Nat) (seed: Nat):
      (seeded seed (() => generateLevel depth)).level.depth = depth
    unfolding generateLevel
:=
  …

-- Or it rewrites with the generated equation.
theorem doubleTwo: double 2 = 4 := rewrite double.unfold in rfl
```

- **`opaque def`**, with or without parameters, arms, effects or
  `decreasing`; `export opaque def` for an export. `opaque theorem` is
  refused (a theorem already stays folded where it's used), and so is
  `opaque instance` (an instance is used by taking it apart), each
  `E-PARSE`. Top level only: a local definition can't be `opaque`.
- **`unfolding f, g`** after the result type (and after `decreasing e`):
  within this declaration's body, `f` and `g` unfold as usual. Its type is
  still checked with every opaque definition hidden. Unfolding is
  transitive: unfolding `f` also unfolds what `f` unfolds, and, for
  definitions that call each other, `f`'s opaque group-mates. `:=` may start
  a line of its own after it, as after `decreasing`.
  - Allowed on `opaque def` and on `theorem`; a theorem with `unfolding`
    stays folded even under `case` and `J`. On a plain `def` it's
    `E-UNFOLDING-TRANSPARENT` (a definition that always unfolds would carry
    the body to places where it's hidden: make it `opaque`, or rewrite with
    `f.unfold`); on an instance, `E-PARSE`; on a local definition, `E-PARSE`
    (a `match` or local definition in a body with `unfolding` unfolds what
    the body does).
  - Each name must be an opaque definition (`E-NOT-OPAQUE`), not one checked
    together with this one, which has no body yet (`E-UNFOLDING-GROUP`).
  - Not with `decreasing` yet (`E-DECREASING`).
- **`f.unfold`**: every opaque `f` without an `unfolding` clause gets the
  theorem `f.unfold (x…): f x… = f.%body x…`, where `f.%body` is a copy of
  the body that computes when something looks inside it (a comparison, a
  `match`), and is otherwise shown by name, as is `f.unfold` itself. So
  `rewrite f.unfold in rfl` proves `f 2 = 4`; a proof that needs to
  rewrite inside the body, or to compute through it inside arithmetic, says
  `unfolding f`. A definition with `decreasing` keeps the `f.unfold` that
  `decreasing` makes. One with an `unfolding` clause gets none, since its
  equation may not be well-typed with what it unfolds hidden (`opaque def
  start: Code unfolding Code := 0`: `start = 0` compares a `Code` with a
  `Nat`); naming it is `E-NO-UNFOLD-EQUATION`.
- `opaque` and `unfolding` are keywords.

Examples: `examples/accept/opaque-*.sw`, `examples/reject/opaque-*.sw`.

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
  round. A row with abilities and a tail, `{A | e}`, is total, so a handler
  can't run a partial computation (`E-PARTIAL`), though its clauses may.
  A row variable used only bare, `{e}`, may stand for a partial row, so
  `List.map xs f` takes a partial `f` and is then partial itself. Other
  std functions (`List.filter`, say) take only callbacks that finish, for now.
- Definitions that call each other must be all partial or all total
  (`E-PARTIAL-MIXED`). A partial one is partial once it has the parameters
  its arms or parameters name: `def mk (n: Nat): Nat -> {Partial} Nat :=
  …` is total, returning a partial function.
- Inside its definition, a partial recursive function as a value can't be
  passed to a helper with a fixed row (`E-PARTIAL-CALLBACK`) or returned
  (`E-PARTIAL-ESCAPE`); its type parameters come first and every recursive
  call passes them on unchanged (`E-PARTIAL-NONUNIFORM`).
- Only `stitchwort run` (on either runtime, or with `--js`), `stitchwort test` and the playground run
  partial code. A test may call partial code, with nothing extra to write: it's a runtime check, and `stitchwort test` runs it as `stitchwort run` runs a partial `main`, with no tick limit, so a test that never finishes is a bug for whoever ran it to stop (D1183);
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
| `x \|> f a b` | Pipe forward: `f x a b`, the value becoming the first argument. The loosest operator except `->`; left-associative. See [Pipe forward](#pipe-forward-) |
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
| `not a` | `Bool.not a`; where a proposition is expected, `Not a`. Only when `not` is the library's (a local `not` is an ordinary function) and has one argument: `List.map bs not` is `Bool.not` as a function. See below |
| `f (x := e)`, `f [x := e]` | Supplying the explicit or implicit parameter `x` by name. See [Named arguments](#named-arguments) |
| `_` | A hole the compiler fills in |
| `?` | A goal: a part not written yet. The checker says what must go there. See [Goals](#goals-) |
| `x`, `Nat`, `Succ` | Names. Constructors and data types start with an uppercase letter |
| `0`, `42`, `-5` | Numeric literals: a `Nat`, or an `Int` where one is expected (`Nat` by default; also a `Fin n`, `SafeNat` or `SafeInt` where one is expected); `-5` is an `Int` (or a `SafeInt`). See [Numbers](#numbers) |
| `'a'`, `'\n'`, `'\u{1F600}'` | `Char` literals: one Unicode scalar value. Escapes are `\n`, `\t`, `\r`, `\\`, `\"`, `\'`, `\$` and `\u{…}` with 1–6 hex digits; `\u{…}` must name a scalar value, so `'\u{D800}'` is an error. Text literals take the same escapes |
| `"héllo"` | `Text` literal: a sequence of Unicode scalar values (see [text-and-io.md](proposals/text-and-io.md)) |
| `"""` … `"""` | `Text` literal over several lines. See "Text blocks" below |
| `include "inputs/day04.txt"` | The `Text` in a file, read when the program is checked. See [`include`](#include) |
| `Type`, `Type 1`, `Prop` | Universes |
| `(e: T)` | Type annotation |
| `[a, b, c]` | `List` literal. In an expression, `[x := e]` supplies an implicit argument and every other `[…]` is a list |
| `{ name = e, age }`, `{ p \| age = e }` | Record literal (with an expected type) and update ([Records](#records)). After an arrow, `{` starts an ability row instead |
| `e.name` | A field, or dot notation: `T.name e …` for `e: T`, with `e` as the first argument. No spaces around the `.`; binds tighter than application; `f().x` is `(f()).x` (`name()` with no space is a call) |
| `.name`, `.drop 1` | Method section: `x => x.name`, `x => x.drop 1` (`Text.drop x 1`). A space before the `.` (or a bracket or line start). At the start of an expression it takes the rest: `(.id == id)` is `x => x.id == id`. See [Method sections](#method-sections) |
| `(== 'S')`, `(k +)`, `(&&)` | Operator section: `x => x == 'S'`, `x => k + x`; a bare operator is `a b => a && b`. Not `-`: `(- 1)` is the number. See [Operator sections](#operator-sections) |
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

### Named arguments

`(x := e)` passes `e` for the explicit parameter named `x`, and `[x := e]` for the implicit or `auto` parameter named `x`: the brackets are the declaration's. They go in any order, mixed with positional arguments, and the call is exactly the positional one, with the same term and hash (`crates/driver/tests/named_arguments.rs` names the arguments of every call in `examples/accept` and compares the hashes).

```
def clampTo (low: Nat) (high: Nat) (value: Nat): Nat := …

clampTo (value := 50) (high := 10) (low := 0)      -- clampTo 0 10 50
clampTo 0 (value := 50) (high := 10)               -- the same
place (y := 2) 1                                   -- place 1 2: 1 takes the first free parameter
[1, 50, 200].map (clampTo (low := 5) (high := 100)) -- value => clampTo 5 100 value
pick [label := "a"] [count := 3] 1                 -- implicits in any order
```

- **Filling.** Arguments fill parameters in the order they're written: a named one takes its parameter, a positional one the first explicit parameter still free, and implicits are inserted as for a positional call. A call means the same however it's bracketed: `(place (y := 2)) 1` is `place 1 2`, and in `(place 1) (x := 2)` the `x` is already given. A name given twice, or given after a positional argument has filled it, is `E-DUPLICATE-ARGUMENT`; a name the function doesn't have is `E-UNKNOWN-NAME`, listing its parameters (`(low)`, `[step]`); the wrong bracket is `E-NAMED-BRACKET` ("`count` is an implicit parameter: write `[count := …]`").
- **Leaving parameters out.** Explicit parameters before the last one given that the call leaves out make it a function of them, in their order, with their names: `clampTo (high := 10)` is `low value => clampTo low 10 value`, of type `(low: Nat) -> (value: Nat) -> Nat`, so `(clampTo (high := 10)) (value := 4) (low := 5)` works. Parameters after the last one given stay as in a partial application. A parameter left out is a variable of that function, never inferred from the other arguments: `use (xs := three)` with `use (n: Nat) (xs: Vec Nat n)` must work for every `n`, so it's `E-TYPE-MISMATCH`, with a note to write `(n := 3)`. Where a value is expected, such a call gets a note naming what it's still waiting for.
- **Where the names come from.** The function's declared type: a definition's or constructor's signature, a parameter's or `let`'s annotation (`let g: (start: Nat) -> (stop: Nat) -> Nat := between` renames them), an annotated expression, or a `let` without annotation that keeps its value's type. A partial application keeps the rest of the names. A type synonym, or a result type a definition computes from the parameters (`def scaler (n: Nat): Scaler n`), gives the names of what it computes to once the arguments before it are given: `scaler 2 (plus := 1) (by := 5)` is `(scaler 2) (plus := 1) (by := 5)`. Never unification: in `(if c then f else g) (low := 1)` the names aren't known (`E-UNKNOWN-NAME`, with a note to annotate). A name a function type repeats is `E-AMBIGUOUS` (pass those by position).
- **Everywhere a call is.** Dot notation (`corner.scale (plus := 1) (by := 2)`, the receiver filling the first explicit parameter), method sections (`.shift (dy := 1) (dx := 2)`), pipes (the value on the left fills the first explicit parameter still free: `5 |> clampTo (high := 3) (low := 0)`), constructors (`Circle (id := "a") (radius := 1)`) and proofs (`between (high := h) (low := l) = between l h := rfl`). A data type's parameters, and the forms of quotients, are given by position.
- **Run order.** In a computation, every argument runs once, where it's written, then the call, as for a positional call (`f (b := say 2) (a := say 1)` prints 2 then 1). A stage of the function (an effectful function returning a function) runs when the parameters before it are given: at the call if they're all given, and otherwise inside the function the call makes, each time it's called (with `staged: (x: Nat) -> {Log} ((y: Nat) -> (z: Nat) -> Nat)`, `staged (z := 3)` is a `(x: Nat) -> {Log} ((y: Nat) -> Nat)` that runs `staged x` when given `x`). An argument whose type needs a parameter that a later computation gives, or that the call leaves out (`use (xs := readVec()) (n := readNat())`), is `E-EFFECT-ORDER`: bind it with `let` first. A positional call gets the same error when an earlier computation's type needs a later one's result (`sized (readVec()) (say 2) rfl`, with `sized [n: Nat] (xs: Vec Nat n) (k: Nat) (same: n = k)`).

- **In the editor.** `stitchwort fmt` keeps `(x := e)` and `[x := e]` as written, with one space around `:=`. The language server offers the parameters not yet given by name when you type `(` or `[` after a function (`clampTo (` offers `low`, `high` and `value`), and hovering a name in `(x := e)` shows the parameter's type. Going to the definition from the name is not supported yet.

Examples: `examples/accept/named-arguments.sw`, `examples/accept/named-arguments-effects.sw`, `examples/reject/named-argument-*.sw`. Design: [named-arguments.md](proposals/named-arguments.md).

### Goals, `?`

`?` stands for a part of a proof or program you haven't written yet. The checker carries on past it and reports, at each `?`, the **goal**: what has to go there, after `⊢`, and the names in scope with their types (a `let`'s with its value too). A `?` can go anywhere an expression can.

```
theorem addZero (n: Nat): n + 0 = n :=
  match n with
    | Zero => rfl
    | Succ k => ?
```

```
[GOAL] Goal: in `addZero`
   ╭─[ add.sw:4:17 ]
   │
 4 │     | Succ k => ?
   │                 ┬
   │                 ╰── k: Nat
   │                     ⊢ Succ (k + 0) = Succ k
───╯
1 goal open: the declarations with them, and what uses them, aren't finished, so they aren't checked
```

- **Inside a branch, the goal is the branch's.** Above, `n` is `Succ k`. Goals are shown *computed*, as `rfl`'s messages are: `Succ (k + 0)`, not `Succ k + 0`. A name the branch replaced isn't listed; one that can't be referred to there (shadowed) is shown as `n✝`. Where nothing says what type the `?` has, the goal says "the type here isn't known yet".
- **A declaration with a `?` is unfinished, not wrong.** It isn't checked, so nothing that depends on it can be trusted, but it isn't an error either: later declarations can use it by its type. So you can state a lemma, leave its proof as `?`, and use it in the main theorem first (Lean's `sorry`). What uses an unfinished declaration is unfinished too, silently: only the `?`s themselves are reported.
- **`check` fails while any goal is open**, after printing them and "N goals open", so a project with holes never passes in CI. `test` runs the tests of what's finished, then fails the same way. `run` runs `main` if `main` is finished (if what it needs has a `?`, it says so and doesn't run). `build` builds nothing while a goal is open. `eval` and the REPL refuse an expression that uses something unfinished. `axioms` refuses an unfinished definition.
- **`?` is never filled in by the compiler**, unlike `_`. Where `_` stands for a proof the compiler can't work out (`E-UNSOLVED`), the error suggests writing `?` there to see what's needed.
- Examples: `examples/goals/` (each one's goals are in `crates/cli/tests/snapshots/examples__goals__*.snap`). The design: [lsp-goal-holes.md](proposals/lsp-goal-holes.md).

### Counterexamples to a theorem

When a theorem's statement checks but its proof doesn't, or its whole proof is `?`, the compiler tries the statement on inputs: every small one first, then random larger ones. If some input makes every hypothesis true and the conclusion false, the statement itself is false, and the error (or the goal) says so in a note, with that input and, for an equation, both sides there:

```
theorem subAdd (a: Nat) (b: Nat): (a - b) + b = a := rfl
```

```
   │ Note 2: this statement is false; a counterexample:
   │           a = 0
   │           b = 1
   │         `a - b + b = a` is false:
   │           left:  1
   │           right: 0
```

- **Only a found counterexample is shown.** Finding none says nothing, and is never a reason to think the statement is true: only a proof is. Nothing about the search can make a declaration check.
- **What's tried**: first every input up to a size, smallest first, so a counterexample found then is a smallest one: `Nat`s and `Int`s by size (0, 1, −1, 2, …), every data type and record of the program and the library by its constructors (`Bool`, `List`, `Option`, pairs, your own types), `Char`s from `'a'`, `'b'`, `'0'`, `' '`, `Text` over those (`""`, `"a"`, …), `Float`s from `0.0`, `1.0`, `-1.0`, `Fin n` and `Vec a n` for a known `n`, and maps and sets made with `Map.fromList` from lists of pairs. Then random inputs, growing to lists of 40 elements and numbers up to 40, with numbers at a machine word's edges (2^32, 2^63, 2^64 − 1, 2^64, …), any character (non-ASCII ones too), and `-0.0`, NaN and the infinities. A random counterexample is shrunk: numbers toward 0, list elements removed, each part made smaller, while it's still a counterexample. Up to 2,000 inputs (half small, half random) and about 200 ms. Random inputs are seeded from the statement, so the same statement always gets the same answer. A type parameter, `[a: Type]`, is taken to be `Nat`, and the note says `(with a := Nat)`.
- **Proof fields**: a record like `{ lo: Nat, hi: Nat, ok: lo <= hi }` is made only where its proof field holds, decided by computing it at the fields made (an equation whose sides compute to the same value, or a conjunction of them): no counterexample has `lo > hi`. A proof field that doesn't compute to equations leaves the type out.
- **Hypotheses are filters**: an input that makes one false is skipped, and later hypotheses may use earlier ones' proofs. With the hypothesis `(h: b <= a)` added, `subAdd` is true, and its (still wrong) proof gets no note.
- **What's left out, silently**: statements with a function parameter, a parameter whose type depends on another (`(n: Nat) (i: Fin n)`), a type with indices (other than `Fin` and `Vec` of a known size), a function field, or a proof field that doesn't compute to equations; and a hypothesis or conclusion nothing decides (`if` couldn't decide it either: `=` on a type without `DecEq`, `List.Sorted` written as a proposition, `Exists`).
- **`stitchwort check --counterexamples`** searches every theorem of the files or namespaces checked, its proof checked or not, with up to 10,000 inputs and 500 ms each (`--counterexample-budget 2s` for more time), prints a line for each theorem found false, `✗ name  counterexample: …`, then a count of the theorems found false, with none found, given up on, inconclusive, and not applicable. `--verbose` prints a line for every theorem: also `~ name  none in N cases (sizes up to k; evidence, not a proof)`, `- name  gave up (hypotheses true in M of N cases)`, `- name  inconclusive (ran out of steps)` and `- name  not applicable: …` (why it's out of scope). A counterexample to a theorem whose proof checked means something is wrong (an axiom it uses, the compiler, or the search), and is printed in full; any counterexample makes the command fail.
- **Trustworthy as a failing `test` is**: the statement runs on the fast runtime, and a counterexample is run again on the reference evaluator before it's shown.
- Examples: `examples/reject/counterexample-*.sw`, `examples/goals/counterexample-*.sw`. The design: [counterexample-search.md](proposals/counterexample-search.md).

### `include`

`include "path"` is a `Text` with the contents of a file, read when the program is checked: `(include "../../../../inputs/day04.txt").lines` is the lines of a puzzle input. The path is a literal in quotes, written like an argument (put it in brackets before a `.`, as above).

- **Relative to the file that has the `include`**, with `/` between names, `..` for the folder above, whatever folder `stitchwort` runs from. It must stay inside the project folder (for a file run on its own, the file's folder); a path above it, or an absolute one, is `E-INCLUDE-OUTSIDE`.
- **The contents are what is hashed, not the path.** The text becomes a literal in the definition, so editing the file reruns exactly the tests that use it, and moving or renaming it, with the same text, changes nothing. Tests in `aoc/src/Aoc/DayNN/Tests/Input.sw` use it to check each day's answers on the committed puzzle input.
- **Errors.** `E-INCLUDE-MISSING` names the file tried (from the project folder); `E-INCLUDE-NOT-TEXT` is a file that isn't UTF-8; `E-INCLUDE-OUTSIDE` includes a path that leaves the project folder, by `..` or through a symlink; `E-INCLUDE-UNAVAILABLE` is anywhere there are no files to read: a single file in the playground (its projects read the bundled files).
- The text is one compact literal like any other, so a 20 KB input costs no more to check or hash than a 20 KB string.

### `&&`, `||` and `not`

Each has two readings, chosen by what's expected, the way `if c` chooses:

- **Where a proposition is expected** (a type: a signature, `if h: …`, an `auto` argument) they're the propositions `And a b`, `Or a b` and `Not a`, and both operands must be propositions. A `Bool` operand is an error (`E-NOT-A-TYPE`) with a note: for a `Bool` `b`, the proposition is `b = True`. `if h: x < y && y < z` gives `h: x < y && y < z` in the `then` branch and `h: Not (x < y && y < z)` in the `else` branch. The library's `Decidable.and`, `Decidable.or` and `Decidable.not` decide them from decisions of each side; both sides are decided before these run, so `if h: p && q` decides `q` even when `p` is false. `And.left`, `And.right` and `Or.neither` take them apart. Two more propositions are in the library (`import Std (Iff, Exists)`), written with operators of their own ([Logic notation](#logic-notation-in--and-exists)): `p <-> q` is `Iff p q`, a record of `forward: p -> q` and `backward: q -> p` (`h.forward x`; `Iff.refl`, `Iff.symm`, `Iff.trans`), and `exists (x: a) => P` is `Exists a ((x: a) => P)`, which says some `x: a` satisfies `P` (`exists (n: Nat) => n * n = 49`), built as `Witness x proof` and taken apart with `Exists.elim` or a `match` whose result is a proposition. Taking the witness out as data is `E-PROP-ELIM` (`examples/reject/exists-witness-to-data.sw`), as for any proposition with a data field.
- **Otherwise** (a `Bool` expected, as in a `def …: Bool`, a test or `if c`, or nothing known, as in `let`) it's a `Bool`, and **each operand is a condition, as `if` takes one**: a `Bool`, or failing that a proposition with a decision procedure, decided. So `x < y && y < z`, `flag && x < 3` and `not (x < y)` are all `Bool`s, and a `Bool` operand means what it always has. `a && b` is `if a then b else False` and `a \|\| b` is `if a then True else b`: `b` isn't evaluated when `a` decides the answer, and when `b` performs operations, they're performed only if `b` is evaluated. Operations in `a` are performed first. With nothing expected, if the `Bool` reading fails, the proposition reading is tried, with everything the first try did undone; if that fails too, the `Bool` reading's error is reported (`E-AUTO-NONE` at an operand nothing decides, as for `if`).
- **The right side knows the left side**, as in `if a then b else False`: when `a` is a proposition (`n != 0`, `x < y`), `b` is checked knowing that `a` holds in `a && b`, and that it doesn't (`Not a`) in `a || b`, so an `auto` argument in `b` can use it. `n != 0 && len % n == 0` works (the `%` needs a proof of `n != 0`), as does `n = 0 || total / n > 2`; in a chain `a && b && c`, `c` knows both `a` and `b`. A `Bool` left side (`n == 0`, `xs.isEmpty`) says nothing about `b`, just as `if n == 0` doesn't: write `n != 0` or `n = 0` for the fact. When `b` needs no proof, `a && b` is the plain `if a then b else False` on the decision's `Bool`, so the library's lemmas about `&&` and `||` on `Bool`s apply to it; when it does, it's `if _: a then b else False` (`Decidable.elim`), as that `if` makes it.

Precedence, loosest first: `->`, then `<->`, then `\|>`, then `\|\|`, then `&&`, then `=` `!=` `==` `<` `<=` `>` `>=` `in` `!in` (the full table is under [Logic notation](#logic-notation-in--and-exists)). So `a \|\| b && c` is `a \|\| (b && c)`, `x < y && y < z` needs no brackets, and `p && q -> r` is `(p && q) -> r`. `not` is a function, so `not x < y` is `(not x) < y`: write `not (x < y)`; prefix `!` binds the same way, tighter than every binary operator (`!x < y` is `(!x) < y`). The printer shows `And p q`, `Or p q` and `Not p` as `p ∧ q`, `p ∨ q` and `¬p` (D1204). A single `&` is still an error.

A test (`test "…" := e`) takes `e` as a condition too: a `Bool`, or a proposition with a decision procedure, so `test "ordered" := 1 < 2 && 2 < 3` and `test "small" := 3 < 5` work.

**Anywhere a `Bool` is expected**, a proposition with a decision procedure is decided, as Lean's `decide` coercion does: `List.filter xs (n => k * n <= size)`, `List.all xs (x => x < 10)`, `def le (a b: Nat): Bool := a <= b`. The expression is elaborated as usual; only if it turns out to be a proposition (its type is `Prop`) and the expected type is the library's `Bool` is it replaced by `Decidable.toBool` of its decision, except that the standard decisions of `<=` and `<` on `Nat` and `Int` are read as the comparison itself: `a <= b` as a `Bool` is `Nat.leq a b` (`Int.leq`, `Int.less`; `a < b` on `Nat` is `Nat.leq (Succ a) b`), so it prints, computes and is generalised as that, and a `Bool` fact about it (`Bool.andLeft`, `match e: a <= b with`) is the `Nat.leq a b = True` you would write by hand. `==` and the other decisions stay `Decidable.toBool` of theirs (`Decidable.toBoolSound`, `toBoolOf`). A proposition nothing decides is `E-AUTO-NONE` at the expression, saying a `Bool` is expected (`List.filter (g => g = f) gs` on functions). Where a proposition is expected nothing changes, and conditions (`if c`, `&&`, `||`, `not`, `test`) still try the `Bool` reading first and then the proposition, as above.

### Logic notation: `in`, `<->` and `exists`

([proposals/logic-notation.md](proposals/logic-notation.md), D1200–D1211.) Three forms for statements about collections and logic, each with a Unicode spelling:

- **`x in c`** (`x ∈ c`) is membership, a proposition: `List.Mem x xs` for a list, and `c.contains x = True` for a `Set` or for the keys of a `Map`. Where a `Bool` is expected (`if x in seen`, `xs.filter (x => x in allowed)`, a test) it is decided, as any decidable proposition is: by `List.decMem` from the element type's `DecEq` for a list, and as `c.contains x` for a set or map. **`x !in c`** (`x ∉ c`) is its negation (`Not`, or `Bool.not` as a `Bool`). Anything else on the right is `E-TYPE-MISMATCH`. It sits with `=` and `<`, not associative: `x in xs && y in ys` needs no brackets, `x in xs = b` is an error. `!x in xs` is an error saying the `!` would apply to the element: write `x !in xs` or `!(x in xs)`. `in` is a reserved word.
- **`p <-> q`** (`p ↔ q`) is `Iff p q`. Not associative (`p <-> q <-> r` is an error), looser than `&&`, `||` and `|>`, tighter than `->`: `p && q <-> r` is `(p && q) <-> r`, and `p <-> q -> r` is `(p <-> q) -> r`.
- **`exists (x: T) => P`** (`∃ (x: T) => P`) is `Exists T ((x: T) => P)`; several parameters, `exists (x y: Nat) => …`, nest one `Exists` each. Like a lambda it takes everything to its right, and like one it may start an expression, the right side of `<->`, or the last operand of `&&` or `||`; elsewhere it needs brackets. After a `.`, `exists` is an ordinary name (a field or method called `exists`), not the keyword. There is no `forall` form: a dependent function `(x: T) -> P` says "for all".

Precedence, loosest first:

| Level | Operators | Grouping |
|---|---|---|
| 1 | `x => e`, `exists (x: T) => P` | take everything to the right |
| 2 | `->` | right |
| 3 | `<->` | none |
| 4 | `\|>` | left |
| 5 | `\|\|` | right |
| 6 | `&&` | right |
| 7 | `=` `!=` `==` `<` `<=` `>` `>=` `in` `!in` | none |
| 8 | `++` | right |
| 9 | `+` `-` | left |
| 10 | `*` `/` `%` | left |
| 11 | prefix `!` `-` | |
| 12 | application, `.` | |

**Unicode spellings** (D1200). Each is the same token as its ASCII form; the formatter keeps whichever was written (D1209), and a proof written either way has the same hash:

| ASCII | Unicode | | ASCII | Unicode |
|---|---|---|---|---|
| `in` | `∈` | | `!` | `¬` |
| `!in` | `∉` | | `<=` | `≤` |
| `->` | `→` | | `>=` | `≥` |
| `<->` | `↔` | | `!=` | `≠` |
| `&&` | `∧` | | `exists` | `∃` |
| `\|\|` | `∨` | | | |

Other symbols get an error naming the replacement: `∀` (write a function type `(x: T) -> P`), `⇒` (`=>` for a lambda or match arm, `->` or `→` for implication), `λ` (`x => e`), `⇔` (`<->`), `≡` (`=`), `⊆` `∪` `∩` and the other set operators (not supported: `Set` has functions), `ℕ` (`Nat`), and so on (`crates/syntax/src/lexer.rs`, `UNSUPPORTED`). There is no user-defined notation (D1207).

**Printing** (D1204, D1211). Goals and messages show `∧` `∨` `¬` `≠` `≤` `∈` `∉` `↔` and `∃ (x: T) => P`, whichever spelling the source used; `->` stays `->`. Comparison on `Nat`/`Int` under a binder may show unfolded (`Nat.leq k y = True`), as before.

**In a `rewrite`.** `rewrite rule in e` uses the same `in`, so a membership test in the rule needs brackets: `rewrite h (3 in xs) in rfl`. Unbracketed, the first `in` ends the rule and the second makes the body a membership test, which is `E-PARSE`, "a membership test in a `rewrite` needs brackets" (`examples/reject/logic-in-rewrite-rule.sw`).

Examples: `examples/accept/logic-notation.sw`, `examples/goals/logic-notation.sw`, `examples/reject/logic-*.sw`.

### Pipe forward `|>`

`x |> f` is `f x`, and `x |> f a b` is `f x a b`: the value on the left becomes the **first** explicit argument, which is where dot notation puts it too (`x.f a b`). That's why the library puts the main argument first (`List.map xs f`, `List.sum xs`), so a pipeline reads in the order things happen:

```
def total: Nat :=
  people
    |> List.map (p => p.age)
    |> List.sum
```

**Library convention:** in a function that takes a main value (the collection, optional or text being operated on) plus other arguments, the main value comes **first**, then the other arguments, then any function arguments last (`xs.foldLeft 0 (acc x => acc + x)`, which suits a lambda that spans lines). Dot notation, a pipe, a method section and the prefix call then all agree: `xs.map f`, `xs |> List.map f`, `xs |> .map f` and `List.map xs f` are the same call. A function of two values of its own type is named so that `x.f y` reads as a sentence, with the subject first: `t.startsWith p`, `a.sub b`, `xs.append ys`, `p.isPrefixOf t`. Pipes are not the same as in F#, OCaml, Elm or Haskell, which pipe into the last argument; they follow Gleam and Elixir.

It is the loosest operator except `->`, and groups to the left: `x |> f |> g` is `(x |> f) |> g`, `a + b |> f` is `(a + b) |> f`, and `x |> f -> T` is `(x |> f) -> T`. Because it's looser than `=`, `xs |> List.sum = 6` is `xs |> (List.sum = 6)`; write `(xs |> List.sum) = 6`.

- **Layout.** A line may start with `|>` to continue the expression, if it's indented at least as far as the line the expression starts on, even at the enclosing block's own column (as `then` and `else` may). `|>` is its own token, so it never clashes with the `|` of arms and alternatives. After a `match`, a `|>` line at or right of the last alternative's `|` continues that alternative's body (the last alternative takes what follows, as with any operator); one further left, but at least at the `match` line's column, pipes the whole `match`.
- **A lambda on the right** takes the rest of the pipeline: `x |> y => f y |> g` is `x |> y => (f y |> g)`, which means the same as `(x |> y => f y) |> g`.
- **The left side is checked first**, and its type is unified with the function's first explicit parameter before the other arguments are checked. So `people |> List.map (p => p.name)` knows `p: Person` when it reaches the lambda (`List.map people (p => p.name)` works the same way, since `people` comes first). A value of the wrong type is `E-TYPE-MISMATCH`, pointing at the function: "`|>` passes the value as the first argument of `List.map`, which takes `List a`; the value before `|>` has type `Text`". A function whose first explicit parameter isn't of the value's type is the same error: there is no search for a later one.
- **The left side runs first** when it performs operations, then the right side's arguments, then the call: `say "left" 1 |> add (say "right" 2)` prints `left`, then `right`.
- **A number literal on the left** is just `f 5`: it takes its type from `f`, as an argument would.

Implicit and `auto` arguments, named arguments and constructors work on the right as in a normal call; the value on the left fills the first explicit parameter they leave free (`5 |> clampTo (high := 3) (low := 0)` is `clampTo 0 3 5`, with `value` the one parameter left).

### Method sections

`.f args` is `x => x.f args`: dot notation with the receiver left out.

```
people.map .name                    -- people.map (p => p.name)
people |> .map .age |> .sum         -- (people.map (p => p.age)).sum
ls.map (.split ',')                 -- ls.map (l => l.split ',')
```

- **Chains and arguments.** `.name.length` is `x => x.name.length`. Arguments after the head section belong to it: `.drop 1` is `x => x.drop 1`. As an argument a section takes none, so bracket it: `List.map people .name`, `people.map (.greet "Hi")`. Like `e.name`, the receiver is the function's first explicit argument (`.split ','` is `t => Text.split t ','`).
- **The space rule.** A section follows a space (or a bracket, or starts the expression): `f p .name` is `f p (.name)`, while `p.name` is still a field access. `p. name` is still an error, and so are `.Name` and `.1`.
- **Pipe.** `xs |> .drop 1` is rewritten by the parser to exactly `xs.drop 1`, with no lambda, so `xs |> .drop 1 |> .sum` is `(xs.drop 1).sum`.
- **Layout.** A section can't start a continuation line as an argument: in `foo xs` followed by an indented `.map f`, the `.map f` would read as another argument of `foo`, so it's a parse error ("a line can't start with a method section"), with a note pointing to `|> .map f` or `(.map f)`. A line starting `|> .map f` is fine.
- **Checking.** A section is a lambda, so it's checked like one: its receiver's type must be known from the expected function type (`people.map .name`, `apply .length "abc"` for `apply (f: Text -> Nat)`), from a pipe's left side, or from an annotation (`(.drop 1: List Nat -> List Nat)`). In an application, a section whose parameter type isn't known yet is checked after the other arguments, so `List.map people .name` works, and so would a section placed before `people` (a plain lambda is checked in place first and waits only if that fails).
- **The partial application.** Where the receiver is the function's only explicit parameter and the section has no arguments, the section is not a lambda but the function `T.f` itself: `.snd` is exactly `Pair.snd` and `.isZero` is `Dial.isZero`, so `xs.any .snd` and `xs.any Pair.snd` are the same term, and a proof that restates a program's expression with the qualified name (`match e: Vec.any Pair.snd next with`) still finds it. A section with arguments stays a lambda: `.sub 3` is `x => Nat.sub x 3`, `.addNat 3` is `x => Mod.addNat x 3`. Implicit arguments are inserted as for the qualified name. A section with chained fields (`.name.length`), or whose arguments don't fit until the receiver's type is fixed, is a lambda too.
- **To the end of the expression (D1192).** A section that *starts* an expression (after `(`, `,`, `:=`, `=>`, `then`, `else`, `|>`) takes the whole expression, operators included: `(.id == id)` is `x => x.id == id`, `(.trim != "")` is `x => x.trim != ""`, `(.fst + 1)` is `x => x.fst + 1`, `(.items |> List.sum)` is `x => x.items |> List.sum`. Every binary operator counts (`+ * ++ == != < <= > >= && || in !in <->`). After a pipe, `xs |> .sum == 6` is `xs.sum == 6`. It's exactly the written-out lambda, the same term. As an argument a section still takes nothing: `f .a == b` is `(f .a) == b`. The section's argument is used once, at the start; a second section in the same expression is a separate function (`(.isZero || .isEven)` is `x => x.isZero || (.isEven)`, a type error whose note says to write the lambda). Operands run each time the function is called, as in a lambda.
- **`_.name`.** `_` is a hole, not a parameter, so `.count _.isZero` is `E-CANNOT-INFER` with the ordinary "can't tell what the value is" message and no special help (D1194). There is no placeholder for a function's argument, `_`, `it` or `$0` (D1196).
- **Unknown receiver.** `let g := .drop 1` or `(.length) "abcd"` is `E-CANNOT-INFER` ("can't tell what `.drop` is applied to"), with a note suggesting a pipe, passing it where a function type is known, or an annotation.
- **No such function.** The ordinary dot-notation error: `xs |> .dorp 1` is `E-UNKNOWN-FIELD`, "`List` has no field or function `dorp`", with a "did you mean `drop`?" note.
- **Effects.** It follows lambda rules: `IO.readAllLines() |> .map (.split ',') |> .length` works in a `{IO}` function.

Examples: `examples/accept/method-sections.sw`, `examples/reject/section-unknown-receiver.sw`, `examples/reject/section-no-such-function.sw`, `examples/reject/section-on-next-line.sw`, `examples/accept/method-section-partial.sw`, `examples/reject/section-underscore.sw`. Design: [method-sections.md](proposals/method-sections.md), [anonymous-lambdas.md](proposals/anonymous-lambdas.md); examples for the end-of-expression form: `examples/accept/lambda-sections.sw`, `examples/reject/section-twice.sw`.

### Operator sections

An operator in brackets with one operand left out is a function of that operand (D1193), and an operator alone is a function of two (D1195). Haskell's sections, with `-` excluded.

```
xs.findIndex (== 'S')        -- x => x == 'S'
xs.filter (> 3)              -- x => x > 3
xs.map (10 +)                -- x => 10 + x
xs.map (++ "!")              -- x => x ++ "!"
xs.foldLeft 0 (+)            -- a b => a + b
rows.foldLeft True (&&)      -- a b => a && b
cs.filter (in vowels)        -- c => c in vowels
```

- **Which operators.** `+ * / % ++ = != == < <= > >= && || in !in <->` and their Unicode spellings (`∈`, `∉`, `↔`, `∧`, `∨`, `≤`, `≥`, `≠`). `|>`, `->` and `=>` are not operators in this sense: `(|> f)` would just be `f`.
- **`-` is not a section.** `(- 1)` and `(-1)` are the number; for the function write `(.sub 1)` or `(x => x - 1)`. `(k -)` is a parse error too. The bare `(-)` is subtraction, `a b => a - b`.
- **One operand, binding tighter.** The operand of `(op e)` or `(e op)` must bind tighter than the operator (`||` takes a whole `&&` chain), so `(+ 1 + 2)` and `(a + b *)` are errors with a note to add brackets: `(+ (1 + 2))`, `((a + b) *)`.
- **A lambda.** A section is exactly the lambda, the same term; `a > b` is `b < a`, so `(> 3)` is `x => 3 < x`. The type of the argument comes from where the section is used, as for a lambda, so `let f := (+ 1)` needs an annotation. A bare operator is a two-parameter lambda: `foldLeft 0 (+)` works where `(a b => a + b)` does.
- **Not a placeholder.** The missing operand is always at the edge. For a missing value in the middle write the lambda (D1196).

Examples: `examples/accept/lambda-sections.sw`, `examples/reject/section-minus-is-negation.sw`, `examples/reject/section-operator-chain.sw`, `examples/reject/section-operand-too-loose.sw`. Design: [anonymous-lambdas.md](proposals/anonymous-lambdas.md).

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

- **The goal.** Every occurrence of the scrutinee in the expected type is replaced by the pattern of the branch. An occurrence is found by shape: the same term, ignoring source positions and binder names. No definition is unfolded to look for it and no metavariable is solved, so `Ord.compare y x` is not an occurrence of `Ord.compare x y`,. (`a <= b` as a `Bool` is `Nat.leq a b`, so it is an occurrence of it; `a == b` is `Decidable.toBool` of a decision, and is not `Nat.equal a b`.)
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

The condition may be written `a <= b` or `Nat.leq a b`: they are the same `Bool` (`match h: a <= b with` was `E-MATCH-MOTIVE` before SW-206, since a proposition is not a `Bool` to match on; it is now read as the `Bool` it decides). On any other type whose decision computes to `Bool.decTrue b`, `match h: c < x with` matches on `b`, the comparison an unfolded `if c < x` holds: on a `Fin`, ordered by `Ord.byKey Fin.toNat`, that is `Nat.leq (Succ (Fin.toNat c)) (Fin.toNat x)`, so the branches see the `if` decided and `omega` reads `h` (D1073, `examples/accept/match-decided-by-key.sw`). Hypotheses whose types mention the condition (`h: Nat.leq a b = False -> …`) are generalised too, and a branch's goal has already computed one step further, so a branch may need less than the same proof under `Bool.inspect` did. Real proofs: `aoc/src/day03/day03.sw` (`pickGe`, `pickLen`, `pickSub`, `pickBestStep`) and `aoc/src/day02/day02.sw` (`window`, `gaussPick`).

**Proving things about a definition with an inner `match`.** A `match` inside an arm that isn't the whole right-hand side (an operand of `||`, say) becomes a generated function whose name source can't write, so a lemma can't mention it. A proof doesn't need to:

- *Arms compute.* A call with constructors where the definition splits is already its right-hand side, so `reach (Cons line rest) c (Succ k) d` is an `if` on `charAt line c == '^'` without any lemma, and any equation of that kind is `rfl`.
- *Match on the condition.* `match e: cond with` refines a hypothesis about the call (a parameter, a lambda's variable or a `let`), because the condition is there once the call has unfolded.
- *Leave the inner `match`'s part as `_`.* Arguments you write out inside a branch (`reach (Cons line rest) c (Succ k) d`) are elaborated afresh and aren't refined, only the goal and the variables in scope are. A `_` is solved by unification from the hypothesis, so the generated function is filled in and never written. The type mismatch note for a written-out argument suggests this.
- *Split its scrutinee to make it compute.* The generated function unfolds once its own scrutinee is a constructor, so `match c with | Zero => … | Succ b => …` turns the hidden operand into `False` or `reach rest b k d`.
- *To state something about it, name it.* Writing the same `match` in a lemma makes a second generated function, which is a different definition. Two such functions are compared by their bodies (the same scrutinee, and the same result in every branch), but not when one calls the definition it's written in, as `reach`'s does, so a lemma about a recursive definition's inner `match` still needs it named (SW-386, D1091). Make the `match` a local `def` in the arm and refer to it from outside as `owner.name` ([Local definitions](#local-definitions)).

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

`rewrite` and `in` are reserved words (`in` is also membership, `x in xs`). `at` is not: it is only special where a rule can end (outside brackets, inside a rule, and not as a field `r.at`). So a variable called `at` is an ordinary name, a rule may start with one (`rewrite at b h in t`, with `at` a lemma), and a rule that passes it as an argument puts it in parentheses, `rewrite f (at) at h`. The result is a `J` term, which the kernel re-checks; the kernel is unchanged.

- **The goal must be known**, without `at`. `rewrite` is checked against a goal: a definition's body, an argument whose type is fixed, a `calc` step, a `let` with a type. With none (`let h := rewrite p in t`), it is `E-REWRITE-NO-GOAL`; give the type with an ascription, `(rewrite p in t: a = b)`, or rewrite a fact's type instead with `at`. In a `calc` step, `rewrite p` is checked against the step's line, `e(i-1) R e(i)`, and may rewrite either side.
- **`at`: rewriting a hypothesis.** `rewrite p at h` searches the type of `h` instead of the goal, by the same rules (below), and is `h` carried along `p`: a fact about `b` where `h` was about `a`. It never needs a goal, so it works in an untyped `let`, under `Eq.sym`, or where the goal has computed past what you'd rewrite: in `d != 0` from `h: 1 <= d`, the goal after `e: d = 0` is `False = True`, with no `0` left in it, but `e => Bool.falseNotTrue (rewrite e at h)` rewrites `h` to `1 <= 0`, which computes to `False = True`. With `in t`, `h` is rebound for `t` (a `let`, so the old `h` is shadowed; a hypothesis whose type mentions the old `h` isn't changed). `in` needs a local name after `at` (`E-REWRITE-TARGET` otherwise); without `in`, any expression may follow `at`, such as a lemma applied to its arguments. To rewrite the goal too, nest: `rewrite p at h in rewrite p in t`. The errors are the goal's, about "the type of `h`". Examples: `examples/accept/rewrite-at.sw`, `examples/reject/rewrite-at-*.sw`; design: [rewrite-hypothesis.md](proposals/rewrite-hypothesis.md).
- **The rule** is any proof of an equation, with its implicit arguments left open if nothing fixes them (`[n: Nat] -> f n = g n` used as `rewrite h`). Explicit arguments left off its end are unknowns too, as if written `_`: `rewrite Nat.addComm` is `rewrite Nat.addComm _ _`. The equation's *left side* needs a function, constructor or variable at its head; an unknown function (`?g x`) is `E-REWRITE-RULE`, as is a proof that isn't an equation whatever its arguments.
- **Premises.** An argument of the rule that is a proof, left off or written `_` (`Nat.addSubCancel x n` needs `x <= n`), is found when the rule matches: by unification with the rest of the rule, else by a hypothesis in scope of exactly its type, else by `omega`. An `[auto]` argument waits until the match has fixed what it is about (`rewrite Nat.modSmall`). Nothing proves it: `E-REWRITE-PREMISE`, naming the premise and the facts there were; give the proof in that argument's place. Examples: `examples/accept/rewrite-premises.sw`, `examples/reject/rewrite-premise-unproved.sw`.
- **Finding occurrences.** The goal is searched in pre-order, outermost first, left to right, and the search never looks inside an occurrence it has chosen. A subterm is an occurrence if it has the same head and number of arguments as `a`, is the same term or has the same type and *computes* to it. Matching the rule's open arguments is one-way: only the rule's own can be solved, and a candidate that fails leaves nothing solved. Every occurrence is replaced, then `t` is checked against the result. If there are none, it is `E-REWRITE-NOTHING`; the message shows the goal (after the rules before this one), what the left side computes to when that differs from how it is written (`Succ n / 1` is looked for as `Succ (Nat.divFuel n n 1)`), and whether the goal already holds by computing, as it does when an earlier rule already replaced what this one would have.
- **Inside a function argument.** An occurrence that uses the variable of a function passed as an argument (`x + 0` in `List.map xs (x => x + 0)`) can't be replaced by `J`, which would need function extensionality. Instead `rewrite` uses the **congruence lemma** of the call the function is passed to, the same lemmas a `decreasing` recursive call inside a function uses (below: `List.mapCong`, `List.sumByCong`, …, found by name beside the function): it rewrites the function's body with its variable as a local, and the lemma turns that equation, for every value of the variable, into one between the two calls. A lemma may also give **facts** about the variable, which are hypotheses while the body is rewritten (so they prove a rule's premises): `FCongRange` gives `low: s <= x` and `high: x < s + c` where the list is `List.rangeFrom c s` (so `List.range n`), `FCongMem` gives `m: List.Mem x xs`. `rewrite` tries `FCongRange`, then `FCongMem`, then `FCong`, using the first whose left side matches the call. Inside a function, a rule whose premise isn't proved there isn't used there; a later rule may do it, and if nothing is rewritten it is `E-REWRITE-PREMISE`. So `rewrite Nat.addZero _` proves `List.map xs (x => x + 0) = List.map xs (x => x)` by `List.mapCong`. It works through several functions inside each other (`List.map xs (x => List.map ys (y => x + Succ y))`), with `in`, `<-` and `at`, and for a function given as a partial application (`List.sumBy xs (f k)`, with a rule about `f k _`). The result is still an ordinary checked proof term.
  - **`_` for the variable.** The rule is elaborated again for each function, with its unknowns (`_`, implicit arguments) solved there, once per function: write `_` for an argument that is the function's variable, `rewrite Nat.mulSucc k _`. A rule with no unknowns (`Nat.mulSucc k i`, with `i` not in scope) doesn't look inside functions.
  - **Order.** Occurrences inside functions are rewritten first, a step each (outermost call first, its inner functions before its own body), then those that use no such variable, in one step.
  - **No lemma.** If an occurrence is there only inside a function passed to `F` and `F` has no `FCong`, it is `E-REWRITE-CONG`, naming the lemma and showing its statement for `F` (`examples/reject/rewrite-inside-function-no-lemma.sw`). Functions the compiler made (an effect's handler) aren't named; nothing is found there.
  - **Limits.** A variable bound by the goal itself (`f y` in `(y: Nat) -> f y = g y`) still can't be rewritten: introduce it first (`y => rewrite …`). Facts come only from the congruence lemma: one about the variable that a different lemma would give (a `filter`'s condition, say) needs that lemma by hand. The search sees definitions unfolded, so a call such as `List.sumBy xs f` is reached as `List.foldLeft …` and goes through `List.foldLeftCong`. An `[auto]` argument of a lemma used as a rule may need saying, `List.sumByAdd [c := Nat] _ _ _`. Examples: `examples/accept/rewrite-inside-function.sw`; design: [proof-automation.md §6.1](proposals/proof-automation.md).
- **Cost.** All the comparisons of one `rewrite` share a budget of evaluation steps. Running out is `E-REWRITE-BUDGET`, never "no match": it says the comparison was too expensive, not that the occurrence is absent. The message shows the part of the goal and the left side in notes, shortened (`STITCHWORT_FULL_TERMS=1` shows them whole). A part that is the same term as the left side (binder names and source locations aside) matches without computing, so the budget goes on parts that differ. State the step with `calc`, or rewrite with a more specific equation. `STITCHWORT_REWRITE_METRICS=1` prints, per `rewrite`, how many subterms were looked at, how many had the right head, how many comparisons ran and the steps they took.
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
let MkSize { width, .. } := s      -- a constructor's fields by name
let { name, .. } := p
let (a, b): (Nat, Nat) := e       -- the right-hand side is checked against the type
let _ := e
(a, b) => a + b
acc (k, v) => acc + v
{ name, .. } => name
```

`let p := e` followed by the rest of the block means `match e with | p => rest`, and a lambda's pattern parameters are matched against its arguments in the same way. `let x := e` and `let (x) := e` are the ordinary `let`.

A pattern made only of tuples, records, variables and `_` is instead projections, outside a proof: `let (a, b) := e` is `let a := e.fst` and `let b := e.snd`, with `e` computed once (in a hidden `let`, unless it's a variable). So a function using one computes even when `e` is unknown: after `def sw (p: (A, B)): (B, A)` whose body is `let (a, b) := p` then `(b, a)` on the next line, `sw p` is `(p.snd, p.fst)` by `rfl`. Where the expected type is a proposition (a proof), it stays the `match`, which splits `e` into a pair and so refines the goal ([proposals/let.md](proposals/let.md) §7, §A.7).

A thunk `() => e` doesn't match at all: its parameter is a `()`, and the lambda is the plain `_ => e` (with the parameter's type `()`), so the same thunk written twice is the same term, and a law about `() => xs.map f` in a theorem's statement applies to `() => xs.map f` written in its proof (`examples/accept/reify-thunk-in-proof.sw`). Only where the type after it mentions the parameter (`(u: ()) -> P u`) is it matched, so that the goal becomes `P ()`.

The one-alternative `match` must cover every value of the type, or the `let` is `E-LET-REFUTABLE`: coverage is by the type, not the value, so `let Some x = Some 3` is rejected by design. Use `match` to say what happens otherwise. Elimination of proofs still applies (`E-PROP-ELIM`). In a block with abilities, the right-hand side runs once, in order, before the rest.

Limits:

- a record pattern in a lambda needs its type known where the lambda is checked, as `p.name` does;
- a pattern `let` that isn't the whole right-hand side is lifted like a `match`, so it isn't available in `partial` functions, data or ability declarations, or the REPL.

Examples: `examples/accept/let-patterns.sw`. Design: [syntax-conveniences.md](proposals/syntax-conveniences.md) section 5.

### `omega`

`omega` is a proof of a linear arithmetic fact about `Nat`s, found by the compiler from the facts in scope and checked by the kernel:

```
theorem stacked (id: Nat) (lastTo: Nat) (rFrom: Nat) (h1: id <= lastTo) (h2: lastTo + 1 <= rFrom): id < rFrom :=
  omega

theorem topGe: (z: Nat) -> (rs: List Range) -> z <= rs.foldLeft z (m r => Nat.max m r.to)
  | z, Nil       => Nat.leRefl z
  | z, Cons r rs => omega [Nat.leMaxLeft z r.to, topGe (Nat.max z r.to) rs]
```

| form | meaning |
|---|---|
| `omega` | proves the goal from every arithmetic fact in scope |
| `omega [e1, e2]` | the same, with the facts `e1` and `e2` (any proofs, such as a lemma applied to its arguments) added |

`omega` is a keyword and a term, like `rfl`: it can be a definition's body, a `calc` step's proof, an argument whose type is fixed, or `(omega: x * 3 = x + x + x)` given to `rewrite`. Where nothing says what it proves (`let p := omega`) it is `E-OMEGA`. The proof it writes is an application of `Std.Omega.prove` (or `Std.Omega.proveEq` for an equation) to the facts and goal as syntax, a certificate saying how to combine them, `rfl` (the kernel running the library's checker) and the facts' proofs; nothing new is trusted. Design and as built: [omega.md](proposals/omega.md).

- **Goals.** `a <= b`, `a < b` and `a = b` between `Nat`s, and `Void` (the facts contradict each other). Any other goal (a `Bool` equation, `xs = Nil`, a type of data) is proved when the facts contradict each other, so `Void.exfalso omega` is just `omega`. Around those: `Not p` (proved as `h => …` with `h: p` as a fact), `And p q`, `Nat.LexLess a1 a2 b1 b2` (a lexicographic `decreasing` obligation: `a1 < b1`, else `a1 = b1` and `a2 < b2`), `(p && q) = True`, `Nat.leq a b = False` (from `b < a`), and a decided proposition `Decidable.toBool d = True`/`False`, which is how `a <= b` inside `&&` comes out. A goal is read as it computes, so `x < 0` is `False = True` and `2 < 3` is `True = True`, both fine.
- **Arithmetic.** `+`, numbers, `Succ`, and multiplication by a number on either side: `x * 3` and `3 * x` (which computes to `x + (x + (x + 0))`; `k * x` is taken for `k` up to 1000, and a larger `k` is `E-OMEGA` with a note to write `x * k`). Truncated subtraction `a - b`, `Nat.max a b` and `Nat.min a b` (also after `max` and `min` have computed to their `if`) are atoms `omega` knows more about: what always holds (`a - b <= a` and `a <= (a - b) + b`; `a <= Nat.max a b`; `Nat.min a b <= a`, and the same for `b`) and, when it has to, the two cases (`b <= a` and `(a - b) + b = a`, or `a < b` and `a - b = 0`; `max` and `min` are one side or the other). A product of two unknowns `x * y` is an atom, the same atom as `y * x` (by `Nat.mulComm`), but `(x * y) * z` and `x * (y * z)` are different. Anything else of type `Nat` is an **atom**, an unknown `omega` knows only to be at least 0: `List.length xs`, `r.to`, `x / 2`, `x % k`, a call. Two atoms are the same if they're the same term or the compiler can quickly show they compute to the same value; otherwise they're different, which can lose a proof but never makes a wrong one. So `get xs i h1` and `get xs i h2` are different atoms unless they compute to the same thing.
- **Facts** are every hypothesis in scope (parameters, pattern variables, `match e:` and `if h:` equations, `let`s, local theorems) and the listed terms whose type, after computing, is `a <= b`, `a < b`, `a = b` on `Nat`, `Not (a <= b)`, `Not (a < b)`, `Not (a = b)` (also written `a != b`; `omega` splits it into `a < b` or `b < a` when it has to), `And p q`, `(p && q) = True`, `Nat.leq a b = False`, `Nat.equal a b = True`/`False`, or `Decidable.toBool d = True`/`False` of one of these. The others are ignored. A quantified fact (`(id: Nat) -> covered rs id = True -> id < b`) is used by applying it: `omega [b id h]`. The emitted proof mentions only the facts it uses.
- **Whole numbers.** `omega` knows the unknowns are whole: from `2 * x <= 3` it gets `x <= 1`, `2 * x = 1` is a contradiction, and when the facts only have fractional solutions it tries a few levels of case splits (`x <= v` or `x >= v + 1`).
- **When it fails** it is `E-OMEGA`, listing the facts and atoms it used and saying which of these it found. None of them is a counterexample to the goal; each says why the search stopped:
  - *an integer model of the arithmetic abstraction*: whole values for the atoms that satisfy every fact and the goal's negation (with atoms like `x * y` or `List.length xs` treated as unknowns, so it may not be a real counterexample);
  - *a rational model of the relaxation*: only fractional values were found, and the case splits didn't rule them out;
  - *unsupported structure*: the goal isn't in the fragment above and the facts don't contradict each other, or (as a note) an atom such as `x * y` is outside it;
  - *budget exhausted*: the search made its limit of rows; nothing is claimed.
- **Not yet**: `if`, `/` and `%` by a number, `||` facts, and `Int`. A goal that is a `Bool` equation between comparisons (`(a <= b) == (c <= d)`) is stage 3.

Examples: `examples/accept/omega-basics.sw`, `examples/accept/omega-stage2.sw`, `examples/accept/omega-day05.sw`, `examples/reject/omega-*.sw`.

### `ring`

`ring` is a proof of an equation between `Nat`s or `Int`s whose two sides are equal as polynomials: equal once products are multiplied out and like terms collected. The compiler writes the proof and the kernel checks it:

```
theorem square (x: Nat): (x + 1) * (x + 1) = x * x + 2 * x + 1 := ring

theorem pairsStep (n: Nat) (p: Nat) (h: p + p + n = n * n): (n + p) + (n + p) + Succ n = Succ n * Succ n := ring [h]

theorem writeTimesMul (k: Nat) (b: Nat): (n: Nat) -> writeTimes k b n = b * multiplier k n
  | Zero   => ring
  | Succ n => rewrite writeTimesMul k b n, multiplierSucc k n in ring
```

| form | meaning |
|---|---|
| `ring` | proves the goal `a = b` |
| `ring [h1, h2]` | the same, using the equations `h1: l1 = r1`, `h2: l2 = r2` (any proofs): it proves `a + r1 + r2 = b + l1 + l2`, or the same with some `l`s and `r`s swapped, and cancels |
| `(ring: a = b)` | states what it proves, for `rewrite` or anywhere the expected type isn't known |

`ring` is a keyword and a term, like `omega`: a definition's body, a `calc` step's proof, an argument whose type is fixed (`Nat.leCongRight x y z ring h`), or `rewrite (ring: i + (p + q) = i + p + q)`. Where nothing says what it proves (`let p := ring`) it is `E-RING`. The proof it writes is `Std.Ring.proveNat env a b rfl` (or `proveInt`, or `proveNatWith`/`proveIntWith` with the hypotheses), where `a` and `b` are the sides as syntax over numbered atoms; `rfl` is the kernel computing both normal forms and finding them the same. `Std.Ring`'s soundness theorems are proved, with no axioms, so nothing new is trusted. Design and as built: [proof-automation.md](proposals/proof-automation.md) §6.2.

- **Arithmetic.** `+`, `*`, numbers and `Succ`; at `Int` also `-`, negation, `x.toInt` (so `(x + y).toInt` is `x.toInt + y.toInt`) and literals like `-3`. `Nat.pow e n` with a number `n` is multiplied out; with an unknown exponent it is an atom, but a call that computes to arithmetic is read as what it computes to, so `Nat.pow 10 (Succ k)` is `Nat.pow 10 k * 10`.
- **Atoms.** Anything else is an unknown: `List.length xs`, `f x`, `multiplier k n`, `x / 2`, `x % 10`, and `a - b` between `Nat`s (truncated subtraction isn't a ring operation; `omega` knows about it). Two atoms are the same if they're the same term or the compiler can quickly show they compute to the same value, as for `omega`.
- **Hypotheses** must be equations of the goal's type. With up to six, each is tried both ways round; with more, only as written. A hypothesis is added once: `ring [h]` doesn't use `2 * h`.
- **When it fails** it is `E-RING`, with both sides' normal forms (highest degree first, in the program's own names) and what the left side has more or less of; with hypotheses, the sides are the ones with the hypotheses added. A note names each atom that looks like it should have been arithmetic (`a - b`, `x / 2`, a power with an unknown exponent), and when the statement is false for small values the counterexample note shows them.

Examples: `examples/accept/ring-basics.sw`, `examples/reject/ring-*.sw`.

### `cases`

`cases` is a proof by cases on whatever the goal is stuck on. The compiler finds the value a definition in the goal is waiting for (`a` in `a ∨ b`, `Float.isNaN x` inside `Float.ieeeLe x y`, `s` in `{ s | id = t }.ref`), splits on it as a `match` would, and goes on in each case until every case is closed:

```
theorem orComm (a: Bool) (b: Bool): (a ∨ b) = (b ∨ a) := cases

theorem andLeft (a: Bool) (b: Bool) (h: (a ∧ b) = True): a = True := cases

theorem ieeeLtLe (x: Float) (y: Float) (h: Float.ieeeLt x y = True): Float.ieeeLe x y = True := cases

theorem parseSmallSome (s: Text) (t: Text) (v: Nat) (h: parseSmallOption s t = Some v): v <= 10 := cases
```

| form | meaning |
|---|---|
| `cases` | splits until each case is closed by computation, a contradiction, a hypothesis, or `omega` |
| `cases in t` | the same, trying the proof `t` in each case first (before splitting it further) |

`cases` and `cases in t` are a keyword and a term, like `omega`: a definition's body, a `calc` step's proof, or an argument whose type is fixed. Where nothing says what it proves (`let p := cases`) it is `E-CASES`. `cases` is a reserved word (the word `cases` stays free for `Text.split`). The proof it writes is the `match` you would have written, a case tree of `case` and `J`, and the kernel re-checks it; nothing new is trusted. Design and as built: [simp.md](proposals/simp.md) (stage 1).

- **What it splits on.** The goal is computed as far as it goes, and `cases` looks for what it is stuck on: a variable or call of a type with two or more constructors (`Bool`, `Option`, `Ordering`, a variant type), taking the innermost one, so that `Float.isNaN x` is split rather than the `Nat.equal` it calls. A record is taken apart into its fields only when nothing else is left. It doesn't take apart recursive types (`List`, `Nat`: that's induction, written as recursion), propositions or indexed families. A hypothesis that says a stuck value is a constructor (`h: f x = True`, `h: parseSmallOption s t = Some v`) is split on too, after the goal; other hypotheses aren't looked at.
- **Each case** gets the equation of its split, named `%case1`, `%case2`, … in messages, and the goal and every hypothesis that mentions the value are rewritten with the constructor, as a `match h: e with` does. Old copies of the rewritten hypotheses are hidden. A hypothesis `Some a = Some v` is turned into `a = v`, and `True = False` closes the case.
- **Closing a case**, in this order: both sides compute to the same value (`rfl`); a hypothesis equates two different constructors; a hypothesis has the goal's type; `t`, for `cases in t`; and, when there is nothing left to split, `omega`. A goal that is itself a comparison (`Nat.leq a b = True`) is given to `omega` before it is split into `True = True` and `False = True`.
- **Budget.** At most 64 cases. Past that it's `E-CASES-BUDGET`, naming the values it split on and the first case still open; prove a fact that decides several cases at once and give it as `cases in t`, or split by hand with `match`.
- **When it fails** it is `E-CASES` for the first case nothing closed: the case is named by its splits (`a = True, Nat.leq n 2 = False`), the notes show that case's hypotheses and goal, and what the goal was stuck on when it stopped (`xs`, a `List`). With `cases in t`, it's `t`'s own error, with a note naming the case. Further notes count the other cases that failed and the ones that were closed, and how.

Examples: `examples/accept/cases-bool.sw`, `examples/accept/cases-data.sw`, `examples/reject/cases-*.sw`.

### Numbers

A non-negative numeric literal is a `Nat` or an `Int`, depending on what's expected (`Nat` if nothing says; a `Fin n` too, where one is expected, [below](#fin-literals), and a `SafeNat` or `SafeInt`, checked to be within 2^53 - 1, [Numbers in an `export`](#numbers-in-an-export)); a negative literal such as `-5` is always an `Int`, and `-0` is `0`. An arithmetic expression or comparison has one number type for all its operands, chosen by the first of these that applies: the expected type; a decimal or exponent literal (`Float`, below); an operand with no literal in it (when there's a prefix minus, only an `Int` or a `Float` one); a prefix minus (which makes it `Int`); any other operand; else `Nat` (D732). So `3 - 5 = -2` is on `Int`, and `x + 1` follows `x`. A `let` binding keeps its own type: `let m := 3 - 5` is a `Nat`, and `m + i` with `i: Int` is an error.

There is no implicit conversion between `Nat` and `Int`: use `n.toInt`, `Int.toNat` (negatives become 0) or `Int.toNatChecked`.

`+`, `*`, `<` and `<=` work on any type with the instance they need ([Interfaces](#interfaces); docs/proposals/interfaces.md §5.13): `x + y` is `Add.add x y`, `x * y` is `Mul.mul x y`, and `x < y` and `x <= y` are `Ord`'s `lessThan` and `lessEq`, with the dictionary found as for any `auto` argument, so a dictionary in scope is used (`[auto ord: Ord Nat]` makes `<` on `Nat` its order). On `Nat` and `Int` with no other dictionary in scope that's the library's instances, whose fields are the built-in operations, and the term is the operation itself (`Nat.add x y`), as it always was. `if x < y` decides with the decider in the same dictionary (`Ord.decLessThan`), also through a definition that unfolds to it. The operand type is chosen as above; an expression with `-`, `/`, `%` or a prefix minus is still on `Nat`, `Int` or `Float` only, and so are literals: generic code writes `Add.zero` and `Mul.one` (`E-TYPE-MISMATCH` otherwise, with a note). Missing an instance is `E-INSTANCE-NONE` (`+` on `Bool`, `<` on functions).

A literal argument of a generic function takes its type from the expected result when that is known: with `i: Int`, `chooseFirst 5 i` checked against `Int` works, because the result type is used before the arguments are checked ([syntax-conveniences.md](proposals/syntax-conveniences.md) section 7). The same holds for a constructor of a generic type whose arguments have number literals (`Point 1 "p" 10` of `Mark i n`): the expected type, through an alias too, gives the constructor's parameters before its arguments are checked. Where nothing is expected but a sibling operand has the type (`[Point 1 "p" 10, m]`, `pair (Point 1 "p" 10) m`, `if b then Point 1 "p" 10 else m`, `Point 1 "p" 10 == m`, with `m: Mark Int Nat`), such a constructor is checked after the others, so its literals aren't defaulted to `Nat` first; the terms and the order things run in don't change (`examples/accept/generic-constructor-literals.sw`). Known limit: where nothing says what the result is, such as `let v = chooseFirst 5 i`, the `5` is still checked as a `Nat` first and fails; write `chooseFirst (5: Int) i`. Design: [integers.md](proposals/integers.md); examples: `examples/accept/int-literals.sw`, `examples/accept/int-choose-first.sw`, `examples/accept/expected-types.sw`.

#### `Fin` literals

A numeral checked against `Fin n` (`import Std (Fin)`), where n computes to a number, is the position it names, with its bound checked by computing `k < n` (D1073, [fin-literals.md](proposals/fin-literals.md); `examples/accept/fin-literals.sw`):

```
import Std (Fin, List)

def digits: List (Fin 10) := [2, 7, 5, 7, 3]
def last: Fin (2 * 5) := 9                     -- n need only compute to a number
theorem two: (2: Fin 5) = FSucc (FSucc FZero) := rfl
test "beside a Fin" := digits.all (d => d < 9)
```

The term is `Fin.ofNatLt n k rfl`, which reduces to `FSucc`s around `FZero`. A numeral at or above n (`def x: Fin 5 := 7`: "7 isn't below 5, so it can't be a `Fin 5`") or a negative one is `E-FIN-LITERAL`, and so is one whose n isn't a known number (`Fin n` for a variable n: build it with `Fin.ofNatLt`, giving the proof; `Fin.toNat 3`, where nothing says what n is: annotate, `(3: Fin 10)`). Only an expected `Fin` makes a numeral one: a literal with nothing expected is still a `Nat`, and arithmetic is never on `Fin` (it has no `Add`; use [`Mod n`](#interfaces) for numbers that wrap). In a comparison or `==` beside a `Fin`, the numeral takes that type, as any operand does. Number patterns on a `Fin` are under [Declarations](#declarations).

#### `Float`

`Float` (`import Std (Float)`, `std/Float/Float.sw`) is a 64-bit IEEE 754 double, the JS `number`: a Rust `f64` and a JS `number` at run time, and in the logic the record of its 64 bits, `{ bits: Nat, valid: Float.isValid bits = True }`, with one NaN. Design: [float.md](proposals/float.md) (stages 1a and 1b are built; `sqrt`, `min`/`max` and `Float.ofText` are later).

```
import Std (Float)

def shift (t: Float) (by: Float): Float := t + by    -- IEEE addition, rounded
theorem tenths: 0.1 + 0.2 = 0.30000000000000004 := rfl
test "zeros" := (0.0 == -0.0) = False                  -- `==` is the same double
test "ieee" := Float.ieeeEq 0.0 (-0.0) = True           -- JS's `===`
test "order" := -0.0 < 0.0                             -- `<` is the total order
test "js <" := Float.ieeeLt (-0.0) 0.0 = False          -- JS's `<`
test "round" := Float.round (-2.5) = -2.0               -- JS's `Math.round`
```

- **Literals.** `1.5`, `80281.87`, `1e3`, `1.5e-7`, `2.0E21`: a digit on both sides of `.`, an exponent `e`/`E` with an optional sign. The value is the decimal correctly rounded to the nearest double; `0.10`, `0.1` and `1e-1` are the same double. A literal that would be an infinity (`1e400`) or isn't zero but rounds to zero (`1e-400`) is `E-FLOAT-LITERAL`. A whole literal at `Float` is exact or refused: `9007199254740993` isn't a double (`E-FLOAT-LITERAL`, naming the two nearest), so write one of those or `9007199254740993.0`. A number right after a `.` is never a decimal literal, so `xs.0.1` is `xs` `.` `0` `.` `1` (and an error: there are no numeric projections).
- **The operand type.** A decimal literal makes the expression a `Float`, before a prefix minus would make it an `Int`: `-1 + 0.5` is `-0.5`. A `Float` operand does too: with `t: Float`, `t + -1` and `-t` are `Float`s. A whole literal in a `Float` expression is a `Float`, and `-k` is `Float.neg k`, so `-0` at `Float` is `-0.0`. `Float` doesn't mix with `Nat` or `Int` (`E-TYPE-MISMATCH`).
- **Arithmetic.** `+ - * / %` are the IEEE operations in the order written, so `(a + b) + c` and `a + (b + c)` can differ; they aren't `Add`'s and `Mul`'s (doubles break their laws). `/` and `%` need no proof that the divisor isn't zero: `1.0 / 0.0` is `Float.infinity`, `0.0 / 0.0` is `Float.nan`, and `%` is JS's (the remainder of truncating division, with the dividend's sign: `-5.5 % 2.0` is `-1.5`). The checker computes them on known doubles, so `rfl` proves `0.1 + 0.2 = 0.30000000000000004`, and a goal shows a double as its literal.
- **Rounding.** `Float.floor`, `Float.ceil`, `Float.trunc` and `Float.round` are JS's `Math.*`. `round` is `Math.round` exactly: a half goes towards +infinity (`round (-2.5)` is `-2.0`, `round 2.5` is `3.0`), a zero result keeps the sign (`round (-0.4)` is `-0.0`), and `round 0.49999999999999994` is `0.0`. `Float.abs`, `Float.isNaN` and `Float.isFinite` (neither infinite nor the NaN) are as JS's.
- **Conversions.** `Float.ofInt i` and `Float.ofNat n` are the nearest double, ties to even, or an infinity beyond the largest (JS's `Number(n)` of a `bigint`). `Float.toInt x` is an `Option Int`: `Some` of the integer the double is when it's whole, of any size (`Float.toInt 1e100` is the integer 1e100's bits stand for, not 10^100), else `None` (a fraction, the infinities, the NaN); both zeros are `Some 0`. `Float.toSafeInt` and `Float.toSafeNat` check the safe range too; `SafeInt.toFloat` and `SafeNat.toFloat` are exact. There's no implicit conversion: `t + i` with `i: Int` is `E-TYPE-MISMATCH`, with a note naming `Float.ofInt`.
- **Equality.** `==` and `=` are "the same double", JS's `Object.is`: `0.0` and `-0.0` differ, and `Float.nan == Float.nan`. JS's `===` is `Float.ieeeEq`, where the NaN isn't equal to itself and `0.0` equals `-0.0`; port `a === b` as `Float.ieeeEq a b`.
- **Order.** `<`, `<=`, `List.sort`, `Map Float`, `Set Float` and derived orders use `Ord Float`, IEEE 754's total order: `-infinity < … < -0.0 < 0.0 < … < infinity < Float.nan`, with all of `Ord`'s laws (`Float.compare` is its comparison). JS's `<` and `<=` are `Float.ieeeLt` and `Float.ieeeLe` (`Bool`s, false with a NaN, the zeros equal). Port `a < b` as `Float.ieeeLt a b`, `a > b` as `Float.ieeeLt b a`, `a >= b` as `Float.ieeeLe b a` (not `!(Float.ieeeLt a b)`, which differs on a NaN); when `a` and `b` are calls rather than values, bind them in order first (`let l := left()`, `let r := right()`, then `Float.ieeeLt r l`), as JS evaluates the left operand first. A sort by the total order can put equal JS keys in another order (`-0` before `0`); a port keeps the original comparator with `List.sortBy`, which is stable.
- **Printing.** `${t}` and `Float.toText` are JS's `String(t)`: `0.30000000000000004`, `1e+21`, `1e-7`, `NaN`, `-Infinity`, and `0` for both zeros. Only the runtimes compute it (Node's `String`, and the same digits in the Rust runtime): the checker doesn't, so a `test` that inspects the text of a double, or anything computed from it, doesn't reduce; test printing with `stitchwort run`. `Show Float`'s `toSource` (what lists and records print their elements with) reads back as the same double: `1.5`, `3.0`, `-0.0`, `Float.nan`, `Float.infinity`, `-Float.infinity` (the last four computed by the checker too).

Examples: `examples/accept/float-literals.sw`, `examples/accept/float-operations.sw`, `examples/reject/float-*.sw`, `examples/extract/floats.sw`, `examples/extract/float-times.sw`.
