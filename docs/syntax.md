# Surface syntax (implemented subset)

**Status:** describes `crates/syntax` as of 15 October 2026. DESIGN.md §4 shows the intended language. Not yet implemented: records, `Partial`, `IO` and a `case` expression.

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

Patterns are variables, `_`, numbers, constructors applied to patterns (nested to any depth, as in `half (Succ (Succ n))`), or `()`. A number pattern `n` means `n` nested `Succ`s around `Zero`, so it's limited to 256. Equations are tried from top to bottom. `()` with a right-hand side matches the unit value; without one, it says the argument's type has no values, and the equation needs no right-hand side:

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

Effectful code is written in direct style. Arguments are evaluated left to right, and the lines of a block in order. A pure function can use a handler inside; what it handles doesn't appear in its type. How this is translated into ordinary data is described in `docs/core.md`, under "Abilities".

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
| `a + b`, `a - b` | Addition, and subtraction stopping at zero. Left-associative |
| `a * b`, `a / b`, `a % b` | Bind tighter than `+`. `/` and `%` need a proof that `b != 0` |
| `f a b` | Application |
| `f [x := e]` | Supplying the implicit parameter `x` by name |
| `_` | A hole the compiler fills in |
| `x`, `Nat`, `Succ` | Names. Constructors and data types start with an uppercase letter |
| `0`, `42` | `Nat` literals |
| `Type`, `Type 1`, `Prop` | Universes |
| `(e : T)` | Type annotation |
| `[a, b, c]` | `List` literal. In an expression, `[x := e]` supplies an implicit argument and every other `[…]` is a list |
| `rfl` | Proof of `a = a` |
| `J (\y p -> P) base proof` | Transport along an equality |

A partially applied constructor is a function: `Succ` on its own means `\n -> Succ n`.
