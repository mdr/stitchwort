# Surface syntax (implemented subset)

**Status:** describes `crates/syntax` as of 15 October 2026. DESIGN.md §4 shows the intended language. Not yet implemented: records, abilities, tests, `let`, a `case` expression, and nested patterns.

## Layout

Interim rule, until the full layout specification (DESIGN.md §14):

- A declaration starts at column 0.
- Every following line that's indented continues it.
- A line containing only `export` belongs to the declaration after it.
- Tabs aren't allowed. `--` starts a comment that runs to the end of the line.

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

-- Exported to JavaScript by `stitchwort build --js`
export
total : List Nat -> Nat
total Nil         = 0
total (Cons x xs) = x + total xs
```

Definitions may be named in either case: `length`, or `Not` for a function returning a type.

Patterns are variables, `_`, `0`, a constructor applied to variables and `_` (one level deep), or `()`. `()` says the argument's type has no values, and an equation using it has no right-hand side:

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
| `a = b`, `a != b` | Equality and inequality (propositions). Not associative |
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
