# Surface syntax (implemented subset)

**Status:** describes `crates/syntax` as of 14 October 2026. DESIGN.md §4 shows the intended language. Not yet implemented: `[auto …]`, records, abilities, tests, `let`, `if`, and a `case` expression.

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

Patterns are variables, `_`, `0`, or a constructor applied to variables and `_`, one level deep.

## Expressions

Loosest-binding first:

| Syntax | Meaning |
|---|---|
| `\x y -> e` | Function |
| `(x y : A) -> B` | Dependent function type |
| `[x y : A] -> B` | Function type with implicit parameters, filled in by the compiler |
| `A -> B` | Function type |
| `a = b` | Equality (a proposition) |
| `a + b` | `add a b` (on `Nat`) |
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
