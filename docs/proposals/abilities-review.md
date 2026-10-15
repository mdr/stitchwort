# Stitchwort: abilities and handlers — design for review

**Status:** draft for review, 15 October 2026. Nothing here is implemented yet. This document stands alone; section references like "DESIGN.md §8" point to the full design document for anyone who has it.

## Background

Stitchwort is a small, strict, pure, dependently typed language, built for fun and to explore ideas. It's implemented in Rust, with a small trusted kernel that re-checks everything the elaborator produces. It extracts to JavaScript, and a playground runs the compiler as WebAssembly.

The goal that matters most for this document: **totality must be a real guarantee.** A function whose type doesn't mention `Partial` must terminate, including everything it calls. Lean's `partial def` is the motivating counterexample: it's invisible in types, so an ordinary `def` can call one and hang. In Stitchwort, partiality is an *ability* (an algebraic effect, in Unison's terminology). It appears in function types and spreads to callers.

What exists today:

- A dependently typed core with numbered universes and an impredicative `Prop` (with subsingleton elimination).
- Data types with parameters (no indices), strict positivity checking, and structural termination checking.
- Case trees, compiled from pattern-matching equations.
- Built-in equality with `J`, and implicit arguments and proof search (`auto`).
- JavaScript extraction, and native arbitrary-precision numbers.

**Abilities aren't implemented at all yet.** Until they are, every definition must pass the termination checker.

### The abilities design so far

Abilities follow Unison and Frank. Code is written in direct style, and function arrows carry ability rows: `a -> {State s, IO} b`, with row variables `{State s | e}`. A plain arrow `a -> b` means pure and total. Handlers are **deep**.

```
ability State s where
  get : () -> {State s} s
  put : s -> {State s} ()

runState : s -> (() -> {State s | e} a) -> {e} (a, s)
runState init prog =
  let run =
    handle prog () with
      | return x     -> \s -> (x, s)
      | get ()  => k -> \s -> k s s
      | put s'  => k -> \_ -> k () s'
  run init
```

**Do handlers terminate?** An earlier draft trusted any handler that resumes `k` at most once. That rule is wrong, and these two counterexamples are in the must-reject suite:

```
-- The handler restarts the computation instead of resuming it.
ability Ping where
  ping : () -> {Ping} ()

bad : (() -> {Ping} a) -> a
bad prog =
  handle prog () with
    | return x     -> x
    | ping () => k -> bad prog     -- never resumes k; loops

-- Landin's knot: a stored function that reads itself back.
ability Cell where
  read  : () -> {Cell} (() -> {Cell} ())
  write : (() -> {Cell} ()) -> {Cell} ()

knot : () -> {Cell} ()
knot () =
  let f = \() -> (read ()) ()
  write f
  f ()
```

The current design (DESIGN.md §8) calls a handler **admissible** if:

1. it's deep, and its clauses don't recurse (the only way to continue is `k`);
2. its ability's operations are data-only: no functions anywhere in their argument or result types, checked transitively after type parameters are filled in. For `State s` this means an `IsData s` constraint;
3. its clauses are total, apart from the outer row;
4. it doesn't handle `Partial`, which only the runtime may handle.

The current design then *conjectures* that admissible handlers terminate, and treats that conjecture as a tracked assumption shown on every result that relies on it.

The design also says the handler semantics must be written down before anything is built, answering three questions:

- Does a clause run inside or outside its own handler?
- How are unhandled operations forwarded?
- What is the exact type of `k`?

This document does that, and proposes an implementation strategy that removes the conjecture.

## Part 1: semantics

### The three questions

1. **Inside or outside?** *Outside.* If a `get` clause itself calls `get ()`, that call goes to the next `State` handler out. (Running inside would let a clause loop back into its own handler.)
2. **Forwarding.** An operation goes to the nearest enclosing handler that handles it. Inner handlers that don't handle it are transparent. When the outer handler resumes, the computation continues under those inner handlers again.
3. **The type of `k`.** For a handler whose result type is `r` and whose remaining row is `e`, handling an operation that returns `b`:

   ```
   k : b -> {e} r
   ```

   Because the handler is deep, `k` re-installs it, so its result is `r`, and calling it may perform only `e`.

### Rules

Evaluation is call-by-value, left to right. `C[…]` is an evaluation context with no handler for `op` between the hole and `H`.

```
handle v with H        ⟶  e_return[v/x]

handle C[op v] with H  ⟶  e_op[v/x, (\y -> handle C[y] with H)/k]
                          if H handles op
```

- The clause replaces the whole `handle` expression, so it runs **outside** `H` (question 1).
- `k` wraps the continuation in `handle … with H` again, which is what makes the handler **deep** (question 3).
- If `H` doesn't handle `op`, the step happens at an outer handler, whose `C` contains `handle … with H` (question 2).

Typing: if `prog : () -> {A | e} a` and `H` handles `A` with result type `r`, then `handle prog () with H : r` with abilities `e`. Each operation clause is checked with `k : b -> {e} r`.

### Examples

```
-- Resuming more than once: every outcome.
ability Choose where
  choose : () -> {Choose} Bool

allResults : (() -> {Choose | e} a) -> {e} List a
allResults prog =
  handle prog () with
    | return x        -> [x]
    | choose () => k  -> append (k True) (k False)

-- Not resuming: stop early.
ability Abort where
  abort : () -> {Abort} a

toOptional : (() -> {Abort | e} a) -> {e} Optional a
toOptional prog =
  handle prog () with
    | return x       -> Some x
    | abort () => k  -> None

-- A clause using the ability it handles: its `get ()` goes to the outer State.
inner : () -> {State Nat | e} Nat
inner () =
  handle (\() -> get () + 1) () with
    | return x      -> x
    | get () => k   -> k (get () * 10)
```

## Part 2: implementation — effects as data

### Two options

**A. Effects in the kernel.**
- **What it involves:** the core gets ability rows on function types, an effect judgment `Γ ⊢ t : A ! ε`, and terms for `handle` and operations. The evaluator implements the rules with continuations.
- **For it:** it's direct and fast.
- **Against it:** it grows the trusted kernel considerably, and handler termination stays a conjecture.

**B. Effects as data (proposed).** The elaborator translates effectful code into ordinary values of a tree data type, before the kernel sees it. The kernel itself doesn't change, apart from one small extension to the termination checker.

```
-- A computation returning `a`, performing operations from a signature:
-- `op` is the type of operation calls, and `res o` is what call `o` returns.
type Comp (op : Type) (res : op -> Type) (a : Type) : Type =
  | Done (value : a)
  | Call (o : op) (rest : res o -> Comp op res a)
```

- **Effectful functions:** `a -> {e} b` becomes `a -> Comp (ops of e) (results of e) b`.
- **Direct-style code** is translated into nested `Call`s. `let n = get (); put (n + 1); n` becomes "call `get`; with its result `n`, call `put (n + 1)`; then `Done n`". This is the main piece of elaborator work.
- **Rows** are sums of signatures, kept in a canonical order. A row variable `e` becomes an implicit signature parameter.
- **A deep handler is a fold**, an ordinary recursive definition:
  - `Done x` runs the `return` clause.
  - `Call o rest` for a handled operation runs the clause with `k = \y -> handler (rest y)`.
  - For any other operation, it rebuilds `Call o (\y -> handler (rest y))`.

  These are exactly the rules in Part 1.

### Why B removes the conjecture

Two existing kernel checks prove that an accepted handler terminates:

- **Positivity.** `Comp` is strictly positive, because `rest`'s domain `res o` doesn't mention `Comp`. So every `Comp` value is a well-founded tree.
- **Structural recursion.** The handler recurses on `rest y`, a structural subterm of `Call o rest`. Coq and Lean accept this rule for function-typed fields. Our termination checker would need that one extension, restricted as in Coq to fields whose result is the type being matched.

The two counterexamples then fail without any special rule:

| Counterexample | What rejects it |
|---|---|
| `Ping` restarts the program from a clause | The recursive call `bad prog` isn't on a smaller tree: termination check |
| `Cell` stores an effectful function | Its signature's result type would have to mention `Comp` of itself: refused by the termination check (a self-referential type function) or by positivity (a self-referential operation type) |

**What I've actually checked**, against today's kernel, with hand-written code:

- The kernel accepts `Comp` exactly as written above.
- A `State` handler written as a fold over `Comp` is refused *only* with a termination error on `runState s (rest s)`. That's the one extension above, which isn't implemented yet.
- Both encodings of `Cell` are refused: a self-referential result-type function fails the termination check, and an operation type whose field mentions `Comp` of itself fails positivity.

**What's argued but not checked:**

- **That rule 2 (data-only operations) and `IsData` become unnecessary.** State holding *pure* functions (`State (Nat -> Nat)`) can't loop. State holding *effectful* functions can't be written down, for the same reason `Cell` can't. I'd want must-reject tests before dropping `IsData`.
- **That the termination-checker extension is sound** alongside this kernel's other features (dependent types, impredicative `Prop`, case trees that refine later hypotheses). It's standard, but I haven't proved it for this kernel.

### Effects and dependent types

Option B also gives a simple answer to "how do effects interact with dependent types?".
- In `(n : Nat) -> {IO} Vec Nat n`, the result is just `Comp … (Vec Nat n)`.
- An effectful result used later in a type is an ordinary variable bound by the continuation's lambda.
- The type checker never runs an operation: operations are `Call` nodes, and comparing types only compares data.

### Costs of B

- Effectful code runs by building and folding trees, which is slower in the evaluator than option A. That's acceptable for tests and the playground at this scale.
- Error messages must talk about abilities, not `Comp`, so the elaborator has to translate them back.
- Extracted JS builds and folds trees too. That's fine at first, since exported functions must be pure. Compiling handlers to generators can come later.

## Part 3: `Partial`

Under option B, `Partial` becomes a tree that may be **infinite**, built one layer at a time. Its signature has one operation, `later`, and a partial definition may recurse only inside the `rest` of a `later` call (*guarded* recursion, as in Capretta's delay monad):

```
spin : Nat -> {Partial} Nat
spin n = spin n
-- translates to, roughly:
spin n = Call later (\_ -> spin n)
```

The rules:

- **Guardedness instead of structural recursion.** The kernel checks partial definitions for guardedness rather than structural recursion.
- **Never unfolded during type checking.** Comparing types looks inside lambdas, so without this rule, comparing two partial values could unfold them forever. Only the runtime unfolds them.
- **Visible in types.** Calling a partial function produces `later` nodes, and only a function whose type includes `{Partial}` may produce them. So partiality spreads to callers, which is the whole point.
- **Handled only by the runtime**, which runs the tree for as long as it takes. User handlers may not handle `later`.
- **Fuel for free.** `withFuel : Nat -> (() -> {Partial | e} a) -> {e} Optional a` can be written as an ordinary prelude function that counts `later` steps. It's total because it recurses on the fuel. This had been postponed as needing special kernel support.

This part is the least developed. The guardedness check and the "don't unfold" rule are new kernel features, though small ones. I haven't tried any of it.

## Part 4: `IO`

`IO` is a signature like any other, but only the runtime handles it, at `main`. The type checker never needs to evaluate `Call` nodes, so it never performs IO.

## Build order

1. `Comp` in the prelude, and the termination-checker extension. Hand-written handlers over hand-written trees.
2. In the elaborator:
   - `ability` declarations, and rows with row variables.
   - The direct-style translation, including the new syntax it needs: `let` and sequencing.
   - `handle … with`.
3. `runState`, `toOptional` and `allResults`, plus the must-reject suite: `Ping`, `Cell`, function-valued state, and a user handler for `Partial`.
4. `Partial`: guardedness, no unfolding while type checking, the runtime loop, `withFuel`.
5. `IO` and `main`, in the command-line runner.

## Questions for the reviewer

1. **Is option B sound as described?** In particular:
   - Does "the kernel accepts the translated handler" really imply that it terminates, given strict positivity and structural recursion through function-typed fields?
   - Is there an encoding of `Cell` or Landin's knot that slips past both checks?
2. **The termination-checker extension.** Accepting `rest y` as smaller than `Call o rest`, restricted to fields whose result type is the matched type: is that restriction enough in a kernel with impredicative `Prop`, dependent pattern matching (branches refine later hypotheses) and no indexed families?
3. **Dropping `IsData`.** Is the argument above right, that once effectful functions can't appear in signatures, pure functions in state are harmless?
4. **`Partial` as guarded recursion.** Is "never unfold partial definitions during type checking" plus guardedness enough to keep type checking terminating and the logic consistent? Is there a known pitfall with mixing a lazily unfolded `Comp` and strict evaluation?
5. **Semantics choices.** Are "clauses run outside their handler" and deep handlers the right defaults, or is there a reason to prefer shallow handlers here?
6. **Anything missing** that the operational rules should specify before implementation starts?
