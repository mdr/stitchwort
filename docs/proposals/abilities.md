# Stitchwort: abilities and handlers

**Status:** draft 2, 15 October 2026. The foundation is implemented (see [Status](#status)): `Comp`, its fold and `bind`, and the termination rule they need. Hand-written handlers for `State`, `Abort` and `Choose` pass the semantic tests below. There's no `ability` or `handle` syntax yet. `Partial` has moved to its own proposal, [`partial.md`](partial.md).

## Changes since draft 1

Draft 1 was reviewed. The review supported option B (effects as data), found a soundness problem in the `Partial` design, and asked for several parts of the specification to be tightened. In response:

- **`Partial` is split out.** Draft 1 let a `Partial` definition build an *infinite* `Comp` tree by guarded recursion. That is unsound: with an infinite tree, an ordinary fold over `Comp` proves `Void` (`drain (forever ())`). Infinite computations need a separate representation, and that is now an open proposal of its own. The counterexample is in the must-reject suite.
- **The comparison with option A is corrected.** Effects in the kernel don't leave handler termination unprovable; they need their own metatheory. Option B's advantage is that it reuses the kernel's existing argument.
- **Termination now rests on two separate things:** the kernel checks that the *translated* program terminates. Whether the translation matches the semantics in Part 1 is a separate obligation for the elaborator, tested by comparing behaviour.
- **The termination rule is specified by provenance** (where the function came from), not by its type: see [The termination rule](#the-termination-rule).
- **The `IsData` claim is corrected.** Draft 1 said state holding effectful functions "can't be written down". That's wrong, and it isn't the problem. State may hold effectful functions whose effects don't refer back to the state's own signature. The must-reject entry "function-valued state" is replaced by specific forms of Landin's knot.
- **New specification items:** rows, handler coverage, the intermediate types in `runState`, `bind`, dependent results, the empty row, and polymorphic operations.
- **Implemented:** the termination rule, `Comp`, `foldComp`, `bind`, and the semantic and must-reject tests. Building them found and fixed a bug in nested pattern matching.

## Background

Stitchwort is a small, strict, pure, dependently typed language, built for fun and to explore ideas. It's implemented in Rust, with a small trusted kernel that re-checks everything the elaborator produces. It extracts to JavaScript, and a playground runs the compiler as WebAssembly.

The goal that matters most here: **totality must be a real guarantee.** A function whose type doesn't mention `Partial` must terminate, including everything it calls. (Lean's `partial def` is the motivating counterexample: it's invisible in types.) Partiality is meant to be an *ability* (an algebraic effect, in Unison's terminology) that appears in function types and spreads to callers.

The language today has:
- A dependently typed core, with numbered universes and an impredicative `Prop` (with subsingleton elimination).
- Data types with parameters (no indices), strict positivity, and structural termination checking.
- Case trees compiled from nested patterns, where branches refine the types of other variables.
- Built-in equality with `J`.
- Implicit arguments and proof search (`auto`).
- JavaScript extraction.

Abilities follow Unison and Frank. Code is written in direct style, and function arrows carry ability rows (`a -> {State s} b`, with row variables `{State s | e}`). A plain arrow `a -> b` means pure and total. Handlers are **deep**.

Two counterexamples show that "handlers that resume at most once" doesn't guarantee termination:

```
-- A handler that restarts the computation instead of resuming it.
ability Ping where
  ping : () -> {Ping} ()

bad : (() -> {Ping} a) -> a
bad prog =
  handle prog () with
    | return x     -> x
    | ping () => k -> bad prog

-- Landin's knot: a stored function that reads itself back.
ability Cell where
  read  : () -> {Cell} (() -> {Cell} ())
  write : (() -> {Cell} ()) -> {Cell} ()
```

## Part 1: semantics

### Rules

Evaluation is call-by-value, left to right. `C[…]` is an evaluation context with no handler for `op` between the hole and `H`.

```
handle v with H        ⟶  e_return[v/x]

handle C[op v] with H  ⟶  e_op[v/x, (\y -> handle C[y] with H)/k]
                          if H handles op
```

- **A clause runs outside its own handler.** It replaces the whole `handle` expression, so if a `get` clause calls `get ()`, that call goes to the next `State` handler out.
- **Deep.** `k` wraps the continuation in `handle … with H` again.
- **Forwarding.** If `H` doesn't handle `op`, the step happens at an outer handler, whose `C` contains `handle … with H`. Resuming re-enters `H`, and any other handlers in between.

Shallow handlers aren't planned.

### Typing

- **`k`.** For a handler whose result type is `r` and whose output row is `e'`, handling an operation that returns `b`:

  ```
  k : b -> {e'} r
  ```

- **The output row.** `handle` removes the handled ability from the *handled computation's* row. The output row `e'` is that remainder **plus whatever the clauses themselves perform**, which may include the handled ability again: a `State` clause may call the outer `State`.
- **Coverage.** For now, a handler that removes an ability must have a `return` clause and a clause for every operation of that ability.
- **`runState` has two effect positions.** In the function-returning presentation, the handler produces a function waiting for the state:

  ```
  run : s -> {e} (a, s)              -- applying it may perform e
  k   : s -> {e} (s -> {e} (a, s))   -- resuming may perform e, and so may the function it returns
  ```

  Both positions are needed. The elaborator must keep track of both rather than lose one.

### Semantic tests

Kernel acceptance can't show that a program does the right thing, so these tests pin down behaviour. They're implemented over hand-written trees in `examples/accept/handlers.sw`, and all pass.

The test program:

```
p () =
  let b = choose ()
  if b then put 1 else ()
  get ()
```

| Test | Expected | Shows |
|---|---|---|
| `allResults (\() -> runState 0 p)` | `[(1, 1), (0, 0)]` | State inside choice: each branch has its own state. Forwarding, and resuming twice |
| `runState 0 (\() -> allResults p)` | `([1, 1], 1)` | Choice inside state: one state threads through both branches |
| A `State` clause whose own `get` scales the outer state's value | `51` for `get () + 1` with outer state `5` | A clause runs outside its handler; the output row keeps `State` |
| `toMaybe (safeDiv 7 0)` | `Nothing` | Not resuming |
| `allResults` written with `foldComp` | the same as the handler, `[7, 6, …, 0]` for three choices | The generic fold |
| State holding a function that uses `Choose` | `[15, 5]` | Effectful functions in state are fine when their effects are independent |

When the direct-style translation exists, these become source programs. Their results, and the order in which operations happen, will be compared with the rules above.

## Part 2: implementation — effects as data

### The options

**A. Effects in the kernel.** The core gets ability rows, an effect judgment `Γ ⊢ t : A ! ε`, and terms for `handle` and operations, run with continuations. It's direct and fast. Handler termination then needs its own metatheoretic argument, separate from the kernel's existing one for inductive types, and the trusted kernel grows considerably.

**B. Effects as data (chosen).** The elaborator translates effectful code into ordinary values of an inductive type, so the kernel's existing account of inductive types covers termination. The kernel adds one rule to the termination checker, and nothing else.

### The representation

These are in the prelude:

```
type Comp (op : Type) (res : op -> Type) (a : Type) : Type =
  | Done (value : a)
  | Call (o : op) (rest : res o -> Comp op res a)

foldComp : (a -> r) -> ((o : op) -> (res o -> r) -> r) -> Comp op res a -> r
foldComp done call (Done x)      = done x
foldComp done call (Call o rest) = call o (\y -> foldComp done call (rest y))

bind : Comp op res a -> (a -> Comp op res b) -> Comp op res b
bind (Done x)      next = next x
bind (Call o rest) next = Call o (\y -> bind (rest y) next)
```

- **`foldComp` is the eliminator handlers are justified by.** `call` receives the operation together with the results of folding every way it could continue, packaged as a function. It may use that function any number of times.
- **A deep handler is a fold.** In practice it's written as a structurally recursive function, which is checked by the same rule as `foldComp`.

### The termination rule

A `Comp` is a well-founded tree: it's strictly positive, because `rest`'s domain doesn't mention `Comp`. The termination checker accepts a recursive call on:

1. a variable bound as a field of a constructor matched from the parameter (as before);
2. a constructor applied to exactly the fields of such a match, which is the matched value itself (`Succ n` where `m` was matched as `Succ n`);
3. **a recursive function field applied to arguments** (new): `rest y`, where `rest` is the *variable bound by the match* for a field whose declared type is a function returning the data type being matched.

Rule 3 goes by provenance. It doesn't accept any application whose result type happens to be the matched type. Only the field variable itself counts: not a lambda wrapping the original tree, not another definition applied to the field, not an alias. Field types are read from the data declaration, as in Rocq. Case branches substitute constructor values into *types*, but never into terms, so the provenance of a variable doesn't change inside a branch.

This corresponds to `Comp`'s dependent eliminator, whose `Call` branch has the induction hypothesis `ih : (y : res o) -> P (rest y)`. Generating that recursor and compiling folds to it would be an alternative implementation. For now the fixpoint checker stays, with the rule above.

**Not yet verified:** a soundness argument for rule 3 alongside this kernel's other features (impredicative `Prop`, and branches that refine other variables' types). The rule is standard. The kernel's must-reject tests exercise it, but they aren't a proof.

### What the kernel rejects

These are must-reject tests in `examples/soundness/`:

| Attempt | Rejected by |
|---|---|
| `forever u = Call Later (\v -> forever u)`, which with `drain` would prove `Void` | Termination: `u` isn't smaller |
| A fake child: `loop ((\b -> Call o rest) True)` | Termination: the head isn't the field variable |
| `Ping`: `bad (Call o rest) = bad (Call o rest)` | Termination: rebuilding the parameter isn't smaller |
| `Cell`, with an effectful function in an operation's *result*: `CellRes Read = Unit -> Comp CellOp CellRes Unit` | Termination: a self-referential type function |
| `Cell`, with an effectful function in an operation's *argument* | Positivity |

**Still to add:** indirect versions of `Cell`, through type aliases, records (once they exist) and mutually dependent abilities (once rows exist).

### `IsData` is replaced by the kernel's own checks

| Case | Treatment |
|---|---|
| State holding pure, total functions (`State (Nat -> Nat)`) | Accepted |
| State holding functions whose effects use an independent signature (`State (() -> {Choose} Bool)`) | Accepted. Tested: storing and running a `Choose` function |
| Effects creating the recursive dependency of Landin's knot | Rejected, because the translated declarations fail positivity or termination |

There's no separate data-only restriction. A signature is accepted when its translation passes the kernel.

### Elaboration decisions still to specify

These come before the direct-style translation:

- **Rows.** Duplicate labels (`{State Nat, State Bool}`) are refused for now. A row is a sum of signatures, in a canonical order. The elaborator must generate explicit, checkable mappings: injecting an operation into a larger row, weakening a computation to a larger row, and handling one label of an abstract row. The hand-written tests use `Plus l r`, with handlers written separately for the left and the right. The general mapping scheme still needs writing.
- **Sequencing is `bind`.** An operation's result is bound by the continuation's lambda, and can index types inside it. It can't escape `bind`'s fixed result type: a function returning `Vec Nat n` for a locally obtained `n` needs a dependent pair. That's a restriction worth stating, not a solved problem.
- **The empty row.** `Comp` over an empty signature is equivalent to a plain value, but it isn't the same type. The plan:
  - pure functions stay plain;
  - code polymorphic in a row and instantiated at the empty row is run with an explicit `runPure : Comp Empty … a -> a`;
  - a pure function used where an effectful one is expected is wrapped with `Done`.
- **Polymorphic operations.** `abort : () -> {Abort} a` is encoded as a primitive operation returning `Empty`, followed by eliminating the impossible result (as in the tests). Other genuinely polymorphic operations would store a type in the operation, which raises universe questions. They're excluded until needed.
- **`Partial` in a row.** Handlers here are inductive folds, so `Partial` can't appear in their residual rows until [`partial.md`](partial.md) is settled.

### Costs

- Effectful code runs by building and folding trees, which is slower in the evaluator than option A.
- Error messages must talk about abilities, never `Comp`.
- Extracted JS builds and folds trees. Even an export whose final row is empty may use multi-shot handlers internally, and the backend must preserve that. Building and folding trees as ordinary data does preserve it, so it's the safe first backend. Generators would need the "at most once" restriction.

## Status

**Done:**
- The termination rule.
- `Comp`, `foldComp` and `bind` in the prelude.
- Handlers written by hand, with the semantic tests and the must-reject tests above.
- A nested-pattern fix that this needed: a branch now refines every variable whose type mentions the matched one, including variables bound earlier (`rest : res o` after `o` is matched as `L Get`).

**Next:**
1. The row mappings (injection, weakening, handling one label of an abstract row), written as hand-written examples first.
2. `ability` declarations and rows on arrows.
3. The direct-style translation, with `let` and sequencing, compared with Part 1 on the semantic tests, including operation order.
4. `handle … with`, with the coverage rule.
5. `IO` and `main`.

## Questions

1. **Rule 3.** Is the provenance rule as stated sufficient for this kernel? Is there a known interaction with impredicative `Prop`, or with branches refining the types of earlier variables?
2. **Rows.** Duplicate labels refused, in a canonical order, with generated mappings: is that a reasonable first design, or is it worth going straight to Koka-style duplicate labels?
3. **Dependent results.** Is a dependent pair the right answer for effectful functions whose result type depends on an operation's result, or is a dependent `bind` worth specifying?
