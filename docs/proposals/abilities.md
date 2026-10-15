# Stitchwort: abilities and handlers

**Status:** draft 3, 15 October 2026. The foundation is implemented (see [Status](#status)): `Comp`, its fold and `bind`, and the termination rule they need. Hand-written handlers for `State`, `Abort` and `Choose` pass the semantic tests below. There's no `ability` or `handle` syntax yet. `Partial` has moved to its own proposal, [`partial.md`](partial.md).

## Changes since draft 2

A second review accepted the architecture and asked for the kernel's structural relation and the row mappings to be made precise. In response:

- **The termination rule is restated as a classification** of each argument against the parameter, which reconciles rule 2 with the `Ping` test. The implementation already behaved this way; the old wording didn't say so. See [The termination rule](#the-termination-rule).
- **Parent provenance is explicit.** A function field's application is smaller only if the matched constructor came from the parameter or a known descendant of it. In the core, this holds by construction: see the fresh-wrapper invariant.
- **Kernel checkpoint.** New must-reject tests cover:
  - a recursive call hidden inside the argument of an accepted call;
  - the function being defined passed to a higher-order helper;
  - the review's dependent `tag`/`payload`/`rest` family, both through the elaborator and as hand-built kernel terms.
- **A kernel hole found and fixed.** Positivity only looked at field types as written, so a definition or data type declared *between* a data type and its constructors could hide a negative occurrence (`MkBad (f : Neg 0)` with `Neg n = Bad -> Void`). Field types may now only use what existed when their data type was declared, and constructors can be defined only once. The elaborator never produced this order, so no program could reach the hole, but the kernel isn't supposed to rely on that.
- **Rows:**
  - a label is the ability declaration;
  - row variables carry "lacks" constraints;
  - signature mappings carry responses back;
  - reordering is an explicit, checked permutation.
- **Dependent results** use a data-level dependent pair. There's no dependent `bind`.

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

A `Comp` is well-founded: it's strictly positive, because `rest`'s domain doesn't mention `Comp`. Every path through it is finite, though there may be infinitely many paths (an operation returning `Nat` branches infinitely). The termination checker needs one parameter position `i` that every recursive call decreases. Each argument passed at position `i` is classified by its relation to parameter `i`:

| Relation | Examples | Enough for a recursive call? |
|---|---|---|
| **The parameter itself** | the parameter variable; a constructor rebuilding it (`Call o rest` where the parameter was matched as `Call o rest`) | No |
| **A strict descendant** | a field of a constructor matched from the parameter or from a descendant; a rebuilt descendant (`Succ n` where a descendant `m` was matched as `Succ n`); a recursive function field of such a match, applied (`rest y`) | Yes |
| **Unrelated or unknown** | anything else, including any other function returning the same type | No |

So the rules are:

1. **Matching** a variable that's the parameter or a descendant makes its fields descendants.
2. **Rebuilding** a matched node gives that node's own classification. Rebuilding the parameter isn't smaller (`Ping`); rebuilding a descendant is (`peel (Succ (Succ n)) = peel (Succ n)`).
3. **Applying a recursive function field** gives a descendant, provided the field's parent was the parameter or a descendant (rule 1). "Recursive function field" is decided from the field's *declared* type in the data declaration (a function type whose result is the matched data type), and only the variable bound by the match counts. It never comes from a type that only reduces to such a function after refinement, so refinement can't give a variable provenance it didn't have.

**Every occurrence is checked.**
- Each recursive call is checked separately, including calls inside the arguments of another call (`hidden (rest (… (hidden (Call Choose rest)) …))` is refused).
- A reference to the function being defined that isn't applied, such as passing it to a helper, is refused.

**The fresh-wrapper invariant.** The review's example `loop t = match Call Later (\_ -> t) with … Call Later rest -> loop (rest ())` would make `rest ()` equal `t`. It can't arise, because in the core a `case` only appears at the top of a definition's body, on a variable. So every matched value is a parameter or a field of an earlier match, never a freshly built value. The kernel rejects a `case` anywhere else (`rejects_a_case_outside_a_case_tree`). **When `match` or `let` expressions are added, they must preserve this:** matching a value that isn't a parameter or a descendant gives fields of unknown relation.

**Refinement.**
- Inside a branch, the constructor value is substituted for the matched variable in the goal and in every variable's type and value, including variables bound before it (`rest : res o` once `o` is matched).
- The invariant this must maintain is that refinement is a well-scoped, typed substitution. Reducing an accepted `case` on an actual constructor must preserve its type.
- Structural relations are computed from terms, never from refined types.
- Tested in the kernel and through the elaborator with the review's family: a constructor with `tag : Bool`, `payload : PayloadType tag` and `rest : PayloadType tag -> Tree`, matched on `tag` after the other fields are bound. Correct uses check, and using the `False` branch's payload as a number fails.

This corresponds to `Comp`'s dependent eliminator, whose `Call` branch has the induction hypothesis `ih : (y : res o) -> P (rest y)`. Generating that recursor and compiling folds to it would be an alternative implementation. For now the fixpoint checker stays, with the rules above.

**Not yet verified:** a soundness proof for these rules in this kernel. Rocq's `Acc`, a `Prop` with a recursive function field, shows that impredicative `Prop` and function-field recursion can coexist, but that says nothing about this implementation. Rocq has had guard-checker bugs where subterm information was lost through matches, or recursion went through higher-order fixpoints. Those are the patterns the tests above target.

### What the kernel rejects

These are must-reject tests in `examples/soundness/`:

| Attempt | Rejected by |
|---|---|
| `forever u = Call Later (\v -> forever u)`, which with `drain` would prove `Void` | Termination: `u` isn't smaller |
| A fake child: `loop ((\b -> Call o rest) True)` | Termination: the head isn't the field variable |
| `Ping`: `bad (Call o rest) = bad (Call o rest)` | Termination: rebuilding the parameter isn't smaller |
| A recursive call hidden inside an accepted call's argument | Termination: every call is checked |
| The function passed to a higher-order helper | Termination: an unapplied reference is refused |
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

- **Rows.**
  - **Labels.** A label is an ability *declaration*: a row has at most one instantiation of each, so `{State Nat, State Bool}` is refused. State of two different types at once needs two ability declarations. This is a deliberate limitation, to revisit (Koka-style duplicate labels with masking) only if a real example needs it.
  - **Row variables carry "lacks" constraints.** `{State s | e}` means `State` is absent from `e`. The constraints survive generalisation and are checked when `e` is instantiated, so a duplicate can't arrive by substitution. A handler's input and output rows are different rows, so its clauses may still use an outer `State`.
  - **Mappings carry responses back.** Because `res` depends on the operation, a mapping between signatures `(op₁, res₁)` and `(op₂, res₂)` is a pair:

    ```
    inject : op₁ -> op₂
    reply  : (o : op₁) -> res₂ (inject o) -> res₁ o

    translate (Call o rest) = Call (inject o) (\r -> translate (rest (reply o r)))
    ```

    For inclusion into a sum, `reply` passes the response through.
  - **Order is explicit.** A row with an abstract tail (`A + (B + e)`) may stop being sorted once `e` is instantiated. So rows that are equal in the source are related in the core by explicit, checked permutations, never assumed to be the same `Comp` type. A permutation reorders the signature, never the operations a computation performs.
  - **Tests before row inference.** Hand-written mappings, checked for: identity, composition of weakenings, a permutation followed by its inverse, and instantiating an abstract tail. Results and operation traces must agree.
- **Sequencing is `bind`. Dependent results use a dependent pair.** An operation's result is bound by the continuation's lambda, and can index types inside it, but it can't escape `bind`'s fixed result type. A function whose result type depends on an input is fine (`(n : Nat) -> {E} Vec Nat n`). One whose result depends on a value it obtains returns the value with it, as a *data-level* dependent pair (not an existential in `Prop`, because the caller needs the index):

  ```
  make : () -> {ReadNat} Sigma Nat (\n -> Vec Nat n)
  ```

  This works with multi-shot handlers too: branches can produce different lengths, all inhabiting `List (Sigma Nat (\n -> Vec Nat n))`. There's no dependent `bind` until an example needs one.
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
1. One generic handler over an abstract residual row, with checked injection and response mappings, run under different row orders and concrete instantiations (the tests listed under Rows).
2. `ability` declarations and rows on arrows.
3. The direct-style translation, with `let` and sequencing, compared with Part 1 on the semantic tests, including operation order.
4. `handle … with`, with the coverage rule.
5. `IO` and `main`.

## Questions

1. **Rows.** Are "lacks" constraints plus explicit permutations the right first account of open rows, or is there a simpler representation that still keeps the core mappings checkable?
2. **The structural relation.** Does the classification table, together with the fresh-wrapper invariant, now specify the checker precisely enough? Are there adversarial patterns beyond the tests listed above that you'd add?
