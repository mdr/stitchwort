# Proposal: how abilities and handlers run

**Status:** draft for discussion, 15 October 2026. Nothing here is implemented. This is the "written operational semantics" that DESIGN.md §15 requires before milestone 7, plus a recommendation for how to build it.

## Summary

- **The behaviour** (what a program means) follows the usual design for deep handlers, as in Koka, Eff and Unison. A handler clause runs *outside* the handler. Operations a handler doesn't handle pass through to the next one out. Resuming `k` re-installs the handler. The precise rules are in [The rules](#the-rules).
- **The implementation** is the main decision. I recommend translating effectful code into ordinary data, a *tree of operations*, before it reaches the kernel, rather than adding effects to the kernel. Then the kernel's existing checks (positivity and structural recursion) prove that admissible handlers terminate. The conjecture in DESIGN.md §8 becomes a theorem that the kernel checks for each program, and `IsData` may no longer be needed.
- **`Partial`** fits the same scheme: a partial computation is a tree that may be infinite, built one step at a time. The type checker never unfolds it. Only the runtime runs it. A generic `withFuel`, which DESIGN.md postponed, then falls out for free.

## What DESIGN.md asks to pin down

DESIGN.md §8 lists three questions. Short answers first, using `State` as the example:

```
ability State s where
  get : () -> {State s} s
  put : s -> {State s} ()
```

1. **Does a clause run inside or outside its own handler?** *Outside.* If the `get` clause itself calls `get ()`, that call goes to the *next* `State` handler out, not to this one. (Running inside would let a clause loop back into its own handler.)
2. **How are unhandled operations forwarded?** To the nearest enclosing handler that handles them. The computation is suspended exactly as for a handled operation, and when that outer handler resumes it, it continues under the inner handler again. Handlers are invisible to operations they don't handle.
3. **What is the type of `k`?** For a handler whose result type is `r` and whose remaining abilities are `e`, handling an operation that returns `b`:

   ```
   k : b -> {e} r
   ```

   `k` resumes the computation *with the handler still in place* (that's what "deep" means), so its result is the handler's result `r`, and calling it can perform only the abilities left over, `e`.

## The rules

Evaluation is strict and left to right, as now. Written as rewriting steps on a running program:

**Calling an operation.** `op v` suspends the computation up to the nearest handler that handles `op`. Everything between the call and that handler is the *continuation*.

**Return.** When the handled computation finishes with value `x`, the `return x` clause runs:

```
handle x with H    ⟶    (return clause of H) with x bound
```

**Handled operation.** If the computation inside `handle … with H` calls `op v`, and nothing between the call and `H` handles `op`:

```
handle C[op v] with H    ⟶    (op clause of H) with its argument bound to v,
                                and k = \y -> handle C[y] with H
```

`C[…]` is the rest of the computation, with a hole where `op v` was. Two things follow from the shape of this rule:

- The clause replaces the whole `handle` expression, so it runs **outside** `H` (question 1).
- `k` wraps the rest of the computation in `handle … with H` again, so the handler is **deep** (question 3).

**Forwarded operation.** If `H` doesn't handle `op`, the step happens at whichever outer handler does. `C` then contains `handle … with H`, and resuming re-enters it (question 2).

**Abilities in types.** A function type `a -> {e} b` says calling it may perform `e`. A plain `a -> b` means pure and total. `handle` removes the handled ability from the row:

```
prog       : () -> {State s | e} a
runState   : s -> (() -> {State s | e} a) -> {e} (a, s)
```

### Examples

```
-- Resuming more than once: collect every outcome of the choices.
ability Choose where
  choose : () -> {Choose} Bool

allResults : (() -> {Choose | e} a) -> {e} List a
allResults prog =
  handle prog () with
    | return x        -> [x]
    | choose () => k  -> append (k True) (k False)

-- Not resuming at all: stop early.
ability Abort where
  abort : () -> {Abort} a

toOptional : (() -> {Abort | e} a) -> {e} Optional a
toOptional prog =
  handle prog () with
    | return x       -> Some x
    | abort () => k  -> None
```

A clause performing the ability it handles (question 1):

```
-- Inside `inner`, `get` answers from the *outer* State: the clause's own
-- `get ()` goes past `inner`'s handler.
inner : () -> {State Nat | e} Nat
inner () =
  handle (\() -> get () + 1) () with
    | return x      -> x
    | get () => k   -> k (get () * 10)
```

## How to build it: two options

### A. Effects in the kernel

The core gets ability rows on function types, an effect judgment `Γ ⊢ t : A ! ε`, and `handle`/operation terms. The kernel's evaluator implements the rules above directly, with continuations.

- **Gain:** a direct implementation of the semantics. Effectful code runs fast in the evaluator.
- **Cost:** the trusted kernel grows a lot: continuations, rows, row polymorphism and the effect judgment. Termination of handlers stays a *conjecture*, a tracked assumption, as DESIGN.md §8 has it now.

### B. Effects as data (recommended)

The elaborator translates effectful code into ordinary values of one data type, a tree of operations, defined in the prelude:

```
-- A computation that returns an `a`, performing operations from a
-- signature: `Op` is the type of operation calls, and `Res op` is what
-- operation `op` gives back.
type Comp (Op : Type) (Res : Op -> Type) (a : Type) : Type =
  | Done (value : a)
  | Call (op : Op) (rest : Res op -> Comp Op Res a)
```

- An effectful function `a -> {e} b` becomes a pure function `a -> Comp (ops of e) (results of e) b`. The kernel never sees ability rows, only this data type.
- Direct-style code is translated into nested `Call`s: `let n = get (); put (n + 1); n` becomes "call `get`, then with its result `n` call `put (n + 1)`, then be `Done n`". This is the main work for the elaborator.
- **A deep handler is a fold** over the tree: a recursive function with one case for `Done` (the `return` clause) and one for `Call`. For a handled operation it runs the clause, with `k = \y -> handler (rest y)`. For any other operation it rebuilds the `Call` with the handler wrapped round `rest`. These are exactly the rules above, written as an ordinary definition.
- Rows are combined by summing signatures. The elaborator keeps them in a canonical order, so `{State s, Abort}` and `{Abort, State s}` are the same type. A row variable `e` becomes an implicit signature parameter.

**Why this answers the termination question.** The kernel already checks two things that together prove an admissible handler terminates:

- **Positivity.** `Comp` is strictly positive, since `rest`'s domain `Res op` doesn't mention `Comp`, so every tree is finite (well-founded).
- **Structural recursion.** The handler recurses on `rest y`, which is structurally smaller than `Call op rest`. Coq and Lean accept this standard rule for function-typed fields. Our termination checker needs a small extension to accept it, limited (as in Coq) to fields whose result is the data type being matched.

The two counterexamples in DESIGN.md §8 are then rejected by these existing checks, with no special rule:

| Counterexample | Why it fails |
|---|---|
| `Ping`: a clause calls the handler on the original program, restarting it | The recursive call isn't on a smaller tree: `E-TERMINATION` |
| `Cell`: an operation stores an effectful function | The operation's argument type would mention `Comp` itself, which needs a recursive signature the kernel's positivity check refuses (and the elaborator can't even form) |

**Checked against today's kernel** (scratch files, not committed):

- The kernel accepts `Comp` as written above, so it passes the positivity and universe checks.
- A `State` handler written by hand as a fold over `Comp` is refused only with `E-TERMINATION` on `runState s (rest s)`. That's the one extension described above.
- Both ways of writing `Cell` are refused. A result-type function that mentions itself gets `E-TERMINATION`. An operation type whose field mentions `Comp` of itself gets `E-POSITIVITY`.

So with option B, *a handler that the kernel accepts terminates*. That's not a conjecture and not a tracked assumption; it rests only on the kernel being correct, like everything else. As far as I can see, this also makes `IsData` unnecessary. State holding *pure* functions (`State (Nat -> Nat)`) can't loop, and state holding *effectful* functions can't be written down, for the same reason as `Cell`. I'd want to check this carefully with must-reject tests before dropping `IsData`.

- **Gain:** the kernel stays as it is (apart from the termination-checker extension above), and handler termination is checked, not assumed. Dependent types work naturally with effects: in `(n : Nat) -> {IO} Vec Nat n`, the result type is just `Comp … (Vec Nat n)`, and a result used later in a type is an ordinary bound variable in the continuation. That settles the open question in DESIGN.md §6, "Effects and dependent types", for free.
- **Cost:**
  - Effectful code runs as tree-building and folding, which is slower in the evaluator than option A. That's fine for tests and the playground at POC scale.
  - Error messages must be phrased in terms of abilities, never `Comp`, so the elaborator has to translate them back.
  - Extracted JS would also build and fold trees. That's acceptable at first, since exports must be pure anyway. Compiling handlers to generators can come later.

## `Partial`

A partial function's recursion can't be a finite tree. With option B it becomes a tree that may be *infinite*, built lazily. The prelude gets a signature with one operation, `later`. A partial definition may make a recursive call only inside the `rest` of a `later` call, so each step builds only one layer:

```
spin : Nat -> {Partial} Nat
spin n = spin n
-- becomes, roughly:
spin n = Call later (\_ -> spin n)
```

- **For the kernel:** a `Partial` definition is checked for *guardedness* (each recursive call is inside a `later`'s `rest`) instead of structural recursion. And it is **never unfolded during type checking**, only when a program runs (principle 2, DESIGN.md §5 rule 7). Without that rule, comparing two `Partial` values could unfold them forever, because comparison looks inside functions.
- **Still visible in types:** `Partial` appears in the type and spreads to callers, because calling `spin` produces a `Comp` with `later` calls in it, and only a function whose type includes `{Partial}` may return one.
- **Handled only by the runtime:** it runs the tree, looping for as long as it takes. Ordinary handlers may not handle `later` (DESIGN.md §5 rule 4).
- **A bonus:** `withFuel : Nat -> (() -> {Partial | e} a) -> {e} Optional a`, which DESIGN.md §5 postponed, can now be written in the prelude. It counts `later` steps and gives up when the fuel runs out. It's total, because it recurses on the fuel. The three requirements DESIGN.md lists for it are met: the "tick" is part of the core encoding, and it's checked by the kernel's guardedness rule. Foreign partial functions remain excluded.

## `IO`

`IO` is a signature like any other, but only the runtime handles it, at `main`, by performing each operation for real. The type checker never runs `IO` operations: they're just `Call` nodes, which it never needs to evaluate.

## What would be built, in order

1. **The core:** `Comp` in the prelude, and the termination-checker extension for function-typed fields. Hand-written handlers over hand-written trees, to test the kernel side alone.
2. **The elaborator:**
   - `ability` declarations, and rows on arrows (`{State s | e}`) with row variables.
   - The direct-style translation of effectful code into `Call`s, including `let` and sequencing (`a; b`), which don't exist yet.
   - `handle … with` clauses.
3. **The standard handlers:** `State` (`runState`), `Abort` (`toOptional`), `Choose` (`allResults`), and the must-reject suite: `Ping`, `Cell`, function-valued state, a user handler for `Partial`.
4. **`Partial`:** guardedness, no unfolding during type checking, the runtime loop, `withFuel`.
5. **`IO` and `main`:** a CLI runner that handles `IO` (console output to start with).

Steps 1–3 deliver the milestone 7 demo ("Effectful code tested through pure handlers. `Ping`, `Cell` and function-valued state are rejected"). Step 4 is what makes totality visible in types. With option B, results no longer need to show a handler assumption, because there isn't one.

## Questions for you

1. **Option A or B?** I recommend B: the kernel checks handler termination instead of trusting a conjecture, at the cost of slower effectful code in the evaluator.
2. **New syntax** this needs that doesn't exist yet: `let x = e` (with the body continuing on the following lines) and sequencing. DESIGN.md already uses both in its examples. Is the layout in DESIGN.md's `tick` example what you want?
3. **Duplicate abilities in a row,** like `{State Nat, State Bool}`: refuse them for now (simplest), or allow them, which needs a way to say which one an operation means?
