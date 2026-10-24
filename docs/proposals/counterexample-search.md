# Proposal: counterexample search for theorem statements

**Status:** draft 1, 24 October 2026. Ticket SW-330; the intent was decided in D570 ("(a) plus
(c)": search when a proof fails and at a `?`, plus explicit property tests, sharing
generators; "(b)", searching every theorem as it's stated, later). Design note only: nothing
here changes the compiler. Decisions for the owner are in [§11](#11-decisions-for-the-owner);
they're labelled CE-1 to CE-6 and need D numbers when recorded.

Labels, as in the other notes:

- **[checked]**: read in the Stitchwort source or docs at the `file:line` given (commit
  `51526521`);
- **[cited]**: read in a source listed in [Sources](#sources) ([I1], [L2] and so on);
- **[inferred]**: my reasoning from checked or cited facts;
- **[unverified]**: believed, not confirmed.

## Contents

0. [Summary](#0-summary)
1. [The goal, and who it's for](#1-the-goal-and-who-its-for)
2. [How other systems do it](#2-how-other-systems-do-it)
3. [Stitchwort today: the pieces we already have](#3-stitchwort-today-the-pieces-we-already-have)
4. [Which statements are in scope](#4-which-statements-are-in-scope)
5. [Generating inputs](#5-generating-inputs)
6. [Running the statement](#6-running-the-statement)
7. [Where it runs](#7-where-it-runs)
8. [Soundness: purely advisory](#8-soundness-purely-advisory)
9. [Reporting](#9-reporting)
10. [Staged plan and acceptance tests](#10-staged-plan-and-acceptance-tests)
11. [Decisions for the owner](#11-decisions-for-the-owner)
12. [Risks](#12-risks)
- [Sources](#sources)

## 0. Summary

- **What:** when a theorem's proof fails (or is still `?`), try the statement on lots of small
  inputs, and if one makes the hypotheses true and the conclusion false, show it next to the
  error: "the statement is false: `xs = [0], ys = [1]`". The same machinery runs explicit
  property tests (`test` with parameters) and an on-demand `stitchwort check --counterexamples`.
- **Why:** a false statement is the most expensive mistake in proving: you can't finish the
  proof, and nothing tells you why. Isabelle runs its Quickcheck "automatically and silently
  every time the user types in a lemma" for exactly this reason [cited: I1 §6.1].
- **How:** small inputs first, every one of them up to a size (as Haskell's SmallCheck and
  LeanCheck do), then random larger ones (as QuickCheck, Lean's Plausible and Coq's QuickChick
  do). Inputs are generated for each data type from its constructors, by the compiler, with no
  user code. The statement's hypotheses and conclusion are decided by the same decision search
  that `if` and `test` already use, and run on the fast runtime, falling back to the reference
  evaluator as tests do.
- **Safety:** it never accepts anything. A found counterexample is re-run on the reference
  evaluator before it's shown; "no counterexample found" is never shown as a pass, and on a
  failing proof it's not shown at all. The kernel doesn't change.
- **First stage (small):** a failing theorem (or one whose whole proof is `?`) over `Bool`,
  `Nat`, `Int`, `List`, `Option`, pairs and the program's own data types and records, with
  conclusions and hypotheses that `=`, `<=`, `<`, `&&`-style `And`/`Or`/`Not` and `Bool`
  decide; enumeration only; the counterexample shown as a note on the error.
- **Recommendation:** build stage 1 as described; take the six decisions in §11 (main ones:
  on by default on proof failure, yes; property tests spelled `test` with parameters, not a
  new `property` keyword; generators built into the compiler first, user generators later).

## 1. The goal, and who it's for

### 1.1 User stories

1. **"The theorem I'm stuck on is actually false."** I write

   ```
   theorem reverseAppend (xs: List Nat) (ys: List Nat):
       List.reverse (xs ++ ys) = List.reverse xs ++ List.reverse ys := …
   ```

   and my proof fails somewhere in the `Cons` case. Today I get a type mismatch, and I may
   spend an hour on it. With this feature the error carries a note:

   ```
   note: this statement is false; a counterexample:
           xs = [0]
           ys = [1]
         left:  [1, 0]
         right: [0, 1]
   ```

   (This is the same example Isabelle's history uses for Quickcheck: there it reports
   `xs = [a1], ys = [a2]` [cited: I1 §6].)

2. **"Is this lemma even true before I try?"** I state a lemma with `:= ?` and see a
   counterexample at the `?` straight away, or nothing, which tells me nothing either way.

3. **"A missing hypothesis."** `theorem subAdd (a: Nat) (b: Nat): (a - b) + b = a` gets
   `a = 0, b = 1` (truncated subtraction gives `0 + 1 = 1`, not `0`). I add `(h: b <= a)` and
   the counterexample goes away, which is a strong hint I've got the statement right.

4. **"A spec I'd like checked on many inputs, without proving it."** A property test:
   `test "sort keeps length" (xs: List Nat) := List.length (List.sort xs) == List.length xs`,
   run by `stitchwort test` on many inputs, and reported as evidence about those inputs, not
   as a theorem (DESIGN.md:558-564 [checked]).

5. **"A wrong `?` deep inside a proof."** In a branch I've got `k: Nat, h: k > 0 ⊢ …`; the
   goal at the `?` is false for `k = 1`. Shown at the hole (a later stage).

### 1.2 What it is not

- Not a prover. It can't show a statement true. Plausible's tactic closes a goal "like
  `admit`" when it finds no counterexample [cited: L3]; we never do that.
- Not a model finder for logic-heavy statements (Isabelle's Nitpick, which uses a SAT solver
  to find finite models [cited: I1 §6.2]). Statements quantified over sets, relations or
  functions are out of scope for now.

## 2. How other systems do it

### 2.1 The systems

**Isabelle/HOL: Quickcheck and Nitpick.** Quickcheck runs on every lemma as it's typed
[cited: I1 §6.1]. It uses Isabelle's code generator to run the statement, and has three
testers: random, *exhaustive* enumeration of small values (an idea it credits to
SmallCheck's authors), and *narrowing* (symbolic inputs refined only as the property looks
at them, as in Lazy SmallCheck) [cited: I1 §6.1]. It "worked automatically whenever all
functions and inductive predicates were executable", with generators for data types made
automatically; its known weak spot was conditional properties `φ ⟹ ψ`, "where most of the
random values simply falsify φ", which led to generators *synthesised from the premises*
[cited: I1 §6.1]. Nitpick instead searches for a finite model that falsifies the conjecture,
via the Kodkod library and a SAT solver, and is better at set theory and logic [cited: I1
§6.2]. Isabelle's Quickcheck was inspired by Dybjer et al.'s random testing in Agda
[cited: I1 §6.1].

**Lean 4: Plausible** (formerly `slim_check`). A tactic, `plausible`, and a command,
`Testable.check` [cited: L1]. The tactic reverts the hypotheses in context into the goal, so
they become quantified variables and premises, then looks for a `Testable` instance
[cited: L3]. A quantifier `∀ x : α` over a type with a sampling instance draws a random `x`
[cited: L2]. A *decidable* hypothesis is a guard: when it's false, the sample is discarded
and counted as "gave up", with up to `numRetries` (10) redraws [cited: L2]. A decidable
conclusion is the test itself; a failure says "`{s}` does not hold" [cited: L2]. Defaults:
100 instances, sizes up to 100, scaled up over the run [cited: L2]. Generators: instances for
`Nat` (0 up to the size), `Int` (−size to size), lists, strings [cited: L4]; `deriving
Arbitrary` for inductive types, choosing among non-recursive constructors at fuel 0 and
weighting recursive ones by the fuel left; indexed families are refused [cited: L5].
Shrinking is a `Shrinkable` instance, re-tried greedily [cited: L2]. Reports: "Found a
counter-example!" with the bindings and the shrink count; "Gave up after failing to generate
values that fulfill the preconditions N times" [cited: L2]. If nothing is found, the tactic
acts like `admit` [cited: L3].

**Coq/Rocq: QuickChick.** A QuickCheck clone as a plugin [cited: Q1]. Properties are anything
`Checkable`, including any proposition with a `Dec` instance (`Dec` is a type class giving a
decision; there are instances for `~`, `/\` and `\/`) [cited: Q2]. `x ==> y` discards the
input when `x` is false [cited: Q2]. Generators, shrinkers and printers are type classes
(`GenSized`, `Shrink`, `Show`), derivable with `QCDerive` for an inductive type [cited: Q2].
Its distinctive part is deriving generators *for inductive relations*: `QCDerive
ArbitrarySizedSuchThat for (fun x => P x)` makes a generator of `x`s that satisfy `P`, rather
than filtering [cited: Q2]; the PLDI 2022 work derives enumerators and checkers too, with
proofs that they're sound and complete for the relation [cited: Q3].

**Haskell: QuickCheck, SmallCheck, LeanCheck.**
- *QuickCheck* (random): 100 tests by default; a size parameter; a `shrink` that by default
  doesn't shrink, and a `genericShrink` that tries subterms, then shrinks the subterms; it
  gives up after too many discarded tests per success; random *showable* functions as
  inputs (`Function`/`Fun`) [cited: H1].
- *SmallCheck* (enumerative by depth): tests every value up to a depth, raising the depth,
  on the observation that "if a program fails to meet its specification in some cases, it
  almost always fails in some simple case" [cited: H2]. Its page now calls it "largely
  obsolete" and points to `falsify` [cited: H2].
- *LeanCheck* (enumerative by size): values come in *tiers*, finite lists of values of
  increasing size; `deriveListable` makes instances for types "without a constraining data
  invariant"; `check` tries 200 values by default [cited: H3].

**Idris 2, Agda, F\*.** I didn't find a built-in counterexample search in their current
releases; this wasn't searched exhaustively [unverified]. Agda had random testing in the
2000s (Dybjer et al.) [cited: I1 §6.1].

### 2.2 How they answer the five questions

| Question | Isabelle Quickcheck | Lean Plausible | QuickChick | Small/LeanCheck |
|---|---|---|---|---|
| Inputs for data types | automatic from the datatype | `deriving Arbitrary` | `QCDerive` | derived (`deriveListable`) |
| Preconditions | filter; generators from premises; narrowing | decidable guard, discard | `==>` discard; generators for relations | filter |
| Deciding the property | runs generated code | `Decidable` instances | `Dec` instances | it's a `Bool` function |
| Small or random | random, exhaustive, narrowing | random, size grows | random (enumerators too) | exhaustive, smallest first |
| Shrinking | n/a for exhaustive | `Shrinkable` | `Shrink` | not needed: smallest first |
| With a failing proof | runs on every lemma, silently | a tactic you call | a command you call | n/a |

**What I take from this** [inferred]:

1. *Automatic, no user code* is what made Isabelle's tool loved (I1 calls it "one of
   Isabelle's best-loved tools"); Haskell's and Coq's need instances. We know every data
   type's constructors, so we can do the automatic thing.
2. *Small inputs first* finds the counterexample people want to see (`[0]`, not a random
   list of 30 numbers) without needing a shrinker. Random inputs come second, for bugs that
   need size.
3. *Hypotheses as filters* is the simple start everyone uses; generators that satisfy the
   hypothesis by construction (QuickChick, Isabelle) are a later improvement for sparse
   hypotheses.
4. *Decidability by instances* (Lean, Coq) fits us exactly: we already have `Decidable` and
   `DecEq` and a decision search.

## 3. Stitchwort today: the pieces we already have

| Piece | Where | What it gives us |
|---|---|---|
| `Decidable p` and its combinators `Decidable.not`, `.and`, `.or`; `Nat.decLessEq`, `Nat.decLessThan`; `Int.decLessEq`, `Int.decLessThan` | `crates/elab/src/std/core/Decidable.sw:11,96,103,108,113,115`, `core/Int.sw:108,110` [checked] | decisions for the logical connectives and orders |
| `DecEq` interface, instances for `Nat`, `Int`, `Bool`, `Char`, `Text`, `List`, `Pair`, `Option`, `Result` | `core/DecEq.sw:11-37` [checked] | `=` on most first-order data |
| Derived `DecEq` for a program's data types and records | `crates/elab/src/derive.rs:1-30`, `records.rs:59` [checked] | `=` on the user's own types |
| `Ord` carries its own `decLessThan`/`decLessEq` | `core/Ord.sw:23-40` [checked] | `<`, `<=` on any ordered type |
| The decision search: finds a `Decidable P` for a proposition `P` (hypothesis in scope, `instance`s returning `Decidable`, `DecEq` for equations) | `crates/elab/src/auto.rs:1-22`, `bind.rs:250` (`decide`), `interfaces.rs:1467` (`decide_eq`) [checked] | turning a statement into something runnable |
| `test` takes "a `Bool`, or a decided proposition, as `if` takes" | `crates/elab/src/lib.rs:1052-1056` (`logic::bool_operand`), `logic.rs:98` (`condition`), `docs/syntax.md:46` [checked] | the exact conversion we need, already used |
| Tests run on the fast runtime by default, falling back to the reference evaluator for what it can't lower; outcomes pass, fail, out of resources | `crates/driver/src/driver.rs:586-593,948,1018-1060`; `crates/cli/src/main.rs:71-73` (`--reference`) [checked] | the run loop, budgets, fallback |
| A failing test explains itself: the two sides of a comparison, quoted and cut to about 200 characters, and where two lists first differ (D601) | `driver.rs:1079` (`failure`), `1147` (`compare`), `1246-1258` [checked] | the report format |
| Fast runtime API: lower definitions, then `Machine::call(f, args)` on runtime values; per-run `Limits` (steps, frames) | `crates/rt/src/lower.rs:53`, `machine.rs:35-42,166` [checked] | calling a checker function many times cheaply |
| Runtime values: `Nat` as `u64` or big, `Int` as `i64` or big, `Text`, constructors as tag + fields with proofs erased | `crates/rt/src/value.rs:20-45` [checked] | what generators produce |
| Derived `Show` (`toSource`) for program types | `crates/elab/src/derive_show.rs:1-12` [checked] | printing a counterexample (the reference quoter in `compare` also works) |
| Diagnostics have `notes`; the LSP appends each as a `Note:` line; severities are error, warning, goal | `crates/syntax/src/diagnostic.rs:4-32,65`; `crates/cli/src/lsp.rs:1471-1474` [checked] | where the report goes |
| Goals at `?`: the expected type and the names in scope, kept per hole | `crates/elab/src/goals.rs:1-60` [checked] | the context for search at a hole |
| A failed declaration "leaves nothing behind for the next" | `crates/elab/src/module.rs:401-405` [checked] | so the statement must be captured before the failure is cleaned up (§6.1) |
| DESIGN's rules for property tests: cache key includes generator, count, sizes, seed; "replay" and "search" are separate commands; a pass is "evidence about the sampled cases" | `DESIGN.md:558-564` [checked] | constraints this design follows |

Gaps found while looking [inferred from grep, not exhaustive]: no `Decidable` instance for
an implication `p -> q` (we don't need one: hypotheses are peeled off, §4), for `Unit` (the
`Prop` one, `core/Logic.sw:12`), or for `Iff`; no existential decision. `List.Sorted le xs`
computes to nested `And`s and `le x y = True` (`std/List/Sort.sw:522-524`), so whether a
hypothesis like it is decided depends on the search unfolding it; stage 1 should test this.

## 4. Which statements are in scope

A theorem's statement has this shape once its binders are read off:

```
(x1: T1) -> … -> (xn: Tn) -> H1 -> … -> Hk -> C
```

with implicit `[a: Type]` parameters, auto (instance) parameters, data parameters `xi`,
hypotheses `Hj` (named or not; a later type may mention an earlier hypothesis's proof, as
in `(i: Nat) -> (h: i < List.length xs) -> List.get xs i h = …`), and a conclusion `C`.

It's **in scope** when:

1. every data parameter's type has a generator (§5);
2. every type parameter can be instantiated (§5.6), and every auto parameter's instance is
   then found;
3. each hypothesis `Hj` and the conclusion `C` has a decision, found by the existing search
   (§3), *under the parameters as variables*. In practice: `=` on a type with `DecEq`, `<`,
   `<=` on `Nat`, `Int` or an `Ord` type, `Bool`-valued expressions written as `b = True`,
   `And`, `Or`, `Not`, and anything else with an `instance … : Decidable …`.

Out of scope, and said so when asked (§9): parameters of function type (until stage 4),
parameters whose type is a `Prop` that isn't decidable, indexed families other than the few
in §5.4, `Exists` in the conclusion, statements about effectful computations, universes.

**Hypotheses** are filters: an input is tried, each hypothesis is decided in order, and if
one is false the input is *discarded*, not counted [inferred; same as Plausible's guards
(L2) and QuickChick's `==>` (Q2)]. A discarded input counts against the budget; if almost
everything is discarded, the result is "gave up", not "no counterexample".

## 5. Generating inputs

### 5.1 Small first, then random

Two phases, sharing one budget (§6.3):

1. **Enumerate** every input up to a size, smallest total size first, the way LeanCheck's
   tiers work [cited: H3]. The first counterexample found is a smallest one, so it needs no
   shrinking, and it's deterministic: the same statement always gets the same answer.
2. **Random**, with the size growing over the run, as QuickCheck and Plausible do
   [cited: H1, L2], for bugs that only show at sizes enumeration can't reach (a list of 12
   elements, a number past `2^64`). The seed is derived from the statement's hash, so the
   run is repeatable and cacheable (DESIGN.md:560 [checked]). A random counterexample is then
   **shrunk** (§5.5).

### 5.2 Sizes

The size of a value is the number of constructors in it, with numbers counted by their value
[inferred: this is a choice, close to LeanCheck's "size" rather than SmallCheck's "depth"
(H2, H3)]: `0`, `True`, `Nil` are size 0 (or 1; the exact offset doesn't matter); `[0, 1]` is
3. A tuple of inputs has the sum of their sizes. Small sizes explode quickly for several
inputs, which is why the random phase exists.

### 5.3 Generators for built-in types

| Type | Enumerated | Random extras |
|---|---|---|
| `Bool` | `False`, `True` | — |
| `Nat` | 0, 1, 2, … | edge values: `2^32`, `2^64 − 1`, `2^64` (the fast runtime switches representation at a machine word, `value.rs:24-28` [checked]) |
| `Int` | 0, 1, −1, 2, −2, … | ±`2^63` and neighbours |
| `Char` | `'a'`, `'b'`, `'0'`, `' '` | any scalar value, including non-ASCII |
| `Text` | `""`, `"a"`, `"b"`, `"ab"`, `"aa"` over a small alphabet | random strings, including a non-ASCII character and a surrogate-pair one |
| `Float` | `0.0`, `1.0`, `-1.0` | `-0.0`, NaN, ±infinity (D701 makes NaN one value [checked: `value.rs:33-35`]) |
| `List a`, `Option a`, `Pair a b`, `Result a e` | from constructors (§5.4) | lengths up to the size |
| `Fin n` (`n` known) | 0 … n−1 | — |
| `Vec a n` (`n` known) | lists of length `n` | — |
| `Map`, `Set` | built from a generated list with the library's own `fromList` | — |

`Map`/`Set` through `fromList` mirrors how the JavaScript boundary builds them, never
trusting a raw tree (DESIGN.md:843 [checked]).

### 5.4 Derived generators for the program's own types

For a data type or record declared in the program, the generator is read off its
constructors, as `DecEq` and `Show` are derived today (`derive.rs`, `derive_show.rs`
[checked]): enumerate each constructor's fields at the remaining size. Same conditions as
those derivations: no indices, no fields of function type.

**Proof fields** (a record with `(ok: lo <= hi)`): the fast runtime erases proofs
(`value.rs:8-9` [checked]), so a generator could produce `lo = 3, hi = 1` and nobody would
notice. That would give *false* counterexamples. Rule: a type with a proof field is
generated only if that field's proposition is decidable; the data fields are generated and
the value is kept only when the decision says yes [inferred]. Otherwise the type has no
generator and the statement is out of scope, with the reason.

**Where generators live (CE-3).** Two ways:

- **(a) Built into the compiler**, in Rust, reading each type's constructors from the checked
  program and making runtime values directly. Nothing is added to the library or checked per
  type; it costs nothing until a search runs. Users can't customise it.
- **(b) A library interface**, say `Enumerate a = { tiers: Nat -> List a }`, derived for each
  type as `Show` is and written by hand where wanted. Customisable, runs in JS too, but every
  declared type pays for a derived instance, and the derived source must be kept in sync.

Recommendation: **(a) now**, and **(b) only for overrides later** (stage 4), when a type has
an invariant the derivation can't respect or a better custom generator.

### 5.5 Shrinking

Only random counterexamples need it. Greedy, as Plausible does [cited: L2]: try smaller
candidates (each subterm of the same type, as QuickCheck's `genericShrink` [cited: H1];
numbers halved and decremented toward 0; list elements removed), keep the first that still
fails, repeat until none does or the budget ends. A candidate must still pass the hypotheses.

### 5.6 Polymorphic statements

`theorem reverseReverse [a: Type] (xs: List a): …` has to be run at some type. Choice
(CE-4): instantiate each type parameter with `Nat` (which has `DecEq`, `Ord`, `Show`, `Add`
and most instances a statement could ask for), and say so in the report (`a := Nat`); or
skip polymorphic statements. Recommend `Nat` [inferred: a statement false at some type is
usually false at `Nat`, since `Nat` has infinitely many distinct values; whether Isabelle
picks a default type this way is unverified]. If an auto parameter's instance isn't found at
`Nat`, try `Bool`, else out of scope.

### 5.7 Functions as inputs

A statement over `(f: Nat -> Nat)` (a `map` fusion law, say) can't be enumerated in general.
QuickCheck's answer is random functions that can be printed (finite tables with a default)
[cited: H1]. Stage 1 to 3: out of scope, said so. Stage 4: finite tables with a default for
functions from first-order types, printed as `f = {0 ↦ 1, _ ↦ 0}` [inferred].

## 6. Running the statement

### 6.1 The checker function

When the elaborator has checked a theorem's *statement* (before its proof), it builds a
**checker**, an ordinary function, using the decision search:

```
%falsify: (x1: T1) -> … -> (xn: Tn) -> Nat
-- 0: discarded at hypothesis 1, … k-1: discarded at hypothesis k,
-- k: holds, k+1: false (a counterexample)
```

made by nesting `Decidable.elim` over the hypotheses' decisions, with each hypothesis's proof
in scope for the later ones (proofs are erased at run time, so this costs nothing), and the
conclusion's decision innermost [inferred]. It's elaborated like any definition, so it's
type-correct by construction, and the kernel could check it, though it doesn't need to: the
result is advisory either way.

Two implementation points [inferred from `module.rs:401-405` [checked]]:

- A failed component is cleaned up. The statement (or the checker) must be captured right
  after the signature is checked, and kept aside for the driver, whether or not the body
  later fails.
- The checker is built lazily, only when a search will run, so a theorem that checks pays
  nothing. That needs the statement kept as a term, with its context.

### 6.2 Engine: fast runtime first, reference to confirm

- The driver lowers the checker with `stitchwort_rt::lower_definitions` and calls it with
  generated runtime values through `Machine::call` [checked: `lower.rs:53`,
  `machine.rs:166`], resetting the step count per input. Thousands of small inputs a second
  is the expected rate [unverified: no measurement yet; the fast-runtime note measured
  about 12× the reference evaluator on a merge sort].
- If the checker can't be lowered, the reference evaluator runs it, as tests already do
  (`driver.rs:948` [checked]), with a smaller budget.
- **Every counterexample is confirmed on the reference evaluator** (the trusted semantics)
  before it's reported. If the two disagree, that's a fast-runtime bug: report it as an
  internal error, never as a counterexample.
- The sides of an `=` are then evaluated and printed exactly as a failing test's are
  (`driver.rs:1147-1175` [checked]).

### 6.3 Budgets

Each search is one operation with its own limits, as each test is (`driver.rs:1020-1022`
[checked]). Per search:

| Where | Inputs | Wall time | Per input |
|---|---|---|---|
| On proof failure / at `?` | up to 2,000 (enumeration, then random) | 200 ms | the machine's normal step limit |
| `check --counterexamples` | up to 10,000 | 2 s per theorem | same |
| Property test | configured; default 1,000 | 10 s | same |

(Numbers are starting points, to tune [inferred].) An input that runs out of steps is
skipped and counted; if most do, the result is "inconclusive", as for tests (DESIGN.md:151,547
[checked]). Wall-time limits make results depend on the machine, so the *count* is the
primary limit and time is a backstop; a result stopped by time is never cached.

## 7. Where it runs

D570 chose (a) on proof failure and at a `?`, and (c) explicit property tests, sharing
generators; (b) on every theorem later [checked: `docs/comparisons/practical-proof-languages.md:773`].

### 7.1 On proof failure (default on; CE-1)

When a theorem's statement checked but its proof didn't, the driver runs the search. If it
finds a counterexample, it's added as a note to the *first* error of that declaration. If
not, nothing is added: "no counterexample in 2,000 cases" on a failing proof is noise, and
could be misread as "the statement is true". In the LSP this runs after the namespace is
checked, in the background, and can be cancelled as checking can (`live.rs:464-467`
[checked]), so typing never waits for it.

### 7.2 At a `?`

Stage 1: a theorem whose *whole* proof is `?` is searched like a failed one, and a
counterexample is a note on the goal diagnostic. Stage 3: any `?` inside a proof. The goal
has a context (`goals.rs:37-60` [checked]): its data variables become inputs, its hypotheses
become filters, `let`s keep their values, and pattern-matched variables are already
substituted ("inside a branch, the goal is the branch's", `docs/syntax.md:1047` [checked]).
This is what Plausible does by reverting the context [cited: L3].

### 7.3 `stitchwort check --counterexamples`

Runs the search on every theorem of the targets, including ones that checked. On a checked
theorem a counterexample is impossible unless something is wrong: an axiom or assumption
used, an unsound kernel, or a bug in the search or the runtime. So it's also a **soundness
canary** worth running in CI now and then [inferred]. This is D570's "(b) later" made
available on demand, without paying for it on every edit.

### 7.4 Property tests (CE-2)

DESIGN §7 has property tests as "later" [checked: DESIGN.md:558]. Spelling options:

- **(a) `test` with parameters:** `test "sort keeps length" (xs: List Nat) := List.length
  (List.sort xs) == List.length xs`. Today's tests are the zero-parameter case. Hypotheses
  are written as `implies`-style conditions in the body, or as parameters `(h: xs != [])`,
  decided like a theorem's.
- **(b) a `property` keyword**, with the same body. More visible, one more keyword.
- **(c) a `theorem` with a `?` proof run by `test`**: no new form, but then a property can
  never be "done" (it stays unfinished, so `check` fails, `docs/syntax.md:1049` [checked]).

Recommend **(a)**: one keyword, the same name, the same runner, cached as tests are.
`stitchwort test` reports a passing one as evidence, not a pass:

```
  ✓ reverse twice        passed
  ~ sort keeps length    no counterexample in 1000 cases (sizes ≤ 12; evidence, not a proof)
  ✗ sort is idempotent   counterexample: xs = [1, 0]  …
```

Its cache key includes the generator version, count, size schedule and seed, and "replay the
known counterexamples" is separate from "search again" (DESIGN.md:560-563 [checked]).

## 8. Soundness: purely advisory

- The kernel is unchanged; nothing the search does can make a declaration check.
- A passing search is never displayed as a pass or a tick on a theorem, never cached as a
  proof, and on a failed proof not displayed at all. (Contrast Plausible's tactic, which
  admits the goal when no counterexample is found [cited: L3].)
- A counterexample is shown only after the reference evaluator agrees (§6.2). It is then as
  trustworthy as a failing `test`: the checker's decisions are proved procedures
  (`Decidable` carries the proof), so `No` at those inputs means the statement is false
  there [inferred]. A later option: offer "add as a test" (a code action writing
  `test "subAdd is false at 0, 1" := not ((0 - 1) + 1 == 0)`), which the kernel checks.
- False counterexamples can only come from bad inputs: a generated value that breaks a
  type's invariant (handled by §5.4's proof-field rule and `fromList` for maps), or a
  runtime bug (caught by the reference confirmation).
- Results that are "not applicable" (§4) say why when asked (`check --counterexamples`,
  property tests); on proof failure they're silent.

## 9. Reporting

### 9.1 On a failing proof (CLI)

```
error[E-TYPE-MISMATCH]: type mismatch
   ╭─[ lists.sw:7:5 ]
   │ …
   = note: this statement is false; a counterexample:
             xs = [0]
             ys = [1]
           `List.reverse (xs ++ ys) = List.reverse xs ++ List.reverse ys` is false:
             left:  [1, 0]
             right: [0, 1]
             first difference at index 0: 1 vs 0
```

With hypotheses, the note lists them as holding (`b <= a` holds); with a type parameter,
`a := Nat`. Values are printed, cut, and compared as a failing test's (D601).

### 9.2 In the LSP and playground

The note travels in `Diagnostic.notes`, which the LSP already appends as `Note:` lines
(`lsp.rs:1471-1474` [checked]); nothing in the protocol changes. Optionally (later) the
counterexample also goes as `relatedInformation` pointing at the statement, and a code
action offers "add as a test".

### 9.3 Explicit runs

`check --counterexamples` prints one line per theorem: `counterexample …`, `none in N
cases (sizes ≤ k)`, `gave up (hypotheses true in M of N cases)`, `not applicable: (f: Nat ->
Nat) is a function`, or `inconclusive (ran out of steps)`.

CE-5 is whether the counterexample on a failing proof is a note on the existing error (my
recommendation: one diagnostic, no new noise, nothing to dismiss) or its own warning
diagnostic `W-COUNTEREXAMPLE` at the statement (easier to see and to filter on).

## 10. Staged plan and acceptance tests

Effort figures are rough guesses [inferred].

### Stage 1: a failing theorem, enumeration, a note (about 3 lane-days)

- Capture the statement of a theorem whose proof failed or is wholly `?`; build its checker
  (§6.1) with the existing decision search.
- Built-in enumeration for `Bool`, `Nat`, `Int`, `List`, `Option`, `Pair`, and derived
  enumeration for the program's data types and records without indices, function fields or
  proof fields. Type parameters at `Nat`.
- Fast runtime, reference fallback, reference confirmation; count budget.
- Note on the first error (or the goal), CLI and LSP.

Acceptance tests (each a file under `examples/`, with snapshots):

1. `reverseAppend` with a failing proof gets `xs = [0], ys = [1]` (or the first one in
   enumeration order) with left/right sides.
2. `subAdd (a b: Nat): (a - b) + b = a` gets `a = 0, b = 1`; with `(h: b <= a)` added and the
   proof still wrong, no note.
3. A true statement with a broken proof (`n + 0 = n` with a wrong `rfl` arm): no note.
4. A user type: `type Shape = | Circle (r: Nat) | Square (s: Nat)` and a false statement
   about an `area` function: the counterexample prints as `Square 1`.
5. A record: `type Point = { x: Int, y: Int }` and a false `Point` equation: prints the
   record.
6. A polymorphic statement reports `a := Nat`.
7. A hypothesis that is never true in the enumeration (`h: List.length xs = 50`): no note
   (gave up silently).
8. A statement with a function parameter, or a non-decidable hypothesis: no note, no error,
   no time spent beyond building nothing.
9. A theorem that checks: the search doesn't run (measured: check time of `std/` unchanged
   within noise).
10. A statement whose checker runs out of steps on every input: no note.
11. The fast runtime and the reference evaluator agree on every acceptance counterexample (a
    test that forces the reference path).

### Stage 2: random phase, more types, the command (about 3 lane-days)

Random inputs with growing size and shrinking; `Text`, `Char`, `Float`, `Fin`, `Vec`,
`Map`/`Set` via `fromList`, records with decidable proof fields; `check --counterexamples`
with its per-theorem lines; the wall-time backstop. Acceptance: a counterexample needing a
list of 12 elements is found and shrunk to a minimal one; a `Nat` bug at `2^64` is found; a
record with `(ok: lo <= hi)` never yields `lo > hi`.

### Stage 3: holes inside proofs (about 2 lane-days)

Context variables as inputs, context hypotheses as filters, `let`s with their values.
Acceptance: user story 5.

### Stage 4: property tests and extensibility (about 4 lane-days)

`test` with parameters (CE-2), results as evidence, the cache key and replay rules of DESIGN
§7; an `Enumerate`-style interface for custom generators (CE-3 (b)); functions as finite
tables. DESIGN §7 and `docs/syntax.md` updated.

### Later, only with a trigger

Generators that satisfy hypotheses by construction (QuickChick's derived generators for
relations [cited: Q2, Q3]; Isabelle's generators from premises [cited: I1]) if "gave up" turns
out common; narrowing; searching every theorem as it's typed (D570 (b)), if stages 1-2 show
it's cheap.

## 11. Decisions for the owner

- **CE-1. Run on proof failure by default?** (a) yes, in the CLI and the LSP; (b) only with a
  flag; (c) only in the LSP. **Recommend (a)**: it only costs time when a proof already
  failed, and it's bounded (200 ms).
- **CE-2. How property tests are written.** (a) `test` with parameters; (b) a `property`
  keyword; (c) theorems with `?` run by `test`. **Recommend (a).**
- **CE-3. Where generators live.** (a) built into the compiler, automatic, not customisable
  (for now); (b) a library interface derived per type. **Recommend (a) first, (b) for
  overrides in stage 4.**
- **CE-4. Polymorphic statements.** (a) instantiate type parameters at `Nat` and say so; (b)
  skip them. **Recommend (a).**
- **CE-5. Report on a failing proof.** (a) a note on the existing error; (b) a separate
  warning. **Recommend (a).**
- **CE-6. Searching every theorem as it's typed (D570 (b)).** (a) keep it later, and offer
  `check --counterexamples` meanwhile; (b) do it in stage 2. **Recommend (a).**

## 12. Risks

- **Time.** A slow checker (a statement that sorts long lists) can eat the budget on few
  inputs. Mitigation: count-first budget, per-input step limit, background in the LSP.
- **False confidence.** Silence on a failing proof could be read as "true". Mitigation:
  silence is the *absence* of a note, and passing property tests are worded as evidence.
- **Invariants.** Generated values that break a type's invariant give false counterexamples.
  Mitigation: proof fields decided (§5.4), library types built through their own functions,
  reference confirmation.
- **Statement capture.** The elaborator throws a failed declaration away today
  (`module.rs:401-405` [checked]); keeping its statement must not let anything else see it.
  Mitigation: keep it in the driver's side table only, never in the globals the next
  declaration sees.
- **Decision coverage.** Some hypotheses users write (`List.Sorted`, custom `Prop`
  definitions) may not be found decidable by today's search (§3, gaps). Mitigation: stage 1
  measures how many of the program's and the library's theorems are in scope, and reports it.

## Sources

- **[I1]** L. C. Paulson, T. Nipkow, M. Wenzel, *From LCF to Isabelle/HOL*, Formal Aspects of
  Computing, 2019; arXiv:1907.02836, §6 "Counterexample Search" (6.1 Quickcheck, 6.2 Nitpick).
  <https://arxiv.org/pdf/1907.02836>. Read (PDF text extracted).
- **[L1]** Plausible README. <https://github.com/leanprover-community/plausible>. Read.
- **[L2]** Plausible, `Plausible/Testable.lean`.
  <https://raw.githubusercontent.com/leanprover-community/plausible/main/Plausible/Testable.lean>.
  Read.
- **[L3]** Plausible, `Plausible/Tactic.lean`.
  <https://raw.githubusercontent.com/leanprover-community/plausible/main/Plausible/Tactic.lean>.
  Read.
- **[L4]** Plausible, `Plausible/Arbitrary.lean`.
  <https://raw.githubusercontent.com/leanprover-community/plausible/main/Plausible/Arbitrary.lean>.
  Read.
- **[L5]** Plausible, `Plausible/DeriveArbitrary.lean`.
  <https://raw.githubusercontent.com/leanprover-community/plausible/main/Plausible/DeriveArbitrary.lean>.
  Read.
- **[Q1]** QuickChick README. <https://github.com/QuickChick/QuickChick>. Read.
- **[Q2]** QuickChick, `doc/QuickChickInterface.v`.
  <https://raw.githubusercontent.com/QuickChick/QuickChick/master/doc/QuickChickInterface.v>.
  Read.
- **[Q3]** Z. Paraskevopoulou, A. Eline, L. Lampropoulos, *Computing Correctly with Inductive
  Relations*, PLDI 2022. <https://pldi22.sigplan.org/details/pldi-2022-pldi/40/Computing-Correctly-with-Inductive-Relations>.
  Abstract only (via search), not the full paper.
- **[H1]** QuickCheck 2.19 documentation, `Test.QuickCheck`.
  <https://hackage-content.haskell.org/package/QuickCheck-2.19.0.0/docs/Test-QuickCheck.html>.
  First part read.
- **[H2]** SmallCheck package page. <https://hackage.haskell.org/package/smallcheck>. Read.
- **[H3]** LeanCheck package page. <https://hackage.haskell.org/package/leancheck>. Read.
