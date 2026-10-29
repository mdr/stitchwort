# Proposal: `decide`, proofs that check every case of a finite statement

**Sources: 23 consulted, 7 read in full as whole documents and 12 more read as whole named
sections, 4 not read** (listed under [Sources](#sources); a claim resting on a section names the
section). Dafny was not consulted at all.

**Status:** draft 1, 29 October 2026. Design only: nothing in the compiler changes. Tickets
SW-800 (`decide`) and SW-807 (a derived list of every value). Prototypes, each checked with
`stitchwort check --no-cache`, are in [decide/](decide/). Three decisions for Matt are in
[§9](#9-decisions-for-matt).

Labels, as in the other notes:

- **[checked: file:line]**: read in the Stitchwort source or docs, at `b02ec6ca`;
- **[run]**: a prototype in `decide/`, checked on 29 October 2026 with the release CLI built
  from main that day (`target/release/stitchwort`, 19:21); times are `STITCHWORT_TIMINGS=decls`,
  one run, elaboration ms + kernel ms;
- **[cited: S]**: read in source S under [Sources](#sources);
- **[inferred]**: my reasoning from checked or cited facts;
- **[unverified]**: believed, not confirmed.

## The short answer

- **The motivating proofs don't need a new proof word.** Today's `cases` (built 26 October,
  two days before day 12 was written) proves day 12's 16-case truth table and day 21's
  25-case `tabulateSame` as one word each, in about 1 ms and 3 ms **[run]**. Day 21's eleven
  `Inr (Inr (…))` membership proofs become one `cases` on the `Bool` form plus
  `List.memContains` **[run]**. A closed decidable goal (Lean's `decide` with no variables) is
  already provable through `auto` **[run]**.
- **Lean's `decide` is what `auto` already is.** Both find the goal's `Decidable` instance,
  evaluate it, and leave a proof term the kernel evaluates again (`of_decide_eq_true` in Lean,
  `Decidable.fromYes d Trivial` here) [cited: L2; checked: crates/elab/src/auto.rs:20-23].
  Lean's `decide` refuses goals with free variables [cited: L2; L3 lines 24-33]; the variables are
  what the AoC proofs have.
- **Recommendation: no `decide` word now; extend `cases` and close SW-800 with it** (option
  (d), [§6](#6-recommendation-extend-cases-and-derive-finite)). Two small additions: a
  leaf closer that runs the goal's decision procedure (so `key ∈ numericKeys` closes once
  `key` is a constructor), and splitting a finite-typed variable of the statement when the
  goal isn't stuck on anything (so `cases` reaches `key` inside a disjunction). Then convert
  days 12 and 21. Nothing new is trusted: the proof is `match`es, `rfl`s and `fromYes` terms
  the kernel re-checks.
- **SW-807 yes, as a library interface `Finite T` with a derived instance** for types whose
  constructors' fields are all finite (enumerations, `Arrow Direction | Activate`, records of
  `Bool`s). Its completeness proof replaces day 21's hand-written ones directly, and its
  generic lemma `Finite.check` is the route for statements too big for `cases`' 64 cases:
  2^16 cases took about 6 s by one `rfl` **[run]**.
- **Never a `native_decide`.** Lean admits each native result as a new axiom and trusts its
  compiler [cited: L2, L4]. Stitchwort's kernel evaluator is fast enough for every size the AoC
  proofs reach.

## 1. The motivating proofs

**Day 12, `rowEndsSplit`** (aoc/src/Aoc/Year2024/Day12/Proofs/Corners.sw:172-189, and its twin
`columnEndsSplit` at :192-209), written as 16 arms of `rfl`:

```
theorem rowEndsSplit: (plot: Bool) → (out: Bool) → (side: Bool) → (sideOut: Bool) →
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut)) = Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out)
  | False, False, False, False => rfl
  | False, False, False, True => rfl
  …                                     -- 12 more
  | True, True, True, True => rfl
```

The notes: "No decision procedure for `Bool`: the two 16-case truth tables in Corners.sw are 16
`rfl` clauses each, generated. And a wildcard in a `match` on three `Bool`s left `s ∧ False`
stuck, so `omega` failed until every case was written out" [checked: aoc/NOTES-2024.md:3570-3576].

**Day 21, `everyNumericKey`** (aoc/src/Aoc/Year2024/Day21/Proofs/Typing.sw:53-64):

```
theorem everyNumericKey: (key: NumericKey) → key ∈ numericKeys
  | Digit0 => Inl rfl
  | Digit1 => Inr (Inl rfl)
  …
  | Enter => Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl rfl))))))))))
```

with `everyDirectionKey` beside it (:66-71), and **`tabulateSame`**
(aoc/src/Aoc/Year2024/Day21/Proofs/Presses.sw:43-68), 25 arms of `rfl` over two
`DirectionKey`s for an arbitrary `costs` function. The notes: "No way to enumerate a finite
type. The proofs check facts for every pair of keys by computing over a list, then need every
key to be in it … What I did: wrote the lists, the membership proofs and the 25 arms by hand"
[checked: aoc/NOTES-2024.md:6788-6797].

Two different kinds of statement are here, and the difference decides the design:

- `rowEndsSplit` is **closed once its variables are fixed**: each case computes to `n = n`.
- `tabulateSame` is **not**: `costs` stays a variable, so each case is `costs (Arrow Up)
  (Arrow Up) = costs (Arrow Up) (Arrow Up)` after computing, true by conversion but not by
  evaluating a `Bool`. A `decide` that evaluates a decision procedure can't prove it: `==` on
  `costs from to` is stuck on `costs` [inferred]. Splitting and then computing can.

## 2. What Stitchwort has today

**`auto` is Lean's `decide` for closed goals.** For `[auto h: P]` the elaborator finds a
decision procedure for `P`, runs it at compile time, and on `Yes` writes `Decidable.fromYes d
Trivial`, "which the kernel re-checks by running `d` itself"; `No` is `E-AUTO-FALSE`, stuck is
`E-AUTO-STUCK` [checked: crates/elab/src/auto.rs:9-23; docs/core.md:288-294]. Membership in a
literal list decides through a chain of `Decidable.or` [checked: auto.rs:58-61]. A one-line
helper makes it a proof word **[run: decide/closed.sw]**:

```
def byDecision [p: Prop] [auto h: p]: p := h

theorem enterIn: Enter ∈ keys := byDecision        -- checks
theorem enterNot: Enter ∈ [Digit0, Digit1] := byDecision
-- [E-AUTO-FALSE] Error: `Digit0 = Enter ∨ Digit1 = Enter ∨ Void` is false
```

**`cases` is the truth-table method for open goals.** It splits on what the goal is stuck on
(a value of a type with two or more constructors, not recursive, not an indexed family, not a
proposition), and closes each case by computation, a contradiction, a hypothesis, `t` for `cases
in t`, or `omega`; at most 64 cases (`E-CASES-BUDGET`) [checked: docs/syntax.md:1631-1658;
crates/elab/src/cases.rs:10-43, :62]. simp.md already called it "the truth-table method, and its
cost is exponential in the number of atoms" [checked: docs/proposals/simp.md:539-543, "That is the truth-table method" at :542], and
named `decide` as a rejected name for it because `auto` already runs decision procedures
[checked: simp.md:833-838].

**What the prototypes show** (all **[run]**, files in [decide/](decide/)):

| proof | how | result | time |
|---|---|---|---|
| day 12 `rowEndsSplit` | `cases` | checks | 0.6 + 0.3 (16,701 steps, 519 nodes) |
| the same, 16 hand arms | as written | checks | 0.3 + 0.3 (12,915 steps, 107 nodes) |
| day 21 `tabulateSame` | `cases` | checks | 1.6 + 1.0 |
| day 21 `everyNumericKey` | `cases` | **`E-CASES`**: "found nothing to split on" | |
| the same, through `Bool` | `numericKeys.contains key = True := cases`, then `List.memContains` | checks | 0.7 + 0.6, then 0.4 + 0.1 |
| six `Bool`s, every one mattering (64 cases) | `cases` | checks | 8.0 + 3.7 (5,938 nodes) |
| seven `Bool`s (128 cases) | `cases` | `E-CASES-BUDGET` | |
| day 12 as option (b), by hand | `List.all` over `[False, True]` four times, one `rfl`, `Finite.check` four times | checks | check 0.5 + 0.2; statement 1.2 + 0.6 |
| 2^10, 2^14, 2^16 cases | one `rfl` on a nested `List.all` | checks | 37 + 29; 773 + 596; 3485 + 2626 |

`everyNumericKey` fails because `key ∈ numericKeys` computes to a disjunction of propositions,
`Digit0 = key ∨ Digit1 = key ∨ …`, which isn't stuck on `key`: nothing in it is a `case` on a
value [run; checked: syntax.md:1652, "doesn't take apart … propositions"].

**Failure reporting is already what SW-800 asks for.** A false truth table (the concave term
left out) gives [run]:

```
[E-CASES] Error: `cases` can't close the case plot = True, out = False, side = True, sideOut = True
  Note 1: goal: 1 = 0
  Note 3: 4 other cases were closed (4 by computation)
  Note 4: this statement is false; a counterexample:
            plot = True
            out = False
            side = True
            sideOut = True
          `Bool.toNat (…) = Bool.toNat (convex plot out side)` is false:
            left:  1
            right: 0
```

The failing case is named by its splits, and the counterexample search (built, D1154) adds the
input with both sides [checked: syntax.md:1223-1247]. Lean's `decide` says only that "the
proposition … is false", without the case [cited: L1 lines 148-153; L2].

## 3. How other languages do it

One line each first; the details follow.

| system | what the user writes | who checks | failure shows the case? | limit | trusted |
|---|---|---|---|---|---|
| Lean 4 `decide` | `by decide` on a closed goal | elaborator `whnf`, then kernel | no: "is false" | reduction cost; WF recursion and `Eq.rec` get stuck | kernel only |
| Lean 4 `decide +kernel` | the same | kernel only, once | no | as above | kernel only |
| Lean 4 `native_decide` | `by native_decide` | compiled code | no | compile time | compiler, `@[implemented_by]`, a new axiom per use |
| Lean 4 `bv_decide` | `bv_decide` on `BitVec`/`Bool` | SAT solver, LRAT checked | yes, an assignment | SAT | code generator, axioms |
| Mathlib `Fintype` | `deriving Fintype`; `decide` over `∀ a` | kernel, through `decidableForallFintype` | no | cardinality | kernel only |
| Rocq | `vm_compute; reflexivity`, `native_compute`; casts `<:` `<<:` | kernel's VM, or OCaml-compiled code | no [inferred] | 5-10 s before `native_compute` pays | VM; OCaml compiler for native [inferred] |
| MathComp | `[forall x, P]` with `forallP` | reflection lemmas | no [inferred] | | kernel |
| Agda | `from-yes (all? P?)` | type checker's normalisation | no: a type mismatch [inferred] | | type checker |
| Idris 2 | `Oh : So (f x)`, `ItIsYes` | type checker | no [inferred] | | type checker |
| Isabelle | `code_simp`, `normalization`, `eval` | simplifier; NbE; generated ML | | | kernel; NbE stack; code generator setup |
| F* | `assert` sent to Z3 | SMT solver, with fuel | | `--fuel` unfoldings | Z3 [inferred] |
| Haskell | `deriving (Enum, Bounded)` | no proofs | | enumerations only | |

**Lean 4.** `decide` "attempts to prove the main goal … by synthesizing an instance of
`Decidable p` and then reducing that instance … The target is not allowed to contain local
variables or metavariables"; `+revert` moves them into the target first; `+kernel` "reduces the
`Decidable` instance only once instead of twice"; `+native` "uses the native code compiler …
admitting the result via an axiom … it depends on the correctness of the Lean compiler and all
definitions with an `@[implemented_by]` attribute" [cited: L1 docstring, L2]. The default mode
evaluates twice, in the elaborator (`whnf dec`) and again in the kernel; on failure it blames the
`Decidable` instance reduction got stuck on, with hints for `Eq.rec` and `Classical.choice`, and
on `false` reports only that the proposition is false [cited: L3, lines 101-194]. Instances
defined by well-founded recursion "might not work because evaluating them requires reducing
proofs" [cited: L1, L2]. `native_decide` compiles the closed `Bool`, runs it, and adds an axiom
`e = true` per use [cited: L4, lines 37-87]. Core has `Decidable (∀ x: Bool, p x)` as `p true &&
p false` [cited: L6, lines 34-39], so a `Bool` truth table with `+revert` is one `decide`
[inferred]. `bv_decide` "provides a counter-example" on failure and "trusts the correctness of the
code generator and adds a axioms asserting its result" [cited: L1 lines 1937-1966, L2].

**Mathlib.** `class Fintype (α) where elems : Finset α; complete : ∀ x : α, x ∈ elems`, and
`decidableForallFintype : Decidable (∀ a, p a)` from a decidable `p` [cited: M1]. The `Fintype`
derive handler takes structures and inductives that aren't recursive and have no indices; for an
enumeration it builds the list of constructors and proves `enumList[ctorIdx x]? = some x` by
`cases x <;> rfl`, so "the proofs are all linear complexity"; otherwise it maps the type to a
"proxy type" of sums and products and pulls `Fintype` back along an equivalence, assuming
`Fintype` for each type parameter [cited: M2]. The linear proof matters here: day 21's
`Inr (… (Inl rfl))` chains are quadratic in the number of constructors in total size [inferred].

**Rocq.** `vm_compute` "first normalizes the terms before comparing them", using bytecode;
`native_compute` compiles to OCaml and is "typically two to five times faster … but requires
considerably more overhead", worth it when the `vm_compute` time is "at least 5-10 seconds" and
input and output are small; both "ignore Opaque markings" and add "a single explicit cast to the
proof term to tell the kernel which reduction engine to use" [cited: R1]. The casts `<:` and
`<<:` say "the virtual machine will be used to type check" and "compilation to OCaml will be used
to type check" [cited: R2]. So the kernel's check runs on the VM or on compiled OCaml, which are
then trusted, with no axiom to show for it [inferred from R1, R2]. MathComp's `finType` supplies
"a duplicate-free sequence of all the elements", with `[forall x, P]` as a boolean and `forallP`
reflecting it to `forall x, P x` [cited: R3, header]. MathComp locks `enum` (`HB.lock Definition
enum`) [cited: R3, the line after the header]; that this is to keep conversion from computing it
is [unverified].

**Agda.** `Dec` is a record of a `does : Bool` and a `proof : Reflects A does`, "so the boolean
part of the decision procedure [can] compute independently from the proof"; `from-yes a?` has
type `From-yes a?`, which is `A` when `a?` computes to `true because …` and `⊤` otherwise [cited:
A1]. `all? : Decidable P → Dec (∀ i → P i)` over `Fin n` is `P? zero ×? all? (P? ∘ suc)` [cited:
A2]. So `from-yes (all? P?)` is a proof by the type checker's normalisation, and a false one is a
type mismatch with `⊤`, naming no case [inferred].

**Idris 2.** `data So : Bool -> Type where Oh : So True`, with `choose`, `decSo`, and `IsYes :
Dec a -> Type` with `ItIsYes : IsYes (Yes prf)` [cited: I1, I2]. Writing `Oh` where `So (f x)` is
expected makes the type checker compute `f x` [inferred]. `DecEq` instances in base are written
by hand (`Bool`, `Nat`, `Maybe`, …) [cited: I3, lines 1-60]; whether a deriving exists elsewhere
is [unverified].

**Isabelle.** Evaluation has three engines: the simplifier ("fully symbolic evaluation and highest
trustablity"), normalisation by evaluation ("the stack of code to be trusted is considerable") and
ML ("a layered stack of code to be trusted, including a user's specific code generator setup …
soundness depends crucially on the correctness of the code generator setup"); as proof methods
they are `code_simp`, `normalization` and `eval` [cited: S1 §6]. Same trade-off as Lean's three
modes.

**F\*.** Goals go to Z3. Recursive functions are unfolded a bounded number of times, set by
`--fuel`; `assert (factorial 1 == 1)` fails at `--fuel 1` [cited: F1, "Recursive functions and
fuel"]. A truth table is a query to the solver, which is trusted [inferred]. How a failing
query reports its case wasn't read.

**Haskell.** `deriving Enum` is "only possible for enumerations (data types with only nullary
constructors)"; `Bounded` for enumerations or one-constructor types; "the first and last
constructors listed in the data declaration are the bounds" [cited: H1 §11.2, §11.3]. No proof
that the enumeration is complete: it is by construction. `DirectionKey = Arrow Direction |
Activate` gets neither [inferred]; Mathlib's handler would take it [inferred from M2].

**What to take.**

1. Lean, Rocq and Isabelle all offer evaluation that trusts more for speed, and all mark it as
   a trust cost. Stitchwort's measured sizes don't need it ([§2](#2-what-stitchwort-has-today)).
2. Lean's `decide` doesn't take variables; `+revert` turns them into `∀`, and instances for `∀`
   over finite types (`Bool` in core, any `Fintype` in Mathlib) evaluate it. That needs an
   enumeration with a completeness proof: SW-807.
3. Only the SAT-based tools (`bv_decide`) and Stitchwort's `cases` with the counterexample note
   name the failing case. Keep that.
4. Mathlib's linear-size completeness proof (through a constructor index) is the one to derive.

## 4. The options

**(a) `decide` by evaluating a `Decidable` instance, as Lean.** Library instances `Decidable ((b:
Bool) → P b)` and, with SW-807, `Decidable ((x: T) → P x)` for a `Finite T`; a word `decide` that
reverts the statement's finite variables and is `fromYes d Trivial`. Costs: the instance for `∀`
must be found by `auto`'s search, which today finds definitions whose result is `Decidable …` by
unification [checked: core.md:290], so a `∀` instance is new search territory [inferred]. It
can't do `tabulateSame` (§1). A failure is "is false"; finding the case means running something
else. Nothing new trusted.

**(b) A derived enumeration, `List.all`, and one soundness lemma.** `Finite T = { all: List T,
complete: (x: T) → x ∈ all }` and `Finite.check: List.all fin.all p = True → (x: T) → p x =
True` (both in decide/enumerate.sw, checked **[run]**). The statement must be a `Bool`
function; nesting per variable. Scales furthest by evaluation (2^16 in about 6 s) and its proof
term is small. Same limit as (a) on `tabulateSame`. Nothing new trusted.

**(c) Native evaluation, `native_decide`-style.** Run the `Bool` on the fast runtime (`crates/rt`)
or JS and admit the result. Both runtimes are untrusted today: "Its output can be wrong, but a
proof never depends on it" [checked: core.md:237]. This would put a runtime, and for JS Node, in
the trusted base, for statements the kernel already checks in seconds. Rejected.

**(d) Extend `cases`.** Already does the 16- and 25-case proofs, with the failing case and a
counterexample in the error, and handles open statements (`tabulateSame`). Missing: splitting a
variable the goal isn't stuck on (membership), closing a leaf that is a closed decidable
proposition, and more than 64 cases. Nothing new trusted.

## 5. Comparing them on the motivating proofs

| | (a) | (b) | (c) | (d) as proposed |
|---|---|---|---|---|
| `rowEndsSplit` | yes | yes, as a `Bool` statement | yes, trusted | yes, today |
| `tabulateSame` (open `costs`) | no | no | no | yes, today |
| `everyNumericKey` | yes | yes (it is `complete`) | yes | yes, with the two additions |
| shows the failing case | no | no (would need a search) | no | yes, today |
| past 64 cases | yes | yes, about 90 µs a case measured | yes | no; points to (b) |
| new trust | none | none | a runtime | none |

## 6. Recommendation: extend `cases`, and derive `Finite`

### 6.1 `cases` (closes SW-800)

**Syntax:** unchanged, `cases` and `cases in t`. No new keyword.

**Two additions** to crates/elab/src/cases.rs:

1. **A decision closer.** After the existing closers and before `omega`: if the case's goal is a
   proposition with a decision procedure and no free variables left in it that the procedure is
   stuck on, run it as `auto` does; `Yes` closes the case with `Decidable.fromYes d Trivial`
   (the kernel runs `d` again), `No` makes the case fail with "this case is false" and its
   splits. This closes `Digit3 = key ∨ …` once `key` is `Digit3`.
2. **Split a finite-typed variable of the statement when nothing is stuck.** Today a variable is
   split only when the goal is stuck on it. Add a last resort: when the goal isn't stuck and no
   closer proves it, split the latest variable in scope whose type is splittable (the same test
   as now: two or more constructors, not recursive, no indices) and that the goal mentions. Then
   `(key: NumericKey) → key ∈ numericKeys := cases` splits `key` and each case closes by (1).

**Types supported:** those `cases` splits: `Bool`, enumerations, constructor types whose fields
it then splits in turn (`Arrow Direction`), records of them. **Not** `Fin n` or bounded `Nat`
ranges: `Fin` is an indexed family and `Nat` is recursive, and `cases` takes apart neither
[checked: syntax.md:1652]. For those, (b) through `Fin.any`-style lemmas: std has `Fin.any` with
`Fin.anyElim` [checked: crates/elab/src/std/Fin/Fin.sw:98-111]; a `Fin.all` with its elimination
lemma is the matching piece, written by hand once. Products are covered by splitting each
component.

**Failure:** as now, `E-CASES` naming the case by its splits, with the counterexample note.
Decision-closer failures say "decided false" in that case's notes.

**Size limit:** the 64-case budget stays. Past it, `E-CASES-BUDGET` gets one more note when every
split variable has a `Finite` instance: "for statements this size, check every case by
computation: `Finite.check`" with the shape of the call. 64 cases cost 11.7 ms and 5,938 term
nodes **[run]**; raising the budget grows the proof term exponentially, where (b)'s stays small,
so the budget is not the knob to turn [inferred].

**Interactions.**

- *Opaque definitions:* a goal that calls an opaque definition without `unfolding` it is stuck
  on that call, which neither splitting nor deciding gets past [inferred from core.md:163-170].
  As for `rfl` today, the fix is `unfolding` or `f.unfold`.
- *Check cache:* nothing new; the proof is ordinary declarations, cached like any other
  [inferred from core.md:423].
- *Erasure:* the proofs are theorems, erased [checked: core.md:468].
- *Proof irrelevance:* unaffected. The closers write `rfl`, `J` and `fromYes` terms, which don't
  compare proofs [inferred]. For a `Finite` instance of a record with proof fields, completeness
  needs `DecEq.uniqueEq` as derived `==` already uses [checked: crates/elab/src/derive.rs:17-21];
  D1′ (proof-irrelevance.md, not built) would make that free.
- *Trust:* nothing added. The proof is the `match` tree `cases` writes now, plus `fromYes`
  terms that `auto` writes now.

**Then:** convert day 12's two truth tables and day 21's `tabulateSame`, `everyNumericKey`,
`everyDirectionKey` (each one word, [§2](#2-what-stitchwort-has-today)), and say in
docs/syntax.md's `cases` section that it is the truth-table method, with a line on
`byDecision`-style closed goals. Whether to name `byDecision` in std is a build detail.

### 6.2 `Finite` (SW-807)

```
interface Finite (a: Type) = {
  all: List a,
  complete: (x: a) → x ∈ all
}

theorem Finite.check [auto fin: Finite a] (p: a → Bool) (checked: List.all Finite.all p = True) (x: a): p x = True
```

- **Derived**, as `DecEq` is (generated source, elaborated and checked, derive.rs:1-7 style
  [checked]), for a declared type that is not recursive, has no indices and isn't a proposition,
  whose data fields all have `Finite` (enumerations; `Arrow (direction: Direction)`; records of
  them); proof fields only if they're equations in `DecEq` types. `all` is the constructors in
  declaration order, each applied to its fields' `all`s (a `flatMap`), so it agrees with derived
  `Ord`'s order [checked: syntax.md, Interfaces, "constructors in the order they're declared"].
- **The completeness proof** goes through the constructor's position, as Mathlib's does: the
  derived `T.%tag` already exists for `DecEq` [checked: derive.rs:33-35]; prove `List.get? all
  (T.%tag x) = Some x` by one `match` with `rfl` arms, then membership from it, so the term is
  linear in the constructors, not quadratic like day 21's chains [cited: M2; inferred].
- **Library instances** for `Bool`, `Ordering`, `Option a`, pairs; `Fin n` by hand.
- **Uses:** `everyNumericKey` is `Finite.complete`; day 21's `fits` can be stated over
  `Finite.all`; statements past 64 cases use `Finite.check` (decide/enumerate.sw shows the
  pattern for day 12).
- No `nodup` field: nothing here needs a count. A cardinality (pigeonhole, day 6's need,
  NOTES-2024.md:1449-1460) would add one later [checked; inferred].

## 7. Assumptions

The recommendation depends on these; if one is wrong, so is the part that rests on it.

1. The AoC statements over finite types stay at or below about six `Bool`s' worth of cases
   (16 and 25 so far, [§1](#1-the-motivating-proofs)). Past 64, (b) is the fallback and works
   ([run], 2^16 in about 6 s).
2. The decision closer can reuse `auto`'s search for a single goal from inside `cases` without
   reorganising either (auto.rs runs obligations in rounds after a declaration is elaborated,
   auto.rs:36-41, "retried in rounds" at :40) [checked; that it reuses cleanly is inferred].
3. Splitting an unstuck variable as a last resort doesn't change any existing `cases` proof:
   today those cases are errors, so only failing proofs reach it [inferred from cases.rs:350-357, the "isn't stuck" error at :355].
4. A derived `Finite` costs little at declaration time for every eligible type. `DecEq`'s
   derivation is the precedent; not measured for `Finite` [unverified]. If it does cost, derive
   it on first use or on request.
5. Day 21's quadratic membership terms are a real cost only at larger sizes; at 11 they cost 0.4 +
   0.1 ms through `memContains` [run]. So the linear proof is about larger enumerations, not
   these.

## 8. What was not reached

- Dafny was not consulted; F* only its SMT-fuel chapter.
- Lean's `Fin n` instance for `∀` in core was searched for and not found
  (Init/Data/Nat/Basic.lean, by grep only) [unverified either way].
- No prototype of the two `cases` additions (they need compiler changes, out of scope here).
- The derived `Finite`'s completeness proof through `T.%tag` wasn't prototyped; enumerate.sw
  writes `Bool`'s by hand.

## 9. Decisions for Matt

**D1960. Close SW-800 by extending `cases` (a decision closer at the leaves, and splitting a
finite variable when nothing is stuck), with no new `decide` word?** [yes]. Alternative: a `decide`
word evaluating `Decidable` instances as Lean does (option (a)); it can't do day 21's
`tabulateSame` and doesn't show the failing case.

**D1961. Build SW-807 as a derived `Finite` interface (a list of every value with a completeness
proof) and `Finite.check`, for non-recursive constructor types with finite fields?** [yes, after
D1960's conversion of days 12 and 21]. Alternative: enumerations only, as Haskell's `Enum`; day
21's `DirectionKey` has a field and would be left out.

**D1962. Never add native evaluation as a proof (`native_decide`)?** [never, until a proof needs
more than about 10 s of kernel evaluation; then revisit with that proof]. Alternative: trust the
fast runtime for closed `Bool`s, adding it to the trusted base.

## Sources

Fetched 29 October 2026 into the lane's scratch directory; line numbers are of those copies.

**Read in full (whole documents):**

- [L3] Lean `src/Lean/Elab/Tactic/Decide.lean` (205 lines): https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Elab/Tactic/Decide.lean
- [L4] Lean `src/Lean/Meta/Native.lean` (87 lines): https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Meta/Native.lean
- [M1] Mathlib `Mathlib/Data/Fintype/Defs.lean`: https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/Data/Fintype/Defs.lean
- [M2] Mathlib `Mathlib/Tactic/DeriveFintype.lean`: https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/Tactic/DeriveFintype.lean
- [A1] Agda stdlib `src/Relation/Nullary/Decidable/Core.agda`: https://raw.githubusercontent.com/agda/agda-stdlib/master/src/Relation/Nullary/Decidable/Core.agda
- [I1] Idris 2 `libs/base/Data/So.idr`: https://raw.githubusercontent.com/idris-lang/Idris2/main/libs/base/Data/So.idr
- [I2] Idris 2 `libs/base/Decidable/Decidable.idr`: https://raw.githubusercontent.com/idris-lang/Idris2/main/libs/base/Decidable/Decidable.idr

**Read in full as named sections of a larger document** (the rest not read):

- [L1] Lean `src/Init/Tactics.lean`: the `DecideConfig`, `decide`, `native_decide` docstrings (lines 1426-1541) and the `bv_decide` family (1919-1974): https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Tactics.lean
- [L2] Lean reference, Tactic Reference, §14.5.18 Decision Procedures (`decide`, `native_decide`, `omega`, `bv_decide`): https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/
- [L5] Lean `src/Init/Prelude.lean`: the `Decidable` docstring and class, `of_decide_eq_true` (lines 1125-1235): https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Prelude.lean
- [L6] Lean `src/Init/Data/Bool.lean`: lines 30-47 (`Decidable (∀ x, p x)` and `(∃ …)` over `Bool`) and 510-523: https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Data/Bool.lean
- [R1] Rocq 9.2 reference, "Applying conversion rules" and "Fast reduction tactics: vm_compute and native_compute": https://rocq-prover.org/doc/V9.2.0/refman/proofs/writing-proofs/equality.html
- [R2] Rocq 9.2 reference, "Type cast": https://rocq-prover.org/doc/V9.2.0/refman/language/core/definitions.html
- [R3] MathComp `boot/fintype.v`: the header comment (lines 1-160) and the `isFinite`/`Finite` declarations after it (to line 200): https://raw.githubusercontent.com/math-comp/math-comp/master/boot/fintype.v
- [A2] Agda stdlib `src/Data/Fin/Properties.agda`: `any?`, `all?` and the note after them (lines 1015-1050): https://raw.githubusercontent.com/agda/agda-stdlib/master/src/Data/Fin/Properties.agda
- [I3] Idris 2 `libs/base/Decidable/Equality.idr`: lines 1-60: https://raw.githubusercontent.com/idris-lang/Idris2/main/libs/base/Decidable/Equality.idr
- [S1] Isabelle, "Code generation from Isabelle/HOL theories" (codegen.pdf), §6 Evaluation: https://isabelle.in.tum.de/doc/codegen.pdf
- [F1] F* book, "Understanding how F* uses Z3": the introduction and "Recursive functions and fuel": https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html
- [H1] Haskell 2010 Report, chapter 11, the introduction and §11.1-11.3: https://www.haskell.org/onlinereport/haskell2010/haskellch11.html

**Not read** (searched with grep, or snippets only; nothing above rests on them):

- Lean `src/Init/Core.lean`, `src/Init/Data/Nat/Basic.lean`, `src/Lean/Elab/Tactic/ElabTerm.lean` (grep for `decide` and bounded-`∀` instances only).
- One web search for F*'s `assert_norm` (result snippets only; no usable source).

**Stitchwort**, at `b02ec6ca`: README.md; DESIGN.md §13; docs/core.md in full; docs/syntax.md
(Interfaces, Expressions, Goals, Counterexamples, `calc`, `rewrite`, `omega`, `ring`, `cases`);
docs/proposals/simp.md (summary, §5, §8.3, §9); counterexample-search.md (§0);
literal-match-facts.md (the problem); proof-irrelevance.md (status, §0);
docs/research/proof-automation.md (C10, C11, §5.4, which this note supersedes: its
"[unverified]" on Lean's `∀`-over-`Bool` instance is now [cited: L6]); aoc/NOTES-2024.md (day 12
§6, day 21 §2); the day 12 and day 21 proofs cited inline; crates/elab/src/cases.rs and auto.rs
(headers), derive.rs and derive_ext.rs (headers), std/Fin/Fin.sw. Not read: omega.md,
nested-data-types.md, opaque-definitions.md and check-cache.md (only core.md's summaries of
them).

**Prototypes** ([decide/](decide/)): `cases_today.sw` (day 12 by `cases`), `day21_today.sw`
(`tabulateSame`, `containsNumericKey`, `everyNumericKey`), `cases_budget.sw` (64 cases; the
128-case error in a comment), `closed.sw` (`byDecision`), `enumerate.sw` (option (b) by hand for
day 12), `scale.sw` (2^10 and 2^14 by one `rfl`).
