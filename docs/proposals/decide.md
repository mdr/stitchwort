# Proposal: `decide`, proofs that check every case of a finite statement

**Sources: 23 consulted, 7 read in full as whole documents and 12 more read as whole named
sections, 4 not read** (listed under [Sources](#sources); a claim resting on a section names the
section). Dafny was not consulted at all.

**Status:** draft 2, 30 October 2026 (draft 1: 29 October), revised after an external review
([decide/review-1.md](decide/review-1.md), verbatim; how each point was addressed is
[§11](#11-review-1-and-how-it-was-addressed)), approved for revision as D2034. Tickets SW-800
(`decide`) and SW-807 (a derived list of every value). Prototypes, each checked with `stitchwort
check --no-cache`, are in [decide/](decide/). The three decisions in [§10](#10-decisions-for-matt)
are decided (yes); the stage plan is [§12](#12-stage-plan). **SW-800's three parts are built**:
[§13, As built](#13-as-built-sw-800). The sections before §13 are the design as written.

Labels, as in the other notes:

- **[checked: file:line]**: read in the Stitchwort source or docs: at `09118ced` for what draft 2
  adds (§6.1, §6.2's `nodup` paragraph, §7, §8), at `b02ec6ca` for citations carried from draft 1;
- **[run]**: a prototype in `decide/`, or a scratch file named in the text, checked with the
  release CLI built from main (draft 1: 29 October, 19:21; draft 2: 30 October, 16:29, at
  `09118ced`), under `dev/memguard --cap-gb 2` and `timeout`; times are
  `STITCHWORT_TIMINGS=decls`, one run, elaboration ms + kernel ms;
- **[cited: S]**: read in source S under [Sources](#sources);
- **[inferred]**: my reasoning from checked or cited facts;
- **[unverified]**: believed, not confirmed.

## The short answer

- **The motivating proofs don't need a new proof word.** Today's `cases` proves day 12's 16-case
  truth table and day 21's 25-case `tabulateSame` as one word each, in about 1 ms and 3 ms
  **[run]**, once their variables are bound before the colon. As the files write them, after the
  colon, `:= cases` fails ("found nothing to split on") **[run, on the real Corners.sw]**. A closed
  decidable goal is already provable through `auto` (`byDecision`) **[run]**.
- **Lean's `decide` is what `auto` already is.** Both find the goal's `Decidable` instance,
  evaluate it, and leave a proof term the kernel evaluates again (`of_decide_eq_true` in Lean,
  `Decidable.fromYes d Trivial` here) [cited: L2; checked: crates/elab/src/auto.rs:20-23].
  Lean's `decide` refuses goals with free variables [cited: L2; L3 lines 24-33]; the variables are
  what the AoC proofs have.
- **Recommendation: no `decide` word; extend `cases` in three parts and close SW-800 with it**
  ([§6.1](#61-cases-closes-sw-800)), each part running only where `cases` today reports an error,
  so no proof that checks today changes:
  1. **`cases` introduces the goal's leading binders** when nothing proves the `Π` goal as it
     stands, so `theorem foo: (x: Bool) → … := cases` works as `theorem foo (x: Bool): … :=
     cases` does (review R1);
  2. **a decision closer, after `omega`**: a case whose goal's decision procedure evaluates to
     `Yes` closes with the `fromYes` term `auto` writes; `No` doesn't fail the case, since its
     hypotheses may still contradict each other **[run]**;
  3. **a fallback split**: when the goal is stuck on nothing, split the mentioned splittable
     variable with the fewest cases, ties to the latest bound (review R2), and say so in the
     diagnostics.

  Then convert days 12 and 21 as written. Nothing new is trusted.
- **SW-807 yes, as a library interface `Finite T = { all, complete }` with a derived instance**,
  no duplicate-freedom field (review R3), plus `Finite.check` for statements past `cases`' 64
  cases (2^16 cases took about 6 s by one `rfl` **[run]**), and `byDecision` made an official std
  idiom.
- **Native evaluation: not now rather than never.** Not until measured kernel evaluation is a
  material limitation on real programs; about 10 s in one proof is the trigger to investigate
  ([§7](#7-native-evaluation)). Faster checking doesn't have to cost trust (certificate checking),
  but `native_decide`-style evaluation does [cited: L1, L2, L4].

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

**The statement's form matters** [run, by the coordinator on the real file, 29 October 2026].
In `Corners.sw` as written, `rowEndsSplit`'s variables are bound after the colon
(`theorem rowEndsSplit: (plot: Bool) → … → …`). Replacing its 16 arms with `:= cases` in that
form fails with `E-CASES`: "the goal isn't stuck on anything `cases` can take apart". Restated with
the variables before the colon (`theorem rowEndsSplit (plot: Bool) (out: Bool) (side: Bool)
(sideOut: Bool): … := cases`), as the prototype writes it, the real file's
`Aoc.Year2024.Day12.Proofs` checks with `--no-cache`. So converting days 12 and 21 means
restating those theorems too, and a `cases` that introduced leading `Π` variables itself would
remove the difference. The file was restored afterwards; nothing in `aoc/` changed. Draft 2
ran this again, with the output, and designs that introduction: [§6.1.1](#611-part-1-cases-introduces-the-goals-leading-binders-r1).

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
| Lean 4 `bv_decide` | `bv_decide` on `BitVec`/`Bool` | SAT solver; its LRAT proof checked in Lean | yes, an assignment | SAT | code generator, axioms; not the solver |
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
   Speed by trusted evaluation is one route, not the only one: certificate checking
   (`bv_decide`'s untrusted SAT solver) is another ([§7](#7-native-evaluation)).
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
the trusted base, for statements the kernel already checks in seconds. Not now ([§7](#7-native-evaluation)).

**(d) Extend `cases`.** Already does the 16- and 25-case proofs, with the failing case and a
counterexample in the error, and handles open statements (`tabulateSame`). Missing: introducing the
variables bound after the colon, closing a leaf whose decision procedure says `Yes`, splitting a
variable the goal isn't stuck on (membership), and more than 64 cases. Nothing new trusted.

## 5. Comparing them on the motivating proofs

| | (a) | (b) | (c) | (d) as proposed |
|---|---|---|---|---|
| `rowEndsSplit` | yes | yes, as a `Bool` statement | yes, trusted | yes: today before the colon; as written, with part 1 |
| `tabulateSame` (open `costs`) | no | no | no | yes: today before the colon; as written, with part 1 |
| `everyNumericKey` | yes | yes (it is `complete`) | yes | yes, with parts 1-3 |
| shows the failing case | no | no (would need a search) | no | yes, today |
| past 64 cases | yes | yes, about 90 µs a case measured | yes | no; points to (b) |
| new trust | none | none | a runtime | none |

## 6. Recommendation: extend `cases`, and derive `Finite`

### 6.1 `cases` (closes SW-800)

**Syntax:** unchanged, `cases` and `cases in t`. No new keyword.

**Three additions** to crates/elab/src/cases.rs, all in `node` (cases.rs:212-271), the function
that closes or splits one case. Today `node` tries, in order [checked: cases.rs:212-270]:
computation, contradiction, taking an equation apart, a hypothesis, `t`; then it looks for an atom
the goal is stuck on and splits it (trying `omega` first when the atom is a whole side of the
goal); with no atom, `omega`; then `E-CASES`. Draft 2 adds three steps between that last `omega`
and `E-CASES`, in this order:

```
1-5.  computation, contradiction, take apart, hypothesis, `t`     -- as today
6.    split what the goal is stuck on                             -- as today
7.    omega                                                       -- as today
8.    the decision closer: `Yes` closes; `No` or stuck goes on    -- new (part 2)
9.    the goal is a Π: introduce its leading binders, back to 1   -- new (part 1)
10.   split a mentioned variable: fewest cases, then latest       -- new (part 3)
11.   E-CASES                                                     -- as today
```

Every new step runs only where today's `cases` reports an error for the case (`E-CASES`, or for
`cases in t` the error `t` gave), so **no proof that checks today
changes its term, its time or its outcome** [inferred from cases.rs:265-270: the only path to
step 8 is the one that now ends in `open_case`]. The parts are numbered in the order they are built
(§12), not the order they run.

#### 6.1.1 Part 1: `cases` introduces the goal's leading binders (R1)

**The evidence.** All five motivating theorems bind some of their variables after the colon:
`rowEndsSplit` and `columnEndsSplit` all four (Corners.sw:172, :192), `everyNumericKey` and
`everyDirectionKey` theirs (Typing.sw:53, :66), and `tabulateSame` binds `costs` before the colon
and `from`, `to` after (Presses.sw:43) [checked]. With the variables after the colon, `:= cases`
fails. Run on the real file (Corners.sw with `rowEndsSplit`'s 16 arms replaced, in this worktree,
restored afterwards; `stitchwort check --no-cache Aoc.Year2024.Day12.Proofs`) **[run]**:

```
[E-CASES] Error: `cases` found nothing to split on, and nothing closes the goal
     ╭─[ aoc/src/Aoc/Year2024/Day12/Proofs/Corners.sw:174:3 ]
 174 │   cases
     │     ╰──── this `cases`
     │ Note 1: goal: (plot: Bool) → (out: Bool) → (side: Bool) → (sideOut: Bool) → Bool.toNat ((plot && not out) && not (side && not sideOut)) = Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out)
     │ Note 2: the goal isn't stuck on anything `cases` can take apart, and neither `rfl`, a contradiction, a hypothesis nor `omega` proves it; give this case's proof as `cases in t`
```

and with the binders introduced by hand, `plot out side sideOut => cases`, the same namespace
`checked 3 namespaces of aoc`, `rowEndsSplit` at 0.7 + 0.3 ms, 16,669 steps, 519 nodes **[run]**.
The prototype [decide/binders.sw](decide/binders.sw) has both checking forms (before the colon,
16,701 steps; the lambda, 16,669; 519 nodes each) and, in comments, the two failing ones (after the
colon; and split, two before and two after, which fails the same way with the goal `(side: Bool) →
(sideOut: Bool) → …`) **[run]**.

**Why it fails.** The atom search walks equations, constructors, data and stuck calls, and stops at
anything else (`Finder::walk`, cases.rs:807-875, `_ => Ok(None)`), so on a `Π` it finds nothing
[checked]. Implicit and `auto` binders already work: the checker introduces those before any
expression is checked against the type (check.rs:3355-3363, "Implicit parameters are introduced
automatically"), so `theorem implicitAfter: [b: Bool] → not (not b) = b := cases` checks today
[checked; run: binders.sw].

**Where it goes: after the closers, not first.** A `Π` goal is proved today in three ways, all in
binders.sw **[run]**: by a hypothesis of exactly that type (`byHyp`), by `omega` refuting the
hypothesis of `P → Void` (`notLess`), and by the term after `in` checked against the whole goal
(`byTerm: … := cases in Bool.orComm`). Introducing first would break `byHyp`: its goal would become
`f a b = f b a`, which no hypothesis is, and that form fails today with `E-CASES` ("found nothing
to split on") **[run]**. Introducing as step 9 keeps all three, because steps 1-8 see the `Π` goal
as now. Since it only replaces an error, the after-colon form then proves a superset of what the
before-colon form proves.

**The design.**

- **Which binders:** every leading binder of the goal, explicit, implicit and `auto`, up to the
  first thing that isn't a `Π`, whatever the binder's type: `costs: Costs` (a function) is
  introduced as a variable, as it is before the colon, and is never split. No stopping at a
  binder whose type isn't splittable: the stopping rule that matters is which variables get
  *split*, and that stays steps 6 and 10. Hypotheses (`b = True → …`) are introduced too, so the
  contradiction and hypothesis closers can use them, as they do before the colon. Implicit and
  `auto` binders are introduced hidden, as the checker does (check.rs:3357-3362); this matters
  only for `(x: A) → [y: B] → …`, where the checker's rule has already run.
- **At any node, not just the first.** Step 9 is part of `node`, so a goal that becomes a `Π`
  after a split (`if b then ((x: Bool) → P x) else Q`) is introduced too.
- **Names in diagnostics:** a named binder is bound under its name, as `cx.bind` does for a
  lambda's parameter (check.rs:3408, "`cx.bind(&first.text, …)`"), so the path of an open case,
  the hypotheses note and `cases in t` all use the written names (`plot = True, out = False, …`),
  the same as before the colon. A binder without a name (`A → B` makes a `Π` named `_`,
  check.rs:1404-1409) is bound under an internal name, `%hyp1`, `%hyp2`, … (like the split
  equations' `%case`, cases.rs:66, not a name a program can write), so the closers see it, and is
  shown as `hypothesis 1 (unnamed): <type>`. A binder that reuses an outer name shadows it, as a
  lambda's does. The counterexample note is unaffected: it is built from the statement, and
  already names after-colon variables (`badAfter: (a: Bool) → (b: Bool) → (a ∧ b) = a := a b =>
  cases` reports `a = True`, `b = False`) [run, in the scratch directory].
- **The proof term:** one `Term::Lam(name, icit, body)` per introduced binder, as the lambda case
  of `check` builds (check.rs:3398-3421), with `body` the rest of `node` under the extended
  context. It is the term `plot out side sideOut => cases` elaborates to: same 519 nodes as
  before the colon **[run]**. Introduction makes no cases and costs no budget.

**Then** the five motivating theorems convert as written, without restating their signatures.

#### 6.1.2 Part 2: the decision closer, after `omega` (review §2)

At step 8: find the goal's decision procedure as `auto` does (auto.rs:9-23), evaluate it, and on
`Yes` close the case with `Decidable.fromYes d Trivial`, which the kernel evaluates again
[checked: auto.rs:20-23]. This closes `Digit3 = key ∨ …` once `key` is `Digit3`. It is the term
`auto` writes today, so nothing enters the trusted base; the review agrees (§2: "I see no trust
problem here").

**Two changes from draft 1**, both from measurement:

1. **`No` doesn't fail the case.** Draft 1 had `No` end the case with "this case is false". That is
   wrong where the case's hypotheses contradict each other: `theorem falseGoalImpossibleCase (n:
   Nat) (h: n + 1 < n): 2 ∈ [1, 3] := cases` checks today, by `omega` refuting `h`, although the
   goal decides `No` [run: decide/closer_order.sw]. So `No` and stuck both go on to step 9; if the
   case ends in `E-CASES`, its notes add "the goal's decision procedure says it is false" (for
   `No`). Nor is the closer limited to goals with no free variables: `Decidable.or` decides left to
   right, so `Or (K1 ∈ keys) (flag = True)` decides `Yes` with `flag` unknown [run:
   closer_order.sw, `leftYes`]. The rule is just "evaluation reaches `Yes`".
2. **After `omega`, not before.** The review questioned the order (§2). Measured:
   - *Outcome:* with `No` going on, the order can't change whether a case closes; both closers are
     sound, and each only closes [inferred].
   - *Existing proofs:* after `omega`, the closer runs only where today's `cases` fails, so every
     proof that checks today keeps its term. Before `omega`, a case `omega` closes today whose goal
     also decides would switch to a `fromYes` term. No such case was found by reading the 141
     `cases` uses in the corpus; whether one exists can't be counted without instrumenting the
     compiler, which this lane doesn't change [not measured].
   - *Time:* on a closed goal both take about 0.1 ms (`Or (5 < 4) (Not (2 = 3))`: `omega` 2,557
     steps, 64 nodes; `byDecision` 2,663 steps, 35 nodes). Where only the closer applies, `omega`
     fails first in about 0.1 ms and 1,211 steps (`K1 ∈ keys`, `E-OMEGA`), against 0.2-1.2 ms for
     the decision itself [run: closer_order.sw, and the 11-key list in the scratch directory]. So
     `everyNumericKey`'s 11 leaves pay about 1 ms for `omega` going first.

   So: no example in the corpus or the prototypes where the order changes the outcome; a measured
   cost of about 0.1 ms a leaf for "after"; and "after" guarantees no existing proof changes.
   After.

**Elaborator first.** The procedure runs in the elaborator and again in the kernel, as `auto` does,
rather than once in the kernel as Lean's `decide +kernel` does [cited: L1]. The review agrees (§2):
the first run is what lets the error name the case that decided false. A kernel-only evaluation, if
it is ever needed, belongs to `auto` as a whole, not to `cases`.

#### 6.1.3 Part 3: the fallback split, fewest cases first (R2)

At step 10: the goal is not stuck on anything step 6 splits, nothing closed it, and it is not a
`Π`. Split one of the goal's variables anyway, chosen as follows.

**Candidates.** A variable in scope (introduced by step 9, bound before the colon, or a field from
an earlier split) that is

- *mentioned*: met as a variable when step 6's walk goes over the goal (`Finder::walk`,
  cases.rs:807-875). This is the goal as computed, not as written, so a variable the statement
  names but computation drops (`const True x`) is not a candidate;
- *splittable*, by today's test (`splittable`, cases.rs:997-1010): data that isn't a proposition,
  has no indices, and isn't recursive;
- *not yet known*: not the left side of a split equation of this case (`is_known`, cases.rs:963).

Hypotheses are not searched for candidates; step 6 already splits what a hypothesis `C … = stuck`
is stuck on (cases.rs:776-805).

**Choice: fewest cases, then the latest bound.** The cost of a candidate is the number of cases its
split makes:

- *a data type:* its constructor count, `data.ctors.len()`, which `splittable` already returns
  (cases.rs:1009) and the budget already counts (`split_on`, cases.rs:1084: "`ctors.len() - 1`"
  more cases);
- *`Bool`:* 2 (it is data with two constructors in std);
- *a record (one constructor):* 1, so it is split first: taking it apart adds no case and gives
  its fields as new candidates (today step 6 splits records only when nothing else is stuck,
  cases.rs:28-29, for the same reason);
- *an indexed family:* never a candidate today, since `splittable` refuses any type with indices
  (cases.rs:1000). If indexed families become splittable, the count is the constructors whose
  indices can match the variable's type, those `match` would not mark impossible, since only
  those make cases. Until then this case doesn't arise.

Ties (equal counts) go to the variable bound latest, which is draft 1's rule. The count is of the
split itself, not of the whole tree below it: `DirectionKey` costs 2 (`Arrow _`, `Activate`), though
fully split it is 5 cases.

**Measurement.** The fallback isn't built, so it can't be run. Two ways instead:

- *On the prototypes and days 12 and 21, the two rules choose the same everywhere* [inferred, by
  reading each proof]. The fallback runs only where today's `cases` fails, and in every motivating
  proof at most one candidate is left when it does:
  - `cases_budget.sw` (`xor6`, 64 cases): every split is a stuck split (step 6); the proof checks
    today, so the fallback never runs.
  - `scale.sw`: no `cases`; one `rfl` on lists of `Bool`s. Nothing to compare.
  - `day21_today.sw`: `tabulateSame` splits `from` and `to` because `DirectionKey.index` is stuck
    on them (step 6); `costs` is a function, never a candidate. `containsNumericKey` is stuck on
    `key`. Both check today.
  - Day 12's `rowEndsSplit` and `columnEndsSplit`: stuck splits only (cases_today.sw checks).
  - Day 21's `everyNumericKey := cases`: one candidate, `key` (11 cases); both rules give 11
    leaves, each closed by step 8. `everyDirectionKey := cases`: `key` (2), then in the `Arrow d`
    case `d` (4), each the only candidate; 5 leaves either way.
- *Where they differ, by hand* [run: decide/fallback.sw]. Each order is written out as the `match`es
  the fallback would make, each leaf `byDecision` (step 8's term):

  | statement | fewest cases first | latest first |
  |---|---|---|
  | `(flag: Bool) (month: Month): Or (flag = True) (Or (flag = False) (month = month))`: only `flag` matters | `flag`: **2 leaves**, 0.4 + 0.0 ms | `month` (12), then `flag` in each: **24 leaves**, 3.0 + 0.2 ms |
  | `(flag: Bool) (key: NumericKey): Or (key ∈ numericKeys) (flag = True)`: only `key` matters | `flag`; each case is still stuck on `key`: **22 leaves**, 15.8 + 0.3 ms | `key` (11): **11 leaves**, 12.3 + 0.2 ms |

  Neither rule always wins: which variable makes progress depends on the goal, not on counts.
  The asymmetry is in the loss. A rule that splits an unneeded variable `u` first multiplies the
  cases by `u`'s count. Fewest-first splits `u` first only when `u`'s count is at most the needed
  variable's, so its loss is bounded by the smaller count (here ×2); latest-first's loss is any
  count at all (here ×12) [inferred]. That is the review's argument (§4), and the reason to take its
  rule.

**Diagnostics.** The fallback splits are marked, so a bad choice can be seen:

- `E-CASES-BUDGET`, when the split that crosses 64 is a fallback split, says so as the first note:
  "`cases` tried splitting `month : Month` as a fallback (the goal isn't stuck on it); this would
  exceed the 64-case budget". When earlier fallback splits contributed but the crossing split is a
  stuck one, the "it split on …" note (cases.rs:194-201) marks them: "it split on 3: `flag`
  (fallback), `month` (fallback), `x`".
- `E-CASES`, for a case still open after fallback splits: the case's path marks them the same way
  ("`cases` can't close the case flag = True (fallback), month = Jan (fallback)"), and its last
  note, today "the goal isn't stuck on anything …" (cases.rs:355-359), adds "it split `flag`,
  `month` as a fallback, though the goal wasn't stuck on them".

**Effect on failing proofs.** A proof that fails today with "found nothing to split on" may, with the
fallback, split up to 64 cases before failing: slower to fail, and the error names a smaller case.
`badAfter`'s error today stops at `a = True` with the goal `b = True`; with the fallback it would
split `b` and report `a = True, b = False (fallback)` with the goal `False = True` [inferred from the
run above].

#### 6.1.4 What stays

- **Types supported:** those `cases` splits: `Bool`, enumerations, constructor types whose fields it
  then splits (`Arrow Direction`), records of them. **Not** `Fin n` or bounded `Nat` ranges: `Fin`
  is an indexed family and `Nat` is recursive [checked: syntax.md:1652; cases.rs:997-1010]. For
  those, `Finite.check` (§6.2) with a hand-written instance; std has `Fin.any` with `Fin.anyElim`
  [checked: crates/elab/src/std/Fin/Fin.sw:98-111].
- **Failure:** as now, `E-CASES` naming the case by its splits, with the counterexample note.
- **Size limit: 64 cases, not raised in advance** (review §7: going up later is easy, going down
  once proofs depend on it isn't). 64 cases cost 11.7 ms and 5,938 term nodes **[run:
  cases_budget.sw]**; the proof term grows with the case tree, where `Finite.check`'s stays small.
  Past 64, `E-CASES-BUDGET` gets one more note when every variable it split has a `Finite`
  instance: "for statements this size, check every case by computation: `Finite.check`", with the
  shape of the call.
- **Interactions** (unchanged from draft 1): an opaque definition the goal calls is stuck for
  every step, as for `rfl`, so the fix is `unfolding` [inferred from core.md:163-170]; the check
  cache and erasure see ordinary declarations [core.md:423, :468]; the closers write `rfl`, `J`,
  `fromYes` and lambdas, none of which compare proofs [inferred]. A later `Decidable ((x: A) → P
  x)` from `Finite` (§6.2) would let step 8 decide a whole `Π` goal before step 9 introduces it:
  the past-64 route, chosen automatically [inferred].

**Then:** convert day 12's two truth tables and day 21's `tabulateSame`, `everyNumericKey`,
`everyDirectionKey`, each to `:= cases` with its signature as written; and in docs/syntax.md's
`cases` section say that it is the truth-table method, that it introduces the goal's binders, and
point closed goals to `byDecision`.

### 6.2 `Finite` and `byDecision` (SW-807)

```
interface Finite (a: Type) = {
  all: List a,
  complete: (x: a) → x ∈ all
}

theorem Finite.check [auto fin: Finite a] (p: a → Bool) (checked: List.all Finite.all p = True) (x: a): p x = True

def byDecision [p: Prop] [auto h: p]: p := h
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
- **`byDecision` becomes an official std idiom** (review §1), not just a pattern in this note: the
  one-line definition above in std's `Decidable` module, documented in docs/syntax.md beside
  `auto` and `cases` as the way to prove a closed decidable statement, and named in `E-CASES`'s
  last note when the open case's goal is closed and decidable. It is `auto` under a name
  [run: decide/closed.sw]; the review's split of names ("`byDecision` = prove this closed
  decidable proposition computationally; `cases` = finite structural case analysis; `omega` =
  arithmetic procedure") is the one to document.
- **Uses:** `everyNumericKey` is `Finite.complete`; day 21's `fits` can be stated over
  `Finite.all`; statements past 64 cases use `Finite.check` (decide/enumerate.sw shows the
  pattern for day 12).

**No `nodup` field (R3).** Nothing in this design reads one [checked against this note]:
`Finite.check` uses `all` and `complete` only (`allMember` in enumerate.sw uses membership, not
distinctness) [run]; the decision closer and the fallback split don't use `Finite`; the
`E-CASES-BUDGET` note only asks whether an instance exists. A count would: day 6's pigeonhole
("`n + 1` values below `n` repeat", aoc/NOTES-2024.md:1449-1460) [checked].

- *The trade-off:* adding a field to `Finite` later breaks every hand-written instance (`Fin n`'s,
  and any a program writes); derived ones are regenerated. Matt's standing rule is that churn is
  not a reason, so what decides it is the end state.
- *The end state needs no field.* For a type with `DecEq`, which every type `Finite` is derived for
  has, a duplicate-free complete list is a function of `Finite`: `List.distinctEq Finite.all`,
  with `List.memDistinctEq` (`x ∈ List.distinctEq xs ↔ x ∈ xs`) and `List.distinctEqNoRepeats`
  already in std [checked: crates/elab/src/std/List/Distinct.sw:86, :95]. So a later
  `Finite.card` and pigeonhole can be library code over `Finite` plus `DecEq`, and no instance
  changes [inferred; that those lemmas are enough for pigeonhole is not checked].
- *If counting ever needs a type without `DecEq`* (a type of functions, say), that is a separate
  interface carrying the distinctness proof, alongside `Finite` rather than inside it. Its form is
  left to when it's built.

**Later, not in SW-807 (review §6).** A proposition-level `Finite.forall`, or a derived `Decidable
((x: A) → P x)` from `Finite A` and pointwise decidability, would let `byDecision` (and step 8)
prove `(x: A) → P x` directly, without restating it as a `Bool` and transferring it with
`Finite.check`. It is new territory for `auto`'s search (instances are found by unification on the
result type, core.md:294) [checked; inferred], so it waits until `Finite.check` is in use.

## 7. Native evaluation

**Policy (D1973):** do not add native proof evaluation until measured kernel evaluation is a
material limitation on real programs. About 10 s of kernel evaluation in one real proof is the
trigger to investigate, not a boundary: crossing it means measuring that proof and asking whether
`Finite.check`, a better decision procedure or a faster kernel evaluator would do, before asking
whether to trust a runtime.

Today's numbers, for scale: 2^16 cases by one `rfl` took about 3.5 s elaboration + 2.6 s kernel
**[run: scale.sw, draft 1]**; the largest motivating proof has 25 cases.

Native evaluation means running the check on the fast runtime (`crates/rt`) or JS and admitting the
result. Both are untrusted today: "Its output can be wrong, but a proof never depends on it"
[checked: core.md:239]. Lean's `native_decide` does this and adds an axiom per use, trusting the
compiler [cited: L2, L4]; Rocq's `native_compute` checks on OCaml-compiled code [cited: R1, R2].

**Faster need not mean more trusted.** Draft 1 said "faster evaluation costs trust". The review
(§8, "One correction") is right that this is too broad. What the systems read show:

- `native_decide` and `native_compute` are faster by trusting the code that runs the evaluation
  [cited: L2, L4, R1].
- Certificate checking is a different route: an untrusted tool does the expensive search and
  produces a certificate, and a checker verified in the prover checks it. Lean's `bv_decide`
  works this way: it "obtain[s] a proof from an external SAT solver and verif[ies] it inside
  Lean", the proof being an LRAT certificate that `bv_check` can read back from a file, so the
  SAT solver is not trusted [cited: L1, re-read 30 October 2026, the `bv_decide` and `bv_check`
  docstrings].
- In `bv_decide` as shipped, though, the check itself still runs on compiled code: its docstring
  says "`bv_decide` trusts the correctness of the code generator and adds a axioms asserting its
  result" [cited: L1]. So `bv_decide` takes the solver out of the trusted base but keeps the
  compiler in it. How it runs the check (the docstring doesn't say; `Lean.ofReduceBool` is
  believed to be the mechanism) is [unverified].
- A certificate checked by the kernel would keep the trusted base where it is, with the speed of
  the search outside it; that is the general principle the review states, and it holds by
  construction for any checker the kernel runs [inferred]. Which system does that at scale was
  not checked [unverified].

So the honest statement is: *native evaluation* costs trust; *faster proofs* need not, if the
expensive part produces something the kernel can check. Neither is needed for Stitchwort's sizes.

## 8. Assumptions

The recommendation depends on these; if one is wrong, so is the part that rests on it.

1. **Sizes.** The AoC statements over finite types stay at or below 64 cases (16 and 25 so far,
   [§1](#1-the-motivating-proofs)). If one doesn't, `Finite.check` is the route and works up to at
   least 2^16 cases in about 6 s [run].
2. **Reusing `auto`.** The decision closer can run `auto`'s search on one goal from inside `cases`
   without reorganising either (auto.rs runs obligations in rounds after a declaration is
   elaborated, auto.rs:36-41) [checked; that it reuses cleanly is inferred].
3. **New steps only replace an error.** Steps 8-10 run only where `node` now returns `open_case`
   (cases.rs:265-270), so no proof that checks today changes [checked; inferred]. This is what makes
   the closer's order (after `omega`) and the introduction's order (after the closers) safe.
4. **No other `Π`-goal `cases` in the corpus is affected.** Reading the 141 `cases` uses outside
   docs/proposals found none whose goal is a `Π` at the `cases`: every after-colon theorem using
   `cases` reaches it inside a match arm [checked by reading; not by instrumenting]. By assumption
   3 they wouldn't change anyway.
5. **Cheap derivation.** A derived `Finite` costs little at declaration time for every eligible
   type. `DecEq`'s derivation is the precedent; not measured for `Finite` [unverified]. If it does
   cost, derive it on first use or on request.
6. **Day 21's quadratic membership terms** are a real cost only at larger sizes; at 11 they cost
   0.4 + 0.1 ms through `memContains` [run]. So the linear proof is about larger enumerations.

## 9. What was not reached

- None of the three `cases` parts was built (compiler changes are out of scope). Part 1 is shown by
  its hand-written equivalent (the lambda), part 2 by `byDecision`, part 3 by hand-written
  `match`es; their diagnostics are designed, not seen.
- Whether a case `omega` closes in today's corpus also decides (so that "closer before `omega`"
  would change its term) was not counted: it needs instrumentation.
- How `bv_decide` runs its LRAT check, and whether any system checks certificates in the kernel at
  scale [unverified, §7].
- Dafny was not consulted; F* only its SMT-fuel chapter. Lean's `Fin n` instance for `∀` in core
  was searched for and not found [unverified either way].
- The derived `Finite`'s completeness proof through `T.%tag` wasn't prototyped; enumerate.sw writes
  `Bool`'s by hand.

## 10. Decisions for Matt

All three remain open. Each assumption is stated in full.

**D1971. **Decided: yes (Matt, 30 October 2026).** Close SW-800 by extending `cases` in three parts, with no new `decide` word: (1) `cases`
introduces the goal's leading binders, explicit, implicit and `auto`, when no closer proves the
`Π` goal as it stands; (2) a decision closer after `omega`, closing a case on `Yes` with
`Decidable.fromYes d Trivial` and going on after `No` or stuck; (3) when nothing is stuck, split
the mentioned splittable variable with the fewest cases, ties to the latest bound, marked
"fallback" in the diagnostics?**
Recommendation: **yes**. Reviewer agrees, with changes, all taken: part 1 added to SW-800 (R1), part
3's heuristic changed from latest-first (R2); the order after `omega` and `No` not failing are this
draft's answers to the review's ordering question. Alternative: a `decide` word evaluating
`Decidable` instances as Lean does (option (a)); it can't do day 21's `tabulateSame` and doesn't
show the failing case.
Assumptions: (i) the new steps run only where `cases` today reports `E-CASES`, so no proof that
checks today changes (cases.rs:265-270); (ii) `auto`'s search can be run on one goal from inside
`cases` without reorganising either; (iii) the statements the AoC proofs need stay within 64 cases,
with `Finite.check` beyond.

**D1972. **Decided: yes (Matt, 30 October 2026).** Build SW-807 as a derived `Finite` interface with exactly two fields, `all: List a` and
`complete: (x: a) → x ∈ all` (no duplicate-freedom field), plus `Finite.check`, for non-recursive,
non-indexed constructor types with finite fields; and make `byDecision` an official std idiom?**
Recommendation: **yes, after D1971's conversion of days 12 and 21**. Reviewer agrees, with change:
no `nodup` (R3; draft 1 had none either, and this draft records why) and `byDecision` in std rather
than an example. Alternatives: enumerations only, as Haskell's `Enum` (day 21's `DirectionKey` has
a field and would be left out); or a `nodup` field now (breaks no instance today, but nothing reads
it).
Assumptions: (i) every type `Finite` is derived for also has derived `DecEq`, so a duplicate-free
list is `List.distinctEq Finite.all` (std/List/Distinct.sw:86, :95) and counting never needs a new
field for those types; (ii) a derived `Finite` costs little at declaration time for every eligible
type (not measured); (iii) a proposition-level `Finite.forall` is a later ticket, not SW-807.

**D1973. **Decided: yes (Matt, 30 October 2026).** Do not add native proof evaluation until measured kernel evaluation is a material
limitation on real programs; about 10 s of kernel evaluation in one real proof is the trigger to
investigate, not a boundary.**
Recommendation: **yes, worded so** ("not now rather than never"). Reviewer agrees, with change: the
policy reworded from draft 1's "never, until a proof needs more than about 10 s", and the comparison
section no longer says faster evaluation must cost trust (§7). Alternative: trust the fast runtime
for closed `Bool`s now, adding it to the trusted base.
Assumptions: (i) kernel evaluation stays fast enough for real proofs: 2^16 cases in about 6 s by one
`rfl` (scale.sw), against 25 cases in the largest motivating proof; (ii) when the trigger is
reached, cheaper routes (`Finite.check`, a better decision procedure, a faster kernel evaluator, a
kernel-checked certificate) are considered before a trusted runtime.

No new decision: the questions the investigation raised (where introduction goes, the closer's
order, what `No` does) each had one answer that keeps every current proof and adds proofs, so they
are recorded as design, not put to Matt.

## 11. Review 1 and how it was addressed

The review is [decide/review-1.md](decide/review-1.md), verbatim.

| # | reviewer point (section of review-1.md) | how addressed | where in this note |
|---|---|---|---|
| 1 | No `decide` keyword (§1) | agreed; unchanged | §6.1, D1971 |
| 2 | Make `byDecision` an official std idiom (§1) | adopted: in std, in syntax.md, named in `E-CASES` | §6.2, D1972, §12 |
| 3 | The decision closer is sound: same `fromYes … Trivial` as `auto` (§2) | agreed; recorded | §6.1.2 |
| 4 | Keep elaborator-first evaluation for diagnostics (§2) | agreed; recorded | §6.1.2 |
| 5 | Closer before `omega` questioned, not blocking (§2) | investigated: moved after `omega`; also `No` no longer fails a case (counterexample to draft 1 in closer_order.sw); no corpus example where order changes the outcome | §6.1.2 |
| 6 | **R1**: `cases` introduces leading Π binders, part of SW-800 (§3) | adopted as part 1; run on the real `rowEndsSplit`; placed after the closers because introducing first breaks `byHyp` | §6.1.1, binders.sw |
| 7 | **R2**: fewest cases, ties by recency; say when the fallback blows the budget (§4) | adopted; counts defined (data, `Bool`, records, indexed families); measured by hand where the rules differ; diagnostic specified | §6.1.3, fallback.sw |
| 8 | **R3**: `Finite` minimal, no `nodup`; record the trade-off (§5) | adopted (draft 1 had none); trade-off recorded; counting shown possible from `Finite` + `DecEq` with existing std lemmas | §6.2, D1972 |
| 9 | `Finite.forall` / `Decidable ((x: A) → P x)` later, not SW-807 (§6) | agreed; recorded as a later extension | §6.2 |
| 10 | Keep 64, don't raise pre-emptively; point larger cases to `Finite.check` (§7) | agreed; recorded | §6.1.4 |
| 11 | Native evaluation: "not now rather than never", 10 s a trigger (§8) | policy reworded | §7, D1973 |
| 12 | Soften "faster evaluation costs trust"; `bv_decide` and certificates (§8, correction) | rewritten; `bv_decide` re-read: it removes the solver from the trusted base but, per its docstring, still trusts the code generator | §7 |

## 12. Stage plan

Each part is one merge, with its tests; tests are snapshot examples in examples/accept and
examples/reject, as for today's `cases`.

**SW-800 part 1: binder introduction** (cases.rs `node`, step 9).
- accept: `rowEndsSplit` after the colon (binders.sw's `rowEndsAfter`), and split before/after
  (`rowEndsMixed`); a hypothesis after the colon used by the contradiction closer (`(b: Bool) → b
  = True → not b = False`); an unnamed hypothesis; a `Π` reached after a split.
- accept, unchanged: binders.sw's `byHyp`, `notLess`, `byTerm`, `implicitAfter` (introduction must
  not pre-empt them).
- reject: an open case after introduction, its path using the written names; an unnamed
  hypothesis shown as `hypothesis 1 (unnamed)`.
- then: convert days 12 (`rowEndsSplit`, `columnEndsSplit`) and 21 (`tabulateSame`) to `:= cases`
  in their written form.

**SW-800 part 2: the decision closer** (step 8).
- accept: `closer_order.sw`'s `falseGoalImpossibleCase` still checks (`No` goes on); `leftYes`'s
  goal by `cases`; a leaf closed only by deciding (`Digit3 = key ∨ …` after a split).
- reject: a case whose goal decides `No`, with the "decision procedure says it is false" note.
- check: the snapshot suite unchanged otherwise (no existing proof changes, assumption 3).

**SW-800 part 3: the fallback split** (step 10).
- accept: `everyNumericKey := cases` and `everyDirectionKey := cases` (5 leaves, with the second
  fallback on `d`); `fallback.sw`'s two statements by `cases`, each with the leaf count the rule
  predicts (2 and 22), as a test of the rule itself.
- reject: `E-CASES-BUDGET` from a fallback split, with "`cases` tried splitting `x : T` as a
  fallback; this would exceed the 64-case budget"; `E-CASES` with a path marked "(fallback)"
  (`badAfter`); a statement past 64 whose variables all have `Finite`, with the `Finite.check`
  note (after SW-807).
- then: convert day 21's `everyNumericKey`, `everyDirectionKey`.

**SW-807: `Finite`, `Finite.check`, `byDecision`.**
- std: `Finite`, `Finite.check` (from enumerate.sw), library instances (`Bool`, `Ordering`,
  `Option a`, pairs, `Fin n` by hand), `byDecision` in the `Decidable` module.
- derive: accept, `Finite` for an enumeration, for `DirectionKey` (a field), for a record of
  `Bool`s, each `all` in declaration order; reject, a recursive type and an indexed family, with
  why.
- accept: day 12's statement by `Finite.check` (enumerate.sw, using the derived `Bool` instance);
  a 2^10 statement by `Finite.check`.
- docs: syntax.md's `cases` section (the truth-table method, binder introduction, the fallback,
  the budget and `Finite.check`), `byDecision` beside `auto`.
- measure: declaration-time cost of deriving `Finite` across std and aoc (assumption 5).

Order: parts 1, 2, 3, then SW-807; part 3's `Finite.check` note waits for SW-807.

## 13. As built (SW-800)

Built 30 October 2026, D1971 (Matt: yes), in three parts, each its own commit. All in
crates/elab/src/cases.rs, except one visibility change in auto.rs. Line numbers are of the lane's
last commit.

**What changed.** `node` (cases.rs:251) now runs, after `omega` (:309), the three new steps in the
designed order (steps 8, 9, 10):

- *Part 2, the decision closer* (`by_decision`, cases.rs:374, called at :315): the goal, if a
  proposition, has its procedure found by `auto::decide` and run in a transaction; `Yes` closes the
  case with `auto::from_yes` (auto.rs:327, made `pub(crate)`, nothing else in auto.rs changed),
  counted as "by deciding" in the closed-cases note; `No` and stuck go on, and an `E-CASES` for the
  case adds "the goal's decision procedure says it is false" (:335-340), except where the goal is
  an equation of two constructors (`visibly_false`, :344), which the goal note already shows false.
  The trust comment is on `by_decision`.
- *Part 1, binder introduction* (`introduce`, cases.rs:411, called at :323): every leading binder
  of a `Π` goal, bound by `cx.bind` under its written name, unnamed ones (`_`) under `%hypN`
  (`UNNAMED`, :404), shown as "hypothesis N (unnamed)" (`hypothesis_name`, :445); the case starts
  again under them; one `Term::Lam` per binder.
- *Part 3, the fallback split* (`Finder::fallback`, cases.rs:1191, used at :330): the walk now
  records the variables it meets in the goal (:1045); the candidate is splittable (`ctors`), not an
  equation, not known in the case; fewest constructors, ties to the higher level. `split_on`
  (:1335) takes `fallback: bool`: the equation is named `%caseN%fallback` (`FALLBACK`, :469), so
  `path` marks it "(fallback)"; the budget note marks the atom; a fallback that crosses the budget
  records `x : T` for the first note (:1350, :224); `open_case` adds "it split `b` as a fallback,
  though the goal wasn't stuck on it".

**Must-hold results** [run]. examples/accept/cases-pi-goals.sw was committed first, with its hash
snapshot made by main's elaborator (`byHyp`, `notLess`, `byTerm`, `implicitAfter`,
`falseGoalImpossibleCase`, `rowEndsBefore`, `rowEndsLambda`); after all three parts the snapshot is
unchanged (`task test:lane AREA=hashes`). `rowEndsAfter := cases` (examples/accept/cases-binders.sw)
hashes `8d5e5e07…`, the same as `rowEndsBefore` and `rowEndsLambda`. `falseGoalImpossibleCase`
checks, hash `0898692d…` before and after.

**Tests** (snapshot examples). Accept: cases-binders.sw (after the colon, mixed, a hypothesis after
the colon used by the contradiction closer, an unnamed hypothesis, a `Π` after a split, an implicit
binder after an explicit one), cases-decision.sw (`inKeys`, `leftYes`, `pickIn`: a leaf closed only
by deciding after a split, `falseGoalImpossibleCase`), cases-fallback.sw (`everyNumericKey`,
`everyDirectionKey`, fallback.sw's two statements, and `flagFewestOfThree`, which latest-first would
take past the budget). Reject: cases-binders-open.sw (written names; `hypothesis 1 (unnamed)`),
cases-decides-false.sw, cases-fallback-open.sw (`badAfter`'s shape), cases-fallback-budget.sw,
cases-fallback-count.sw (the fallback's order and case count, by a statement false in one case).
No snapshot that existed before this lane changed.

**Converted proofs**, statements as written (lines are the declaration, before → after):

| proof | before | after | elab + kernel ms, by hand (main) | by `cases` |
|---|---|---|---|---|
| Day 12 `rowEndsSplit` | 18 | 3 | 0.4 + 0.2 | 1.0-1.3 + 0.3 |
| Day 12 `columnEndsSplit` | 18 | 3 | 0.3-0.4 + 0.2 | 0.9-1.0 + 0.3 |
| Day 21 `tabulateSame` | 26 | 2 | 1.9 + 1.7 | 2.7-2.9 + 1.1-1.2 |
| Day 21 `everyNumericKey` | 12 | 1 | 0.7-0.8 + 0.2 | 42.6-45.2 + 0.8 |
| Day 21 `everyDirectionKey` | 6 | 1 | 0.2 + 0.1 | 12.7-13.6 + 0.3-0.4 |

Times are `STITCHWORT_TIMINGS=decls`, `check --no-cache Aoc.Year2024.Day12.Proofs
Aoc.Year2024.Day21.Proofs`, 3 runs each; main is `target/release/stitchwort` of the main checkout
on main's `aoc/`. The whole `aoc` check, `--no-cache`, user CPU: main 39.16, 39.36, 38.46 s; this
branch 38.62, 36.73, 39.64 s: no difference beyond the noise.

**Where the membership proofs' time goes** [run, `sample` on `check --no-cache
Aoc.Year2024.Day21.Proofs`]: in `auto::decision_procedures`, which in a project sorts each
namespace's and the library's definitions by path on every call, and `Decidable.or` on an 11-item
membership calls `decide` once per item, in each of 11 cases. In file mode the same proof is 14.4 ms
(examples/accept/cases-fallback.sw). It is `auto`'s cost for every obligation in a project, not
`cases`'; caching that order belongs in `auto` (follow-up, not done here: the cache has to survive
session rewinds, which touches more than auto.rs).

**Hashes.** `task test:lane AREA=hashes` passes: the prelude's and every pinned example's hashes
are unchanged. In aoc (every declaration's hash, dumped before and after by a scratch test, not
committed), exactly the five converted declarations and their dependents change, all in
`Aoc.Year2024.Day12.Proofs` (11 names: the two tables, `cellUp`, `cellDown`, `cellLeft`,
`cellRight`, `rowCorners`, `columnCorners`, `cornersEqualSides`, `sidesCorrect`, `part2Correct`) and
`Aoc.Year2024.Day21.Proofs` (22: the three proofs, `nextCostsCheapest`, `numericFitted`,
`directionalFitted`, `numericWalksYours`, `directionalWalksYours`, `throughRobotsCost`,
`optimalIfCheapestWalks`, `optimalWithoutRobots`, `yourPressesThrough`, `yourPressesLength`,
`pressesForLength`, `pressesForTypes`, `lengthAchieved`, `shortestIfOptimal`, `complexitiesAnswer`,
`part1Correct`, `part2Correct`, `shortestWithoutRobots`, `answerWithoutRobots`), plus the new
`%match` helpers; a hash covers what it depends on (crates/core/src/hash.rs:1-6). games/rogue: no
hash changed.

**Deviations, with reasons.**

1. *Implicit and `auto` binders after an explicit one are bound by name*, not hidden as §6.1.1
   said. Hidden, the closers and the hypotheses note couldn't see them (`visible` skips nameless
   levels), so `(n: Nat) → [auto h: n = 3] → …` would lose `h`; bound by name, they act as they do
   before the colon. A leading implicit is still introduced by the checker, hidden, before `cases`
   runs, as before.
2. *`keyFewest` makes 12 cases, not 22*: the case `flag = True` is `… ∨ True = True`, which `omega`
   (step 7) closes before anything else, so `key` is split only under `flag = False`. fallback.sw's
   count assumed every leaf closed by deciding. The rule chose `flag` first as predicted
   (cases-fallback-count.sw's path starts `flag = False (fallback)`).
3. *`tabulateSame` was converted with part 1*, as §12 plans; it needs only binder introduction.
4. *The "decides false" note is left out for a goal that is visibly an equation of constructors*
   (`False = True`): there it repeats the goal note. Otherwise the note is as designed.
5. *The budget note's wording is the review's* ("`cases` tried splitting `x : T` as a fallback; this
   would exceed the 64-case budget"), without §6.1.3's "(the goal isn't stuck on it)".
6. *Not built*: the `E-CASES-BUDGET` note pointing to `Finite.check`, and naming `byDecision` in
   `E-CASES`, which wait for SW-807. No unit tests were added: the closers need a loaded library
   (`Bool`, `List`, membership), which the elaborator's unit tests don't load; the examples test
   each part.

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

**Draft 2's web use:** no web searches; one fetch, re-reading [L1]'s `bv_decide`, `bv_check` and
`bv_decide?` docstrings on 30 October 2026 (the first 100,000 characters of the file, which hold
them).

**Stitchwort**, at `b02ec6ca`: README.md; DESIGN.md §13; docs/core.md in full; docs/syntax.md
(Interfaces, Expressions, Goals, Counterexamples, `calc`, `rewrite`, `omega`, `ring`, `cases`);
docs/proposals/simp.md (summary, §5, §8.3, §9); counterexample-search.md (§0);
literal-match-facts.md (the problem); proof-irrelevance.md (status, §0);
docs/research/proof-automation.md in its 29 Oct version, replaced on 30 Oct (C10, C11, §5.4, which this note supersedes: its
"[unverified]" on Lean's `∀`-over-`Bool` instance is now [cited: L6]); aoc/NOTES-2024.md (day 12
§6, day 21 §2); the day 12 and day 21 proofs cited inline; crates/elab/src/cases.rs and auto.rs
(headers), derive.rs and derive_ext.rs (headers), std/Fin/Fin.sw. Not read: omega.md,
nested-data-types.md, opaque-definitions.md and check-cache.md (only core.md's summaries of
them).

**Stitchwort, draft 2**, at `09118ced`: crates/elab/src/cases.rs in full; check.rs (the
`check` cases for lambdas and implicit `Π`s, :3355-3421, and arrows, :1400-1411); omega.rs
(`prove_case`, `prove_goal`, `negated`); std/List/Distinct.sw (theorem list); std/Bool/Bool.sw
(theorem list); the day 12 and day 21 signatures; the 141 uses of `cases` in `.sw` files outside
docs/proposals, read with their enclosing declaration's signature.

**Prototypes** ([decide/](decide/)), draft 2 adds `binders.sw` (R1: `rowEndsSplit` before the
colon and as a lambda, the after-colon and split forms' errors in comments, and the `Π` goals
`cases` proves today), `closer_order.sw` (the closer's order and what `No` does) and
`fallback.sw` (R2: both rules written out by hand on two statements). Draft 1's: `cases_today.sw` (day 12 by `cases`), `day21_today.sw`
(`tabulateSame`, `containsNumericKey`, `everyNumericKey`), `cases_budget.sw` (64 cases; the
128-case error in a comment), `closed.sw` (`byDecision`), `enumerate.sw` (option (b) by hand for
day 12), `scale.sw` (2^10 and 2^14 by one `rfl`).
