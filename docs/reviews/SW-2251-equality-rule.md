# SW-2251: review of the equality-in-the-round note (D3250)

An independent review of `docs/proposals/equality-in-the-round.md` (SW-2236), for
D3250, with the literature Matt asked for (D3251). 7 Nov 2026. I read the note, the
code it names (`value.rs`, `reference.rs`, `native.rs`, `nat_add.rs`, `float.rs`,
`unify.rs`), the elaborator's shape-reading rules (`cases.rs`, `omega.rs`,
`rewrite.rs`, `matching.rs`, through a search I then checked by hand at the sites
cited), this week's merges, and the reviews SW-2125, SW-2158, SW-2234 and SW-2239.
Nothing was built and no test was run. I ran the note's six probes and six of my own
with the release binary (`target/release/stitchwort`, built 17:33 from `main`), glued
and with `STITCHWORT_GLUE=0`. Line numbers are from `f460de933`. Questions start at
D3260.

Labels: **[read]** (code read here), **[probed]** (a file below shows it), **[cited]**
(from a source linked in §3), **[inferred]** (my reasoning).

## Verdict on D3250: adopt, with changes

The note's diagnosis is right, and its main idea is the right one: laziness may only
ever short-cut to "equal", and "different" or "stuck" is said only on a rigid head.
That is the standard discipline. Coquand's algorithm, Abel's typed and untyped
conversion, Lean 4's kernel, Rocq and smalltt only conclude "not convertible" on
weak-head normal forms with different rigid heads, and treat "same constant, same
arguments" as a shortcut that can only say yes. Agda's same-head mismatch is final,
but only because in its theory a stuck call is a true neutral (§3). All six
probes reproduce. Gluing makes no difference to them (G4 can't be run unglued, F8).

But the rule as written isn't yet the rule we want to adopt:

1. **Rule C doesn't cover G6, and a stuck call can't count as rigid.** The formal text
   counts "a call stuck in its case tree whose blockers have rigid heads" as a rigid
   head. Then `ignoresFirst 1 x` and `ignoresFirst 2 x` are two rigid heads whose
   parts differ, and rule C *allows* "different". The note gets G6 right only through
   a prose sentence that contradicts its definition. G6 isn't about laziness at all.
   It is about *delta*: unfolding a definition to its body. Lean's kernel and Rocq's
   treat same-head-different-arguments exactly as the note's prose does: compare the
   arguments, and if they fail, unfold and go on (§3). (F1)
2. **There are more gaps of G6's kind, which the plain oracle can't see.** I found G7
   (a tree's leaf against the other tree's stuck `case`) and G8 (two alike
   number-literal `match`es). Both fail in every mode, including the reference with
   every fold off, because they're gaps in the *stuck-call* rule that the reference
   shares (`reference.rs:756-771`, `:848-939`). (F2, F3)
3. **"Test against a plain reference" isn't strong enough as the test of record.**
   The reference shares the shape predicates (`opens_by_tree`, `nat_add::stuck`,
   `native::compare_with`) and the representations (`Value::Nat`, `Chars`). It
   gives the same wrong answer as every other mode for G3, G6, G7 and G8, so it
   can't flag them. What finds them is the relation's own laws: transitivity,
   and stability under substitution (`pickA n x = pickB n x` holds for unknown `n`,
   and `generic 3 x` proves it at 3, but `rfl` can't). (F4)
4. **G2 belongs in comparison and elimination, not in `+`'s evaluation.** Fixing it
   where `+` evaluates changes the goals users see and what `rewrite` finds, and
   adds work on a hot path. Make the note's fallback the default. (F6)

So: adopt the principle as a kernel rule in `core.md`, with three changes to its text.
(a) A stuck call that opens by tree isn't rigid: its rigid form is its residual case
tree, and name-and-arguments is an equal-only shortcut. (b) The limits are named,
every mode shares them, and each is an opaque constant compared by its arguments:
recursive definitions, calls folded by name and stuck, lift leaves, natives, and
`NumCase` nodes until G8 is fixed. (c) The test of record is a set of properties, not
one evaluator: agreement with the plain mode, an equivalence, stable under
substitution, and agreement with ground truth on closed terms. D3260 asks for this.

**The top five recommendations:**

1. Restate rule C and the definition of "rigid" as above before `core.md` takes it
   (F1). No code waits on this. S2 does it.
2. Merge S2 and S4 into one Opus lane for the stuck-call comparison: G1, G3, G6, G7
   and, if cheap, G8. They are all in `walk_tree` and `same_stuck_trees`, the
   reference's `same_trees`, and the same-head arms of `conv_step`, `conv_in` and
   `unify_step`. Run side by side, they'd conflict line by line (F2, F14).
3. In S1, test transitivity over triples, stability under substitution and ground
   truth on closed terms, as well as the plain switch. Give the reference a step
   budget first (F4, F5).
4. Fix G2 lazily, at the comparison and the `case` that read a stuck `m + n`, not in
   `+`'s evaluation (F6).
5. Make design B's discipline a type, not a grep. Give the structural arms a
   `Rigid` value that only `head` can make, and give the shortcuts a result that
   can't say "different" (F9). Measure before S5 (F13).

## Findings

| # | Where | Finding | Severity | Confidence | Size |
|---|---|---|---|---|---|
| F1 | note §2.2, `value.rs:3372-3405`, `reference.rs:756-771`, `unify.rs:1576-1608` | Rule C as worded allows G6's "different": stuck calls count as rigid heads. Lean and Rocq unfold after a same-head argument failure | high (spec) | high | S (text) |
| F2 | `value.rs:3700-3745` (`same_stuck_trees`'s `_ => false`, `:3744`), `reference.rs:892-938` | **G7, new:** a leaf on one side against a stuck `case` on the other is "different", even when the leaf is a call that opens to that same `case` | medium | high | M |
| F3 | note §5.2, `reference.rs:756-771` | G6, G7 and G8 aren't laziness gaps. The plain reference has the same arms, so T1 can't find them. Only transitivity (G6) or substitution stability (G3, G7) can | medium | high | in S1 |
| F4 | note §5.2 T1, `reference.rs:10-13` vs `:735`, `:316`, `:644` | The reference "never calls anything in `value.rs` that evaluates", but it does share the shape predicates and the number and text representations. The plain switch removes lazy forms but not representations: G3 passes T1 | medium | high | in S1 |
| F5 | `reference.rs:14-15` | The reference counts no resources and recurses on the Rust stack. A plain mode that unfolds theorems and `decreasing` helpers eagerly can hang or overflow a test. D2543 needs a budget that fails | medium | medium | S |
| F6 | note §4.3 G2, `nat_add.rs:84-103`, `rewrite.rs:1529` | G2 fixed in evaluation changes read-back (`x + two 0` becomes `2 + x`), so `rewrite`'s syntactic key and `match`'s generalisation find different occurrences. It's also hot work with no cell (SW-1829's shape). Do it in `head` | medium | medium | in S3 |
| F7 | `cases.rs:1724-1733`, `omega.rs:1959` | **Elaborator gaps, confirmed:** `cases` can't find the blocker behind a number scrutinee (`pick 3 b`, `pick (Succ Zero) b`), and `omega` treats a folded `decreasing` call as an atom (`x + two 0 > x`) | medium | high | M |
| F8 | std `Float/Float.sw:197-232`, pins | With `STITCHWORT_GLUE=0`, std's `Float` fails its pins (`E-BUILTIN`, `Float.neg`, `abs`, `sub`), so no program importing `Float` checks unglued. The note's "G4 fails unglued" wasn't observable | low-medium | high | S-M |
| F9 | `unify.rs:1311-1316`, `value.rs:3177-3201` | A boolean `false` from a shortcut means "don't know" in some places and "different" in others: `same_spines`, and the unifier's nested same-call `return Ok(false)`. The grep check in B can't tell them apart. Use types | low-medium | high | in S5 |
| F10 | `value.rs:3657`, `reference.rs:881` | **G8:** two alike `NumCase` trees are "different" (`isThreeA n = isThreeB n`). It's documented, but neither the note's rule text nor its plan names it | low | high | S-M |
| F11 | `unify.rs:1122-1160` (`BLOCKED_DEPTH = 3`) | A stuck call made stale by a solution deeper than three calls isn't recomputed, so the unifier compares a non-rigid head. A limit that picks an answer, against D2543. Elaborator only: the kernel never sees an unknown | low-medium | medium | S-M |
| F12 | note §2.2 "Consequence" | "Conversion with all of them is conversion with none" holds only if the plain mode keeps the same stuck-call policy (`opens_by_tree` still excludes what `folds` names). If S1 makes `opens_by_tree` follow the plain switch, plain is *more* complete, and T1 reports limits as bugs | low | high | S (text) |
| F13 | note §4.3 | The speed table is reasoning, not measurement. Three things to count before S5 and C, below | medium (process) | high | in S3/S5 |
| F14 | note §6 | S2 and S4 touch the same functions. S3 should lead with G5 and G4 and put G2 in `head`. S5 is too large for 90 minutes as one lane | low | high | — |

The details are in §1 to §6, by the brief's questions.

## 1. Is the rule right?

### 1.1 Sound

**Yes, as far as it goes, and it can't make anything unsound** **[read]**. The rule only
removes "different" and "stuck" answers. The new "equal" answers come from unfolding,
so a lazy form only changes how far to compute. "Equal" shortcuts stay sound under one
condition, which the code already meets: arguments are compared in shortcut mode, so
proof fields are compared too (`core.md`, "Proof irrelevance"; `value.rs:3195`). I
checked the five equal-only shortcuts in `conv_step` (same glued call, same folded
call, same closure, sealed spines, `CallMemo`). Each answers "equal" only from equal
arguments in shortcut mode, or "nothing" by falling through.

The one soundness-adjacent risk is termination, not truth. Rule E makes more things
compute. A `case` on `m + f n` that used to stay stuck now runs `f n`. A `decreasing`
call whose fuel is large, or a folded theorem, could now hit the budget where it didn't
before. D2543 makes that an error, not a wrong answer. That's correct, but it's a new
way for a proof that checked yesterday to fail today. S3 and S5 should count E-RESOURCE
failures over std and the AoC days they're allowed, as well as steps.

### 1.2 Not stated precisely enough: stuck calls (F1)

§2.2 defines a rigid head to include "a call stuck in its case tree whose blockers
have rigid heads". Rule C says "different" is allowed on "two rigid heads that differ,
or on parts compared this way that do". By that wording `ignoresFirst 1 x` and
`ignoresFirst 2 x` are rigid (stuck on `x`), and their parts `1` and `2` differ. So
rule C permits exactly the answer G6 says is wrong. The paragraph after the quote
("Rule C covers stuck calls too...") is what fixes G6. It isn't in the proposed
`core.md` text, and it contradicts the definition above it.

What the code means by a stuck call, and what Lean and Rocq do with one, suggests the
right wording. A call of a definition that opens by tree has no rigid form of its own.
It is a name for its residual case tree, the `case` it's stuck on with the branches
it hasn't taken. "Same definition, equal arguments" is a shortcut to "equal".
Otherwise, unfold both (delta) and compare the residual trees by congruence. Lean's
kernel does exactly this in `lazy_delta_reduction_step`: same head, then the
arguments, then unfold both. So does Rocq's `conversion.ml`: same constant, then
`convert_stacks`, then unfold by the oracle (§3) **[cited]**. Proposed text, replacing
the last clause of "Heads" and adding to rule C:

> A head is *rigid* if it's a sort, function type, lambda, data type, constructor, `Eq`
> or `Refl`, or a neutral value headed by a variable, an unsolved metavariable, an
> axiom, a hidden or pending definition, or a stuck `case` (of a residual case tree)
> whose scrutinee has a rigid head. A call of a definition that **opens by tree** and
> is stuck is not itself a head: its head is its residual tree. A call of a
> definition that doesn't open by tree (recursive, folded by name, with a lift leaf,
> native, or with a `NumCase` node: the *limits*) is rigid once its blockers are, and is
> compared by its arguments.
>
> **Rule C** ... "Same definition, equal arguments" is an equal-only shortcut; for a
> definition that opens by tree, two calls whose arguments differ are compared by
> their residual trees, as two different definitions' are.

That makes the "Consequence" checkable: each mode, plain included, implements one
relation, the one these rules define, with the same limits (F12).

### 1.3 Complete? Two more gaps (F2, F10)

**G7: a leaf against a stuck `case` [probed].** `same_stuck_trees` walks both trees to
a leaf or a stuck `case`. If one side reaches a leaf and the other a `case`, it
answers "different" (`value.rs:3744`, `_ => return Ok(false)`; the reference's
`same_trees` likewise, `reference.rs:938`). The leaf may be a call that opens to that
very `case`:

```
def k (x: Nat): Nat := match x with | Zero => 0 | Succ m => m
def viaHelper (c: Bool) (x: Nat): Nat := match c with | True => k x | False => 1
def inline (c: Bool) (x: Nat): Nat :=
  match c with | True => (match x with | Zero => 0 | Succ m => m) | False => 1

theorem atTrue (x: Nat): viaHelper True x = inline True x := rfl        -- accepted
theorem leafAgainstCase (c: Bool) (x: Nat): viaHelper c x = inline c x := rfl  -- E-REFL
```

This is the same rule as F1, one level down. A leaf that evaluates to a call that
opens by tree should be opened and walked on. It terminates for the reason the tree
rule already does: such definitions aren't recursive, so each opening goes down the
definition order. A user meets this whenever one of two alike helpers calls a
sub-helper where the other inlines it. That's what lifting a `match` to a helper
does.

**G8: number-literal trees [probed].** `isThreeA n = isThreeB n`, for two copies of
`match n with | 3 => 10 | _ => 20`, is E-REFL. `walk_tree` gives up on any `NumCase`
node (`value.rs:3657`). `core.md` documents this ("a `NumCase` ... is 'different', as
before"), and the note's G3 fix (the branch view for `Case` nodes) doesn't touch it.
Either the merged stuck-call lane compares `NumCase` nodes (the same arms and
default, each body compared), which is small, or the rule names it as a limit. I'd
fix it: it's the number-literal twin of G3, and S1's substitution check will report it
as soon as it has a `NumCase` helper pair.

**Laziness the note missed.** I looked for a seventh lazy form. Two are close to one:

- **A stuck call made stale by a solution** (F11, elaborator only). `pick ?b 5` stuck,
  then `?b := True`. `force` replaces a solved unknown only at the head, so the call
  stays stuck, and the unifier's `stale`/`afresh` recompute it only three calls deep
  (`BLOCKED_DEPTH`, `unify.rs:1130`). Deeper than that, a non-rigid head is compared
  as rigid. The rule's "nothing it's stuck on is lazy" covers it in principle, so
  `head` in the unifier must include it. A depth cut-off that turns into "different"
  is a limit that chooses (D2543). **[read; not probed]**
- **`Apart` facts on variables** (`value.rs:157-162`). A `NumCase` takes its default for a
  variable known to be none of its arms. `Head`'s equality ignores the fact
  (`value.rs:175-185`), so it never makes two values differ. It's a context fact, not
  laziness. Sound as is. **[read]**

`Closure::apply_lazy` passes a placeholder for an unused argument, not a thunk. The
body can't see it, so it isn't a lazy form **[read]**.

### 1.4 Is G6 a different problem?

**Yes.** G6 is the stuck-call rule having one arm for "different definitions" (tree
comparison) and another for "same definition" (arguments only). It fails in the
plain reference too, and it isn't about anything lazy at the head. It shares the
note's principle, a shortcut's failure taken as final, which is why the note grouped
it there. But the cure is the delta rule of §1.2, not `head`. The probe shows it
breaks transitivity: `ignoresFirst 1 x ≡ alsoIgnores 2 x ≡ ignoresFirst 2 x`, but
`ignoresFirst 1 x ≢ ignoresFirst 2 x` **[probed]**. The unifier shows it too:
`needSame x rfl` (solving `a` from `ignoresFirst ?a x = ignoresFirst 2 x`) is accepted,
with `a := 2`. `needSame [a := 1] x rfl` is E-REFL **[probed]**. Once G6 is fixed, the
unifier should still try the arguments first, keeping what they solve (first-order
approximation, as Lean's `isDefEq` does), and fall back to the trees only after undoing
them. The note says this.

## 2. Do G1-G6 reproduce?

All with the release binary, built 17:33 from `main` (after SW-2157 and SW-2241). The
probe files are in my scratchpad, copied from SW-2242's
`docs/repros/sw-2236/` (read only there), with mine beside them.

| Probe | Glued | `STITCHWORT_GLUE=0` | Is it what the note says? |
|---|---|---|---|
| G1 `pickA (yes 0) x = pickB (yes 0) x` | E-REFL; `plainTrees` passes | E-REFL | yes: `walk_tree`'s scrutinee is a folded call, so `Other` (`value.rs:3654`) |
| G2 `x + two 0 = Succ (Succ x)` | E-REFL; `plainSum` passes | E-REFL | yes: `nat_add::stuck` views `n` with `force` only (`nat_add.rs:94`) |
| G3 `pickA 3 x = pickB 3 x` | E-REFL, and **also** `pickA (Succ Zero) x` | E-REFL, both | yes: `Value::Nat` scrutinee, so `Other` |
| G4 `Float.ofNat (two 0) = Float.ofNat 2` | E-REFL; `plainFloat` passes | **can't run**: std's `Float` fails its pins unglued (F8) | yes (glued): `known_bits` and `as_nat_with` read through `force` only (`float.rs:716`) |
| G5 `isThree (Succ (two 0)) = 10` | E-REFL; the other two pass | E-REFL | yes: `branch`'s `NumCase` views the base without unfolding (`value.rs:1971-1987`) |
| G6 `ignoresFirst 1 x = ignoresFirst 2 x` | E-REFL; `otherDef` and `middle` pass | E-REFL | yes, but it's a delta gap, not a laziness gap (§1.4) |
| G7 (new) `viaHelper c x = inline c x` | E-REFL; `atTrue` passes | E-REFL | leaf against stuck `case` (§1.3) |
| G8 (new) `isThreeA n = isThreeB n` | E-REFL | E-REFL | `NumCase` trees (§1.3), documented |
| G9 (new) `x + two 0 > x := omega` | E-OMEGA, and `h: x = two 0` gives no `x = 2` | E-OMEGA | `omega`'s atoms (F7) |
| G10 (new) `pick 3 b = True := cases` | E-CASES; `pick (Succ k) b` passes | E-CASES | `cases`'s `blocker` (F7) |
| G11 (new) `needSame [a := 1] x rfl` | E-REFL; `needSame x rfl` passes | E-REFL | G6 in the unifier |
| G12 (new) `late`, an `rfl` whose unknown is solved later as 3 | E-REFL at the `rfl`, correctly postponed; `generic 3 x` proves the same statement | the same | G3 as a failure of substitution stability; no kernel/elaborator disagreement |

Two side results. `rewrite` with `h: two 0 = x` in the goal `2 = x` finds nothing
(E-REWRITE-NOTHING). That's by design: `rewrite`'s occurrence search is syntactic
(`rewrite.rs:1529`'s key), as Lean's `rw` is up to instances. It isn't a bug of this
class. Using `h: x + 2 = 5` where `x + two 0 = 5` is expected is G2 again.

**More in the elaborator (F7).** The search over the shape-reading rules (25 sites)
found these. I checked the two that are bugs by hand, and probed them:

- **`cases`'s `blocker`** (`cases.rs:1716-1733`) takes a `case` step only on
  `Value::Ctor`. A `Nat` matched by `Zero`/`Succ` (a `Term::Case`) on a number, or a
  `List` on compact text, ends the walk with `None`, so `cases` splits on the wrong
  thing: "can't close the case `pick 3 b = False`". This is G3's representation gap in
  the elaborator. `cases.rs:1338` (`walk`) and `:1589` (`is_ctor_form`, which misses
  `Chars`) have the same shape.
- **`omega` and `ring` atoms** (`omega.rs:1959`, `ring.rs:764`) use `force`, not
  `unfold_folded`, so a `decreasing` call or a dictionary method's result is an atom.
  Lean's `omega` also treats unknown functions as atoms, but in Stitchwort `two 0` *is*
  a number by computation, and `rfl` (once G2 is fixed) will say so. The fix is to
  give the atom quoter the head view for `Nat`-typed values, bounded by the budget.
- **One-step lazy delta in the unifier** (`unify.rs:1760`, `one_step_apart`) applies
  only to glued `Call`s, never to folded-by-name calls. That loses only speed, not
  answers, because the folded arm unfolds them later.
- **Syntactic by design, not bugs:** `rewrite` and `match` occurrence search
  (`rewrite.rs:738-761`, `:1529`; `matching.rs:1888-2002`), `search.rs`'s keys, and
  `bind::decide_written`. They compare read-back terms, where a folded-by-name call
  stays a name. That makes F6 matter. Anything that changes what evaluation returns,
  as opposed to what comparison concludes, changes what these find.

## 3. Prior art

Sources were checked by a research pass at Lean master `43906412f3`, Rocq master
`dc58c4f8`, Agda master `a6c0faf9`, and Idris 2 and smalltt master, and against the
papers. Claims not confirmed from a source are marked unverified. The note's §4.2,
written from memory, has the broad shape right. Below is what the sources say, and
what Stitchwort should take from each.

**Lean 4's kernel.** `is_def_eq_core`
([type_checker.cpp L1179-1254](https://github.com/leanprover/lean4/blob/43906412f3dd8fdb91afe99c2cabc8394ea92470/src/kernel/type_checker.cpp#L1179-L1254))
works in this order:

1. quick checks;
2. `whnf_core` of both sides (β, ι, projections, no δ);
3. `is_def_eq_offset` on every lazy step;
4. lazy delta;
5. structural comparison, eta and eta for structures, last.

It reaches its final `false` only once lazy delta is exhausted and `whnf_core` changes
nothing. The comment there reads "at this point, t_n and s_n are in weak head normal
form". In
[`lazy_delta_reduction_step`](https://github.com/leanprover/lean4/blob/43906412f3dd8fdb91afe99c2cabc8394ea92470/src/kernel/type_checker.cpp#L974-L1031),
the side with the greater height (`ReducibilityHints.regular n`) unfolds first. With
the same constant on both sides, it compares the arguments, and **on failure caches
the failed pair, unfolds both and goes on**. A failed same-head argument comparison is
never "different". That is the answer to G6. Numbers:
[`is_def_eq_offset`](https://github.com/leanprover/lean4/blob/43906412f3dd8fdb91afe99c2cabc8394ea92470/src/kernel/type_checker.cpp#L1051)
peels a successor from each side, and a literal against anything else is "unknown",
never "different". That's SW-2157's rule, and rule C's. `reduce_nat` computes on
literals only when neither side has free variables. The caches: `whnf_core`, `whnf`,
and a failure cache keyed by the pair. Unfoldings aren't shared; each step re-runs
`whnf_core(unfold(..))`. **[cited]**

**Lean's elaborator** (`Meta.isDefEq`).
[`isDefEqDelta`](https://github.com/leanprover/lean4/blob/43906412f3dd8fdb91afe99c2cabc8394ea92470/src/Lean/Meta/ExprDefEq.lean#L1868)'s
doc reads "same head symbol ... First try to solve unification by unifying arguments.
If it fails, unfold both and continue." The argument heuristic is always applied to
`match` helpers, "because they will not be unfolded when smartUnfolding is turned on".
Well-founded definitions have been irreducible in the elaborator since v4.9.0
([release notes](https://lean-lang.org/doc/reference/latest/releases/v4.9.0/),
PR #4061), because unfolding through their decreasing proofs was costly and seldom
useful. The kernel still unfolds them. **[cited]**

**Known Lean bugs that look like ours** **[cited]**:

- [lean4#14806](https://github.com/leanprover/lean4/pull/14806): the kernel cached
  equalities in a union-find. Kernel defeq is "sound but incomplete, and therefore
  not transitive", so answers depended on query order, and someone derived `False`.
  The fix keys the cache by the pair.
  [#15706](https://github.com/leanprover/lean4/issues/15706) (open) still finds order
  dependence, including `reduce_nat` behaving differently in `whnf` and in lazy
  delta.
- [#2258](https://github.com/leanprover/lean4/issues/2258) and
  [#3213](https://github.com/leanprover/lean4/issues/3213) are transitivity failures
  through unit-like and Prop-structure eta. The
  [reference manual](https://lean-lang.org/doc/reference/latest/The-Type-System)
  says outright that defeq is "reflexive and symmetric, but not transitive".
  [#14977](https://github.com/leanprover/lean4/issues/14977) plans a decidable,
  transitive algorithm.
- [#15447](https://github.com/leanprover/lean4/issues/15447) is the cost of comparing
  arguments first. `bind (.error e) K1 =?= bind (.error e) K2` costs time in the size
  of `K1` and `K2`, though ι would throw them away.

**Rocq.** [`eqappr`](https://github.com/rocq-prover/rocq/blob/dc58c4f8c58010de56374d41f4cdea9840355f9b/kernel/conversion.ml#L413)
head-reduces with βιζ but not δ. In the
[two-constants case](https://github.com/rocq-prover/rocq/blob/dc58c4f8c58010de56374d41f4cdea9840355f9b/kernel/conversion.ml#L469-L535)
it tries `convert_stacks`, then `with NotConvertible -> unfold_ref_with_args`. It
raises "not convertible" only when neither side can unfold, at rigid catch-alls. The
oracle, `Conv_oracle`, only orders unfolding. Its interface says it "does not
introduce incompleteness", and `Opaque` is "a hint to unfold this constant last"
([refman](https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html)).
A stuck `match` is a `ZcaseT` frame on the stack above a δ-head, so unfolding the head
re-enables ι. That's Stitchwort's residual tree, made explicit. The lazy machine
updates closures in place, call-by-need, so unfoldings are shared (read from code
comments only). Primitive ints and floats compare by value. Rocq's
[critical-bugs list](https://github.com/rocq-prover/rocq/blob/master/dev/doc/critical-bugs.md)
has many conversion-machine bugs: the wrong environment, missing substitutions, and
native and primitive-float mistakes (#12483, #16096). That is the risk of every fast
path. The MetaCoq tour
([§4.1](https://arxiv.org/pdf/2107.07670)) says comparing arguments first gives
"faster successes but also potentially costly backtracking". **[cited]**

**Agda.** [`compareAtom`](https://github.com/agda/agda/blob/a6c0faf9c7700806ca1af088f816dc79af8d4543/src/full/Agda/TypeChecking/Conversion.hs#L576)
reduces both sides to weak-head normal form (`reduceB`). Two blocked sides postpone,
not fail. Two unblocked calls of the same definition compare by their eliminations,
and a mismatch is final. **That's right for Agda and not for us**: a stuck
clause-defined function is a true neutral in Agda's theory, because it doesn't unfold
to a term. Stitchwort's definitions unfold to case trees (`core.md`, "Case trees";
SW-386's tree rule is that delta), which puts it with Lean and Rocq. Agda's
first-order shortcut (`--lossy-unification`) falls back to full reduction when it
fails ([L199-222](https://github.com/agda/agda/blob/a6c0faf9c7700806ca1af088f816dc79af8d4543/src/full/Agda/TypeChecking/Conversion.hs#L199)).
Its documented incompleteness is wrong solutions to unknowns (`f ?0 = f 1` with a
constant `f` sets `?0 := 1`)
([docs](https://agda.readthedocs.io/en/latest/language/lossy-unification.html)). The
unifier's argument-first try after G6 will have that too. **[cited]**

**Idris 2.** `Glued` holds a term thunk and a normal-form thunk
([Normalise.idr](https://github.com/idris-lang/Idris2/blob/main/src/Core/Normalise.idr)).
`convert` normalises both sides first, so a same-head argument mismatch is final.
The closest analogue to SW-386 is
[`chkConvCaseBlock`](https://github.com/idris-lang/Idris2/blob/main/src/Core/Normalise/Convert.idr#L251-L290).
Two different stuck case-block helpers are equal if their trees match structurally
(`chkSameDefs`). Failing that, they're equal if their scrutinees convert and they come
from the same source location, which the source calls "a bit of a hack". It has the
same one-sidedness as G6: a special rule for two *different* helpers. **[cited]**

**smalltt and the elaboration zoo.** [GluedEval.hs](https://github.com/AndrasKovacs/elaboration-zoo/blob/master/GluedEval.hs)
has `VTop Name Spine ~Val`: one lazy form, with its unfolding shared through
laziness. smalltt's
[`unify`](https://github.com/AndrasKovacs/smalltt/blob/master/src/Unification.hs#L321-L370),
with the same top-level head, runs `unifySp ... Flex` and, on failure, catches it and
unifies the unfoldings in `Full` mode. Flex failures are always provisional, and only
`Full` mode's are final. The
[README](https://github.com/AndrasKovacs/smalltt/blob/master/README.md) says it
"backtracks at most once on any path" and solves no unknown approximately in the flex
pass. That's rule C, with a mode flag doing the work of B′'s `Quick` type. **[cited]**

**Theory.** Abel, Öhman and Vezzosi
([POPL 2018](https://research.chalmers.se/publication/527432/file/527432_Fulltext.pdf)):
the algorithm "will reduce ... to weak head normal form, compare the heads, and, if
they match, recurse". Its neutrals are headed by variables only. There are no
δ-constants, so a stuck call of an unfoldable definition isn't neutral there.
Inequality is concluded only between weak-head normal forms with different rigid heads
or neutrals of different structure, and completeness is proved by a Kripke logical
relation. Abel and Coquand ([FI 2007](https://www.cse.chalmers.se/~abela/lfsigma.pdf))
give the untyped version with surjective pairs. This is the justification for rule C,
and for §1.2's point that a stuck δ-call has no rigid form of its own. **[cited]**
(Coquand 1996 couldn't be fetched: unverified.)

**Testing.** The [Lean Kernel Arena](https://arena.lean-lang.org) runs the official
kernel, lean4lean, nanoda and others on shared good and bad tests. Both #14806
exploits were caught by independent checkers.
[Lean4Lean](https://arxiv.org/abs/2403.14064) found one soundness bug. MetaCoq's
verified checker follows the kernel's arguments-then-unfold strategy. I found no
published metamorphic or NbE-oracle testing of conversion checkers. §5's property
suite would be new ground, but cheap. **[cited]**

**What to copy:**

- Lean's and Rocq's same-head rule: arguments first, then unfold both. That's G6 and
  G7.
- Lean's `is_def_eq_offset` stance: a literal against something else is "unknown".
  Already SW-2157's.
- Rocq's explicit residual `match` above a δ-head, as the model for the residual tree
  of §1.2.
- smalltt's "flex failures are provisional, at most one backtrack", as the shape of
  rule C in the unifier.
- A pair-keyed failure cache, as Lean has and as `CallMemo` already is.

**What to avoid:**

- Any cache that closes equalities transitively (union-find, equivalence classes).
  Stitchwort's relation has known non-transitivities until G6 is fixed, plus proof
  irrelevance's subtleties. lean4#14806 turned that combination into `False`.
  `CallMemo`, `TreeMemo` and the reference's `EQUAL_CALLS` are keyed by the pair
  today (checked), and design C's shared cells must stay that way.
- Idris's location hack.
- Agda's final same-head mismatch, which suits its theory, not ours.
- Lean's #15447: comparing large arguments that ι would discard. G6's fallback makes
  this more likely, because a failing argument comparison is now followed by a tree
  comparison. `CallMemo`'s `Differ::Arguments` record keeps it to once per pair.

## 4. The design

### 4.1 Is B right?

**Yes, B is the right shape, and C is rightly deferred.** It's Lean's: one `whnf_core`
that every rule calls, a separate delta step, and equal-only quick checks before
either. Three changes:

- **B′: make it a type** (F9). Today a `bool` from a shortcut means "equal or don't
  know" in `same_spines` (`value.rs:3177-3201`). The unifier's nested same-call
  `return Ok(false)` (`unify.rs:1311-1316`) means "don't know, the outer level
  compares the unfoldings", yet reads as "different". A grep for `match` on `Value::`
  can't tell these apart. Two small types would let the compiler check rule C:
  - `struct Rigid(Value)`, constructible only by `head`, which the structural arms
    take;
  - a shortcut result `enum Quick { Equal, Unknown }`, with no `Different`.

  Rule E is the same: `case_view(g, d, &Rigid)`. This costs nothing at run time, and
  it's what makes "a reviewer can check" true.
- **The delta step for stuck calls is its own function**, not part of `head`. `head`
  unfolds what's lazy at the top (glued, folded, fields, solved unknowns, stale
  stuck calls). `open_stuck` turns a stuck call that opens by tree into its residual
  tree, for comparison only. That keeps evaluation's results unchanged (no new
  unfolding in read-back, F6), and it matches Lean's split between `whnf_core` (no
  delta) and `lazy_delta_reduction`. Rocq's `whd_stack` and `unfold_reference` are
  split the same way.
- **G2 in `head`, not in `+`'s evaluation** (F6). For a stuck `Nat.add m n`, `head`
  unfolds `n` and re-applies R3 and R4. `head` is called only where a comparison or
  an elimination reads the sum, so goals keep `x + two 0` and only `rfl` and `match`
  look inside. The note offers this as a fallback. It should be the default, because
  evaluation's results feed read-back, and read-back feeds `rewrite`, `match`
  generalisation and hover.

**Alternatives the note didn't weigh:**

- **D. Fall back, and flag, on "different".** Before reporting a conversion failure
  (E-REFL, E-TYPE-MISMATCH, the kernel's rejection), re-run the comparison with every
  lazy form off. If that says "equal", accept it and, in test builds, panic with the
  pair. Failures are rare in the kernel and in final elaborator errors, so it costs
  almost nothing on success paths. It closes G1 to G5 for users at once, and turns
  every test run into an oracle for the fast path. Against: SW-1166's blow-up
  (unglued AoC took 24 min and 13 GB) means the slow path on a large failing term
  can turn an E-REFL into an E-RESOURCE. It doesn't help unification, where
  "different" is common and drives backtracking. And it doesn't touch G6 to G8, where
  the plain relation is itself incomplete. **Verdict:** worth having as a test-build
  assertion in `conv` (a cheap, always-on detector), not as user-facing behaviour.
  It should be part of S1.
- **E. Lean's heights.** Lean picks which side to unfold by a definitional height
  (`ReducibilityHints.regular n`). Stitchwort has no need: it unfolds one side only
  through glued calls and the folded arm, and a stuck call's tree is opened only for
  comparison. Heights would matter only if C makes every call lazy. Note it for C's
  design.
- **F. Agda's `Blocked` (SW-1845).** Recording a stuck call's blocker makes "is this
  rigid?" constant-time, and gives `cases`, `blocked` and `stale` one source of
  truth (F7, F11). It fits behind B's `head`. It's the natural follow-on to S5, more
  than C is.

### 4.2 Speed risks

SW-1829's lesson (record eta's rule 2 re-ran stuck field calls at every level, AoC
over 400 s, then 69 s once the stuck value was kept; `code-review-core.md` F1) applies
to B in three places:

- **`head` on a folded call has no cell**, so every caller recomputes it. In
  `conv_step` that's fine: the result is pushed and seen once. In `walk_tree`, the
  number case and R3/R4, a chain of `d` folded calls can be re-unfolded per level.
  SW-2125 F6 already found O(d²) runs.
- **G6 and G7 in the unifier** make every failing same-head stuck pair try a tree
  comparison, with a trail and an undo. Unification fails a lot by design
  (overloading, instance search, `blocked` postponement).
- **G2 in evaluation** would put an unfolding on the path of every stuck `+`. That's
  F6's reason to keep it in `head`.

**What to measure before committing S5 (and before deciding C):** a counting build (a
`cfg(feature = "reference")` counter, off in release) over std and two or three AoC
days rich in `decreasing` and `+`, reporting:

1. per shape-reading site, how often it meets each lazy form (glued, folded by name,
   field, `k * x`, solved or stale unknown) and each representation;
2. per folded value (by pointer), how many times it's unfolded within one outermost
   comparison or evaluation: the number that decides C;
3. in the unifier, how many same-head stuck pairs fail their spines, and how long the
   tree fallback takes on them.

Plus steps and wall time on those days before and after each fix lane, and the count
of E-RESOURCE failures (§1.1). This is S3's "step counts", made specific.

## 5. The tests

**Is a plain reference the right thing to decide by?** It's the right test for the
laziness half of the rule, G1, G2, G4 and G5, and it is cheap. It isn't enough as the
test of record (F3, F4):

- **It shares policy.** `reference.rs` claims independence (`:10-13`), and its
  *evaluation* is independent. But it calls `crate::value::opens_by_tree` (`:735`),
  `nat_add::stuck` (`:316`), `native::compare_with` and `view_with` (`:392`, `:644`)
  and `proof_field`. A gap in those is in both.
- **It keeps the representations.** Plain mode turns off folds, not `Value::Nat` or
  `Chars`, so G3 (and F7's `cases` gap) pass T1.
- **It shares the stuck-call rule.** G6, G7 and G8 fail in plain mode too.
- **It can be wrong or slow** (F5). It counts no resources and recurses on the Rust
  stack (`reference.rs:14-15`). Plain mode unfolds theorems (computes proofs) and
  `decreasing` fuel eagerly. SW-1166's blow-up came from big programs, as the note
  says, but a single T2 term wrapping a theorem's proof in `idD` can be big. Add a
  step counter that fails (D2543) before T1 lands.

**What I'd make the test of record** (all in `proof_equivalence`, sharing its terms):

1. **Plain agreement**: T1 as proposed, with the budget.
2. **Equivalence**: transitivity over random triples from the pool, not only the
   all-pairs closure the matrix has now. Plus twin helpers (`ignoresFirst` and
   `alsoIgnores`) in the pool. This finds G6.
3. **Substitution stability**: "equal with `n` unknown stays equal at `n = 0, 1`"
   exists already. Widen it to the numbers past the arms of a `NumCase` (3), to
   `Succ`-spelled and literal values, and to compact text. Add alike helpers taking
   a number and a `Bool` first. This finds G3, G7 and G1.
4. **Ground truth on closed terms**: for closed terms of `Nat`, `Bool` and `List Nat`,
   compare the answer with equality of the fully evaluated values. That's an oracle
   with no shared policy, since closed first-order values have one normal form.
5. **Device insertion** (T2): as proposed. Its terms feed 1 to 4.

On the budget: T1 to T5 within `task test:one -- proof_equivalence`, at a few seconds
in release, with a count variable for the daily tier, as the note proposes. T3, the
completeness fuzz, daily tier only. I agree with the note's split. The one change: the
test-build assertion of alternative D (§4.1) costs nothing to run and catches the
laziness class in every test that converts anything.

## 6. The plan

The order (tests, then fixes, then refactor) is right. Changes:

| Stage | Change |
|---|---|
| S0 (new, before S2) | `core.md` text: the corrected rule (F1, F12), with the limits named. Can go in S2 if D3260 is yes. |
| S1 | Add the properties of §5 (transitivity on triples, substitution stability, closed ground truth), the reference's step budget (F5) and the test-build fallback assertion (alternative D). G1 to G8 as known failures. Est. 90 min, not 75. |
| S2 + S4 → one lane | The stuck-call comparison: G1, G3 (scrutinee views), G6 (delta after a spine failure), G7 (open a leaf that is a call), G8 (`NumCase` nodes, or name it a limit), in `value.rs`, `reference.rs` and `unify.rs`. Opus, about 90 min. |
| S3 | G5 and G4 first (small, low risk), then G2 *in `head`*, with §4.2's counts. Opus, 75 min. |
| S3b (new) | Elaborator: `cases`'s `blocker`, `walk` and `is_ctor_form` on numbers and compact text; `omega` and `ring` atoms through the head view (F7). Sonnet, 60 min. |
| S5 | Split it: (a) `Rigid` and `Quick` types and `head` in `conv_step` and `conv_in`; (b) the unifier, with `stale` folded into `head` and `BLOCKED_DEPTH` made a failure or removed (F11). Measure (§4.2) before (a). Opus, 2 × 75 min. |
| S6, S7 | As proposed. Consider F (Agda-style blockers, SW-1845) before C. |

Separate small tickets: F8 (std's `Float` pins unglued) and the `core.md` sentence
"any other shape (a `NumCase`, a number or a list as scrutinee) is different, as before",
which goes when S2 lands.

**Before D3250 is decided:** only the text of the rule. Nothing in the code needs to
change first, and S1 can start either way. Its known-failure list doesn't depend on
the wording.

## Checked and sound

- `conv_step`'s order (`value.rs:3205-3455`): the equal-only shortcuts come first, then
  the folded arm, numbers, compact text, then structure. The `Call` arm forces before
  record eta, as rule 1's comment requires. The note's §3.2 is right about this.
- `unfold_folded` (`value.rs:2490-2530`) and the reference's (`reference.rs:357-385`):
  both stop on "stuck in its own tree" by pointer equality, and the value.rs one
  forces a glued result between levels (SW-2126, SW-2127).
- `native::run` declines a folded argument and the definition's tree runs instead.
  Correct, as the note says. Float primitives have no tree to fall back on, which is
  G4.
- The machine's `NumCase` "every arm below `k`" and `Apart` decisions decide on a
  non-rigid base correctly, because `k + x ≥ k` whatever `x` is. They're the "as far
  as the decision needs" clause of rule E, and they should stay.
- `Head`'s equality ignores `Apart` (`value.rs:175-185`).
- The elaborator postpones an `rfl` whose unknown is solved later (G12), so G3 gives no
  elaborator/kernel disagreement there.
- The unifier's same-head arm (`unify.rs:1576-1608`) puts blocked pairs aside in a
  nested run with a trail, so the G6 fallback has the machinery it needs.

## 1 Nov review (rust-codebase-review.md), in scope

Its only point in this scope is §2.2's praise of `reference.rs` as an independent
evaluator. **Changed:** it is still independent in control flow, but now shares the
shape predicates named in F4. That's fine for its original job (catching machine
mistakes) and too weak for the job the note gives it. `code-review-core.md` F1 (stuck
field calls dropping their cell, likely SW-1829) was fixed by the SW-1829 lane (merge
`38474acaf`, cited in the note). Its lesson is §4.2's first bullet.

## Tickets to file

Grouped into lanes:

1. **Rule text** (Opus, 30 min, or inside lane 3): `core.md` gets the corrected rule C,
   rigid heads, residual trees and named limits (F1, F12). After D3260.
2. **S1 widened** (Sonnet, 90 min): plain switch with a step budget in `reference.rs`;
   transitivity on triples; substitution stability at numbers, literals and text;
   closed ground truth; device insertion; the test-build fallback assertion; G1 to G8
   as known failures. Test: `task test:one -- proof_equivalence`.
3. **Stuck-call comparison** (Opus, 90 min): G1, G3, G6, G7, G8 in `walk_tree` and
   `same_stuck_trees`, the reference's `same_trees` and the unifier's same-head arm.
   Tests: `proof_equivalence`, `conv_shortcut`, `case-tree-chains.sw`, unify unit tests.
4. **Blockers through `head`** (Opus, 75 min): G5, G4, then G2 lazily, with §4.2's
   counts. Tests: `proof_equivalence`, `nat_add_rule`, `natives`, the float gate.
5. **Elaborator shape rules** (Sonnet, 60 min): `cases`'s `blocker`, `walk` and
   `is_ctor_form` on numbers and compact text; `omega` and `ring` atoms (F7). Tests:
   the `cases` and `omega` accept examples touched, plus G9 and G10 as new examples.
6. **`STITCHWORT_GLUE=0` and std's `Float`** (Sonnet, 30-45 min, F8): find why the
   unglued elaboration of `Float.neg`, `abs` and `sub` hashes differently (likely
   SW-1746's folded read-back of solved unknowns), and either make it agree or pin
   by the glued elaboration. Test: the float gate, unglued.
7. **S5a and S5b** (Opus, 75 min each), after the measurements of §4.2: the `Rigid`
   and `Quick` types and `head` in conv and the reference, then the unifier with
   `stale` and `BLOCKED_DEPTH` (F9, F11).

## Questions for Matt

**D3260:** Adopt D3250 with three changes: (a) a stuck call that opens by tree isn't
rigid, and two calls of one such definition whose arguments differ are compared by
their trees (G6), as Lean and Rocq do; (b) the limits (recursive, folded by name and
stuck, lift leaf, native, `NumCase` until fixed) are named, and every mode shares
them; (c) the test of record is the property suite of §5 (agreement with the plain
mode, equivalence, substitution stability, closed ground truth), not the plain
evaluator alone. [rec: yes. (a) is what makes the rule cover G6 and G7 at all. (b) keeps
"laziness changes nothing" a checkable claim. (c) is what finds G3, G6, G7 and G8,
which the plain evaluator passes today.]

## Calls I made

- I ran the release binary on tiny files, as the lane brief allowed (overriding the
  general review brief's "no runs"). The probes are copies in my scratchpad. Nothing
  was run in SW-2242's worktree.
- I count G6 and G7 as delta gaps, not laziness gaps, and put them in one lane with G1
  and G3, because they're all in the same three functions.
- I recommend fixing G8 rather than documenting it, but leave that to the lane, if its
  cost turns out higher than "the same arms, each body compared".
- I didn't probe F11 (the stale-call depth): building a four-deep stale call needs
  more than a two-line file. It's marked medium confidence.
- I judged `rewrite`'s and `match`'s syntactic occurrence search to be by design, not
  a gap. Lean's `rw` makes the same choice.
