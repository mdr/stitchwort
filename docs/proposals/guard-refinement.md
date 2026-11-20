# A guard in a proof's `match` that refines the goal

**Status:** design note, 20 November 2026 (SW-4375, from SW-4047 item 1;
docs/reviews/SW-4047-guard-refinement.md). Waiting on Matt: D3701 (§8).
Nothing is built.

Claims are marked **[source]** (read at `666429fbd`), **[measured]** (the
main checkout's release binary, built 11:44 today, on scratch files in the
lane's scratchpad; quoted below) or **[docs]** (other systems, from the
page or source file cited).

## 1. In plain words

**The problem.** A guard in a theorem's `match` tells the arm that its
condition held, but leaves the goal as it was. If the goal is about a
function that tests the same condition, the function's `if` stays stuck
and the arm can't compute through it:

```
def weight (c: Char): Nat := if c == '(' then 1 else 2
theorem weightOpen ∀ (c: Char): 1 <= weight c := match c with
  | c if c == '(' => byComputing   -- E-REFL
  | c => byComputing               -- E-REFL
```

**[measured]** Both arms fail: "computing the left side gives `1 <= (if
c.toNat.equal 40 then 1 else 2)`". Writing the same split as `match g: c ==
'(' with | True => byComputing | False => byComputing` checks: that form
replaces `c == '('` with `True` or `False` in the goal and the hypotheses,
and the `if` computes. Today the proving guide tells people to switch to
that form ("A guard in a proof's `match` gives a fact but refines
nothing"), which means a proof can't follow a program written with guards
arm for arm, which is the natural way to prove things about it.

**The change.** In a proof, read `| p if c => a | rest` as `| p => match
g: c with | True => a | False => rest`: the guard's condition is replaced by
`True` in the arm and by `False` in the arms below, in the goal and in the
hypotheses. The facts the arms get keep today's names and D3699's forms.

**What it should do.** The repro above checks as written. A proof about a
guarded function can mirror the function's own arms (the formatter's
lexer proofs are the main users: `GoodItemProofs.sw:395` mirrors
`Lexer.sw:155`'s `if !isWordChar next`). Programs, their hashes and
existing proofs in the repo are unchanged as far as can be checked without
building (§5.2: five guarded proof arms, all five emulated and still
checking). One kind of proof that checks today stops checking (§6), none of
it in the repo.

## 2. How it works today

**[source]** `check_guard` (crates/elab/src/lib.rs:6953) checks a guarded
arm as `if c then <arm> else <the arms below>` through
`check::check_if_with`. When the goal is a proof, that is `check_proof_if`
(check.rs:7524): `Decidable.elimProof d (h => arm) (_ => rest)`, whose
motive is the goal unchanged (a constant motive). The arm gets `h: P` (for
a `Bool` guard `c`, `P` is `c = True`), the arms below get `¬P`, hidden.
Nothing in the goal or the hypotheses is touched.

**[source]** `match g: e with` (matching.rs, `generalised` →
`generalised_now`, matching.rs:991) generalises: it finds `e` (for a
decided proposition, the `Bool` it decides, matching.rs:559-573) in the
goal and in the hypotheses' types, makes a motive over it, copies the
hypotheses that mention it, checks the motive, and gives each arm the goal
with `True` or `False` in place. Its `decided_if` hook (matching.rs:2373)
also refines a program's `if h:` that was compiled as `Decidable.elim` on
the decision, not only the `Bool` form.

**[measured]** The two forms give different facts:

| written | first arm's fact | below's fact |
|---|---|---|
| `\| n if g: n < 3 =>` | `g: n < 3` | `¬(n < 3)`, unnamed |
| `match g: n < 3 with` | `g: n ≤ 2` (that is `(n <= 2) = True`) | `g: (n <= 2) = False` |
| `\| c if g: c == '(' =>` | `g: (c == '(') = True` | `¬((c == '(') = True)`, unnamed |

## 3. Options

**(a) Refine, as `match g:` does.** A guarded arm in a proof generalises
the guard's condition. End state: one rule, "a guard in a proof splits
like `match` on its condition"; the proving-guide bullet goes, and proofs
follow guarded programs arm by arm. Cost to users: the goal in a guarded
arm may now be computed further than before, so a `rewrite` that used to
do the computing finds nothing (§6). The fact forms stay as today's and
D3699's (§5.4), not `match g:`'s, so `cases`, `arithmetic` and lemma
arguments see the same hypotheses.

**(b) Keep today's split; show the fact (SW-4376).** The goal display lists
an unnamed guard's fact (`(c == '(') = True`, `¬…` below), which `cases`
already uses but the user can't see. End state: guards stay "a fact, no
refinement"; to compute through a program's `if` the user still rewrites
by hand (`rewrite g`, or the function's equation `weight.eq1 … g`) or
rewrites the proof as `match g:`. Cost: nothing breaks; the repro still
fails, and the user has to learn the difference between the two splits.

**(c) Both.** (a) plus SW-4376's display. Under (a) the display is still
wanted: refinement replaces the condition in the goal, but where the goal
didn't mention it (`pattern-guards.sw:144`, goal `m = 0 ∨ m > 0`) the fact
is the only trace of the guard, and `arithmetic` / `cases` use it unseen.
SW-4376 is independent and small; (c) costs (a) plus a Sonnet ticket.

(d) **Refine only when a name is given** (`| p if g: c =>`) was considered
and dropped: it makes the name change the meaning, which Stitchwort avoids
elsewhere (a `match` refines whether named or not).

## 4. Prior art

- **Lean 4.** `match` has no guards: the alternative grammar is `with (|
  (term,*)|* => term)*` **[docs]** (Lean reference, "Pattern Matching",
  lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/). Its `match`
  generalises by default: "the pattern match elaborator automatically
  determines the motive by finding occurrences of the discriminants in the
  expected type", and occurrences in the context's variables "are
  generalized and substituted by default", off with `(generalizing :=
  false)` **[docs]** (same page). The tactic-mode `if t then tac1 else
  tac2` is `by_cases t`, which only adds `h : t` / `h : ¬t` to the context
  **[docs]** (docstring of `tacIfThenElse`, src/Init/Tactics.lean, and
  `by_cases`, src/Init/ByCases.lean, lean4 master): that is today's
  Stitchwort guard. `split` is the refining form: "given `n : Nat`, and a
  target `if n = 0 then Q else R`, `split` will generate one goal with
  hypothesis `n = 0` and target `Q`, and a second goal with hypothesis
  `¬n = 0` and target `R`" **[docs]** (`split` docstring, same file). So
  Lean offers both, under different names; the one users reach for on a
  goal with the program's `if` in it is `split`, which refines.
- **Rocq / Equations.** Gallina's `match` has no guards (not re-checked
  here). Equations' `with` clauses are its guards: "we actually abstract
  the discriminee term from the expected type of the clause", so the
  clause's type is refined, and each `with` node becomes an auxiliary
  definition whose equation is "an indirection to the auxiliary
  definition" **[docs]** (doc/equations_intro.v in the Coq-Equations repo).
  How `funelim` treats a `with` was not found in that file; not checked.
- **Agda.** `with` abstraction is the classic form: "All occurrences of the
  term in the goal type and argument types will be generalised", and this
  "is not always type correct and may result in a (sometimes cryptic) type
  error" **[docs]** (Agda docs, "With-Abstraction"). Idris's `with` is said
  to be the same; not checked.

So where a proof assistant has a guard-like construct inside a match
(Equations' and Agda's `with`), it refines the goal; the non-refining form
exists only as a separate tactic (`by_cases`). Option (a) puts Stitchwort's
guard with `with`; today's behaviour is `by_cases` spelled like `with`.
The ill-typed abstraction Agda warns about is §6's second case.

## 5. Effects

### 5.1 Terms

Theorem terms change for guarded proof arms: `Decidable.elimProof` with a
constant motive becomes the generalised `match`'s helper. Programs are not
touched (`check_proof_if` runs only for a proof goal), so no definition's
hash changes, and std's native pins are unaffected. Theorems with a
guarded arm get new hashes; migration cost doesn't count (D2303).

### 5.2 Existing proofs

A scan of every tracked `.sw` file (an awk pass for arms `| … if … =>`
inside `theorem`s; it can miss a guard written over several lines or a
proof-valued `def`) finds 14 guarded arms in theorems. Nine are in programs
written inside a theorem's statement (`Parse.Gives (() => match … | Some
kind if takes kind => …)` in tools/fmt and tools/toyfmt): their goal is
data, so they're unaffected. Five are proof arms:

| arm | goal mentions the guard? | emulated as `match g:` |
|---|---|---|
| `examples/accept/pattern-guards.sw:144` `\| n, m if n > 5 ∧ m > 0 => Inr arithmetic` | no | checks |
| `examples/accept/pattern-guard-proofs.sw:26` `\| n if n < 3 => Inl arithmetic` | yes (`n < 3 ∨ 3 <= n`) | checks |
| `examples/accept/catch-all-facts.sw:62` `\| 5 if b => Inl byDecision` | no | checks |
| `examples/goals/catch-all-facts.sw:33` `\| 5 if b => ?` | no (`p n`) | goal text unchanged, expected |
| `tools/fmt/src/Syntax/GoodItemProofs.sw:395` `\| ['!','i','n',next,.._] if !isWordChar next => cases` | yes (`symbol input`) | a miniature checks |

**[measured]** "Emulated" means each was rewritten into the `match g:` form
in a scratch file (`em2.sw`; the fmt one as a 3-arm `symbol`/`fixed`
miniature of `Lexer.sw:155`) and checked with today's binary: all pass.
The emulation gives `match g:`'s fact forms, not the guard's (§5.4), which
matters only to `arithmetic` on a proposition guard, which handled both.
The fmt file itself wasn't checked (paper lane), so the real
`symbolFixed` is the one to watch in the build lane.

**[measured]** Hypotheses and lemma arguments survive refinement: in a
`match g: n < 3` arm, closing `1 <= weight n` with a lemma `pos n: 1 <=
weight n`, or with a hypothesis `h: 1 <= weight n` passed to a function
expecting that type, both check (`k.sw`).

### 5.3 `E-REWRITE-NOTHING`

**[measured]** A rewrite whose job was to do the refinement by hand finds
nothing once the arm is refined. Both of these check today and fail in the
`match g:` form, with `E-REWRITE-NOTHING`:

```
| c if g: c == '(' => rewrite g                              -- d.sw
| n if g: n <= limit => rewrite clamp.eq1 limit n g then arithmetic   -- m.sw
```

The second is the pattern D3699's guard equations were shaped for (the
equation takes the guard's fact in its own form), so it is the likely one
in the wild. In the refined arm the goal is already `n ≤ limit`; the error
even says "the proof checks without this rewrite: the goal already
computed past it; drop the `rewrite`". No proof in the repo does either
(no guarded proof arm is named, §5.2). See §6 for what to do about it.

### 5.4 Fact forms, proposition guards and `&&`

The refinement should change only what the arms' goals and hypotheses
look like, never which fact the guard gives, so the forms stay D3699's
(docs/syntax.md, "Equations"; pattern-guards.md, "Changed by D3699"),
which `f.eqK` and `f.induct` already use:

- **A `Bool` guard `c`** (a comparison on data, `xs == []`, `isWordChar
  next`): split on `c` itself; the arm gets `c = True`, the arms below
  `c = False`. Today the arms below get `¬(c = True)`, so this also brings
  the in-proof guard into line with D3699's `notArmJ`.
- **A proposition guard** (`n < 3`, `n ≠ 3`, `if h: P`): split on its
  decision's test `d.holds` (what `match g: P` matches,
  matching.rs:559-573), and give the arm `P` by `d.sound`, the arms below
  `¬P` by `d.refute`, as today, not `match g:`'s `(n <= 2) = True`. This
  refines both ways a program can have compiled `if P`: the `Bool` form
  (`unused_proof_if`) through the scrutinee, and the `Decidable.elim` form
  (when the program used the proof) through `decided_if`. An `if h: P`
  whose `P` is `b = True` fails as `b = False`, as D3699 says.
- **`&&` guards** are one `Bool`, `(a && b)`, not split (D3699): the
  refinement replaces `a && b` where the goal has it, and nothing where the
  goal has only `a`; the arm reads the conjunction with `guard.read` as
  today. A conjunction of decided sides whose proof the arm uses (SW-4344,
  `if i < n && 0 < i => xs.getLt i`) splits on the decision of `P ∧ Q`, so
  `decided_if` refines the program's `Decidable.elim`, and its fact stays
  `(i < n && 0 < i) = True` as SW-4344 states it. A chain with a computed
  middle (`lo <= f x <= hi`) has its middle put back, as for every fact.
- **Names** don't change: the arm sees its `g` if it named one, the arms
  below see nothing by name (`auto` and `cases` still find the hidden
  fact), as pattern-guards.md §3.3 says.

The same three forms are what `byWalking` (SW-4239) and `f.induct` split
guards into, so a proof by arms, by walking and by induction see the same
facts.

## 6. D3688: can a proof that checks today stop checking?

Yes, in two ways, so Matt should see them, though D3688 is about proved
tools and this is the proof language itself.

1. **A rewrite that did the refinement by hand** (§5.3): `rewrite g`,
   `rewrite g at h`, or `rewrite f.eqK … g` where the call's `if` is the
   guard's own condition. Mitigation (a1): in a guarded proof arm, a
   rewrite that finds nothing because the guard's refinement already made
   the change is a warning (`W-REWRITE-GUARD-REFINED`, quick fix "drop the
   `rewrite`"), not an error; the rewrite's equation is then simply not
   used. The elaborator already detects this case (the "checks without
   this rewrite" note). With (a1) these proofs keep checking. Without it,
   they need the rewrite dropped. Zero such proofs in the repo.
2. **An ill-typed generalisation** (Agda's "sometimes cryptic type
   error"): a hypothesis whose type depends on the condition in a way the
   motive can't abstract, or a condition that can't be found until an
   unknown is solved (`blocker`, which makes a `match` wait). Mitigation:
   when the generalisation fails or would wait, fall back to today's
   non-refining split for that guard, silently. Then no proof fails for
   this reason; it only doesn't gain anything.

With both mitigations, every proof that checks today still checks, so (a)
is a pure widening; that is what I recommend. The costs of the
mitigations: (1) makes a guarded arm accept a pointless rewrite that a
`match g:` arm rejects; (2) means "a guard refines" has an exception the
user can't see (the arm behaves as today), which a later `W-` warning could
show if it confuses anyone.

## 7. Implementation sketch and size

- `check_guard` (lib.rs:6953): when the goal is a proof
  (`check::proof_expected`), build the condition as a scrutinee (the
  `Bool` from `logic::condition`, or the decision's `holds` for a
  proposition) and call a new matching.rs entry point that generalises one
  `Bool` scrutinee and takes its two arms as closures (the arm's leaf
  check and the `otherwise` tree check, as `CheckedBranch` does today),
  instead of `Alt`s. It reuses `generalised_now`'s occurrence test,
  hypothesis copying and motive check; the only new code is the closures
  and binding the arms' facts in §5.4's forms instead of `match g:`'s
  equation.
- Fallback: on a motive error or a `blocker`, call `check_proof_if` as
  today (§6.2).
- (a1): mark the arm's context as "refined by a guard" so the rewrite's
  `E-REWRITE-NOTHING` path, in the case its note 2 already detects,
  warns instead.
- Tests: the repro (accept), the `clamp.eq1` rewrite (accept with the
  warning), a proposition guard whose program used `Decidable.elim`, a
  `&&` guard, a guard on a pattern variable of a list pattern
  (`GoodItemProofs` shape), the fallback (a dependent hypothesis), the goal
  snapshot of `examples/goals/catch-all-facts.sw`, and the five arms of
  §5.2; plus the soundness set, since theorem terms change.
- Docs: drop the proving-guide bullet and say how guards split; update
  docs/syntax.md (pattern guards), pattern-guards.md §3.3/§4 and the guide's
  proofs chapter.

Size: Opus (proof semantics, the `match` machinery). The D3699 lanes took
about 45 min (SW-4341, 07:40 to 08:27 with review) and 16 min (SW-4344);
this one adds a new entry point into the generalisation, so about 75 min,
plus 20 min for (a1); SW-4376 (display) separately, about 20 min on
Sonnet.

## 8. Recommendation and the decision

Recommend **(c) with both §6 mitigations**: a guard in a proof refines the
goal and hypotheses as `match` does, keeping D3699's fact forms; a rewrite
made pointless by that refinement warns instead of failing; a guard that
can't be generalised splits as today; and SW-4376 shows the fact. No
proof that checks today stops checking, the repro checks, and a proof can
follow a guarded program arm by arm, as Equations' and Agda's `with` allow.

**D3701:** should a guard in a proof's `match` refine the goal and
hypotheses as `match g:` on its condition does (keeping today's fact
forms), with a pointless rewrite left as a warning and a fallback to
today's split where the goal can't be generalised? [rec: yes]
