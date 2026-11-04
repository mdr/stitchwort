# Review: proof irrelevance, draft 4 (D2355)

**Reviewer:** independent Opus lane (SW-1268), 4 November 2026, at `f4674240f`.
**Scope:** `docs/proposals/proof-irrelevance.md` draft 4, mainly the parts new
in it (§5.1's glued-call part, §5.7's new part, §7.1-7.3, §7.10, the new tests
17-23), read against the code: `crates/core/src/value.rs` (`conv_step`,
`same_spines`, `CallMemo`, `glues`, `is_folded`, `same_stuck_trees` and
`TreeMemo`, `shortcuts_disabled`), `crates/core/src/check.rs` (`admit_group`,
`telescope`), `crates/core/src/unify_index.rs`, `crates/core/src/globals.rs`
(`Def`), `crates/elab/src/unify.rs`, docs/core.md, and Carneiro's thesis (text
extraction).

Line numbers are at `f4674240f`. "[run]" means checked with the release CLI
from the main checkout today; everything else is read from the source.

## Summary

| # | Question | Verdict |
|---|---|---|
| 1 | Soundness of the planned conversion | **Sound** (no false acceptance found), with two spec errors that would break the note's own consistency claims: the bound on masked positions (arity, not telescope) and the incomplete list of shortcuts |
| 2 | Decidability and termination of the checks | **Sound** |
| 3 | §7.10: gluing is an optimisation again; transitivity | **Gap**: the argument is right in outline, but it covers only the shortcuts it lists, and there are more (one in the kernel's tree memo, hidden opaque calls, three in the unifier) |
| 4 | The subject-reduction gap: only constructor fields? | **Gap**: two more sources as specified (positions beyond the arity; hidden opaque calls); both close with small spec changes. Acceptable as stated once they're fixed |
| 5 | Is stage 1 well defined? | **Gap**: several decisions open, the biggest that D1980 (refuse self-referential propositions eliminating into data, part of SW-93) is missing from the note and invalidates tests 18 and 21 as written |
| 6 | Blockers | **No design blocker.** Stage 1 should start once the note has the changes in "Suggested note changes" below; none needs a new decision of Matt's except, perhaps, the order of D1980 |

## 1. Soundness

**Verdict: sound.** I found no way for the planned rules to equate two values
that differ in the proof-irrelevant model, or to change what a program
computes. Two spec points (1.4, 1.5) would let the implementation contradict
the note's own claims if followed literally, but neither is unsound.

Evidence, by the shapes the brief named:

**1.1 Evaluation is untouched.** Nothing in §7 changes `eval`, `force`, `J`,
`case` or the natives; the masks live only in `conv` and the unifier. So a
program computes exactly as today, and erasure and JS are unaffected. Every
equation the masks add is "two proofs of one proposition are equal", which
holds in Carneiro's model (L4 §6, every proposition a set with at most one
element), given the same-type invariant (note §7.4), which matches his
Lemma 3.4(3)'s premise that both sides have the same type. I checked the
thesis text: Lemma 3.4(3) is stated for `Γ ⊢ e : α`, `Γ ⊢ e' : α`, and the
remark that the application case needs both sides typed is there; Corollary
6.8 is the "no proof of ⊥" corollary; §4.1's `κ` / `≡p` split and Theorem
4.7 (Church-Rosser up to `≡p`) are as the note says. The note's uses of the
thesis are accurate.

**1.2 Acc-style recursion on proofs.** Any definition that recurses on a proof
must take it apart with a `case` (structural descent comes from a `case`), and
a `case` with a branch clears the mark (§7.1). Passing the proof to a theorem
or helper that takes it apart (`Acc.inv`-style) clears it too, because that
helper's parameter isn't inert and clause 1 only allows inert positions. With
indices, `Acc` can now be written (§5.5 below), but `E-PROP-ELIM` refuses its
large elimination because its `x` is a data field (docs/core.md:114, D140), so
Carneiro's construction still needs a `Loop`-like type, which D1980 will
refuse.

**1.3 Proofs through constructor fields, partial application, eta, mutual
recursion.** Walked each:

- Storing the parameter in a field clears it (D2354), and so does any
  occurrence the three clauses don't list, so aliasing through a `let`
  (`let y := x` then a `case` on `y`) is caught: clause 1-3 are a whitelist,
  which is the right shape.
- A proof inside a constructor that is itself inside an inert argument
  (`g (Both x y)` at an inert position of `g`) is allowed by clause 1, and is
  safe: `g` never looks at it.
- Partial application: `g x` underapplied with `x` at an inert position of
  `g`, passed to `List.map`, say. Clause 1 allows it; the two partial
  applications compare equal through the mask in `same_spines` /
  `push_eta`, and once applied they unfold under §7.10's claim. Safe.
- Eta: `f` (underapplied, next parameter inert) against `y => f q` compares
  `f x z` with `f x q` at a fresh `z`, both full calls, and the mask skips the
  position. Equal in the model. Transitivity with a third lambda holds.
- Mutual recursion: the greatest fixed point is the right choice, because
  "never looked at" is a safety property, and §7.10's induction is on the
  length of an evaluation, which is finite under the kernel's termination
  check. The round bound in §7.3 (candidates + 1 walks) is right.
- Stuck cases: `case` only appears at the top of a case tree
  (`check.rs:1725`, and `stuck_tree` panics otherwise, `value.rs:1654`), and a
  stuck tree always returns the *definition's* spine
  (`Neutral(Def(id), spine)`, `value.rs:1652`). So D2353's clause 3 is safe:
  an empty `case` on `x` leaves `f`'s call with `x` at `f`'s own, inert,
  position.

**1.4 Indexed families (the note's §11 question 2).** The note's §3 says "data
types have parameters but no indices", which is no longer true: docs/core.md
has indexed families, `case` with index unification, and an impossible branch
has no body (docs/core.md:40, 119-133). Read against `unify_index.rs`:

- D2353 with indices is safe. A branch is impossible only by a *conflict*,
  and conflict and injectivity are only at a data type in `Type`, never at a
  proposition (`unify_index.rs:238-241`, "Proofs are never taken apart",
  D137). So whether a branch is impossible never depends on which proof was
  given.
- Masks and index unification agree. Deletion (`conv`) runs before
  injectivity (`unify_index.rs:184`), so with the field mask
  `MkBox (Inl ())` and `MkBox (Inr ())` at `Box (Unit ∨ Unit)` are deleted,
  not decomposed into the conflicting `Inl () = Inr ()`. I checked this order
  specifically: with injectivity first, a type
  `T: Box (Unit ∨ Unit) → Type = | A: T (MkBox (Inl ()))` plus the field mask
  would give a closed proof of `Void` (`A` accepted at `T (MkBox (Inr ()))`,
  and an all-impossible `case` on it). The order makes this safe, so stage 1
  must keep it: worth a comment at `unify_index.rs:184` and a must-reject
  test.
- Prop-typed *indices* (allowed: a Prop-valued field is always allowed, and
  an index obeys the same rule): the note says data types' proof
  *parameters* are masked, and `Data(D, args)` holds parameters then indices
  (docs/core.md:32). Masking Prop indices would be safe too (index
  unification never conflicts on a proposition), but the note has to say
  which (§5 below).

**1.5 Positions beyond the arity (spec error).** §7.3 step 1 says candidates
come from `check::telescope`, and "positions beyond the telescope (a
definition whose result is a function computed by its case tree) are never
candidates". But `check::telescope` peels *every* `Pi` of the type
(`check.rs:3740-3757`), while the body binds only `Def::arity` parameters
(`globals.rs`, `arity`: "the number of leading lambdas"). For

```
def g (n: Nat): 0 = 0 -> Bool :=
  match n with
    | Zero => h => J (y e => Bool) True h
    | Succ m => g m
```

(accepted today **[run]**; the recursive call `g m` with one argument shows
the arity is 1), position 1 is in the telescope but not bound by the body. The
walk over the body never sees `h`, so it would be *vacuously* inert. A stuck
`g n rfl` and `g n h` (spine `[n, h]`, `value.rs:1652`) would then be equal,
while `g 0 rfl` computes to `True` and `g 0 h` to a stuck `J`. That is a
subject-reduction failure from a definition mask, which §5.7 and §7.10 say
can't happen. The fix is one line: candidates are positions `< Def::arity`,
and `inert_params` has length `arity`. The note's parenthetical already
describes this case; it names the wrong bound.

**1.6 The unifier.** `same_arguments_solving_nothing` (`unify.rs:1278-1294`)
already undoes anything the call shortcut solves, and `same_arguments`
(`unify.rs:1253`) keeps solutions only if all arguments unify, so a
shortcut that fails part-way never leaves a stray solution. The §7.5 rule is
right. Three unifier sites need the shortcut mode and aren't in §7.2's list
(see 3.2).

## 2. Decidability and termination

**Verdict: sound.**

- The inert analysis is a greatest fixed point on a finite set of flags,
  clearing only: at most (candidates + 1) walks of each body in the group,
  each walk finite. It reads terms, never evaluates.
- `conv`'s work: in normal mode it skips more than today. In shortcut mode
  it compares exactly what today's shortcut does, minus the inert arguments
  (constructor fields are compared today too). So relative to *today*, the
  shortcut never falls back where it didn't before; the note's "except that
  the shortcut sometimes unfolds where it didn't" (§0, §7.3) is relative to
  draft 3, not to today, and should say so.
- `CallMemo` keyed by mode: a pair can now be compared once per mode, so at
  most twice where today it is once. I walked `f (f (… (MkBox p)))` against
  the same with `q`: the shortcut-mode chain records each inner pair as
  different in shortcut mode, and the normal-mode fallback at each level
  finds the inner pair's shortcut answered from that record. Linear, as
  today. Worth a bench-style test at depth 24, like SW-395's.
- Normalisation stays as open as the note says; I have nothing to add to
  §5.7.

## 3. §7.10: gluing as an optimisation, and transitivity

**Verdict: gap.** The induction is the right argument, and the two premises
it identifies (inert masks only; shortcut mode compares constructor fields)
are what's needed. Gaps:

**3.1 The relation must be closed under application.** The lambda step
("closures `≈ᵢ` at a fresh variable") and the call step both use that
related closures applied to related arguments give related results, which is
a substitution property of `≈ᵢ` itself. The argument is then a logical
relation proved by induction on evaluation, not a plain induction. It goes
through, since `≈ᵢ` has no field masks and the inert masks are the only other
skips, but the note should say it's what's being assumed. Also: clause 1
should say "inside an argument at an inert position of *some enclosing*
call", since `Fin.ofNatLt`'s `Void.absurd (Bool.falseNotTrue h)` relies on the
outer call, and the walk should stop descending at an inert argument.

**3.2 There are more shortcuts than the four in §7.2.** Each place that
answers "equal" for something that can still unfold, without unfolding it,
needs the shortcut mode:

- **`TreeMemo`** (`value.rs:2886-2930`): pairs found *equal* by
  `same_stuck_trees` are remembered, keyed by relation, level, epoch,
  definitions and shape (`MemoKey`, `value.rs:2861`), and the memo
  is thread-wide for the outermost tree comparison, so it spans nested
  `conv`s in different modes. A pair found equal in normal mode would be
  answered "equal" in shortcut mode. It needs the mode in `MemoKey`, as
  `CallMemo` does. This is the only place in the kernel where "equal" is
  remembered, so it's the one that matters most.
- **Hidden opaque calls**: a call of an opaque definition outside its
  transparency set is `Neutral(Def(f), spine)` and never unfolds
  (`value.rs:1678-1679`; docs/core.md:165, "compares two calls of it by
  their arguments, never by its body"). Compared in normal mode,
  `ou (MkBox p)` and `ou (MkBox q)` are equal while `ou` is hidden, and
  differ where it's transparent (`ou := Box.unbox`). Today transparency only
  ever adds equalities; with field masks it would also remove some. The
  note's §7.3 sees this for inert marks ("an opaque definition's marks come
  from its hidden body too") but not for field masks. Fix: compare a hidden
  call's arguments in shortcut mode (a shortcut that never falls back).
- **The unifier**, beyond `unify.rs:983`: the folded-dictionary arm
  (`unify.rs:999-1004`, `same_arguments`), partial applications
  (`unify.rs:1205-1226`, "the spines, or else eta"), and, most important,
  **calls blocked on a metavariable** (`unify.rs:1185-1204`, "Calls stuck on
  an unknown may be equal without that, once it is solved: their spines are
  compared"). A blocked call will unfold once the metavariable is solved, so
  it's a shortcut. In normal mode, `g ?n (MkBox p)` and `g ?n (MkBox q)` unify,
  then `?n := 0` lets `g` unbox, and the kernel rejects what the elaborator
  accepted. Not unsound (the kernel re-checks), but it's an elaborator/kernel
  disagreement of the kind §7.10 is meant to rule out.

Places I checked that need nothing: `same_closure` / `identical`
(`value.rs:3268-3330`: syntactic identity, stronger than either mode);
`native::compare_lazily` (hands its bases back to `conv`, so the mode just
has to be threaded through `ConvTask`, which is an implementation detail
worth stating); the kernel's stuck-call arm (`value.rs:2537-2553`: a stuck
call can't unfold within the comparison, so field masks there are the §5.7
gap, not a gluing difference).

A refinement the note could mention (not required): field masks only need to
be off for constructors that a case can reach *now*. Inside the spine of a
stuck `Neutral` (not a `Call`), nothing can take them apart during this
comparison, so shortcut mode could keep field masks there. It would make
D2352 cheaper; it isn't needed for correctness.

**3.3 Transitivity.** "Masks are fixed by the head" covers structural
comparison and eta (I walked `f` / `y => f y` / `y => f q`). It doesn't by
itself cover SW-386's comparison of two different definitions by their case
trees, where the heads differ. I believe it holds there too: a tree walk never
scrutinises an inert argument, so `F x p` and `F x q` walk the same branches,
and the leaves are compared with the same masks. But that is a separate step
the note's §6 should state (it's §11 question 3), and the property test
should include by-tree pairs.

## 4. The subject-reduction gap

**Verdict: gap, then acceptable.** As written, the note has two more sources
than constructor fields:

1. positions beyond the arity (1.5), if implemented from the telescope;
2. hidden opaque calls (3.2): a type checked with `f` hidden can stop being
   equal to itself where `f` is transparent, which is the same kind of
   failure (a judgement that changes when more is known).

With those two fixed (arity bound; hidden calls in shortcut mode), I agree
that constructor fields are the only source: data types' proof parameters
can't be one, because types are never taken apart, and inert masks can't be,
by §7.10. The `MkBox`/`Box.unbox` shape (`castViaBox`, `g (MkBox p) n` stuck
on `n`) is a real gap, failures only (an elaborator error, a kernel
rejection of an elaborated term, or the budget), and the note is honest
about it. Acceptable, given the model argument, which I agree with (1.1).

## 5. Is stage 1 well defined?

**Verdict: gap.** An implementer would have to decide:

1. **D1980 (Matt, 30 October, on SW-93):** refuse eliminating a
   self-referential proposition into data, as part of SW-93, measuring
   std/examples/AoC/rogue first. The note doesn't mention it. Under it,
   `steps: Loop → Nat → Bool` and `loopNat: Loop → Nat` are refused, so
   test 18 (both halves, and its paired example) and test 21's must-reject
   can't be written as they are; §5.1's examples become "refused since
   SW-93". `Loop.inv: Loop → Loop` and `bad: Loop → Void` (into `Prop`) stay
   allowed, so tests 7 and 14 survive. Test 21 can use a non-recursive
   one-constructor proposition (`type Tok: Prop = | MkTok`, `tokNat t`).
   The order (D1980 before the masks, in the same branch) should be in §9.
2. **D1981:** record eta must exclude all-proof records. Not stage 1 work,
   but the note should carry it, as SW-93 does.
3. **Prop-typed indices**: masked in `Data` or not (1.4). Recommend: not in
   stage 1, stated explicitly; mask only parameters.
4. **The arity bound** (1.5).
5. **The full list of shortcut sites** (3.2), and that the mode is threaded
   through `ConvTask`/`conv_with`, the `same_stuck_trees` callback and
   `TreeMemo`'s key.
6. **Definitions without a body, and natives.** A natively computed
   definition runs `native::run`, not its body, but its marks would come
   from its body. Today the only native with a proof argument is
   `eqNatSound`, documented as never looking at it (`native.rs:113-118`);
   the note should require "a native never looks at an argument at an
   inert position" (a debug assertion or a test). For a declaration with no
   body: no marks, or all candidates? Recommend no marks.
7. **Clause 2's wording**: kernel lambdas have no domain
   (`term.rs:179`, `Lam(Name, Icit, body)`); the parts values drop are a
   `let`'s type and an `Ann`'s type. Say that.
8. **`reference.rs`**: does it recompute the inert flags independently, or
   read them from `Globals`? "Independently written" (§7.2) suggests the
   former for `conv`; the flags are the riskier part, so recommend an
   independent recomputation, compared in a test.
9. **The check cache** stores and replays the flags (§7.3): that is a cache
   format change. Fine, but list it.
10. **Done criteria.** SW-93's body still says "tests 1-16"; the note has
    23, plus property tests (equivalence, gluing) that need a generator of
    well-typed values of one type, which doesn't exist as far as I can see.
    Say whether the property tests are required for stage 1 or a follow-up,
    and what the bench comparison must show.

Everything else (where the flags go, the fixed point, the `J` boundary,
`CallMemo`'s key, the unifier rule, the undo trail) is specified well enough
to implement.

## 6. Anything else that would block stage 1

Nothing in the design. The masked conversion is sound, decidable, and with
the changes below consistent with gluing. I'd not start stage 1 before the
note has items 1 (D1980 and the test rewrite), 4 (arity) and 5 (the shortcut
list including `TreeMemo`) from §5, because those are the ones an implementer
following the note literally would get wrong.

Small things:

- §3's "Data types have parameters but no indices … So Lean's `Acc` can't be
  written as is" is stale. `Acc` can be declared now; what stops it is
  `E-PROP-ELIM`'s rule against data fields (docs/core.md:114).
- §0: "the shortcut sometimes unfolds where it didn't" is relative to
  draft 3, not today (2).
- §7.2's line numbers for the unifier (`unify.rs:111`, `:118`, `:219`) are
  draft 3's.

## Suggested note changes

1. §7.3 step 1: candidates are positions `< Def::arity`; `inert_params` has
   length `arity`. Add test 24: `g` from 1.5, `g n rfl = g n h` with `n` a
   variable is `E-REFL` (paired: `g 1 h = g 0 h` accepted).
2. §7.2: add `TreeMemo` (mode in `MemoKey`), hidden opaque calls (shortcut
   mode, no fallback), and the unifier's folded, partial-application and
   blocked-on-metavariable sites. Add tests: an opaque `ou := Box.unbox`,
   `ou (MkBox p) = ou (MkBox q)` rejected hidden and transparent; and a
   unit test comparing the same stuck-tree pair in both modes in one `conv`.
3. §5.1, §8, §9: integrate D1980. Rewrite test 18 (the `cast` shape already
   covers the gluing risk; the `Loop` shape becomes a must-reject for
   `E-PROP-ELIM`) and test 21 with a non-recursive proposition; keep 7 and
   14.
4. §3: indexed families exist; §7.1/7.3: say whether Prop indices are
   masked (recommend not); add a comment and a test that index unification's
   deletion runs before injectivity (the `T (MkBox (Inl ()))` shape in 1.4,
   must-reject `E-NONEXHAUSTIVE`/`E-TYPE-MISMATCH`, whichever fires).
5. §7.10: state that the induction is a logical relation (closure under
   application of related values), that clause 1 means any enclosing call,
   and add the by-tree comparison to the transitivity argument (§6) and
   property test.
6. §7.1 clause 2: "a `let`'s type, an `Ann`'s type" (kernel lambdas have no
   domain).
7. §7.3: natives never look at inert arguments (assert); declarations
   without bodies get no marks.
8. §0, §7.3: the fallback cost is relative to draft 3; against today, the
   shortcut falls back no more often.
9. §8: a depth-24 test of nested calls differing only in a proof field, to
   pin `CallMemo`'s linear behaviour with two modes.
10. §5.7: name the two extra sources and say how the changes above remove
    them, so "constructor fields are the only source" is backed by the spec.
11. Carry D1981 in §9 stage 4 or §7.6.
