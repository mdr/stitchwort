# Proposal: refold proofs by irrelevance, not by read-back shape

**Status:** draft 1, 28 November 2026; a design note, nothing built. Ticket
SW-4983, from SW-4905's findings. Recommendation: **yes, in a narrower form
than the ticket asks**: compare refold's forms up to proofs at proof
positions (stage 1, no types needed), and leave folding whole proof
subterms by their type (the ticket's rule) for later, only if stage 1's
measurements show it is worth its cost.

## The problem

When a solution is put back inside a `let`, `unify::refold` folds each
occurrence of the `let`'s value back to its variable, so the program shares
the value and the term stays small. It finds occurrences by shape: it reads
the value back in up to three forms (`unify::value_forms`: as written,
folded, unfolded), keeps those `unify::worth_folding` allows, and compares
each with every subterm of the solution (`matching::same_shifted`, in
`refold`'s hook). The forms are collected by `unify::zonk_let` and, for a
lifted helper, by `Lift::around` (`crates/elab/src/lift.rs`), which also
refolds each `let`'s forms by the `let`s before it.

So a data `let` that mentions a proof `let` folds only if the proof inside
the solution has the same read-back as the proof inside the `let`'s form.
In derived `Ord`'s `%equal` (`derive_ord.rs`, the `tagged` branch):

```
let %t := Ordering.tagsEqual c (T.%tag %s) (T.%fields (C %a0 …) %s) %h
let %e : T.%tag %s = c := Eq.flipped (And.left %t)
let %b0 := T.%C%0%at %s %e
```

The solutions (found on unfolded goals, D484) hold `T.%C%0%at %s P`, where
`P` is `%e`'s value read back unfolded. `%b0`'s own forms, refolded by
`Lift::around`, are `T.%C%0%at %s %e`. They match only because `%e`'s
unfolded form is in the table: the solution's `P` folds to `%e` first, then
`T.%C%0%at %s %e` folds to `%b0`. SW-4905 tried skipping the unfolded form
of proof-valued `let`s (it is costly: `%sameIff`'s `%k` ran into
`cheap_limits` after about 26 K steps); `%b0` then stopped folding, and
`%equal`'s term in `examples/accept/derive-ord-data.sw` grew from about 28 K
to 42 K characters (measured in SW-4905), moving the hashes of
`derive-ord-data`, `eqeq-proof-fields` and `update-identity`.

Yet the proof argument can't matter. `T.%C%0%at`'s second parameter is a
proposition, so by rule I (docs/core.md, "Proof irrelevance") any two
proofs there are equal, and `T.%C%0%at %s P` is `T.%C%0%at %s %e` to the
kernel, whatever `P` is.

## The change

**Stage 1 (recommended now): match up to proofs.** In `refold`'s hook, call
`matching::same_shifted_but_proofs(g, normal, t, by + under, 0)` instead of
`matching::same_shifted`. That function already exists (SW-4674, for
`rewrite`'s searches): below a head that matched, it takes two arguments at
a proof position as equal without looking at them, where a proof position
is read off marks the kernel derived: a definition's parameter whose type
is a proposition (`matching::proof_parameter`, the binder marks on its
type), a constructor's proof field (`Ctor::field_sorts`) and a data type's
proof parameter (`Data::proof_params`). It skips nothing at the root, and
nothing that still mentions an unknown. One companion change: in
`unify::ctor_type_fixed`, a proof field no longer counts towards fixing a
constructor's parameters (it is skipped by the comparison, so it can't fix
anything the folded term relies on).

Then, as a second commit in the same lane, retry SW-4905's skip: a `let`
whose type is a proposition (`value::mark_of_type`) gets only its as-written
form from `value_forms`, no folded or unfolded read-back.

**Stage 2 (not now): fold whole proofs by type.** At a subterm that is a
proof (on a term, a call whose head is a definition with `Def::proof`, as
`value::is_proof` reads it), compute its type and fold it to a proof `let`
in scope whose type converts with it. Details and costs in §3.

## What it should do

- **Robustness (by construction).** A data `let` whose value takes a proof
  folds back whatever form that proof was read back in. The `%b0` failure
  in SW-4905 can't happen.
- **Term size: stage 1 alone, about unchanged; stage 1 with the skip, about
  28 K characters for `%equal`, not 42 K** (estimated: the 14 K SW-4905 saw
  was `%b0`-like occurrences failing to fold, which stage 1 folds without
  `%e`'s forms). Whether the skip leaves any whole unfolded proof of `%e`'s
  proposition unfolded elsewhere in the term (a proof unknown solved with
  the other side, by the unifier's `by_rule_i`) can only be measured; if
  it does, those are what stage 2 is for.
- **Steps: a small saving** (estimated). The skip avoids two read-backs of
  every proof `let` that isn't a function (functions already get none,
  SW-4905). SW-4905 measured the proof skip alone at 2.60 M steps and the
  function skip alone at 2.58 M for `derive_cost`'s 16 constructors of 3
  fields; the two overlap on `%k`, so what the skip adds on top of today's
  2.58 M isn't known, likely a few percent at most. Stage 1's comparison
  costs one mark lookup per argument of a call compared, about what
  `same_shifted` already costs.
- **Hashes** of declarations whose terms change move (full hashes only for
  proofs such as `%equal`: a theorem's interface hash covers its statement,
  `crates/core/src/hash.rs`). Migration cost doesn't count (D2303).
- **Messages: none change** (expected). `refold`'s output goes to the
  kernel and into lifted helpers, not into messages: goals and type errors
  are printed from values (`pretty::term_for_message` on read-backs), not
  from zonked solutions. The test plan checks this.

## 1. Soundness

The kernel checks every term, so a wrong fold is a rejection (an internal
error), never an unsound acceptance. The question is whether the folded
term is always accepted.

Folding replaces a subterm `t` (at a position where it was checked at type
`T`) by `let`-variable `x : A` whose value read back is `n`. The kernel
accepts `x` there iff `A ≡ T`.

- **`n ≡ t`.** They are equal except at proof positions. There both sides
  are proofs of one proposition (the position's parameter type,
  instantiated at the arguments before it, which are equal by induction
  along the spine), so rule I makes them equal: "two values both marked
  proofs are equal", and the relation stays an equivalence because marks
  are decided from the value alone and survive substitution (docs/core.md,
  rule I; `value::by_rule_i`, `value::is_proof`). Its precondition, both
  sides having one type, is what the induction gives. The kernel marks
  every binder itself (docs/core.md, "Proof marks": it never trusts the
  elaborator's), so both sides are marked when it compares them.
- **`A ≡ T`.** `n` is `type_fixed` (`worth_folding`): a call of a variable
  or definition, whose type is its codomain at the written arguments, so
  `t`'s type is the same codomain at arguments equal to `n`'s, `T ≡ A` by
  congruence. A constructor's type is its data type at its parameters,
  which the term doesn't write: `ctor_type_fixed` requires a field that
  fixes each one. A proof field that is skipped can't be that field
  (`C (p : Foo a)` with only `p` mentioning `a` would let `C p1 : D A` fold
  into a position of type `D B`), hence the companion change. A data
  type's proof parameter is no concern: `Data(..)` is a type, whose own
  type (its sort) doesn't depend on the arguments.
- **`J`'s proof is not skipped**, and `same_in` already compares it: `J`'s
  result type depends on the proof's right end, which only its type gives.
- **At the root nothing is skipped** (`same_in`, finding E of
  docs/proposals/full-proof-irrelevance-audit.md): a proof `let`'s form
  would otherwise match every proof. Folding a whole proof needs its type:
  stage 2.

Running is unaffected: proofs are erased (docs/core.md, "Running a
program"), and a proof `let` the kernel marked is skipped at run time.

Stage 2's soundness is the same argument at the root: `t : P` with `P`
computed from `t`'s head, `x : A` with `A ≡ P` checked by the kernel's
`value::conv` (no unknowns, no solving) in the context at the occurrence.
Then the kernel accepts `x` against `T ≡ P ≡ A`, and anything containing it
is unchanged up to rule I.

## 2. Stage 1 in detail

- `unify::refold`: the hook takes `g` (it has it) and calls
  `same_shifted_but_proofs`. `same_proofs`' "no unknown in either" rule is
  right here too: a kept unknown (`keep`) may still be solved.
- `unify::ctor_type_fixed`: skip field `i` when `Ctor::field_sorts[i]` is
  `Prop`. This can only make fewer forms `worth_folding`; it bites only
  for a parameter that no data field fixes, only a proof field whose type
  is a data type mentioning it (`rigidly_mentions` never looks into an
  equation, and `Refl` isn't fixed), which is rare.
- `unify::value_forms`: for a value whose type is a proposition, only
  `quote_as_written`. `value_forms` doesn't see the type, so the callers
  pass the mark: `zonk_let` has the `let`'s type `a`, `Lift::around` the
  draft's `let` (`draft.lets[l]`). With rule F, a proof's folded and
  as-written read-backs differ only in their arguments' read-back, and
  those arguments sit at positions stage 1 now skips when they are proofs.
- Docs: `refold`'s and `value_forms`' comments, and the note in
  `same_shifted_but_proofs` that it serves searches ("where the head fixes
  the types of the arguments compared": refold's `worth_folding` gives the
  same guarantee).

## 3. Stage 2: folding by type, and why not yet

**Candidates.** Only proof subterms whose type can be computed from the
term alone: a call `f a1 … ak` with `f` a definition marked `Def::proof`
(rule F keeps proof calls folded, so nearly every proof in a read-back is
one). Not a variable applied to arguments when the variable is bound
inside the term: `Term::Lam` doesn't write its parameter's type, so nothing
gives it. Not `Refl` (its type isn't written) and not a constructor of a
proposition with parameters (those aren't written either). Only maximal
candidates: once a proof doesn't fold, its inside is irrelevant and is
still searched by shape only, so each node is typed at most once.

**Cost per candidate.** Evaluate the arguments in an environment of
variables (`Value::var` at each level, as `zonk_let` does), instantiate
`f`'s type at them, and `conv` the result against each proof `let`'s type
in scope (values use levels, so the `let`'s type, evaluated once at its
`let`, needs no shifting). Evaluation is lazy and linear in the argument
terms; the conversion is usually of two small propositions (`T.%tag %s = c`),
but a proposition that computes can make it as costly as any `conv`. Both
fit in `cheap_limits` as an attempt (`unify::cheaply`), with one budget per
`refold` call rather than per candidate, so a solution full of proofs costs
at most one budget. A cheap filter first: the codomain's head read off
`f`'s declared type (an equation, or a data type's id) against each `let`
type's head; most pairs differ there and cost nothing more.

**Gain.** Where stage 1 already folds every data occurrence, what is left
is whole proofs spelled out in a different form from every proof `let` of
their proposition. They cost term size and hashing time only: the kernel
compares any two proofs by rule I without looking inside, so their size
never costs a comparison. Estimated small for the three examples, since
proofs reach solutions mostly as arguments of data calls (`%at`) or inside
equations' sides, which stage 1 covers; measure after stage 1 before
building it.

**What it would need beyond that.** Plumbing of the binder context into
`fold_back` (it walks terms with only a count of binders crossed), so a
candidate's free variables can be given values; and care with
`Lift::around`'s case-split scopes, where a `let`'s form is in a context
with fields bound after the `let` (its type would be too).

## 4. Test plan

Lane tests, by name, one command at a time:

1. A unit test beside
   `unify::tests::a_let_whose_value_mentions_a_later_variable_folds_back_where_it_is_in_scope`,
   on `proof_fixture`'s types: a form `f x p` (`f` with a proof parameter)
   folds a solution's `f x q` for a different proof `q`; a constructor with
   a proof field folds with a different field; a constructor whose only
   field fixing a parameter is a proof doesn't fold; a bare proof form
   folds nothing but itself (the root rule). It fails before the change
   (the first two cases).
2. `derive_cost` (`crates/driver/tests/library/derive_cost.rs`): record
   the steps before and after, with and without the skip, for the
   performance log.
3. `check` of `examples/accept/derive-ord-data.sw`, `eqeq-proof-fields.sw`
   and `update-identity.sw`: they check and their tests pass. For the term
   size, `STITCHWORT_DUMP_KERNEL=Main.Shape.%equal` doesn't do today: its
   printer writes a case tree as `case r of …` (`pretty::Printer::go_rest`),
   so it prints about 150 characters for `%equal`. The lane should make the
   dump print in full (`pretty::term_in_full`), a small change that also
   serves later work, and record `%equal`'s length before and after.

Verifier, after merging: `hash_stability` re-recorded and checked
(`task snap:hashes`; term-changing lanes re-record prelude, examples and
projects), `pinned_hashes`, `std_library`, and the example kinds, whose
reject examples pin every message: a changed message there stops the lane.
The orchestrator's usual whole `tools/fmt` `check --no-cache` for an
elaborator change, since `refold` runs in every elaboration with `let`s.

## 5. Decisions

None for Matt, in this author's view: the change keeps every result,
message and proof, changes only the shape of elaborated terms (and so
hashes, D2303), and the kernel still checks everything. It is not quite
under D3447, which assumes hashes unchanged, so the orchestrator should
confirm it is its call.
