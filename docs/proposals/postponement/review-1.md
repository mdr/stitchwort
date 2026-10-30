External review of draft 2, 30 October 2026, as received

I think this is a **good proposal and I would proceed with it**, but I would change two things before treating the design as settled:

1. make the invariant around partially elaborated/“kept” terms much stronger; and
2. strengthen the termination story, because the current argument does not quite cover rollback/re-execution.

The basic idea—one per-declaration queue, blocker-indexed suspended checks, explicit scoped resume points, and defaults only after ordinary information flow has reached quiescence—is considerably cleaner than the collection of catch-and-retry mechanisms it replaces. That is especially compelling given that the existing special cases already recover `E-CANNOT-INFER` **1,073 times in successfully elaborated code**. Postponement Queue Review

The prototype evidence is also unusually useful: all three motivating cases become accepted, 687 rejected examples retain their errors, all AoC/roguelike tests pass, and the measured AoC run is actually about 5% faster. The 26 changed hashes are small enough to inspect individually, which you have done. Postponement Queue Review

## 1. Resume order and semantic soundness

**Creation order within a scope is a perfectly reasonable operational choice. Scoped W1 is also the right choice.**

I would distinguish three properties, though:

- **kernel soundness**: can elaboration produce an ill-typed term?
- **coherence**: can scheduling choose between two distinct well-typed elaborations?
- **predictability**: is that choice understandable to the programmer?

The kernel gives you the first property. It does **not** give you the latter two. As the proposal itself says, every elaborated term is checked independently by the kernel, so a bad queue implementation cannot prove false propositions. Postponement Queue Review But two well-typed terms can of course compute differently.

And you already have evidence that elaboration order affects choices. The unscoped-W1 experiment changes acceptance of the `Counts.size` example because the same postponed syntax is resumed under different transient states. Postponement Queue Review That is exactly the class of behaviour scoped W1 prevents.

So I would state an explicit design principle:

> **Postponement may delay a choice, but must not expose a postponed item to information outside the lexical elaboration scope that would have been available to that item in a non-postponing elaboration.**

That makes scoped W1 more than a heuristic. It becomes an isolation rule.

This is very similar to why Lean has explicit synthesis checkpoints such as `withSynthesize`; pending synthetic metavariables are deliberately processed at controlled boundaries rather than whenever arbitrary metavariables happen to change. [GitHub](https://github.com/leanprover-community/lean4-metaprogramming-book/blob/master/lean/main/07_elaboration.lean?utm_source=chatgpt.com)

### The place I am more worried about: kept receivers

This risk from page 15 deserves promotion from “open question” to **design invariant**:

> “A queued `.field` keeps a receiver elaborated before its type was known, with implicit arguments inserted under assumptions that may later be wrong.” Postponement Queue Review

Suppose elaborating `e` itself involves any choice affected by an expected type, overload resolution, implicit insertion, defaulting, abilities, coercions, etc. Keeping its already-elaborated core term while postponing only `.f` can freeze a choice that would differ if `e` were elaborated once its eventual type was known.

The kernel will catch an **incompatible** choice. It will not catch an alternative **compatible but semantically different** one.

Agda can safely keep an already-checked projection principal because “checked” is doing important work there. Your proposal currently appears to say “anything already elaborated” can be kept. Postponement Queue Review

I would therefore use one of these rules:

**Preferred:** only retain subterms whose elaboration is known to be stable under future information. Otherwise retain syntax + environment and re-elaborate that part.

Or, more conservatively:

> A suspended item may retain a core subterm only if the subterm was elaborated against a fully known type, or if elaboration of that syntactic category is independent of expected-type information.

That would remove my main coherence concern.

---

## 2. Termination

I don't think the current termination argument is complete.

The individual statements are plausible:

- K1 doesn't directly queue itself again;
- K2 advances through finite receiver-type unfolding;
- syntax nodes create finitely many items per surviving attempt;
- defaults remove waiting;
- the ladder itself doesn't snapshot. Postponement Queue Review

The hole is exactly what your question identifies: **“per surviving attempt” is not a global bound**.

A resumed item can enter code that takes snapshots. A later failure can restore an earlier state, recreating a situation in which the same syntax is attempted and queues the same logical item again. Saying that rollback removes its queue entries proves consistency of the restored state, but not that execution cannot revisit that state indefinitely.

You need either a stronger operational invariant or a measure that includes attempts.

I would probably not try to prove termination from “number of queue items decreases”. Instead define queue processing around item states:

```text
waiting(blocker)
running
done
failed
```

and establish:

> Within one non-rolled-back elaboration branch, a particular suspension occurrence can transition `waiting → running` at most once for each strictly more informative blocker state.

Crucially, **a `running` item must not be recursively selected by a nested resume point**.

Then separately bound backtracking:

> Every restoration returns to an explicit finite-choice attempt, and that attempt never retries the same alternative with the same metavariable state.

That second statement is probably already approximately true of Stitchwort's existing snapshot machinery, but the design should say it. Without it, there isn't yet a well-founded measure.

A possible lexicographic argument is:

1. number of unexplored finite alternatives in the current attempt tree;
2. number of unsolved metavariables that can unblock queued items;
3. number of not-yet-resumed suspension occurrences in the current branch;
4. finite K2 receiver-unfolding depth.

Successful unification decreases (2); successful resumption decreases (3) or progresses (4); failure consumes an alternative in (1). Rollback may increase 2–4, but only while strictly decreasing 1.

If you cannot establish a finite attempt tree, then the step budget isn't merely a defensive implementation limit: it is covering an actual gap in the termination argument.

I'd keep the budget regardless.

---

## 3. Is W1 a substitute for delayed unification?

**It is a pragmatic substitute for many cases, but not a complete substitute.**

Your own results establish this nicely. W3/W4 alone are insufficient because an unfilled placeholder can reach `Eq.trans` before the declaration-level point; W1 is needed to fill it earlier. W2 is independently necessary because elaborated local constructs must be resolved before helper lifting. Postponement Queue Review

But the page-15 concern remains:

> a comparison that sees an unfilled placeholder fails instead of waiting; W1 happens to be enough for the present corpus. Postponement Queue Review

I would expect new examples eventually to break this.

Consider a nested construction where:

```text
placeholder is produced
→ a defeq comparison consumes it
→ information solving its blocker arises later in the same non-application construct
```

No number of “end of application” checkpoints makes that general.

So my recommendation is:

**Implement the syntax-postponement queue now, but plan to make unification comparisons themselves suspend on metavariables.**

That doesn't require your unifier to suddenly become an active scheduler. It can return something like:

```text
Yes
No
Blocked(Set UnknownId)
```

rather than just yes/no.

The caller can then turn `Blocked` into a declaration-level constraint. Agda's architecture is closer to this: constraints have blockers and can wake when the relevant metavariable is solved. Postponement Queue Review

This is also the conceptual strength of OmniML: suspension is attached directly to the information dependency and wakes when that dependency changes, rather than relying on a sufficiently dense set of chronological retry points. [arXiv](https://arxiv.org/abs/2511.10343?utm_source=chatgpt.com)

I **would not block this queue work on it**, though. The queue is useful independently.

I might therefore change stage 6 from:

> “Later: let unification wait on unknowns”

to something more explicit such as:

> “Expected follow-up: tri-state unification / postponed defeq constraints, if corpus or fuzzing produces cases where placeholders cross W1 unresolved.”

That acknowledges W1 as an engineering compromise rather than suggesting it is theoretically equivalent.

---

## 4. Default order: record first, then Nat

For the system described here, **yes, field-name default before numeral default is the right order**.

Your prototype gives the reason almost perfectly.

In the list example, choosing `Nat` for `[1, 4]` prematurely prevents the later record choice from establishing that `p.row : Int`. With K4, delaying the numerals lets:

```text
record default
→ Position
→ p.row : Int
→ numerals : Int
```

which is exactly the desirable information-flow direction. Postponement Queue Review

This is also consistent with Lean treating numeral defaulting as a late fallback rather than an ordinary inference step; Lean's postponed elaboration machinery distinguishes ordinary progress from later default-instance processing. [GitHub](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/SyntheticMVars.lean?utm_source=chatgpt.com)

Could there be a case where a numeral ought to choose the record?

For example:

```text
type RN = { x : Nat }
type RI = { x : Int }

{ x = 1 }
```

Conceptually, yes: if `1` had independently become `Nat`, that could help distinguish `RN` from `RI`.

But **under the rule you actually propose**, SW-805 looks only at field *names*. Postponement Queue Review It doesn't perform candidate-directed type checking of fields. So defaulting `1` to Nat does not give the SW-805 rule any additional evidence anyway.

If someday record inference becomes:

> enumerate matching records → check fields against candidates → retain viable candidates

then this question should be revisited. That would be much closer to constraint solving.

For current Stitchwort: **record identity first, Nat last**.

---

## 5. Error reporting

Two separate recommendations.

### A resumed item that fails

Definitely report **its new error against the now-known type**, at the original syntax span.

That is strictly better information than pretending inference was still impossible.

For example, if:

```text
q.x
```

was postponed because `q : ?a`, and eventually `?a = String`, then:

```text
String has no field or function `x`
```

is the real error.

Reporting:

```text
can't tell what q is
```

would now be false.

This matches the Lean behaviour described in the proposal: failures are eventually reported against the postponed syntax with the information now available. Postponement Queue Review

### Several items remain stuck

I would **not simply report every item**.

I'd report every **independent root stuck item**, with a small cap, while suppressing obvious downstream consequences.

For example:

```text
A blocked on ?1
B blocked on placeholder produced by A
C blocked on placeholder produced by B
```

should probably produce A, not three errors.

Whereas:

```text
A blocked on ?1
D blocked on unrelated ?7
```

can profitably report both.

So I'd group waiting items by dependency/root blocker and report perhaps the first 3 independent roots. That gets the advantage of Lean/Idris-style multiple diagnostics without cascades.

---

## 6. Scoped W1

**Yes. Keep it scoped. I would make this non-negotiable.**

Your experiment is stronger evidence than analogy with Lean: unscoped W1 actually changes the accepted language because postponed syntax can run inside speculative attempts that are later rolled back and then run again under a different interpretation. Scoped W1 preserves today's rejection; unscoped W1 accepts the `Counts` example. Postponement Queue Review

That means the scope isn't merely an optimisation.

It's an **elaboration isolation boundary**.

The implementation technique described—snapshotting queue length plus a resumption log, and undoing both newly queued items and resumptions—is therefore exactly the sort of machinery I'd want. Postponement Queue Review

Lean's own use of explicit nested `withSynthesize` regions points in the same direction: synthesis checkpoints can limit themselves to pending work introduced inside a particular region instead of indiscriminately consuming unrelated postponed work. [GitHub](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Binders.lean?utm_source=chatgpt.com)

---

# A few smaller comments

### K3 as `x : ?D => ...`

This is elegant. It reduces method sections to the same underlying problem as dot lookup instead of maintaining their own scheduling semantics:

```text
.f
⇒ x : ?D => x.f
                ^ K2
```

That kind of normalization is exactly what I would want from this refactor. Postponement Queue Review

### Path 3 should indeed remain separate

I agree strongly with keeping “after expected type” proof-search retry separate. That's genuinely a different phenomenon: changing the **goal supplied to a search procedure**, rather than delaying syntax because its input type shape is unavailable. Postponement Queue Review

Trying to force both through one abstraction would make the queue less principled, not more.

### Placeholders should probably be opaque to consumers

The `==` regression where generic equality gets selected because the operand has a placeholder is a warning sign. Postponement Queue Review

I'd lean toward a rule like:

> A synthetic placeholder representing postponed syntax is not ordinary unknown evidence and consumers must not make irreversible elaboration choices from its apparent shape.

Lean makes a related distinction with “synthetic opaque” metavariables precisely because ordinary definitional equality must not simply solve them behind the elaborator's back. [GitHub](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Binders.lean?utm_source=chatgpt.com)

That might prevent other instances of “operator commits while operand is still suspended”.

---

# Suggested change to the design's invariants

I think the document would benefit from a short explicit section along these lines:

> **Queue invariants**
>
> 1. A placeholder represents exactly one suspended source occurrence within one elaboration attempt.
> 2. Only the suspension that created a placeholder may fill it.
> 3. A suspended item is resumed only inside the scope in which it was created.
> 4. A running item cannot recursively resume itself.
> 5. Restoring a snapshot restores queue state and all resumptions made since that snapshot.
> 6. Retained elaborated subterms must be stable under additional type information; otherwise source syntax is retained and re-elaborated.
> 7. Defaults run only when ordinary elaboration, unification, instance solving and effect constraints are quiescent.
> 8. No irreversible elaboration choice may depend on an unfilled postponement placeholder.

Those rules say more about correctness than the particular W1/W2/W3/W4 locations do.

## Bottom line

I'd rate the proposal **approve with revisions**, rather than “needs redesign”.

The architecture is good, the empirical work is convincing, and replacing four bespoke retry mechanisms with one explicit scheduling facility is a worthwhile simplification. The document also does a particularly good job of distinguishing what the prototype actually demonstrates from the unimplemented K3/K4 claims—for example, the crucial `Position`/`Int` behaviour is explicitly marked unverified until K4 exists. Postponement Queue Review

The one thing I would **not** ship merely on the current argument is the claim of termination. And before K2 becomes foundational infrastructure, I'd settle the “kept receiver” rule so that postponement cannot freeze type-sensitive elaboration decisions.

Otherwise, the proposed staged rollout is sensible, including only removing each old path after its counter reaches zero. Postponement Queue Review

My strongest recommendations, in order, are therefore: **keep scoped W1; formalise placeholder/suspension invariants; re-elaborate any receiver that isn't demonstrably stable; strengthen the backtracking termination argument; and treat delayed unification constraints as the likely next step rather than trying to make ever more resume points approximate them.**