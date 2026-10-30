External review of draft 1, 30 October 2026, as received

I think this is a strong proposal and I would accept the overall design, with a few changes before implementation. The most important are: **make `cases` introduce leading Π-bound variables automatically; keep `Finite` minimal; and treat the new “split when unstuck” behaviour more carefully than the current “latest variable” heuristic.**

The conceptual decomposition is particularly good. Stitchwort already has two distinct mechanisms hiding here: `auto`/`Decidable` proves closed computational propositions, while `cases` specializes open expressions until ordinary definitional equality, hypotheses, contradiction, or `omega` can finish them. That distinction explains why `tabulateSame`—with its arbitrary `costs` function—really is a case-splitting problem rather than a decision-procedure problem. Truth-Table Proofs Review

### 1. I agree: don't add a `decide` keyword

You effectively already have it:

```text
def byDecision [p: Prop] [auto h: p]: p := h
```

and the important semantics are already provided by `auto`: run the `Decidable`, emit a normal `Decidable.fromYes ...` proof, and have the kernel verify it. Truth-Table Proofs Review

I don't think syntax-level familiarity with Lean is enough justification for another primitive-looking proof construct. In fact, I slightly prefer Stitchwort's distinction:

- `byDecision` = prove this closed decidable proposition computationally.
- `cases` = establish this by finite structural case analysis.
- `omega` = arithmetic procedure.

Those names say something meaningful about the proof.

I **would**, however, make `byDecision` a blessed standard-library idiom rather than treating it as merely an example helper. That gives users the discoverability benefit of Lean's `by decide` without adding language machinery.

Lean itself reinforces the architectural distinction rather than undermining it: current Lean's `decide` requires a closed target unless variables are reverted, and `decide +kernel` exists specifically to have the kernel perform the reduction once. [Lean Language](https://lean-lang.org/doc/reference/latest/ValidatingProofs/?utm_source=chatgpt.com)

### 2. The decision closer is sound

I see no trust problem here.

The proposed closer:

1. synthesizes a `Decidable p`;
2. the elaborator evaluates it;
3. if it gets `Yes`, it emits an ordinary `Decidable.fromYes d Trivial`;
4. the kernel evaluates/checks that term itself.

That's exactly the existing `auto` proof story, merely invoked as one of the leaf closers of `cases`. Truth-Table Proofs Review

So I agree with the document's claim that **nothing new enters the trusted base**: `cases` still emits ordinary match trees, the decision closer emits proof terms already emitted by `auto`, and `Finite` is normal checked library code. Truth-Table Proofs Review

I would keep elaborator-first evaluation rather than trying to emulate Lean's `+kernel` mode initially. The duplicate evaluation is theoretically inelegant, but here it buys something valuable: `cases` can say **which split failed and that the residual proposition decided false**. The whole feature is aimed at tiny truth tables; optimizing away one evaluation isn't worth damaging that UX.

If this eventually becomes expensive, *then* a kernel-only evaluation API might be worthwhile as a general compiler facility, rather than something special inside `cases`.

One small ordering question: I'm not convinced the decision closer intrinsically belongs **before `omega`**. Truth-Table Proofs Review If both are applicable, `omega` can prove symbolic statements whereas a decision closer only helps sufficiently closed ones. But since you explicitly require that nothing be stuck on a variable, the overlap is probably tiny. I wouldn't block the design on it.

### 3. I would definitely add Π-introduction to `cases`

This is my strongest requested change.

The page-9 discovery shows that:

```text
theorem foo (x: Bool): ... := cases
```

works while the equivalent:

```text
theorem foo: (x: Bool) → ... := cases
```

doesn't. Truth-Table Proofs Review

That is a bad distinction for a high-level tactic. Whether a binder has already been introduced is an implementation-state fact, not something users should have to understand when asking Stitchwort to perform exhaustive case analysis.

I'd therefore make the algorithm approximately:

```text
cases:
    introduce leading Π binders as necessary
    repeat existing "goal stuck on x" splitting
    try closers
    if still unsolved:
        consider fallback finite splitting
```

That also brings Stitchwort conceptually closer to what Lean achieves through `decide +revert`, without needing an explicit `revert` operation in ordinary use. Lean's current implementation explicitly supports moving relevant locals into the target for essentially this reason. [Lean Language](https://lean-lang.org/doc/reference/latest/ValidatingProofs/?utm_source=chatgpt.com)

I'd put this in the proposal as **part of SW-800**, rather than relegating it to an optional third addition.

### 4. “Split the latest mentioned variable” is the part I'd reconsider

The idea of splitting a variable even when evaluation isn't currently blocked on it is right. Otherwise `everyNumericKey` remains an artificial hole in the tactic's behaviour. Truth-Table Proofs Review

But:

> split the latest variable in scope that the goal mentions

feels too syntactic.

Consider a goal mentioning a 12-constructor enumeration `big` and a `Bool flag`. Choosing one merely because it was introduced later can make the difference between 2 and 12 branches. In more complicated goals, repeated choices can amplify badly.

I'd make this a **fallback search heuristic with a cost**, perhaps:

> When no ordinary split or closer applies, choose a mentioned splittable variable whose elimination may make progress, preferring the variable with the smallest branching factor.

Even just **smallest number of resulting cases, ties broken by recency** is a stronger default.

You could go further and inspect occurrences, but I don't think it's necessary yet.

The 64-leaf budget protects you from catastrophe, so this isn't a soundness issue; it's mainly about keeping `cases` predictable.

I would also make the diagnostic explicit when this fallback happened. If it subsequently blows the budget:

> `cases` tried splitting `foo : Foo` as a fallback; this would exceed the 64-case budget.

That will make future heuristic mistakes much easier to diagnose.

### 5. `Finite` is the right abstraction for this job

For the actual requirement,

```text
interface Finite (a: Type) = {
  all: List a,
  complete: (x: a) → x ∈ all
}
```

is enough. Truth-Table Proofs Review

I **would not require duplicate-freedom yet**.

`Finite.check` only needs coverage. Duplicates make checking inefficient, but don't invalidate it. Requiring `NoDuplicates all` introduces an invariant for which the present feature has no consumer.

There's a nice conceptual distinction available later:

```text
Finite A
    all + completeness

Fintype/Cardinal/UniqueFinite A
    all + completeness + no duplicates
```

or whatever names fit Stitchwort.

Adding `nodup` now because counting *might* happen later feels contrary to the otherwise admirably minimal proposal.

There is one trade-off worth recording explicitly: **adding `nodup` to `Finite` later would break manually-written `Finite` instances**. If you are almost certain enumeration cardinality is coming soon, that's an argument for doing it now. Otherwise I'd still choose the smaller abstraction.

### 6. I might generalise `Finite.check` in the library, but not in this ticket

The proposed helper is specifically:

```text
Finite.check
  (p: a → Bool)
  (checked: List.all Finite.all p = True)
  (x: a): p x = True
```

Truth-Table Proofs Review

That's a very clean primitive.

Eventually you may want the corresponding proposition-level combinator, roughly:

```text
Finite.forall :
  ((x : A) → Decidable (P x)) →
  ... →
  (x : A) → P x
```

or a way of deriving `Decidable ((x : A) → P x)` from a `Finite A` plus pointwise decidability.

That would let the `Finite` machinery compose directly with `byDecision`, rather than requiring users to rephrase propositions via `Bool` and then transfer the result with a library lemma.

But I **wouldn't put that complexity into SW-807**. `Finite.check` is sufficient to establish the architecture first.

### 7. Keep the 64-case limit

The measurements strongly support the proposed boundary.

`cases` handles 64 Boolean cases in about 12 ms total, while the enumeration approach grows to roughly 6 seconds at \(2^{16}\) cases. Truth-Table Proofs Review Truth-Table Proofs Review

The important distinction isn't simply speed. `cases` generates a structural proof proportional to the case tree, whereas `Finite.check` lets the *proof program* express iteration generically. They should occupy different scaling regimes.

I therefore like:

> ≤64: `cases` is pleasant, diagnostic and transparent.  
> >64: stop and suggest `Finite.check`.

I would **not raise it pre-emptively**. If someone later has a convincing 100-case proof where `Finite.check` is awkward, changing 64 to 128 is trivial. Going the other direction after users start depending on enormous generated case trees is harder.

### 8. “No native evaluation” is right, but don't make it a philosophical prohibition

The proposal's current wording is almost exactly where I'd land:

> Revisit only if a real proof needs more than about 10 s of kernel evaluation.

Truth-Table Proofs Review

That's better than declaring `native_decide` morally forbidden.

There is a genuine trust distinction. Current Lean's native evaluation infrastructure compiles and executes a closed Boolean computation and then introduces its result axiomatically; Lean's own documentation explicitly discusses the larger trusted base involved. [Lean Language](https://lean-lang.org/doc/api/Lean/Meta/Native.html?utm_source=chatgpt.com) Rocq similarly provides `vm_compute` and an OCaml-backed `native_compute` precisely because kernel reduction and fast external evaluation occupy different engineering points. [Rocq](https://rocq-prover.org/doc/V9.1.0/refman/proofs/writing-proofs/equality.html?utm_source=chatgpt.com)

Stitchwort currently doesn't have the workload that justifies paying that cost. That's enough reason not to implement it.

I would phrase the policy as:

> **Do not add native proof evaluation until measured kernel evaluation is a material limitation on real programs.**

rather than attaching too much significance to exactly 10 seconds. Ten seconds is a useful trigger for investigation, not a semantic boundary.

### One correction to the comparison section

I'd soften the claim:

> “Faster evaluation costs trust.”

Truth-Table Proofs Review

It's directionally useful but too broad. Faster evaluation *can* enlarge the TCB; it doesn't inherently have to. Proof-producing reflection and certificate checking can push expensive computation outside the kernel while keeping an independently checked proof/certificate. Modern Lean's `bv_decide`, for example, uses a SAT solver to obtain an LRAT certificate and verifies that certificate as part of the proof architecture. [Lean Language](https://lean-lang.org/doc/api/Lean/Elab/Tactic/BVDecide.html?utm_source=chatgpt.com)

That doesn't affect the Stitchwort decision—you absolutely don't need a SAT/certificate architecture for 16 Boolean cases—but I'd avoid turning the empirical observation about `native_decide`/`native_compute` into a general principle.

### My recommended final design

I'd approve the proposal with SW-800 defined as **three** changes rather than two:

1. `cases` automatically introduces relevant leading Π-bound variables.
2. When ordinary closers leave a sufficiently closed decidable leaf, it may close it through the existing `Decidable.fromYes` mechanism.
3. When nothing is stuck, it may fall back to splitting a mentioned splittable variable, preferably using a cheap branching-factor heuristic rather than simply “latest variable”.

Keep the 64-case budget and direct larger cases to `Finite.check`. Derive the minimal `Finite { all, complete }`; don't add `nodup` yet. Keep `byDecision` as the standard user-facing spelling for closed decidable proofs. Don't add native evaluation until actual workloads demonstrate the need.

So on the document's six explicit questions: **yes, yes, yes-but-with-a-better-heuristic, yes-without-nodup, yes, and “not now rather than never.”**

The overall architecture is unusually clean: **`cases` for symbolic finite elimination; `Finite` for scalable exhaustive enumeration; `Decidable` for closed computation; the kernel checks all three.** That seems like the right split for Stitchwort.