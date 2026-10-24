I think the research note is strong, but I would **not follow its recommendation of (b)**. I’d choose **(d): keep abilities on arrows, and add restricted reification for proofs**.

The key issue is that the note establishes two different facts and then treats them as if they imply the same design:

1. Stitchwort’s *core representation* of an effectful computation is ordinary inspectable `Comp` data.
2. Therefore `{Fail} A` should be admitted as a source-level value type.

I don’t think (2) follows from (1). The core representation can remain available to the proof system without making it part of ordinary source-level value semantics.

### 1. The owner's “abilities belong on arrows” instinct is basically right

Not because effects *intrinsically* belong on arrows. CBPV makes clear that there really are separate notions of values and computations, and Frank demonstrates that a suspended computation can itself be a value. The survey correctly points this out. Pasted text(20261024-123420) Pasted text(20261024-123420)

But Frank is actually evidence **against (b) as currently designed**.

Frank has:

- a computation,
- an explicit suspension turning it into a value,
- and an explicit `!` turning the suspension back into a computation.

Stitchwort under (b) would instead have something considerably stranger:

```text
c: {Fail} A
```

where merely mentioning `c` may mean either:

> pass this computation tree around as a value

or:

> execute this computation here

depending on its expected type.

That isn't really the CBPV/Frank distinction. It erases the distinction syntactically and asks bidirectional typing to recover it.

The survey identifies exactly this unusual property: none of the surveyed systems makes “pass versus run” depend on the expected type everywhere. Pasted text(20261024-123420)

I think that observation deserves substantially more weight than the recommendation gives it.

### 2. I would choose (d), but make `reify` proof-specific

Your motivating problem is extremely narrow:

> proofs need to inspect the already-existing `Comp` representation.

The motivating lemma isn't evidence that normal programs need first-class `{Fail} A` values. It's evidence that **the proof language needs access to the semantic representation of an effectful term**. Pasted text(20261024-123420)

So I would write the conceptual API as something like:

```text
theorem Fail.toResultThen
  (t: () -> {Fail} a)
  (k: a -> {Fail} b):
  ...
=
  match Effect.reify t with
  | Done x => ...
  | Call ... => ...
```

where `Effect.reify` is allowed in theorem/proof contexts and erased.

That gives you almost exactly F*'s division:

```text
programming semantics: effectful computations are abstract
proof semantics: representation can be revealed
```

The note already identifies F* as probably the closest precedent: effectful computation is abstract normally, while `reify` exposes the underlying representation for extrinsic reasoning. Pasted text(20261024-123420)

That division seems exceptionally well suited to Stitchwort.

### 3. “But what is the type of `reify` if rows are internal?”

I don't think this should force you into publicly exposing `{e} A` as a normal type.

There are several possibilities, in descending order of preference.

The cleanest is to make reification an **elaborator/proof primitive rather than an ordinary library function**. Conceptually it has a type like:

```text
reify :
  (() -> {E} A)
  -> Reified E A
```

but `Reified E A` need not be a source-spellable general-purpose datatype. The elaborator already knows the concrete `op`/`res` types produced by the effect translation.

For a concrete effect such as `Fail`, it can expose enough structure for:

```text
Done x
Fail.stop msg
```

without exposing the row encoding.

Alternatively, expose effect-specific eliminators:

```text
Fail.cases :
  (() -> {Fail} A)
  -> (A -> R)
  -> (Text -> R)
  -> R
```

with the important proviso that this is proof-only if you want to preserve runtime abstraction.

That may actually be a better user-facing proof interface than exposing generic `Call` plus injections into internal row sums. The note itself reaches the same concern around the `Call` pattern. Pasted text(20261024-123420)

I would **not** expose a general runtime `Effect.Tree e A` merely to make `reify` look like an ordinary function. That would turn an implementation representation into a language commitment.

### 4. The biggest problem with (b) is not syntax; it's semantics

The note sells (b) partly as a cautious syntactic compromise:

> computation types can only be written after `:`.

I don't find that boundary particularly principled.

Consider:

```text
(c: {Fail} A)
```

Okay.

A record field:

```text
{ work: {Fail} A }
```

Apparently okay.

But:

```text
List ({Fail} A)
```

not okay.

So `{Fail} A` is simultaneously a type sufficiently first-class to:

- be the type of a variable,
- possibly be the type of a record field,

but insufficiently first-class to:

- instantiate a type parameter,
- occur under a type constructor,
- be named by an alias.

That's not a semantic category. It's a parser fence.

The survey explicitly presents “widen later” as an advantage. Pasted text(20261024-123420) But I think that understates the danger: once users learn that `{Fail} A` means **a computation value that auto-runs in value context**, widening it to generic positions amplifies that semantic rule dramatically.

So (b) is safe syntactically but isn't obviously a good intermediate language design.

### 5. `id c` is the red flag

This is the example I would use to decide D1141.

Suppose:

```text
id : a -> a

c : {Fail} Nat
```

What does:

```text
id c
```

mean?

Under the current rules cited by the note, since `id` expects an ordinary `a`, `c` runs rather than being passed. Pasted text(20261024-123420)

That is deeply surprising if `{Fail} Nat` has just been presented to the programmer as the *type of the variable `c`*.

In a normal first-class computation system I would expect:

```text
id c == c
```

without executing anything.

You could fix that by saying type inference can instantiate:

```text
a := {Fail} Nat
```

but then you have effectively chosen option (a), because computation types need to participate normally in generic type formation.

This exposes a tension:

**Either `{Fail} A` is genuinely a value type, in which case generic polymorphism ought to treat it like one, or it isn't, in which case allowing `(c: {Fail} A)` is misleading.**

That's the strongest argument against (b), in my view.

### 6. Runtime freedom makes (d) much more attractive

The note is also right to worry that observable `Done`/`Call` commits the language to materialising the free-monad representation. Pasted text(20261024-123420)

I would go further: this is probably the strongest architectural reason **not** to expose it in ordinary programs.

Today:

```text
Comp
```

can be regarded as an elaboration/semantic model.

Tomorrow you might compile:

```text
foo : A -> {State, Fail} B
```

using:

- evidence passing,
- CPS,
- handler specialization,
- native JS exceptions in some circumstances,
- direct state threading,
- fusion eliminating intermediate requests,

without ever allocating the `Comp` nodes implied by the core representation.

If ordinary executable code can say:

```text
match c with
| Done ...
| Call ...
```

then those optimisations become observationally constrained.

But if only **erased proofs** can reify, there need be no runtime representation commitment at all.

This is exactly the kind of abstraction boundary I would preserve while the language is young.

### 7. I would therefore answer the five questions this way

**1. Do effect annotations belong on arrows?**

For Stitchwort's *surface programming language*, yes, I would keep that mental model for now.

Not because CBPV says computations can't be values—it says almost the opposite—but because turning a computation into a value normally requires an explicit suspension boundary. Stitchwort currently lacks such a visible boundary because forcing is implicit.

**2. Which option?**

**(d), arrows only + proof-oriented `reify`.**

If eventually programmers have a genuine need to store computations, I'd introduce an explicit suspension type/construct rather than generalising the current syntax blindly:

```text
Susp {Fail} A
```

or perhaps:

```text
Comp {Fail} A
```

with explicit:

```text
force c
```

At that point you have a proper CBPV/Frank-like distinction.

I would not let today's proof requirement silently determine tomorrow's first-class computation semantics.

**3. Hazards of (a)/(b)?**

The `id c` behaviour is worse than the parse ambiguity.

The parse ambiguity of (a) is fixable syntax. The semantic ambiguity—

```text
c
```

means either *this value* or *run this value* based on its context—

is much harder to undo.

Generic abstraction makes this especially problematic.

**4. Inspection only in proofs?**

Yes.

Unless you discover a compelling runtime-programming use case, I would make reification/`Done`/`Call` inspection proof-only and erased.

Handlers should remain the ordinary-programming way to observe effects.

**5. What did the survey miss?**

Its biggest gap is that it groups together two quite different ideas:

> computations can be first-class

and

> computations can be implicitly forced based on expected type.

The first has lots of precedent.

The second has almost none—and the survey itself discovers that fact. Pasted text(20261024-123420)

Frank in particular should be read as:

> first-class computations are perfectly reasonable **provided suspension/forcing is explicit**

rather than as straightforward support for option (a) or (b).

### My proposed decision text

I would record D1141 approximately as:

> **Choose (d).** Ability annotations remain part of function result types in the ordinary surface language. Effectful computations therefore remain suspended as thunks when they must be passed as values.
>
> Proofs may use an erased `reify`/effect-specific eliminator to expose the elaborated computation representation and reason by cases over it. Reification is not available to runtime code and therefore does not commit the runtime representation to materialised `Comp` trees.
>
> If a future programming use case requires stored first-class computations, revisit this independently and introduce an explicit suspension/forcing abstraction rather than extending the current implicit run-or-pass rule.

That gives you the proof you need **without making D1141 a much larger semantic decision than the motivating problem requires**.