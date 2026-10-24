Yes. My recommendation is:

**Keep design C. Keep D1122. For D1142, allow programs to quantify over the row index, but I would avoid exposing it as an ordinary-looking datatype named `Row` if you can cheaply give it dedicated surface syntax.**

So I’d separate the semantic decision from the syntax decision.

Design C itself looks reasonable. The important property is that `CompIn Empty a` reduces definitionally to `a`, while non-empty rows reduce to `Comp … a`. That gives you exactly the thing you were after: pure instantiations of effect-polymorphic functions really are pure, not merely propositionally equivalent to pure functions. Pasted text(20261024-125133)

I don’t see anything fundamentally unsound or especially exotic there. It is an unusual encoding, but it is an unusual encoding in service of a very specific dependent-type requirement: you want existing proofs about pure functions to continue to apply definitionally. The fact that the kernel just sees an ordinary indexed family is a strong point.

The biggest design smell is not `CompIn`; it is that the implementation datatype `Row` is starting to leak into source syntax.

### I would distinguish “row variable” from “value of datatype Row”

Semantically, your `e` behaves much more like a **kinded effect-row parameter** than like a normal user value.

This:

```text
type Handlers (e: Row): Type = ...
```

works, but it visually tells the programmer:

> `Row` is an ordinary datatype, and `e` is an ordinary value.

That is not really the abstraction you want.

Programs cannot:

- construct one,
- destruct one,
- compare one,
- inspect one,
- meaningfully compute with one.

They may only quantify over it and pass it parametrically. That is much closer to:

```text
e : Effects
```

or Koka-style “`e` has effect-row kind” than a first-class datatype.

So if you already have or expect a syntax distinction for these sorts of indices, I would prefer something like:

```text
type Handlers [e]: Type =
  | MkHandlers
      (onStep: Nat -> {Partial | e} Nat)
      (onDone: Nat -> {Partial | e} Nat)

def drive [e]: Handlers e -> Nat -> {Partial | e} Nat := ...
```

where `[e]` is understood specifically as an effect-row parameter.

Or, if explicit annotation is desirable:

```text
[e: Effects]
```

I mildly prefer **`Effects`** over `Row`, because it describes the source-language concept rather than the implementation representation.

If introducing syntax is disproportionate right now, though, **`[e: Row]` is perfectly acceptable as an interim design**. I would not block the feature on this.

### The D1122 abstraction boundary is more important than the spelling

Your claim here is:

> without constructors and eliminators a `Row` value can only be passed on, so parametricity holds. Pasted text(20261024-125133)

Broadly, yes—but I would phrase the guarantee somewhat more carefully.

Preventing users from naming:

- `Empty`
- `Ops`
- `rowOp`
- `rowRes`
- `CompIn`
- etc.

does prevent the **obvious direct observation** of `e`. The name-resolution mechanism is sufficient as an implementation technique for that abstraction boundary. You do not need a sophisticated module calculus merely to make the abstraction real.

But the real invariant you need is stronger:

> **There must be no source-language operation whose behaviour can depend on which representation of `Row` was supplied.**

That means I would specifically audit all of these channels:

- definitional equality,
- typeclass/interface resolution,
- auto proof search,
- overloaded operations,
- type-level reduction,
- equality/refl proofs involving types indexed by `e`,
- pretty-printing or reflection facilities,
- future generic derivation.

The particularly interesting one is **definitional equality**.

Users cannot write:

```text
match e with ...
```

but they *can* potentially observe consequences of the fact that:

```text
CompIn Empty A  ≡  A
```

while:

```text
CompIn (Ops ...) A  ≡  Comp ... A
```

That distinction is intentional: it is literally the purpose of design C.

So strictly speaking, effect-row polymorphism here is **not parametric in the strongest System-F relational-parametricity sense**. The type theory itself computes differently depending on the hidden row.

That isn't necessarily a problem. What you really require is:

> user programs cannot deliberately branch their term-level behaviour on the identity/shape of the row.

I would write D1122 in those terms rather than claiming unrestricted “parametricity”.

### Can users distinguish `e` indirectly with `rfl`?

Potentially they can distinguish **types produced after a row has already been instantiated**, but I don't immediately see a way for a universally quantified function to use that to branch on an abstract `e`.

Inside:

```text
def f [e: Row] ...
```

`e` is neutral.

So:

```text
CompIn e A
```

doesn't reduce.

The programmer cannot prove:

```text
CompIn e A = A
```

by `rfl`, because that only becomes true after `e := Empty`.

And because they cannot eliminate `e`, they cannot write separate proofs for `Empty` and `Ops`.

That's the crucial property.

At an application site where the elaborator knows `e = Empty`, things reduce—but that is specialization of the generic program, not observation performed *by* the generic program.

So I think you're okay here.

### Instance resolution deserves an explicit rule

This is the indirect channel I would be most suspicious of.

Suppose one could somehow get:

```text
instance Foo A
instance Foo (Comp op res A)
```

and an effect-polymorphic definition asks for:

```text
Foo (CompIn e A)
```

Then resolution might choose differently once `e` is known.

That's not necessarily unsound, but it can undermine the intuitive statement:

> an effect-polymorphic program cannot change its semantics depending on the row.

I would decide explicitly whether instance resolution is allowed to exploit reduction of `CompIn e A` after row specialization.

My inclination would be:

- inside a definition abstract over `e`, resolution must not inspect/speculate about `e`;
- once `e` is concretely instantiated, ordinary reduction is fine.

That parallels what you're already doing with unification.

### `Row : Type 1` looks fine for now

Given the current restriction that operation signatures live in `Type 0`, the universe level is exactly what I'd expect:

```text
Ops : (op : Type 0) -> (res : op -> Type 0) -> Row
```

requires `Row` to live at least one universe up. Your own note explicitly recognises the future generalisation to something like `Row u`. Pasted text(20261024-125133)

I would not hold up the design waiting for universe polymorphism.

But I would document this as a **representation limitation**, not as a deep property of effects. Eventually:

```text
Row u
CompIn : Row u -> Type u -> Type u
```

or something close to that is the natural generalisation.

### The canonical `Empty` rule is okay because it is an elaborator invariant

The `Ops NoOp NoRes` issue initially sounds worrying, but given:

1. users cannot construct rows,
2. the elaborator is the only source of them,
3. `Empty` is always emitted for no effects,

this is fine.

And importantly, as the note says, violating that invariant doesn't threaten logical soundness; it threatens definitional equations and performance. Pasted text(20261024-125133)

That's exactly the kind of invariant an elaborator may reasonably maintain.

I would add one strong test, though:

> Every pathway that creates or solves a row should assert that `Ops NoOp NoRes` is impossible.

You already cover the major paths. I'd make that a named invariant in code, rather than merely a convention distributed across the row machinery.

### Your inference machinery is the part I'd watch most closely

The design C encoding is conceptually simple.

The complicated bit is:

```text
CompIn ?e B ≟ T
```

because the family isn't injective:

```text
CompIn Empty (Comp op res A)
=
CompIn (Ops op res) A
```

in the relevant case.

Your apartness + postponement + defaulting scheme is defensible, and the examples are thoughtful. Pasted text(20261024-125133)

But this is where I'd expect future edge cases.

In particular, this line from the design deserves a permanent warning label:

> the spine rule is an approximation. Pasted text(20261024-125133)

Because `CompIn` is non-injective, treating two stuck `CompIn`s structurally is not logically complete.

That is okay for elaboration if:

- failure falls back to postponement,
- the kernel checks the final result,
- this can only affect inference/acceptance rather than soundness.

But I'd keep this implementation choice isolated. Don't let generic unification machinery come to assume `CompIn` injectivity.

### I like the default-to-pure behaviour

Defaulting unresolved effect rows to empty is quite natural:

```text
List.map f xs
```

with nothing indicating an effect should mean the pure interpretation.

And your rule is conservative because you delay the decision until other constraints have had a chance to solve the row. Pasted text(20261024-125133)

The diagnostics also matter a lot here. The note:

> “the row of this call was set to the empty row”

is exactly the sort of explanation I'd want when defaulting later causes a mismatch.

### One thing I would change in the documentation

I would stop describing `Row` as “rows as values” in user-facing conceptual material.

Internally, yes, it is literally an inductive value:

```text
Empty | Ops op res
```

But conceptually it is an **effect-row index**.

That wording matters because you have just deliberately decided in D1141 that computations should *not* become ordinary first-class source values. Pasted text(20261024-125133)

It would be slightly odd immediately afterward to teach people that effect rows themselves are ordinary values.

### My D1142 decision

I'd record something like:

> **D1142: Programs may quantify over effect rows, but rows remain abstract indices.**
>
> A program may declare an effect-row parameter and pass it parametrically, because this is required for effect-indexed data types such as `Handlers e`.
>
> Programs may not construct, inspect, compare, or eliminate rows. `Empty`, `Ops`, `CompIn`, and the row eliminators remain standard-library internal.
>
> The current implementation may expose this as `[e: Row]`; however `Row` is not intended to be an ordinary user datatype. A dedicated spelling such as `[e: Effects]` or implicit effect-row binders may replace it later without changing the semantic model.

And if you want me to choose between the concrete alternatives **today**:

**Choose D1142(a), let users write `Row`. Don't invent syntax solely to hide the name.**

But I'd regard:

```text
[e: Row]
```

as implementation-facing syntax that you may later polish into something like:

```text
[e: Effects]
```

or simply:

```text
[e]
```

once you have enough examples to know what feels natural.

Overall, this design is **not doing anything alarmingly weird**. The unusual part—`CompIn Empty A = A` definitionally—is deliberate and well motivated. The places deserving continued scrutiny are **non-injectivity/inference and indirect observation through type-directed mechanisms**, not the basic row representation itself.