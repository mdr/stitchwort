# Core language rules

**Status:** describes what's implemented in `crates/core` as of 14 October 2026. DESIGN.md describes where the language is going; this document describes where it is.

The core is the small, explicit language that every Stitchwort definition is translated into before it's checked. The surface language (`docs/syntax.md`) is turned into core terms by the elaborator (`crates/elab`).

## How this differs from DESIGN.md today

| DESIGN.md | Implemented now |
|---|---|
| A separate trusted kernel re-checks the elaborator's output (principle 4) | **Done.** The elaborator (`crates/elab`) has its own type checker, with metavariables and unification. It produces complete core terms, which the checker in `crates/core` (the kernel) re-checks from scratch. |
| Implicit arguments, `auto` | Implicit arguments are implemented ([below](#elaboration)). `auto`, `Decidable` and division with non-zero proofs are not yet |
| Abilities, `Partial` | None. Every term has the empty effect row, so the effect judgment `t : A ! ε` always has `ε = {}`. Non-terminating definitions are rejected outright. |
| Tracked assumptions | There's no `assume` yet, so every checked definition is assumption-free |
| Evaluation budget, "inconclusive" results | Not yet. Evaluation is guaranteed to terminate, but may be slow |
| Native numbers | `Nat` is unary in the evaluator (number literals up to 10,000). Extracted JS uses `bigint` |
| Pattern matching | One constructor deep, no nested patterns. No forward references or mutual recursion |
| Data types | Parameters but no indices. Equality is the only built-in indexed type |
| Universes | Numbered, no polymorphism, no cumulativity |

## Terms

Variables are de Bruijn indices in terms and de Bruijn levels in values.

| Term | Meaning |
|---|---|
| `Var(i)` | A local variable |
| `Def(f)` | A top-level definition |
| `Data(D, params)` | A data type applied to all its parameters |
| `Ctor(D, c, fields)` | Constructor `c` of `D` applied to all its fields. Parameters come from the expected type |
| `Sort(s)` | `Prop` or `Type i` |
| `Pi(x, i, A, B)` | `(x : A) -> B`, or `[x : A] -> B` when `i` is implicit |
| `Lam(x, i, b)` | `\x -> b` |
| `App(f, a, i)` | Application, to an explicit or implicit argument |
| `Ann(e, T)` | `(e : T)` |
| `Case(x, D, branches)` | Match variable `x : D params`, one branch per constructor. Only appears at the top of a definition, forming a case tree |
| `Eq(A?, a, b)` | `a = b`. `A` is filled in by the checker |
| `Refl` | `rfl : a = a` |
| `J(P, d, p)` | Transport along an equality |
| `Loc(span, t)` | A source location, ignored except for error messages |
| `Meta(m)` | A metavariable. Only used inside the elaborator: the kernel rejects terms containing one |

## Universes

```
Prop : Type 0        Type i : Type (i+1)
```

The universe of a function type:

| `A : s₁`, `B : s₂` | `(x : A) -> B : …` |
|---|---|
| `s₂ = Prop` | `Prop` (impredicative) |
| `s₂ = Type j` | `Type (max (level s₁) j)`, where `level Prop = 0` |

There's no cumulativity: a `Type 0` isn't automatically a `Type 1`.

## Typing

Checking is bidirectional. `Γ ⊢ t ⇒ A` infers a type, and `Γ ⊢ t ⇐ A` checks against one. Types are compared with conversion `≡` (below). Checking returns a completed term, with each `Eq`'s type filled in.

**Inferred:**

- `Var`, `Def`: from the context or the declaration.
- `Data(D, ps)`: each parameter is checked against its declared type. The result is `D`'s universe.
- `Sort(s) ⇒ Sort(succ s)`.
- `Pi(x, A, B)`: `A` and `B` must be types. The universe follows the table above.
- `App(f, a)`: `f ⇒ (x : A) -> B`, `a ⇐ A`, giving `B[a/x]`.
- `Ann(e, T)`: `T` is a type, `e ⇐ T`, giving `T`.
- `Eq(_, a, b)`: infers `a`'s type `A` (or `b`'s, if `a` can't be inferred) and checks the other side against it. Gives `Prop`.
- `J(P, d, p)`: `p ⇒ x = y` at type `A`. `P` must be written `\y' p' -> T` with `T` a type, where `y' : A` and `p' : x = y'`. Then `d ⇐ P x rfl`, giving `P y p`.
- `Ctor` of a data type *without parameters*: checked against that type.

Implicitness only has to agree: `App(f, a, i)` needs `f`'s type to be a function type with the same `i`, and `Lam(x, i, b)` checks only against a function type with the same `i`. The kernel never inserts implicit arguments. It sees them already filled in.

**Checked:**

- `Lam(x, i, b) ⇐ (x : A) -> B` (same `i`): `b ⇐ B` with `x : A`.
- `Ctor(D, c, fs) ⇐ D ps`: each field is checked against its declared type, with the parameters and earlier fields substituted in.
- `Refl ⇐ a = b`: requires `a ≡ b`. Otherwise error `E-REFL`.
- `Case`: see below.
- Anything else: infer, then require the inferred type `≡` the expected one. If both are universes, the error is `E-UNIVERSE`, otherwise `E-TYPE-MISMATCH`.

## Data types

A declaration `type D (params) : s = | C₁ fields | …`:

- **Parameters** are checked as a telescope.
- **The universe `s`** defaults to `Type`.
- **Each field type** is checked in the context of the parameters and the earlier fields.
- **Universe constraint (`E-UNIVERSE`).** A field whose type is in `Type i` is only allowed if `D : Type j` with `i ≤ j`, or `D : Prop`. Prop-valued fields are always allowed.
- **Strict positivity (`E-POSITIVITY`).** `D` may only appear in a field's type as `D` applied to exactly its own parameters, or as the result of a function type whose inputs don't mention `D`. Nested occurrences, like `List D`, are rejected conservatively.
- **Erased fields:** a field is erased if its type is a proposition or a type former (a universe, or a function returning one).

## Case trees

`Case(x, D, branches) ⇐ G`, where `x : D ps` is a variable in the context:

1. There must be exactly one branch per constructor, in declaration order (`E-NONEXHAUSTIVE`).
2. **`Prop` elimination (`E-PROP-ELIM`).** If `D : Prop` and `G`'s universe isn't `Prop`, then `D` must have at most one constructor, and every field of it must be a proof. This is Lean's subsingleton-elimination rule. It's stated over the declaration's fields, not over runtime erasure: a `Type` field is erased but still disqualifies (`HiddenType`). `D` has no indices, so the "or appears in an index" clause from DESIGN.md §6 doesn't arise yet. Equality is built in, and its eliminator `J` is always allowed.
3. **Goal refinement.** For constructor `c` with fields `f₁ … fₖ`, the branch is checked with the fields in scope, against `G` with `x` replaced by `c f₁ … fₖ`. Inside the branch, `x` also *evaluates* to that constructor value, so its uses compute. Other context entries that mention `x` aren't refined. That's incomplete but sound.

## Equality

- `Eq(A, a, b) : Prop` and `Refl ⇐ a = b` when `a ≡ b`.
- `J` computes: `J P d rfl ⟶ d`. With any other proof it's stuck.
- `Eq` satisfies the elimination rule: one constructor, no fields. So `J` may produce data (transport).
- There's no definitional proof irrelevance: two different proof terms aren't automatically equal.

## Definitions

1. **Declare:** the signature is checked to be a type. For `theorem`, it must be a proposition (`E-NOT-A-PROP`). The definition is added *without a body*.
2. **Define:** the body is checked against the signature. While this happens, the definition has no body, so recursive references to it are opaque and never unfold.
3. **Termination (`E-TERMINATION`).** There must be one parameter position `i` such that every recursive call passes, in position `i`, a variable bound as a field of a constructor matched out of parameter `i` (directly, or through further matches on such fields). A bare or under-applied recursive reference fails.
4. The body's number of leading lambdas becomes the definition's **arity**.

If a body fails to check, the definition stays without a body (opaque), so later declarations can still refer to it. A file with any errors produces no guarantees and can't be extracted.

## Evaluation and conversion

Normalisation by evaluation (`crates/core/src/value.rs`):

- **Unfolding policy.** A definition applied to fewer than its arity arguments stays folded, as a neutral term headed by the definition. Once it has all its arguments, it unfolds **only if its case tree can take a step**, meaning every case it reaches is on a constructor. Otherwise it stays folded. That makes conversion terminate even though `length a xs` mentions `length`. Definitions with arity 0 always unfold.
- **Conversion `≡`:** structural on values, with eta for functions (`f ≡ \x -> f x`). Folded definitions are equal when they're the same definition applied to convertible arguments.
- **Running a program** uses the same evaluator, strictly. Arguments are evaluated before calls.
- **Comparing types** reduces under binders. It never reaches an effectful operation, because there aren't any yet.

## Elaboration

The elaborator (`crates/elab`) checks surface syntax bidirectionally, following András Kovács' elaboration-zoo, and produces core terms for the kernel.

- **Metavariables.** An unknown, such as an implicit argument or a `_` hole, becomes a metavariable applied to the variables in scope (except variables a case branch has replaced by a constructor). Its solution is a closed function of those variables.
- **Inserting implicit arguments.** When a function's type starts with implicit parameters, the elaborator applies it to fresh metavariables, unless an argument names one with `f [x := e]`. When checking against an implicit function type, it inserts an implicit lambda.
- **Pattern unification.** `?m x₁ … xₙ = t` is solved when the `xᵢ` are distinct variables. The solution is `\x₁ … xₙ -> t`. There's an occurs check, so `?m` can't appear in `t`, and a scope check, so `t` may only mention the `xᵢ`. **Pruning:** if `t` contains another metavariable applied to variables outside the `xᵢ`, that metavariable is narrowed so it can't depend on them.
- **Constructors.** A constructor's data parameters come from the expected type, or from fresh metavariables. An inferred constructor of a parameterised type is wrapped in a type annotation, so the kernel can infer it too.
- **Zonking.** After a declaration is elaborated, solved metavariables are substituted in. Any left unsolved is an error (`E-UNSOLVED`) at the place it was created.
- **Implicitly bound type variables.** An unknown lowercase name in a signature becomes an implicit parameter at the front if *every* use of it is where a type is expected: the domain or result of a function type, a binder's type, or an argument of a data type whose parameter is a type (`List a`, `Or p q`). Its own type is a metavariable, usually solved to `Type`, which is also the default. Any other use (`length xs` with `xs` unbound) stays an unknown name.
- **Equations.** Parameters are bound from the signature. Implicit ones are in scope by their signature names. Explicit ones are matched by the equation's patterns, so `length (Cons x xs)` has one pattern while `length` has two parameters.

What the elaborator *doesn't* check is left to the kernel: `Prop` elimination, positivity, universe constraints on fields, and termination. Those errors come from the kernel, with source locations kept from the elaborated term.

## Erasure and JS extraction

What's erased:

- **Definitions:** a definition is erased (not emitted) if its type is a proposition or a type former.
- **Parameters:** a parameter is erased if its type is a proposition or a type former. Calls to definitions drop erased arguments. Lambdas keep all their parameters, and erased arguments passed to them become `undefined`.
- **Terms:** `Data`, `Sort`, `Pi`, `Eq` and `Refl` compile to `undefined`. `J P d p` compiles to `d`.
- **Case on a proof:** this is only possible for the subsingleton propositions above, so it compiles to its single branch.

Representations: `Nat` is `bigint` (`Zero` is `0n`, `Succ n` is `n + 1n`, and a case on `Nat` tests `=== 0n`). Other data types are `{ tag, …fields }`, omitting erased fields.

The exportability check, the boundary encodings and the decode → compute → encode contract are as described in DESIGN.md §12, restricted to `Nat`, `List` and parameterless data types built from them.

## Error codes

| Code | Meaning |
|---|---|
| `E-PARSE` | Syntax error |
| `E-UNKNOWN-NAME` | Name not in scope |
| `E-DUPLICATE` | Name defined twice, or a built-in name redefined |
| `E-MISSING-SIGNATURE` / `E-MISSING-DEFINITION` | Equations without a signature, or the other way round |
| `E-ARITY` | Wrong number of patterns or arguments |
| `E-NOT-A-CONSTRUCTOR` / `E-NESTED-PATTERN` | Unsupported or invalid pattern |
| `E-TYPE-MISMATCH` | Types don't match |
| `E-UNIVERSE` | Universe mismatch, or a field too large for its data type |
| `E-CANNOT-INFER` | Needs a type annotation |
| `E-NOT-A-TYPE` / `E-NOT-A-FUNCTION` / `E-NOT-A-SORT` | Wrong kind of thing |
| `E-NOT-A-PROP` | A `theorem` whose type isn't a proposition |
| `E-REFL` | `rfl` used for sides that don't compute to the same value |
| `E-NONEXHAUSTIVE` | Missing pattern-match case |
| `E-TERMINATION` | Recursion not structurally decreasing |
| `E-POSITIVITY` | Data type used in a negative position |
| `E-PROP-ELIM` | Matching on a proof to produce data, where that's not allowed |
| `E-EXPORT` | Export can't cross the JS boundary |
| `E-UNSOLVED` | An implicit argument the elaborator couldn't work out |
| `E-UNSUPPORTED` | Not implemented yet |
