# Core language rules

**Status:** describes what's implemented in `crates/core` as of 16 October 2026. DESIGN.md describes where the language is going; this document describes where it is.

The core is the small, explicit language that every Stitchwort definition is translated into before it's checked. The surface language (`docs/syntax.md`) is turned into core terms by the elaborator (`crates/elab`).

## How this differs from DESIGN.md today

| DESIGN.md | Implemented now |
|---|---|
| A separate trusted kernel re-checks the elaborator's output (principle 4) | **Done.** The elaborator (`crates/elab`) has its own type checker, with metavariables and unification. It produces complete core terms, which the checker in `crates/core` (the kernel) re-checks from scratch. |
| Implicit arguments, `auto` | Implemented ([below](#elaboration)). Decision procedures are found by their result type (any function returning `Decidable …`), not registered explicitly |
| `if` | Both branches are functions, so only the chosen one runs. Branches must produce data (`Type`), not proofs, until universe polymorphism exists |
| Abilities, `Partial` | Abilities and handlers are implemented by translation into the prelude's `Effect.Comp` trees ([below](#abilities)), so the core has no effect judgment: an effectful function's type *is* a function into `Effect.Comp`. `Partial` is implemented at stage 1 ([below](#partial-computations)): a partial computation is a value of the opaque type `Effect.Delay`, which only the runtime runs. `IO` is an ordinary ability declared in the prelude, with `IO.simulate` as an ordinary handler for it; nothing performs it for real yet. |
| Tracked assumptions | There's no `assume` yet, so every checked definition is assumption-free |
| Evaluation budget, "inconclusive" results | Not yet. Evaluation is guaranteed to terminate, but may be slow |
| Caching (§11) | Test results are cached by content hash. Kernel checks and generated JS aren't cached yet, and nothing is cached across elaboration |
| Numbers | `Nat` only; no `Int` yet. Numbers are native and can be any size (see [Numbers](#numbers)) |
| Pattern matching | Nested patterns, but no overlap warnings |
| Declaration order | Free: every name is visible throughout its module, definitions may call each other ([groups](#groups-of-definitions)), and data types may refer to each other ([data groups](#groups-of-data-types)) |
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
| `Pi(x, i, A, B)` | `(x : A) -> B`; with `i` implicit, `[x : A] -> B`; with `i` auto, `[auto x : A] -> B` |
| `Lam(x, i, b)` | `\x -> b` |
| `App(f, a, i)` | Application, to an explicit or implicit argument |
| `Ann(e, T)` | `(e : T)` |
| `Let(x, A, v, b)` | `let x : A := v; b`: a transparent local definition. `x` takes a slot (`b` is under one binder) but stands for `v` itself ([proposals/let.md](proposals/let.md)). A leaf, never a case-tree node: no `Case` may appear under it. It also carries whether running skips `v`, which the kernel sets when it checks it (below); hashing ignores that |
| `Case(x, D, branches)` | Match variable `x : D params`, one branch per constructor. Only appears at the top of a definition, forming a case tree |
| `Chars(range)` | A `List Char`, stored compactly: the characters of a range of an array, standing for `Cons (MkChar c rfl) … Nil` ([text](#text)) |
| `NumCase(x, arms, default)` | Compare variable `x : Nat` with numbers: one arm per number, in strictly increasing order (at least one), and a default. Only appears where `Case` may |
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
- `Let(x, A, v, b)`: `A` is a type in any universe (a proof, data or a type are all defined the same way), `v ⇐ A`, then `b ⇒ B` with `x : A := v` in the context, giving `B[v/x]`. In the context `x` evaluates to `v`'s value, not to a variable, so while checking `b` its uses compute (ζ-reduction), and `B`, a value, never mentions `x`: it's already `B[v/x]`, usable outside the `let`. Checked the same way against an expected type, with `b ⇐` it. While checking, `v` is computed only when the checker first evaluates a term that mentions `x` (a type, or an argument a type depends on), and then once; running a program computes it strictly.
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
- **Strict positivity (`E-POSITIVITY`).** `D` may only appear in a field's type as `D` applied to exactly its own parameters, or as the result of a function type whose inputs don't mention `D`. Nested occurrences, like `List D`, are rejected conservatively. In a [data group](#groups-of-data-types), this holds for every member, in the fields of every member.
- **Erased fields:** a field is erased if its type is a proposition or a type former (a universe, or a function returning one).
- **Records** (`declare_data_group_as`, docs/proposals/records.md): a data type may be declared as a record, which must have exactly one constructor (`E-MALFORMED` otherwise). The flag is fixed when the type is declared and hashed; checking never depends on it (it only says how JS represents the type). The elaborator gives a record a projection per field, an ordinary definition by a one-branch case. A record's proof field may get a **validator** (`add_field_validator`): a decision procedure for the field's proposition, in the context of the parameters and earlier fields, which the kernel checks has type `Decidable P` (as for an export's precondition), and which extracted JS runs to establish the field for decoded input.

## Case trees

`Case(x, D, branches) ⇐ G`, where `x : D ps` is a variable in the context:

1. There must be exactly one branch per constructor, in declaration order (`E-NONEXHAUSTIVE`).
2. **`Prop` elimination (`E-PROP-ELIM`).** If `D : Prop` and `G`'s universe isn't `Prop`, then `D` must be alone in its data group, have at most one constructor, and every field of it must be a proof (propositions defined together never eliminate into data, a conservative rule taken from Lean). This is Lean's subsingleton-elimination rule. It's stated over the declaration's fields, not over runtime erasure: a `Type` field is erased but still disqualifies (`HiddenType`). `D` has no indices, so the "or appears in an index" clause from DESIGN.md §6 doesn't arise yet. Equality is built in, and its eliminator `J` is always allowed.
3. **Refinement.** For constructor `c` with fields `f₁ … fₖ`, the branch is checked with the fields in scope, against `G` with `x` replaced by `c f₁ … fₖ`. Inside the branch, `x` also *evaluates* to that constructor value, so its uses compute, and the constructor value is substituted for `x` throughout the context: in every variable's type and value, including variables bound before `x` (with nested patterns, `rest : res o` is bound before `o` is matched). For example, in `Decidable.fromYes (No r) u`, the hypothesis `u : Decidable.IsYes d` becomes `u : Decidable.IsYes (No r)`, which computes to `Void`.
4. **No constructors.** A case with no branches is how an absurd pattern `()` compiles. It's only accepted when the data type has no constructors, and since such a type is trivially a subsingleton, it may produce anything.

`NumCase(x, [(k₁, b₁), …, (kₘ, bₘ)], d) ⇐ G` is how number patterns compile (docs/proposals/number-patterns.md). `x` must be a variable of the prelude's `Nat`, and the numbers strictly increasing with `m ≥ 1`; anything else is `E-MALFORMED`, since the elaborator never produces it. Each arm `bᵢ` is checked with the number `kᵢ` substituted for `x` throughout the context and the goal, as a `Case` branch substitutes its constructor value. The default `d` is checked with nothing new known about `x`: not a predecessor, and not that it differs from the `kᵢ`. So a `NumCase` stands for the nested `Zero`/`Succ` cases that count down to `kₘ`, with the default copied to every other leaf, and accepts no more than they would (it accepts less: the copies of the default know more about `x`). It binds nothing, so it's no evidence of structural descent for termination, but evidence from cases around it still counts in every arm and the default.

It evaluates by the value of `x`: a number takes its arm, or the default; `k + x'` (a number of `Succ`s around something unknown) takes the default when every `kᵢ < k`, since it's at least `k`; anything else is stuck, so the definition stays folded. Failing to show that `x` is some `kᵢ` is never taken to mean it isn't.

## Equality

- `Eq(A, a, b) : Prop` and `Refl ⇐ a = b` when `a ≡ b`.
- `J` computes: `J P d rfl ⟶ d`. With any other proof it's stuck.
- `Eq` satisfies the elimination rule: one constructor, no fields. So `J` may produce data (transport).
- There's no definitional proof irrelevance: two different proof terms aren't automatically equal.

## Definitions

Definitions are admitted in **groups** of one or more that may call each other (`define_group`; `define_def` is a group of one). The elaborator submits each strongly connected component of the module's definitions as one group ([below](#groups-of-definitions)).

1. **Declare:** the signature is checked to be a type. For `theorem`, it must be a proposition (`E-NOT-A-PROP`). The definition is added *without a body*.
2. **Arity.** The body's number of leading lambdas (looking through source locations, and counting implicit, type and proof lambdas) is the definition's **entry arity**, fixed, for every member of the group, before any body is checked. It's the one number used for unfolding (below), for the saturation rule and the graphs of the termination check, and for extraction. Lambdas inside the case tree belong to its result: `f : Nat -> Nat -> Nat; f Zero = \x -> x; …` has arity 1.
3. **Define:** each body is checked against its signature. While this happens, no member of the group has a body, so references to any of them are opaque and never unfold.
4. **Termination (`E-TERMINATION`)**, by size change ([details](proposals/mutual-recursion.md#6-termination-for-a-group-of-functions)), for the whole group at once: a call from any member to any member (itself or another) is a call. Every occurrence of a member, wherever it is (under lambdas, in types, inside other calls' arguments), must be applied to at least that member's arity's arguments; a bare or partial one is refused, with a suggestion to write `\x -> f a x`. Each such call is summarised by a *size-change graph*: for each parameter position of the callee, whether the argument there is
   - **strictly smaller (`<`)** than parameter `i`: a variable bound as a field of a constructor matched out of parameter `i` (directly, or through further matches on such fields); a constructor applied to exactly the fields of a match on such a field (`Succ n` in the branch where `m` is `Succ n` is `m`); or a *recursive function field* applied to arguments (`rest y`, where `rest` is the variable bound for a field whose declared type is a function returning the matched data type; only that variable counts, not other functions of the same type);
   - **at most (`≤`)** parameter `i`: the parameter itself, or a constructor applied to exactly the fields of a match on the parameter itself (that *is* the parameter, in that branch);
   - otherwise **unknown**: lambda-bound variables, other functions' results, `J`, numbers. A `NumCase` binds nothing, so it adds no evidence.

   A `let`-bound variable has exactly the relation its value has (`let y := x'` with `x'` smaller than `x` is smaller than `x`), decided from the terms, never by conversion; calls are looked for in a `let`'s annotation, value and body.

   Arguments beyond the arity get no entry, but are searched for calls too. The group is accepted if, closing the calls' graphs under composition (every sequence of calls, through any members), every graph from a member to itself that composes with itself to give itself has a `<` from some parameter to the same parameter (`crates/core/src/sct.rs`). Calls are never merged: two calls that each shrink a different argument don't make one call that shrinks both. So recursion where one argument gets smaller while the others are passed on unchanged, lexicographic recursion (Ackermann's function) and swapped arguments (`f (Succ x) y = f y x`) are accepted. Running out of resources while deciding is `E-RESOURCE`: inconclusive, so the group fails. Arity 0 can't recurse: its graphs have no entries.
5. **Install, all or nothing.** Every member gets its body and becomes final at once. If anything fails for any member, including running out of resources, every member fails and none has a body or a hash.

### Groups of definitions

- **What a group may refer to** (docs/proposals/mutual-recursion.md §5.2): a signature, only final declarations; a body, final declarations and members of its own group. A reference to any other pending declaration is `E-MALFORMED`, so a cycle can't be split into two groups that each look non-recursive. Every member must be pending and listed once.
- **Bigger groups are safe.** A group may contain definitions that don't actually call each other; calls that form no cycle add no loops to the termination check.
- **The elaborator's groups.** Every top-level name is visible throughout its module. The elaborator collects each declaration's free references (a local variable named like a definition isn't a reference to it), splits the declarations into strongly connected components and checks them in dependency order, earliest in the source first among those ready. A component of several definitions, or of one that calls itself, is one group. Its signatures are elaborated first, and a signature that mentions a member is `E-MUTUAL-SIGNATURE`; then its bodies. A component of data types is a [data group](#groups-of-data-types); one mixing data types and definitions, or with an ability, is refused (`E-MUTUAL-KIND`).
- **Hashes.** A group of two or more definitions is hashed as a unit: members are ordered by their *shape* (their hash with references to members replaced by one marker; ties in submission order), the group's hash covers every member's type and body in that order with references to members as their index, and each member's hash is the group's hash and its index. A single definition is hashed as before.

### Groups of data types

Data types are admitted in **data groups** of one or more whose fields may mention each other (docs/proposals/mutual-recursion.md §5.4, §7). `declare_data` and `define_ctors` are a group of one.

- **Declare** (`declare_data_group(params, sort, names)`): one parameter telescope, checked once in one context, and one universe, shared by every member by construction. The parameters may refer only to final declarations; a reference to a declaration that doesn't exist yet, including one a member is about to become (ids are plain indices), is `E-MALFORMED`, and nothing is added. Each member records its group (the members, in declaration order), fixed then and never changed. The members are pending.
- **Define** (`define_data_group`): the constructors of every member, in one call. Every member of the group must be listed, once, and nothing else; otherwise `E-MALFORMED`, and every member fails. A field may mention final declarations and the group's members *as types*; a member's constructors, or a `case` on one, are pending references (`E-MALFORMED`; the elaborator says `E-MUTUAL-CONSTRUCTOR`). Positivity is checked for every member in every field; the "declared later" guard allows the group's own members and nothing declared after the group. Either every member becomes final, with its constructors, at once (until then none can be built, matched on or hashed), or every one fails.
- **Termination.** A field of a constructor matched out of a parameter is smaller than it, whatever its type, so `size (Node n kids) = Succ (sizeForest kids)` is a smaller call. A function field returning any member of the matched type's group (`child : Nat -> Layer` in a `Branching`) is a recursive function field: its results are smaller.
- **`Prop`.** A member of a group of two or more propositions never eliminates into data; proof-to-proof matching is unaffected.
- **The elaborator's groups.** A strongly connected component of data types is one group: their parameters (which must be the same, names included, `E-MUTUAL-PARAMETERS`) and universes are elaborated, then all their constructors. A header mentioning a member is `E-MUTUAL-SIGNATURE`. A cycle with a definition, or with an ability, is `E-MUTUAL-KIND`.
- **Hashes.** A group of two or more is hashed as a unit, ordered by name (ties in declaration order): the group's hash covers the parameters, the universe, the number of members and each member's name and constructors, with references to members (as types, constructors or in a `case`) as their index; each member's hash is the group's hash and its index. So changing any constructor of any member changes every member's hash.

**Admission** ([details](proposals/kernel-admission.md)). Each definition and data type is *pending* (declared), *final* (its body or constructors admitted) or *failed*. Only final definitions have a body, so only they unfold; only final data types can be matched on, and only final declarations have a hash. Whatever a signature, body, data parameter, constructor field or validator refers to must be final, apart from the members of a definition's group in its body and the members of a data type's group (as types) in its fields. A reference to a pending declaration is refused (`E-MALFORMED`), so a cycle can't be split across two definitions and a data type without its constructors yet is never treated as empty. Defining something twice is refused too. If a body or constructors are refused, the declaration fails, and anything using it is still checked but fails too (`E-FAILED-DEPENDENCY`, which the elaborator doesn't report when the original error is reported). So later declarations can refer to a failed one without cascading "unknown name" errors, but nothing built on it is ever accepted. A file with any errors produces no guarantees and can't be extracted.

## Evaluation and conversion

Normalisation by evaluation (`crates/core/src/value.rs`):

- **Unfolding policy.** A definition applied to fewer than its arity arguments stays folded, as a neutral term headed by the definition. Once it has all its arguments, it unfolds **only if its case tree can take a step**, meaning every case it reaches is on a constructor (and every `NumCase` can choose an arm or its default, as above). Otherwise it stays folded. That makes conversion terminate even though `List.length a xs` mentions `List.length`. Definitions with arity 0 always unfold.
- **Arguments are computed only when a type needs them.** The type of `f a` is `f`'s result type with `a`'s value put in, so checking would compute `a`. When the result type doesn't mention its parameter, as in `constant 0 (List.length bigList)`, `a` isn't computed at all; the same goes for constructor fields and data parameters that later types don't mention (`Closure::apply_lazy`, `later_types_mention`). A computation that does appear in a type is still run while checking: in `test "t" = f x == y`, the equation `f x = y` is the type of the decision, so `f x` is computed when the test is checked as well as when it runs.
- **Conversion `≡`:** structural on values, with eta for functions (`f ≡ \x -> f x`). Folded definitions are equal when they're the same definition applied to convertible arguments. A definition applied to fewer arguments than it takes is a function too, so it's compared by applying both sides to a fresh variable: `F` defined by `F o = PlusRes … o` equals `PlusRes …`.
- **`let`** evaluates its value once, strictly, before the body, which sees it in its environment: `eval(Let(x, A, v, b), ρ) = eval(b, ρ ++ [eval(v, ρ)])`. Quoting never produces a `Let`, and conversion needs no case for it, since values don't contain one. A `let` takes a slot in terms (de Bruijn indices count it) but no variable level stands for it, so the levels in use have a gap there, as after a case split. When running (with erasure, below), a `let` the kernel marked is skipped, its slot getting the placeholder: one whose `A` would make a parameter erased (a proposition or a type former), or whose body doesn't use `x`.
- **Running a program** uses the same evaluator, strictly. Arguments are evaluated before calls. `stitchwort run` and `stitchwort test` (never the checker) also **erase** as JS extraction does (`crates/core/src/erase.rs`): arguments for erased parameters (proofs and types) and erased constructor fields aren't computed, a definition whose result is erased isn't run, `J` on an erased proof takes its base, and a `case` on an erased proof takes its only branch. This is safe because nothing matches on a type, and a proof is matched into data only when it has one possible shape (`E-PROP-ELIM` below), so the run takes the same branches with or without erasure; only proofs and types, which are never printed or compared, differ. A record carrying `ok = Int.modNatLt x 100` costs nothing at run time.
- **Comparing types** reduces under binders. It never reaches an effectful operation, because there aren't any yet.

## Numbers

`Nat` means `Zero | Succ Nat`, but a number is stored as one arbitrary-precision value (`Term::Nat`, `Value::Nat`; `crates/core/src/native.rs`), following option A of [the proposal](proposals/native-numbers.md):

- A number has type `Nat`. Matching on `n` takes the `Zero` branch if it's 0, and otherwise the `Succ` branch with field `n - 1`, without building a chain.
- Conversion treats `3` and `Succ 2` as equal (`Succ x` is never equal to a number unless `x` is). Evaluating `Succ` of a number, or `Zero`, gives a number.
- **Numbers with unknowns.** `k + x`, for a number `k` and an `x` that isn't a number, is kept as one value (`Value::NatAdd`), meaning `Succ` applied `k` times to `x`. That's what `Nat.add`'s definition computes, one step per unit. Numbers compare by these `k + x` forms. `Nat.sub`, `Nat.leq` and `Nat.equal` take off the `Succ`s both arguments share in one step, as their definitions do one at a time. `k * x` for a literal `k` still unfolds `k` times, because its normal form really is that big.
- **Native implementations.** `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.leq`, `Nat.equal`, `Nat.divFuel`, `Nat.decEq`, `Nat.equalRefl` and `Nat.equalSound` run natively when all their number arguments are numbers (or `Succ`s around one). Otherwise they unfold as usual, so proofs by induction are unaffected. Each gives exactly what its definition computes, proofs included: `Nat.decEq` gives `Yes rfl`, or `No (Nat.equalFalse m n rfl)` (its definition asks `Nat.equal`, and the prelude's `Nat.equalFalse` turns `Nat.equal m n = False` into `Not (m = n)`); `Nat.equalRefl n`, and `Nat.equalSound m m h`, give `rfl` ([native numbers](proposals/native-numbers.md#as-built-what-a-native-must-compute)).
- **Arithmetic lemmas.** The prelude proves, in `Std.Nat`, by induction and `Eq.cong`/`Eq.trans`: `addZero`, `addSucc`, `addComm`, `addAssoc`, `addCancelLeft`; `mulZero`, `mulOne`, `mulSucc`, `mulComm`, `mulAssoc`, `mulDistribLeft`, `mulDistribRight`; `leRefl`, `leTrans`, `leAntisym`, `zeroLe`, `leSucc`, `leAddRight`, `leAddLeft`, `lessIrrefl`, `lessTrans`, `lessLe`; `subSelf`, `addSub`, `subLe`; and `divMod` (`n = (n / d) * d + n % d`) and `modLess` (`n % d < d`), each taking a proof that `d != 0`. Division with remainder is unique (`divUnique`, `modUnique`: `n = q * d + r` with `r < d` gives `n / d = q` and `n % d = r`), with `modSmall`, `divSmall`, `addDivSelf`, `addModSelf`, `modSelf` and `divOne`, which take an `auto` proof. Their helpers (`divMulLe`, `divFuelLe`, `divFuelBound`, `subLtAdd`, and others) are in the prelude too. `n % d` is defined as `n - (n / d) * d`, with the quotient on the left: multiplication recurses on its left argument, so with a literal divisor and an unknown quotient it stays put, where `d * (n / d)` would unfold into `d` additions while checking. `LessEq` and `LessThan` are the `Bool` `Nat.leq` made into propositions, so a `Nat.leq m n = True` proof is already an `m <= n` proof.
- **Trust.** The native implementations are trusted (DESIGN.md §13). They're registered by name only while the prelude loads, and registration checks each definition's type and arity, and that `Nat`, `Bool` and `Decidable` have the expected shapes (`E-BUILTIN`). `crates/driver/tests/natives.rs` compares the whole result of each (not just its constructor) with its own definition on every small input and on random larger ones, and with one step of its definition on numbers above 2^64.

Extracted JS uses native `bigint` arithmetic for the same definitions.

## Text

`Text` means `MkText (chars : List Char)`, and a `Char` is `MkChar code valid`. But a text literal's characters are stored as one range of an array (`Term::Chars`, `Value::Chars`; `crates/core/src/chars.rs`), following option B1 of [the proposal](proposals/compact-text.md#as-built-stage-2), whose meaning is its expansion, `Cons (MkChar c rfl) … Nil`:

- `"ab"` elaborates to `MkText` of a range, which has type `List Char`. `""` is `MkText Nil`; `['a', 'b']` and `'a'` are still constructors.
- Matching on a range takes the `Nil` branch if it's empty, and otherwise the `Cons` branch with fields `MkChar c rfl` and the rest of the range, without building the list. Evaluation never makes a list compact: `Cons` builds cons cells, so `"ab" ++ t` is two cons cells in front of `t`.
- Conversion compares two ranges by their characters, and a range against anything else by expanding it one cell. So `"a"` and `Cons (MkChar 97 h) Nil` are equal only if `h` and `rfl` are, which for a proof variable `h` they aren't. Unification does the same, but solves a metavariable against a range with the range.
- Quotation gives back a range (copied into its own array if it's less than half of the one it shares, so a short suffix doesn't keep a long literal alive), and hashing covers the characters and `List`'s and `Char`'s hashes, not the array.
- A range is never structurally smaller than anything: descent only comes from matching, where its rest is a `Cons` field.
- **Trust.** These rules are trusted (DESIGN.md §13). The representation is registered while the prelude loads, only if `List` and `Char` (and through `Char`, `Char.isScalar`) have the content hashes it was written for, since the expansion's `rfl : Char.isScalar c = True` relies on `Char.isScalar`'s definition and on each `c` being a Rust `char`. Otherwise literals are constructors, the kernel refuses a range (`E-MALFORMED`), and a test fails until the hashes are updated. `crates/driver/tests/compact_text.rs` compares complete results with the constructor form.

## Elaboration

The elaborator (`crates/elab`) checks surface syntax bidirectionally, following András Kovács' elaboration-zoo, and produces core terms for the kernel.

- **Metavariables.** An unknown, such as an implicit argument or a `_` hole, becomes a metavariable applied to the variables in scope (except variables a case branch has replaced by a constructor). Its solution is a closed function of those variables.
- **Inserting implicit arguments.** When a function's type starts with implicit parameters, the elaborator applies it to fresh metavariables, unless an argument names one with `f [x := e]`. When checking against an implicit function type, it inserts an implicit lambda.
- **Pattern unification.** `?m x₁ … xₙ = t` is solved when the `xᵢ` are distinct variables. The solution is `\x₁ … xₙ -> t`. There's an occurs check, so `?m` can't appear in `t`, and a scope check, so `t` may only mention the `xᵢ`. **Pruning:** if `t` contains another metavariable applied to variables outside the `xᵢ`, that metavariable is narrowed so it can't depend on them. **Fallback:** when the spine isn't a pattern (`?m … (f o) = g … (f o)`), the last arguments are unified and then the rest (`?m … = g …`). This finds *a* solution rather than the most general one, which is safe because the kernel re-checks everything.
- **Constructors.** A constructor's data parameters come from the expected type, or from fresh metavariables. An inferred constructor of a parameterised type is wrapped in a type annotation, so the kernel can infer it too.
- **Zonking.** After a declaration is elaborated, solved metavariables are substituted in. Any left unsolved is an error (`E-UNSOLVED`) at the place it was created.
- **Auto arguments.** Inserting an `[auto x : P]` argument creates a metavariable and records an obligation. Once the declaration is elaborated, each obligation is proved (`crates/elab/src/auto.rs`):
  1. a hypothesis in scope whose type unifies with `P`;
  2. otherwise a **decision procedure**: a definition whose result type is `Decidable …`, trying the most recently defined first, so a file's own procedures take priority over the prelude's. Its arguments are found by unifying `Decidable …` with `Decidable P`. Arguments it still needs that are `Decidable` (like `Decidable.not`'s) are found recursively, up to depth 8, and auto arguments by proof search. It's evaluated at compile time:
     - `Yes` → the proof is `Decidable.fromYes d Trivial`. The kernel accepts this only if `Decidable.IsYes d` computes to `Unit`, so it re-checks the decision itself;
     - `No` → `E-AUTO-FALSE`;
     - stuck on unknown values → `E-AUTO-STUCK`, with a hint to use `if h : P then … else …`;
     - no procedure fits → `E-AUTO-NONE`.

  Failed attempts are undone, by restoring the metavariables from a snapshot.
- **`if`.** `if c then a else b` elaborates to `Bool.ifThenElse c (\_ -> a) (\_ -> b)`. `if h : P then a else b` finds a decision procedure for `P` (it must exist, but may be stuck: it runs at runtime) and elaborates to `Decidable.elim d (\h -> a) (\h -> b)`, with `h : P` in `a` and `h : Not P` in `b`.
- **Operators.** `a != b` is `Not (a = b)`. `a == b` is `Decidable.toBool d`, where `d` is a decision procedure for `a = b`, found as for `if h :`. `<`, `<=`, `+`, `-`, `*`, `/`, `%` are the prelude's `Nat.LessThan`, `Nat.LessEq`, `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`. `Nat.div` and `Nat.mod` take `[auto ok : d != 0]`.
- **Implicitly bound type variables.** An unknown lowercase name in a signature becomes an implicit parameter at the front if *every* use of it is where a type is expected: the domain or result of a function type, a binder's type, or an argument of a data type whose parameter is a type (`List a`, `Or p q`). Its own type is a metavariable, usually solved to `Type`, which is also the default. Any other use (`List.length xs` with `xs` unbound) stays an unknown name.
- **Equations.** Parameters are bound from the signature. Implicit ones are in scope by their signature names. Explicit ones are matched by the equation's patterns, so `length (Cons x xs)` has one pattern while `length` has two parameters. Equations compile to a case tree by the usual matrix method: split on the first constructor pattern in the first remaining equation, and in each branch replace that column by the constructor's fields (rows with a variable there get wildcards). The first equation whose patterns are all variables wins. A column with a number pattern in the first remaining equation compiles to a `NumCase`, unless some equation has `Zero` or `Succ` in that column: then it's split into `Zero` and `Succ` like any constructor column, and a number pattern `n` is `Succ` of the pattern `n - 1`. In a `NumCase`, the arm for each number keeps, in order, the equations with that number in the column and those with a variable or `_`; the default keeps only the latter, and there must be at least one (`E-NONEXHAUSTIVE`). In a column of the prelude's `Int` with a number pattern, `k` is the pattern `OfNat k` and `-k` is `NegSucc (k - 1)` (`-0` is `OfNat 0`), so the column splits into those two constructors, and each field column is a `Nat` column as above.

What the elaborator *doesn't* check is left to the kernel: `Prop` elimination, positivity, universe constraints on fields, and termination. Those errors come from the kernel, with source locations kept from the elaborated term.

## Abilities

Abilities are translated into ordinary data before the kernel sees them, so the kernel's existing checks (positivity and termination) are what show that handlers terminate. The design, and why, is in [docs/proposals/abilities.md](proposals/abilities.md). The translation is in `crates/elab/src/effects.rs`.

- **`ability A params where op : X -> {A params} Y …`** generates:
  - a data type `A params`, with a constructor `A.op (x : X)` for each operation;
  - `A.res : params -> A params -> Type`, giving each operation's result type;
  - `A.elim`, which dispatches a handler's clauses on an operation.

  An operation's argument and result can't mention `A` itself (Landin's knot). The kernel's positivity and termination checks would refuse the generated declarations anyway, but less clearly.
- **Rows.**
  - `{A, B | e}` is the operation type `Effect.Plus A (Effect.Plus B (Effect.sigOp e))`, with matching result types built from `Effect.PlusRes`.
  - Abilities are sorted by where they're declared in the source (whatever order they were checked in). A closed row ends in `Effect.NoOp`.
  - A row variable `e` has type `Effect.Sig` (an operation type together with its result types) and is bound implicitly.
  - Each ability appears at most once (`E-DUPLICATE`).
  - `a -> {E} b` is `a -> Effect.Comp (ops E) (res E) b`.
- **Computation mode.** Checking against `Effect.Comp` over a row of abilities:
  - Expressions that perform nothing become `Effect.Comp.Done v`.
  - An operation call becomes `Effect.Comp.Call (inject op) (\r -> Effect.Comp.Done r)`, injected into the row with `Effect.Plus.L`/`Effect.Plus.R`.
  - Effectful arguments, conditions and operands run first, left to right, through `Effect.bind`.
  - A `let` whose value performs operations, and the lines of a block, are `Effect.bind`s; a `let` whose value is pure is a transparent `Let(x, A, v, rest)`, even when the rest performs operations ([proposals/let.md](proposals/let.md), stage 3).
  - A call to an effectful function whose row differs from the current one is moved into it with `Effect.translate` and a generated `Effect.SigMap`. Every ability it uses must be in the row (`E-ABILITY`). An unknown row variable in the callee is solved with the rest of the row.
  - A result type that depends on an operation's result is refused (`E-EFFECT-ESCAPE`); return a pair instead.
- **Pure contexts.** Code there may perform only what it handles itself: it's elaborated in the empty row and run with `runPure`. A `let` counts as performing only if its value or the rest of the block does (the rest is asked again once the name is bound, so calling a `let`-bound effectful function counts); a block that performs nothing is elaborated directly, as `Let(x, A, v, rest)`, with no `runPure` or `Done` ([proposals/let.md](proposals/let.md), stages 1 and 3).
- **`handle e with …`**, with output row `out`:
  - `e` runs in the row `{A} + (out without A)`, with fresh unknowns for `A`'s parameters.
  - The result is `foldComp done step e`, where `done` is the `return` clause, and `step` dispatches `A`'s operations to the clauses through `A.elim`, forwarding every other operation into `out`.
  - Clauses are elaborated in `out`, so a clause can perform `A` again: it goes to the next handler out.
  - The `return` clause and a clause for each operation are required (`E-HANDLER`).
- **Different orders, fewer abilities.** An effectful function passed where a row lists its abilities in a different order, or lists more of them, is wrapped as `\x -> translate m (f x)`. Plain unification can't reorder or widen a `Plus` chain.
- **Unknown tails.** When a call needs abilities the context's row doesn't list, and the row ends in an unknown, the unknown is solved with them plus a fresh unknown, so later calls can add more. Two open rows `{A | ?f}` and `{B | ?t}` meet with a fresh `?r`: `?f := B∖A | ?r` and `?t := A∖B | ?r`.
- **Operations as values.** `op` on its own is `\x -> op x`, of type `(x : A) -> {Ability args} B`.
- **Messages** show computation types as rows (`{State Nat | e} a`) and the unit type as `()`.

The termination checker accepts recursion on `rest y` for a recursive function field `rest`, which is what makes folds over `Effect.Comp` structural ([Definitions](#definitions)).

## Partial computations

Stage 1 of docs/proposals/partial.md. The kernel's part is small and has no
computation rules (`crates/core/src/partial.rs`, trusted for consistency):

- `Effect.Delay : (op : Type) -> (res : op -> Type) -> Type -> Type`, and the
  constants `Effect.now`, `Effect.lift` (an `Effect.Comp` as an `Effect.Delay`), `Effect.bindD`, `Effect.mapSig` and
  `Effect.pfix : [op res A] [B : A -> Type] -> ((x : A) -> Effect.Delay (Effect.Plus (Effect.Rec A) op)
  (Effect.PlusRes (Effect.RecRes B) res) (B x)) -> (x : A) -> Effect.Delay op res (B x)`.
- They're prelude signatures without equations. `define_primitive` admits
  each, once, `Effect.Delay` first, after checking its type is exactly that one by
  conversion (`E-BUILTIN` otherwise): final, with no body, so it never
  unfolds. An application of one is a neutral term, and conversion compares
  them structurally. `Effect.Delay` isn't a data type: there's no `case` on one,
  and a data type nested in one is refused by positivity. Hashed by name and
  type. Consistency: reading every `Effect.Delay op res a` as a one-element set
  models them all, and none extracts an `a`.

The elaborator's part (`crates/elab/src/effects.rs`, `partial.rs`;
untrusted):

- **Mode.** A row with `Partial` is an `Effect.Delay` rather than an `Effect.Comp`:
  sequencing is `Effect.bindD`, a result `Effect.now`, an operation `Effect.lift (Effect.Comp.Call op Effect.Comp.Done)`,
  a partial call in another order `Effect.mapSig m`, and a total computation in a
  partial context `Effect.lift` (`Effect.translate` first if needed). A partial
  computation in a total context is `E-PARTIAL`; so is a partial function
  where a total one is expected (row variables never stand for `Partial`)
  and a handled computation that's partial.
- **Recursion.** A recursive group (by the module's SCCs) whose members are
  all partial at their entry arity is translated, so nothing recurses in
  the core. For a group `f, g, …` with fixed parameters `ps` (its leading
  large parameters: types, families, rows): `f.Request ps` (one
  constructor per member, holding its other parameters), `f.Response ps`
  by cases, `g.recur` (the request `Effect.lift (Effect.Comp.Call (Effect.Plus.L (Recur (g.request xs)))
  Effect.Comp.Done)`) for each member, `g.description` (the member's equations, with
  every member's name standing for its `.recur`, in the row `{Effect.Rec
  (f.Request ps), ρ}`), `f.body` by cases, and the members `g ps xs = Effect.pfix
  (f.body ps) (g.request xs)`, admitted with one `define_group`. Each is an
  ordinary declaration the kernel checks as usual. A group mixing partial
  and total members is `E-PARTIAL-MIXED`; the members must share their
  fixed parameters and row, and calls must pass the fixed parameters on
  (`E-PARTIAL-NONUNIFORM`). The private `Effect.Rec` is a row label only while
  describing; a recursive call flowing where its requests can't be answered
  is `E-PARTIAL-ESCAPE`, or `E-PARTIAL-CALLBACK` as an argument.
- Messages show an `Effect.Delay` as a row with `Partial`: `{IO, Partial} Nat`.

The runtime's part (`crates/core/src/step.rs`; trusted only for "runs what
was written") is `step`: the stack-safe machine of
`crates/partial-model/src/machine.rs` on the evaluator's values, running a
`Effect.Delay` to its next observation: `Now v`, `Later rest` (one tick per
recursive call; entering an `Effect.pfix` is free), or an operation, returned
unperformed with the rest of the step. `crates/driver/src/run.rs` steps
`main ()`, performs operations, and counts ticks. Nothing it computes is
given back to the checker.

JS extraction erases every `Effect.Delay` to one token: a call to a function whose
result is an `Effect.Delay` with all its arguments is `delayed`, without computing
them; with fewer, a function returning it. An export whose type mentions
`Effect.Delay` is `E-JS-PARTIAL`, and so is extraction if an `Effect.Delay` constant ever
had a body.

## Tests and content hashes

`test "name" = expr` checks `expr` against `Bool` and adds it to the kernel as an unnamed definition. `stitchwort test` evaluates each test; `True` passes.

Every checked declaration has a content hash (`crates/core/src/hash.rs`, BLAKE3). A definition's hash covers whether it's a theorem, its type and its body, after elaboration (so implicit arguments are included). Inside it:

- **references to other declarations are hashed as their hashes**, so a hash covers everything it depends on;
- **a recursive reference is a fixed marker**;
- **names aren't hashed**: not the definition's own, not binder names, not local variables (which are de Bruijn indices). Source locations aren't hashed either;
- **data types are nominal**, so their hash includes their name, their constructors' names, their fields' names (which are the keys of their JS objects), and whether they're records.

Renaming a function or reformatting code changes no hashes. Changing a body changes its hash and the hash of everything that uses it.

**The test cache** stores each result under `.stitchwort/cache/tests/<compiler version>-<fingerprint>-<modes>-<test hash>`. A test runs again only when its hash changes. Failures are cached as well as passes. The fingerprint is a hash of the source of the syntax, core, elaborator (with the prelude) and driver crates, made when the compiler is built (`crates/driver/build.rs`), so a changed compiler doesn't reuse results even with the same version number; the modes say whether natives and compact text were on (`n1c1`), so a run with either switched off doesn't reuse results found with them on. The local cache is trusted. `--no-cache` ignores it.

## The prelude

`crates/elab/src/prelude.sw` defines everything above that isn't built in: `Void`, `Unit`, `Not`, `Void.absurd`/`Void.exfalso`; `Nat` with `+ - *`, `Nat.pred`, `/`, `%`, `Nat.equal`; `Bool` with `not`, `Bool.ifThenElse`, `Nat.leq`, `Bool.decEq`; `<=` and `<` as propositions computed via `Nat.leq`; `List`, `List.length`, `List.append`, and a pure list toolkit (`map`, `filter`, `foldLeft`, `foldRight`, `sum`, `product`, `maximum`, `minimum`, `zip`, `zipWith`, `zipWith3`, `take`, `drop`, `get`, `any`, `all`, `count`, `find`, `mapMaybe`, `concat`, `concatMap`, `replicate`, `range`, `reverse`, `last`, `elem`, `partition`, `lookup`, usable as `xs.map f`) with `Nat.min`, `Nat.max`, `Nat.absDiff`, `Nat.pow` (examples/accept/list-toolkit.sw); `Eq.cong`, `Eq.sym`, `Eq.trans`; constructor disjointness and injectivity; and `Effect.Comp` (computations as trees of operations, docs/proposals/abilities.md) with `Effect.foldComp` and `Effect.bind`; the `IO` ability (`print`, `readLine`, `readAll`) and `IO.simulate`, which runs a program against scripted input and records what it prints (docs/proposals/text-and-io.md); `Decidable` with `Decidable.IsYes`, `Decidable.fromYes`, `Decidable.toBool`, `Decidable.elim` and decision procedures for `=` on `Nat`, `<=`, `<`, `Not`, and `b = True`, and for `=` on `List`, `Pair` and `Maybe` given one for the elements (`List.decEq`, `Pair.decEq`, `Maybe.decEq`; `auto` fills that argument by searching under the binders, examples/accept/eqeq-containers.sw).

**Sorting** (examples/accept/sort.sw): `List.sort : List Nat -> List Nat`, `List.sortBy : (a -> a -> Ordering) -> List a -> List a` (with `Nat.compare`, `Text.compare`, ...) and `List.sortWith : (a -> a -> Bool) -> List a -> List a`, which takes a "may come before" test (`Nat.leq`); `sortBy` is `sortWith` with `Ordering.isLessEq (cmp x y)`, and `sort` is `sortWith Nat.leq`. It's a stable bottom-up merge sort whose runs are kept like a binary counter (slot `i` empty or a sorted run of 2^i elements), so every function is structurally recursive and it's O(n log n): 2,000 numbers sort in a few hundredths of a second under `stitchwort run`. Stability isn't proved. Correctness is `List.sortWithSorted`/`List.sortBySorted`/`List.sortSorted` and `List.sortWithPerm`/`List.sortByPerm`/`List.sortPerm` (and `List.sortLength`):
- `List.Sorted le xs` says each element may come before the next (`le x y = True`, as a conjunction `And`, the prelude's `type And (p q : Prop) : Prop = Both ...`); for a transitive `le` that orders every pair. The sortedness proofs need only that `le` is total (`le x y = False -> le y x = True`; `Nat.leqTotal`, `Nat.compareTotal`), not transitivity, since adjacent pairs are all a merge compares.
- `List.Perm xs ys` is `(p : a -> Bool) -> List.occurrences p xs = List.occurrences p ys`: every test is passed by as many elements of each. Counting makes the proofs arithmetic on `+` (the count of a merge is the sum of the counts) instead of rearranging an inductive permutation with swap and transitivity steps, and it needs no equality on the elements; with decidable equality it's the usual meaning (test with `Nat.equal v`). `List.permRefl`, `permSym`, `permTrans`, `permLength` come with it.
- Proofs about `if le x y then ... else ...` use `Bool.inspect b motive t f`, which cases on `b` while remembering `b = True` or `b = False`; a separate helper that matched on the `Bool` would lose the size-change evidence for the recursive call.

Division is defined by structural recursion on fuel (`n` steps is always enough when the divisor isn't zero). Its non-zero precondition is what makes `n / 0` a compile-time error rather than a convention.

## Erasure and JS extraction

What's erased:

- **Definitions:** a definition is erased (not emitted) if its type is a proposition or a type former.
- **Parameters:** a parameter is erased if its type is a proposition or a type former. Calls to definitions drop erased arguments. Lambdas keep all their parameters, and erased arguments passed to them become `undefined`.
- **Terms:** `Data`, `Sort`, `Pi`, `Eq` and `Refl` compile to `undefined`. `J P d p` compiles to `d`.
- **Case on a proof:** this is only possible for the subsingleton propositions above, so it compiles to its single branch.

Representations: `Nat` is `bigint` (`Zero` is `0n`, `Succ n` is `n + 1n`, a case on `Nat` tests `=== 0n`, and a `NumCase` is a `switch` whose arms each return, followed by the default). Other data types are `{ tag, …fields }`, omitting erased fields; a record is `{ …fields }`, with no tag (docs/proposals/records.md §11).

The exportability check, the boundary encodings and the decode → compute → encode contract are as described in DESIGN.md §12, restricted to `Nat`, `Bool`, `List` and parameterless data types built from them.

**Preconditions.** An export's proof parameters (like `[auto ok : percent <= 100]`) aren't passed by JS. For each one, the elaborator finds a decision procedure in the context of the earlier parameters. The kernel checks it has type `Decidable P` (`add_validator`), and that the data type used really is shaped like `Decidable`, with its first constructor carrying a proof of `P`. The generated wrapper decodes the inputs, runs each decision procedure on them, and throws `StitchwortInputError` unless it says `Yes`. A proof parameter with no decision procedure makes the export `E-EXPORT`.

Only definitions reachable from the exports (and their checks) are emitted, in the kernel's order, which is dependency order (a definition refers only to earlier ones and to members of its own group). Each definition has one calling convention, decided once and used at its declaration, every reference, application and first-class use, and in its export wrapper: a *function* if it has runtime parameters; otherwise a *thunk* (a function of no arguments, called as `f()`) if its body is a case tree (such as `absurd`, whose only parameter is an erased proof, so it only runs if it's reached) or it's a member of a group of two or more (so it never calls a sibling while the module loads, before the sibling is defined); otherwise a *value*, computed when the module loads. Only a function's tail calls to itself become loops: definitions in a group that tail-call each other use a stack frame per call, and running out is a `StitchwortResourceError`.

## Error codes

| Code | Meaning |
|---|---|
| `E-PARSE` | Syntax error |
| `E-UNKNOWN-NAME` | Name not in scope |
| `E-UNKNOWN-FIELD` / `E-RECORD-FIELD` / `E-NOT-A-RECORD` / `E-RECORD-UPDATE` | A record has no such field; a literal or pattern leaves a field out or gives one twice; a record operation on something that isn't a record; an update that replaces a field without the later fields whose types mention it |
| `E-DUPLICATE` | Name defined twice, or a built-in name redefined |
| `E-MISSING-DEFINITION` | A `def` header with no body (only the prelude's primitives may) |
| `E-ARITY` | Wrong number of patterns or arguments |
| `E-NOT-A-CONSTRUCTOR` | A pattern that isn't a constructor |
| `E-TYPE-MISMATCH` | Types don't match |
| `E-UNIVERSE` | Universe mismatch, or a field too large for its data type |
| `E-CANNOT-INFER` | Needs a type annotation |
| `E-NOT-A-TYPE` / `E-NOT-A-FUNCTION` / `E-NOT-A-SORT` | Wrong kind of thing |
| `E-NOT-A-PROP` | A `theorem` whose type isn't a proposition |
| `E-REFL` | `rfl` used for sides that don't compute to the same value |
| `E-NONEXHAUSTIVE` | Missing pattern-match case |
| `E-MATCH-MOTIVE` | A `match` whose scrutinees can't be generalised in this version (the same variable twice, one scrutinee part of another, one's type mentioning another) or whose generalised type is ill-formed |
| `E-MATCH-EQUATION` | The equation of `match h : e with` can't be formed (the types differ); not reported in the first version |
| `E-TERMINATION` | Recursion that can't be shown to terminate, or a recursive call not given all its arguments |
| `E-POSITIVITY` | Data type used in a negative position, inside another type, or with other parameters (for any member of its data group) |
| `E-MUTUAL-SIGNATURE` / `E-MUTUAL-CONSTRUCTOR` / `E-MUTUAL-PARAMETERS` / `E-MUTUAL-KIND` | A type or header mentioning something it's checked together with; a field using a constructor of its own group; data types defined together with different parameters or universes; a cycle mixing data types and definitions, or with an ability |
| `E-PROP-ELIM` | Matching on a proof to produce data, where that's not allowed |
| `E-EXPORT` | Export can't cross the JS boundary |
| `E-UNSOLVED` | An implicit argument the elaborator couldn't work out |
| `E-AUTO-FALSE` / `E-AUTO-STUCK` / `E-AUTO-NONE` | An auto argument is false, can't be decided at compile time, or has no decision procedure |
| `E-NOT-EMPTY` | An absurd pattern `()` for a type that has values |
| `E-UNSUPPORTED` | Not implemented yet |
| `E-ABILITY` | An operation or effectful call where its ability isn't allowed, or a malformed `ability` |
| `E-HANDLER` | A handler without a `return` clause or a clause for every operation |
| `E-EFFECT-ESCAPE` | A result type that depends on the result of an operation |
| `E-PARTIAL` | Running partial code where the type doesn't say `Partial`: in a total function, a handled computation, or for a row variable |
| `E-PARTIAL-MIXED` | A recursive group with partial and total members |
| `E-PARTIAL-CALLBACK` / `E-PARTIAL-ESCAPE` | Inside a partial recursive definition, the definition passed to a helper whose callback has a fixed row, or returned or stored where nothing can answer its requests |
| `E-PARTIAL-NONUNIFORM` | A partial recursive call that changes its type parameters, type parameters after ordinary ones, members with different type parameters or rows, or arguments that can't be packed into a request |
| `E-JS-PARTIAL` | An export whose type mentions `Partial` |
| `E-RESOURCE` | Checking or evaluation ran out of steps, stack depth or printing size before finishing: there's no answer, rather than a wrong one (docs/proposals/stack-safe-evaluation.md) |
| `E-BUILTIN` | A prelude type or definition the compiler implements natively, or `Effect.Delay` and its constants, doesn't have the expected shape |
| `E-FAILED-DEPENDENCY` | A declaration uses one that has errors (reported only when that one's errors aren't) |
