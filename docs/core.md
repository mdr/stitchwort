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
| Numbers | `Nat`, plus `Int` as a data type over `Nat`. `Nat` numbers are native and can be any size (see [Numbers](#numbers)) |
| Pattern matching | Nested patterns, but no overlap warnings |
| Declaration order | Free: every name is visible throughout its module, definitions may call each other ([groups](#groups-of-definitions)), and data types may refer to each other ([data groups](#groups-of-data-types)) |
| Data types | Parameters and indices ([indexed families](proposals/indexed-families.md): declarations, and `case` with unification, below; syntax in docs/syntax.md). Equality is built in |
| Universes | Numbered, no polymorphism, no cumulativity |

## Terms

Variables are de Bruijn indices in terms and de Bruijn levels in values.

| Term | Meaning |
|---|---|
| `Var(i)` | A local variable |
| `Def(f)` | A top-level definition |
| `Data(D, args)` | A data type applied to all its parameters, then all its indices |
| `Ctor(D, c, fields)` | Constructor `c` of `D` applied to all its fields. Parameters and indices come from the expected type |
| `Sort(s)` | `Prop` or `Type i` |
| `Pi(x, i, A, B)` | `(x: A) -> B`; with `i` implicit, `[x: A] -> B`; with `i` auto, `[auto x: A] -> B` |
| `Lam(x, i, b)` | `x => b` |
| `App(f, a, i)` | Application, to an explicit or implicit argument |
| `Ann(e, T)` | `(e: T)` |
| `Let(x, A, v, b)` | `let x: A := v; b`: a transparent local definition. `x` takes a slot (`b` is under one binder) but stands for `v` itself ([proposals/let.md](proposals/let.md)). A leaf, never a case-tree node: no `Case` may appear under it. It also carries whether running skips `v`, which the kernel sets when it checks it (below); hashing ignores that |
| `Case(x, D, branches)` | Match variable `x: D params indices`, one branch per constructor. A branch has no body when its constructor is impossible ([below](#unifying-indices)). Only appears at the top of a definition, forming a case tree |
| `Chars(range)` | A `List Char`, stored compactly: the characters of a range of an array, standing for `Cons (MkChar c rfl) … Nil` ([text](#text)) |
| `NumCase(x, arms, default)` | Compare variable `x: Nat` with numbers: one arm per number, in strictly increasing order (at least one), and a default. Only appears where `Case` may |
| `Eq(A?, a, b)` | `a = b`. `A` is filled in by the checker |
| `Refl` | `rfl: a = a` |
| `J(P, d, p)` | Transport along an equality |
| `Loc(span, t)` | A source location, ignored except for error messages |
| `Meta(m)` | A metavariable. Only used inside the elaborator: the kernel rejects terms containing one |

## Universes

```
Prop: Type 0        Type i: Type (i+1)
```

The universe of a function type:

| `A: s₁`, `B: s₂` | `(x: A) -> B: …` |
|---|---|
| `s₂ = Prop` | `Prop` (impredicative) |
| `s₂ = Type j` | `Type (max (level s₁) j)`, where `level Prop = 0` |

There's no cumulativity: a `Type 0` isn't automatically a `Type 1`.

## Typing

Checking is bidirectional. `Γ ⊢ t ⇒ A` infers a type, and `Γ ⊢ t ⇐ A` checks against one. Types are compared with conversion `≡` (below). Checking returns a completed term, with each `Eq`'s type filled in.

**Inferred:**

- `Var`, `Def`: from the context or the declaration.
- `Data(D, args)`: the parameters, then the indices, are checked against their declared types, as one telescope. The result is `D`'s universe.
- `Sort(s) ⇒ Sort(succ s)`.
- `Pi(x, A, B)`: `A` and `B` must be types. The universe follows the table above.
- `App(f, a)`: `f ⇒ (x: A) -> B`, `a ⇐ A`, giving `B[a/x]`.
- `Ann(e, T)`: `T` is a type, `e ⇐ T`, giving `T`.
- `Let(x, A, v, b)`: `A` is a type in any universe (a proof, data or a type are all defined the same way), `v ⇐ A`, then `b ⇒ B` with `x: A := v` in the context, giving `B[v/x]`. In the context `x` evaluates to `v`'s value, not to a variable, so while checking `b` its uses compute (ζ-reduction), and `B`, a value, never mentions `x`: it's already `B[v/x]`, usable outside the `let`. Checked the same way against an expected type, with `b ⇐` it. While checking, `v` is computed only when the checker first evaluates a term that mentions `x` (a type, or an argument a type depends on), and then once; running a program computes it strictly.
- `Eq(_, a, b)`: infers `a`'s type `A` (or `b`'s, if `a` can't be inferred) and checks the other side against it. Gives `Prop`.
- `J(P, d, p)`: `p ⇒ x = y` at type `A`. `P` must be written `y' p' => T` with `T` a type, where `y': A` and `p': x = y'`. Then `d ⇐ P x rfl`, giving `P y p`.
- `Ctor` of a data type *without parameters*: checked against that type; with indices, its type is `D` applied to its result indices, with the fields substituted (`FZero [2] ⇒ Fin 3`).

Implicitness only has to agree: `App(f, a, i)` needs `f`'s type to be a function type with the same `i`, and `Lam(x, i, b)` checks only against a function type with the same `i`. The kernel never inserts implicit arguments. It sees them already filled in.

**Checked:**

- `Lam(x, i, b) ⇐ (x: A) -> B` (same `i`): `b ⇐ B` with `x: A`.
- `Ctor(D, c, fs) ⇐ D ps is`: each field is checked against its declared type, with the parameters and earlier fields substituted in. Then the constructor's result indices, with the parameters and fields substituted, must be convertible with `is` (`E-TYPE-MISMATCH`: `VNil` builds a `Vec a 0`, not a `Vec a 1`).
- `Refl ⇐ a = b`: requires `a ≡ b`. Otherwise error `E-REFL`.
- `Case`: see below.
- Anything else: infer, then require the inferred type `≡` the expected one. If both are universes, the error is `E-UNIVERSE`, otherwise `E-TYPE-MISMATCH`.

## Data types

A declaration `type D (params): s = | C₁ fields | …`:

- **Parameters** are checked as a telescope.
- **Indices** (`declare_indexed_data_group`, docs/proposals/indexed-families.md §6.1): an index telescope after the parameters, checked in their context, each index's type in the context of the earlier ones. `D`'s type is `(params) -> (indices) -> s`; `Vec (a: Type): Nat -> Type` has the parameter `a` and one index. Most types have none.
- **The universe `s`** defaults to `Type`.
- **Each field type** is checked in the context of the parameters and the earlier fields.
- **Result indices.** Each constructor of a type with indices states the indices of its result, terms in the context of the parameters and its fields, checked against the index telescope (each index's type with the parameters and the earlier result indices substituted). As many as there are indices (`E-MALFORMED` otherwise); none for a type without indices. The result's parameters aren't written: they're always the type's own. `VCons [n: Nat] (x: a) (xs: Vec a n)` has the result index `Succ n`.
- **Universe constraint (`E-UNIVERSE`).** A field whose type is in `Type i` is only allowed if `D: Type j` with `i ≤ j`, or `D: Prop`. Prop-valued fields are always allowed. An index's type obeys the same rule (no large indices, D142): `Ty: Type -> Type` is refused, since its index `Type` is in `Type 1`, and `Ty: Type -> Type 1` is the form to write.
- **Strict positivity (`E-POSITIVITY`).** `D` may only appear in a field's type as `D` applied to exactly its own parameters, and then to indices that don't mention `D`, or as the result of a function type whose inputs don't mention `D`. Nested occurrences, like `List D`, are rejected conservatively. A constructor's result indices mustn't mention `D` either. In a [data group](#groups-of-data-types), this holds for every member, in the fields and result indices of every member.
- **Erased fields:** a field is erased if its type is a proposition or a type former (a universe, or a function returning one).
- **Records** (`declare_data_group_as`, docs/proposals/records.md): a data type may be declared as a record, which must have exactly one constructor (`E-MALFORMED` otherwise), and no indices (`E-MALFORMED`). The flag is fixed when the type is declared and hashed; checking never depends on it (it only says how JS represents the type). The elaborator gives a record a projection per field, an ordinary definition by a one-branch case. A record's proof field may get a **validator** (`add_field_validator`): a decision procedure for the field's proposition, in the context of the parameters and earlier fields, which the kernel checks has type `Decidable P` (as for an export's precondition), and which extracted JS runs to establish the field for decoded input.

## Case trees

`Case(x, D, branches) ⇐ G`, where `x: D ps is` is a variable in the context (`is` empty for a type without indices):

1. There must be exactly one branch per constructor, in declaration order (`E-NONEXHAUSTIVE`).
2. **`Prop` elimination (`E-PROP-ELIM`).** If `D: Prop` and `G`'s universe isn't `Prop`, then `D` must be alone in its data group, have at most one constructor, and every field of it must be a proof (propositions defined together never eliminate into data, a conservative rule taken from Lean). This is Lean's subsingleton-elimination rule. It's stated over the declaration's fields, not over runtime erasure: a `Type` field is erased but still disqualifies (`HiddenType`). One addition: a case whose every branch is impossible (by a conflict, below) may produce anything, since it's never reached (`Le (Succ n) 0 -> Nat`). The "or appears in an index" clause from DESIGN.md §6 isn't adopted (D140): a field that a proof's indices determine still disqualifies (`IsSucc k -> Nat` reading `IsSucc`'s `n` is refused). Equality is built in, and its eliminator `J` is always allowed.
3. **Refinement.** For constructor `c` with fields `f₁ … fₖ`, in this order: the fields are bound, after everything in scope; for a type with indices, `c`'s result indices are unified with `is` ([below](#unifying-indices)), each solution substituted throughout the context and the goal; then the branch is checked with the fields in scope, against `G` with `x` replaced by `c f₁ … fₖ`. Inside the branch, `x` also *evaluates* to that constructor value, so its uses compute, and the constructor value is substituted for `x` throughout the context: in every variable's type and value, including variables bound before `x` (with nested patterns, `rest: res o` is bound before `o` is matched). For example, in `Decidable.fromYes (No r) u`, the hypothesis `u: Decidable.IsYes d` becomes `u: Decidable.IsYes (No r)`, which computes to `Void`.
4. **Impossible branches.** A branch whose unification finds a conflict is impossible: it has no body. A body on an impossible branch, or no body on a possible one, is `E-MALFORMED` (the elaborator decides which, and the kernel checks). For `get: Vec a n -> Fin n -> a`, the `VNil` branch is *possible* (`n := 0`): its body is a case on `i: Fin 0` whose branches are both impossible.
5. **No constructors.** A case with no branches is how an absurd pattern `()` compiles. It's only accepted when the data type has no constructors, and since such a type is trivially a subsingleton, it may produce anything.

### Unifying indices

docs/proposals/indexed-families.md §6.3; `crates/core/src/unify_index.rs`, which the elaborator will call too, so there's one implementation. The problem for a branch is a telescope: `D`'s index telescope, with `ps` for the parameters, `is` on the left and `c`'s result indices on the right. Constraints are formed from a **stack of telescopes**, one binder at a time: a binder's constraint is `{ type, lhs, rhs }` with `type` its type evaluated with the earlier *left* values, and it's formed only once every earlier binder is solved; if its type evaluated with the earlier *right* values differs, the problem is stuck. So both sides of every constraint have the same type. Each constraint, with both sides evaluated in the current refined context, gets the first rule that applies:

- **Deletion.** `lhs ≡ rhs`: solved. This is axiom K (D138): `sameK (p: Same x x): p = Refl` is provable by matching.
- **Solution.** One side is a *flexible* variable: one that still stands for itself (a parameter, or a field of this or an enclosing case not yet replaced), other than the matched `x`. If both are, the one bound later is solved as the earlier one (it's usually a field the user didn't name); if its occurs check fails, the other way round. The **occurs check**: the variable mustn't occur in the other side, nor in the type of any variable of it, nor, transitively, in the types of the variables those mention. A failed occurs check is stuck (`n = Succ n`), never impossible. A solution `y := t` is substituted through the whole context (values and types), the goal and the rest of the problem, and `y` then evaluates to `t`, as a matched variable does. The context is semantic (values by level), so a variable bound before a field can get a type mentioning it (`h: P n` becomes `h: P (Succ m)`); among the flexible variables, "the type of one mentions another" stays acyclic.
- **Injectivity.** `type` is a data type in `Type i` (never `Prop`) and both sides are the same constructor: its fields are pushed as a new telescope (with `type`'s parameters), compared in order.
- **Conflict.** `type` is a data type in `Type i` and the sides are different constructors: the branch is **impossible**.
- For `Nat`, a number is `Succ` of its predecessor, and `k + x` is `Succ` applied `k` times; a compact list expands one cell.
- **Anything else is stuck**, and the case is refused (`E-INDEX-STUCK`): a type former on a side (`List a = List Nat` at `Type`: types are never taken apart, D139), an application that doesn't compute (`n + m = 0` with `n` unknown: `+` counts down its first argument, so declare `Succ n`, not `n + 1`), a failed occurs check, and an equation between proofs (its type is a proposition) that deletion and solution don't settle. Proofs are never taken apart: telling `A = B` at `P: Prop` impossible would contradict proof irrelevance (D137, tests 22-25 of the note).

The problem is solved when the stack is empty. Only a conflict makes a branch impossible; stuck never does.

**Termination** reads no decrease from an index equation (D143): after `n := Succ m`, `m` isn't smaller than `n` (test 13), though a constructor's implicit fields, like `m` in `VCons [m] x xs`, are stored fields, so smaller than the vector. A recursive function field is recognised from the constructor's declared field type, never from its type in a branch (test 12, Agda issue #6654). An impossible branch has nothing to walk.

`NumCase(x, [(k₁, b₁), …, (kₘ, bₘ)], d) ⇐ G` is how number patterns compile (docs/proposals/number-patterns.md). `x` must be a variable of the prelude's `Nat`, and the numbers strictly increasing with `m ≥ 1`; anything else is `E-MALFORMED`, since the elaborator never produces it. Each arm `bᵢ` is checked with the number `kᵢ` substituted for `x` throughout the context and the goal, as a `Case` branch substitutes its constructor value. The default `d` is checked with nothing new known about `x`: not a predecessor, and not that it differs from the `kᵢ`. So a `NumCase` stands for the nested `Zero`/`Succ` cases that count down to `kₘ`, with the default copied to every other leaf, and accepts no more than they would (it accepts less: the copies of the default know more about `x`). It binds nothing, so it's no evidence of structural descent for termination, but evidence from cases around it still counts in every arm and the default.

It evaluates by the value of `x`: a number takes its arm, or the default; `k + x'` (a number of `Succ`s around something unknown) takes the default when every `kᵢ < k`, since it's at least `k`; anything else is stuck, so the definition stays folded. Failing to show that `x` is some `kᵢ` is never taken to mean it isn't.

## Equality

- `Eq(A, a, b): Prop` and `Refl ⇐ a = b` when `a ≡ b`.
- `J` computes: `J P d rfl ⟶ d`. With any other proof it's stuck.
- `Eq` satisfies the elimination rule: one constructor, no fields. So `J` may produce data (transport).
- There's no definitional proof irrelevance: two different proof terms aren't automatically equal.
- Axiom K holds: matching deletes an index equation that already holds ([above](#unifying-indices)), so `p = Refl` for `p: Same x x` of an equality family, and through `J`, K for `=`. That's consistent, and rules out only univalent and higher-dimensional readings of equality (docs/proposals/indexed-families.md §6.5).

## Definitions

Definitions are admitted in **groups** of one or more that may call each other (`define_group`; `define_def` is a group of one). The elaborator submits each strongly connected component of the module's definitions as one group ([below](#groups-of-definitions)).

1. **Declare:** the signature is checked to be a type. For `theorem`, it must be a proposition (`E-NOT-A-PROP`). The definition is added *without a body*.
2. **Arity.** The body's number of leading lambdas (looking through source locations, and counting implicit, type and proof lambdas) is the definition's **entry arity**, fixed, for every member of the group, before any body is checked. It's the one number used for unfolding (below), for the saturation rule and the graphs of the termination check, and for extraction. Lambdas inside the case tree belong to its result: `f: Nat -> Nat -> Nat; f Zero = x => x; …` has arity 1.
3. **Define:** each body is checked against its signature. While this happens, no member of the group has a body, so references to any of them are opaque and never unfold.
4. **Termination (`E-TERMINATION`)**, by size change ([details](proposals/mutual-recursion.md#6-termination-for-a-group-of-functions)), for the whole group at once: a call from any member to any member (itself or another) is a call. Every occurrence of a member, wherever it is (under lambdas, in types, inside other calls' arguments), must be applied to at least that member's arity's arguments; a bare or partial one is refused, with a suggestion to write `x => f a x`. Each such call is summarised by a *size-change graph*: for each parameter position of the callee, whether the argument there is
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

### Recursion on a measure (`decreasing`)

The kernel knows only structural recursion. `def f (x: A) (c: C): B decreasing m x := body` (docs/syntax.md; docs/proposals/well-founded-recursion.md, option B) is elaborated (`crates/elab/src/decreasing.rs`) into ordinary declarations, each checked by the kernel like any other, so nothing new is trusted:

1. `f.%step (x: A) (%rec: (y: A) -> (c: C) -> [auto decreasing: m y < m x] -> B) (c: C): B`: the body, with every recursive call `f y c'` elaborated as `%rec y c'` and its `decreasing` argument found by `auto` or given as `[decreasing := p]`. Not recursive; its `match`es are lifted as usual and take `%rec` as a capture.
2. `f.%go (k: Nat) (x: A) (c: C) (h: m x < k): B`, structural on `k`. `Zero` is absurd (`m x < 0` is `False = True`); `Succ k` is `f.%step x (y c' p => f.%go k y c' (Nat.leTrans (Succ (m y)) (m x) k p h)) c`.
3. `f (x: A) (c: C): B := f.%go (Succ (m x)) x c (Nat.leRefl (m x))`, marked folded (`Def::fold`, as a dictionary is): applied to all its arguments it stays `f x c` until something takes it apart (a `case`, or a comparison its name doesn't settle). So on open arguments goals show `f x c`, and on known ones tests and `rfl` compute: the fuel is a number, one step per call, and `m x` is computed once per outside call.
4. For a `def` (not a theorem): `f.%step.%respects` (and one for each lifted helper that passes `%rec` on), proving that `f.%step` gives equal results for two `%rec`s equal on every argument. Its case tree is `f.%step`'s; each leaf is proved by rewriting one recursive call at a time with `J`. A call `F … c …` whose function argument `c` (an `if`'s branch, or a callback such as `List.sumBy`'s) contains recursive calls is rewritten as a whole by `F`'s congruence lemma `FCong`, found by name beside `F`'s declaration and checked to have the shape `F`'s parameters, each function parameter twice, then one premise `(x…) -> c1 x… = c2 x…` per function, proving `F …c1… = F …c2…` (`Decidable.elimCong`, `Bool.ifThenElseCong`, `List.sumByCong`, …). Each premise is proved under exactly its own binders, by the same rewriting inside the function's body; the call's other arguments are rewritten first, by `J`. No function extensionality is needed: a function whose result is itself a function, or one stored in data, is refused.
5. `f.%irrel`: `f.%go k x c h = f.%go j x c g`, by induction on both fuels.
6. `f.unfold (x: A) (c: C): f x c = f.%step x (y c' => f y c') c`: the definition's own equation, which `f.%step` unfolds to the body with `f` in its recursive calls. Users name it `f.unfold` (it's in scope like a local definition, `f.go`).

`f`'s **run body** (`Def::run_body`, `check::set_run_body`) is `x c => f.%step x (y c' => f y c') c`: the kernel checks its type and arity, never its termination, and never unfolds it. `stitchwort run` (`crates/rt`) and JS run it instead of the body, so the fuel, `f.%go` and the measure are never computed there (a run body isn't hashed; the check cache stores it). `stitchwort test` and `run --reference` use the kernel's evaluator, with the fuel.

### Groups of data types

Data types are admitted in **data groups** of one or more whose fields may mention each other (docs/proposals/mutual-recursion.md §5.4, §7). `declare_data` and `define_ctors` are a group of one.

- **Declare** (`declare_data_group(params, sort, names)`, or `declare_indexed_data_group` with an index telescope for each member): one parameter telescope, checked once in one context, and one universe, shared by every member by construction. Each member has its own indices (`Even`/`Odd` can be mutual), checked in the parameters' context. The parameters may refer only to final declarations; a reference to a declaration that doesn't exist yet, including one a member is about to become (ids are plain indices), is `E-MALFORMED`, and nothing is added. Each member records its group (the members, in declaration order), fixed then and never changed. The members are pending.
- **Define** (`define_data_group`): the constructors of every member, in one call. Every member of the group must be listed, once, and nothing else; otherwise `E-MALFORMED`, and every member fails. A field may mention final declarations and the group's members *as types*; a member's constructors, or a `case` on one, are pending references (`E-MALFORMED`; the elaborator says `E-MUTUAL-CONSTRUCTOR`). Positivity is checked for every member in every field; the "declared later" guard allows the group's own members and nothing declared after the group. Either every member becomes final, with its constructors, at once (until then none can be built, matched on or hashed), or every one fails.
- **Termination.** A field of a constructor matched out of a parameter is smaller than it, whatever its type, so `size (Node n kids) = Succ (sizeForest kids)` is a smaller call. A function field returning any member of the matched type's group (`child: Nat -> Layer` in a `Branching`) is a recursive function field: its results are smaller.
- **`Prop`.** A member of a group of two or more propositions never eliminates into data; proof-to-proof matching is unaffected.
- **The elaborator's groups.** A strongly connected component of data types is one group: their parameters (which must be the same, names included, `E-MUTUAL-PARAMETERS`) and universes are elaborated, then all their constructors. A header mentioning a member is `E-MUTUAL-SIGNATURE`. A cycle with a definition, or with an ability, is `E-MUTUAL-KIND`.
- **Hashes.** A group of two or more is hashed as a unit, ordered by name (ties in declaration order): the group's hash covers the parameters, the universe, the number of members and each member's name and constructors, with references to members (as types, constructors or in a `case`) as their index; each member's hash is the group's hash and its index. So changing any constructor of any member changes every member's hash.

**Admission** ([details](proposals/kernel-admission.md)). Each definition and data type is *pending* (declared), *final* (its body or constructors admitted) or *failed*. Only final definitions have a body, so only they unfold; only final data types can be matched on, and only final declarations have a hash. Whatever a signature, body, data parameter, constructor field or validator refers to must be final, apart from the members of a definition's group in its body and the members of a data type's group (as types) in its fields. A reference to a pending declaration is refused (`E-MALFORMED`), so a cycle can't be split across two definitions and a data type without its constructors yet is never treated as empty. Defining something twice is refused too. If a body or constructors are refused, the declaration fails, and anything using it is still checked but fails too (`E-FAILED-DEPENDENCY`, which the elaborator doesn't report when the original error is reported). So later declarations can refer to a failed one without cascading "unknown name" errors, but nothing built on it is ever accepted. A file with any errors produces no guarantees and can't be extracted.

## Evaluation and conversion

Normalisation by evaluation (`crates/core/src/value.rs`):

- **Unfolding policy.** A definition applied to fewer than its arity arguments stays folded, as a neutral term headed by the definition. Once it has all its arguments, it unfolds **only if its case tree can take a step**, meaning every case it reaches is on a constructor (and every `NumCase` can choose an arm or its default, as above). Otherwise it stays folded. That makes conversion terminate even though `List.length a xs` mentions `List.length`. Definitions with arity 0 always unfold, except dictionaries.
- **Dictionaries stay folded by name.** A definition the elaborator marks as a dictionary (`Def::fold`: an instance, or another definition whose result is an interface, docs/proposals/interfaces.md) stays folded once it has all its arguments, `Nat.instAdd` or `List.instShow Nat.instShow`, until something takes it apart: a `case` on it (a projection) unfolds it, as do conversion and unification when the name alone doesn't settle a comparison (the same dictionary applied to equal arguments is equal; otherwise both sides are compared unfolded). So what's equal doesn't change, only when it's computed, and the flag isn't hashed. Elaborated terms, messages and extracted JS then name the dictionary instead of writing out its record. While a program runs (erasure, below), dictionaries unfold at once, as other definitions do.
- **Theorems stay folded too** (SW-281). A `theorem` applied to all its arguments stays folded in the same way, so a proof that's only passed along (an argument, a constructor field, a solved implicit argument) is never computed. A theorem's value is a proof, and only three things look inside a proof: a `case` on it (a proposition with one constructor, `E-PROP-ELIM`), `J`, and a comparison; each unfolds a folded call first, the first two inside the machine (so a proof built from many folded steps uses no Rust stack). Natives never take a proof. So, as for dictionaries, what's equal doesn't change, only when (and whether) it's computed. One cost: a folded proof that's taken apart twice is computed twice (there's no sharing); a strict evaluator computed it once even when nobody looked. Elaborated terms keep the theorem's name where they had its computed proof, which changed some hashes.
- **Glued calls (elaborator only, off for now).** With `Globals::glue` on, a definition with a case tree applied to all its arguments evaluates to `Value::Call`: the call, which means its unfolding, computed by `force` the first time something looks inside and then shared by every copy (docs/proposals/folded-calls.md). Natives and dictionaries don't glue, and nothing glues while a program runs. Everything that takes a value apart calls `force` first, so a call behaves exactly as its unfolding: read-back writes the unfolding, and conversion compares unfoldings. The kernel always checks with gluing off (D483); the elaborator's unification tries two calls of the same definition by their arguments first. A kept unfolding records `Globals::meta_epoch` and is recomputed once metavariable solutions have been taken back, as it may have used one. Stage 1 of the note: the switch is off everywhere except under `STITCHWORT_GLUE=1`, a testing aid.
- **Arguments are computed only when a type needs them.** The type of `f a` is `f`'s result type with `a`'s value put in, so checking would compute `a`. When the result type doesn't mention its parameter, as in `constant 0 (List.length bigList)`, `a` isn't computed at all; the same goes for constructor fields and data parameters that later types don't mention (`Closure::apply_lazy`, `later_types_mention`). A computation that does appear in a type is still run while checking: in `test "t" = f x == y`, the equation `f x = y` is the type of the decision, so `f x` is computed when the test is checked as well as when it runs.
- **Conversion `≡`:** structural on values, with eta for functions (`f ≡ x => f x`). Folded definitions are equal when they're the same definition applied to convertible arguments (a folded dictionary is also compared by unfolding, above, before numbers are compared by their `k + x` forms, so a folded `f n` that unfolds to `1 + …` is compared as a number). A definition applied to fewer arguments than it takes is a function too, so it's compared by applying both sides to a fresh variable: `F` defined by `F o = PlusRes … o` equals `PlusRes …`.
- **`let`** evaluates its value once, strictly, before the body, which sees it in its environment: `eval(Let(x, A, v, b), ρ) = eval(b, ρ ++ [eval(v, ρ)])`. Quoting never produces a `Let`, and conversion needs no case for it, since values don't contain one. A `let` takes a slot in terms (de Bruijn indices count it) but no variable level stands for it, so the levels in use have a gap there, as after a case split. When running (with erasure, below), a `let` the kernel marked is skipped, its slot getting the placeholder: one whose `A` would make a parameter erased (a proposition or a type former), or whose body doesn't use `x`.
- **Running a program** with `stitchwort run --reference`, or running a `test`, uses the same evaluator, strictly. (`stitchwort run` itself runs the program on a separate, untrusted runtime, `crates/rt`: an erased IR and a machine that keeps its frames on the heap, differential-tested against this evaluator; docs/proposals/fast-runtime.md. Its output can be wrong, but a proof never depends on it.) Arguments are evaluated before calls. `stitchwort run` and `stitchwort test` (never the checker) also **erase** as JS extraction does (`crates/core/src/erase.rs`): arguments for erased parameters (proofs and types) and erased constructor fields aren't computed, a definition whose result is erased isn't run, `J` on an erased proof takes its base, and a `case` on an erased proof takes its only branch. A run that reaches an impossible branch (which a well-typed program never does) fails with an internal error; while checking, such a case just stays stuck. This is safe because nothing matches on a type, and a proof is matched into data only when it has one possible shape (`E-PROP-ELIM` below), so the run takes the same branches with or without erasure; only proofs and types, which are never printed or compared, differ. A record carrying `ok = Int.modNatLt x 100` costs nothing at run time.
- **Comparing types** reduces under binders. It never reaches an effectful operation, because there aren't any yet.

## Numbers

`Nat` means `Zero | Succ Nat`, but a number is stored as one arbitrary-precision value (`Term::Nat`, `Value::Nat`; `crates/core/src/native.rs`), following option A of [the proposal](proposals/native-numbers.md):

- A number has type `Nat`. Matching on `n` takes the `Zero` branch if it's 0, and otherwise the `Succ` branch with field `n - 1`, without building a chain.
- Conversion treats `3` and `Succ 2` as equal (`Succ x` is never equal to a number unless `x` is). Evaluating `Succ` of a number, or `Zero`, gives a number.
- **Numbers with unknowns.** `k + x`, for a number `k` and an `x` that isn't a number, is kept as one value (`Value::NatAdd`), meaning `Succ` applied `k` times to `x`. That's what `Nat.add`'s definition computes, one step per unit. Numbers compare by these `k + x` forms. `Nat.sub`, `Nat.leq` and `Nat.equal` take off the `Succ`s both arguments share in one step, as their definitions do one at a time. `k * x` for a literal `k` still unfolds `k` times, because its normal form really is that big.
- **Native implementations.** `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.leq`, `Nat.equal`, `Nat.divFuel`, `Nat.decEq`, `Nat.equalRefl` and `Nat.equalSound` run natively when all their number arguments are numbers (or `Succ`s around one). Otherwise they unfold as usual, so proofs by induction are unaffected. Each gives exactly what its definition computes, proofs included: `Nat.decEq` gives `Yes rfl`, or `No (Nat.equalFalse m n rfl)` (its definition asks `Nat.equal`, and the prelude's `Nat.equalFalse` turns `Nat.equal m n = False` into `Not (m = n)`); `Nat.equalRefl n`, and `Nat.equalSound m m h`, give `rfl` ([native numbers](proposals/native-numbers.md#as-built-what-a-native-must-compute)).
- **Arithmetic lemmas.** The prelude proves, in `Std.Nat`, by induction and `Eq.cong`/`Eq.trans`: `addZero`, `addSucc`, `addComm`, `addAssoc`, `addCancelLeft`; `mulZero`, `mulOne`, `mulSucc`, `mulComm`, `mulAssoc`, `mulDistribLeft`, `mulDistribRight`; `leRefl`, `leTrans`, `leAntisym`, `zeroLe`, `leSucc`, `leAddRight`, `leAddLeft`, `lessIrrefl`, `lessTrans`, `lessLe`; `subSelf`, `addSub`, `subLe`; and `divMod` (`n = (n / d) * d + n % d`) and `modLess` (`n % d < d`), each taking a proof that `d != 0`. Division with remainder is unique (`divUnique`, `modUnique`: `n = q * d + r` with `r < d` gives `n / d = q` and `n % d = r`), with `modSmall`, `divSmall`, `addDivSelf`, `addModSelf`, `modSelf` and `divOne`, which take an `auto` proof. Their helpers (`divMulLe`, `divFuelLe`, `divFuelBound`, `subLtAdd`, and others) are in the prelude too. `n % d` is defined as `n - (n / d) * d`, with the quotient on the left: multiplication recurses on its left argument, so with a literal divisor and an unknown quotient it stays put, where `d * (n / d)` would unfold into `d` additions while checking. `LessEq` and `LessThan` are the `Bool` `Nat.leq` made into propositions, so a `Nat.leq m n = True` proof is already an `m <= n` proof.
- **Trust.** The native implementations are trusted (DESIGN.md §13). They're registered by name only while the prelude loads, and registration checks each definition's type and arity, and that `Nat`, `Bool` and `Decidable` have the expected shapes (`E-BUILTIN`). `crates/driver/tests/natives.rs` compares the whole result of each (not just its constructor) with its own definition on every small input and on random larger ones, and with one step of its definition on numbers above 2^64.

**`Int`** is a data type, not a new kernel value: `type Int = OfNat (n: Nat) | NegSucc (n: Nat)`, where `OfNat n` is `n` and `NegSucc n` is `-(n + 1)`. Its operations are ordinary prelude definitions over those constructors: `Nat.toInt`; `Int.neg`, `add`, `sub` and `mul`; `Int.div`/`mod` (Euclidean), `tdiv`/`tmod` (truncating), `fdiv`/`fmod` (flooring) and `modNat`; `decEq`, `leq`, `less`, `compare`, `LessThan` and `LessEq`; and `natAbs`, `abs`, `toNat`, `toNatChecked`, `sign`, `toText` and `Text.toInt`. The kernel evaluates them by unfolding, through the `Nat` natives, so a closed `Int` normalizes to a constructor around a `Nat` number. **There are no kernel natives for `Int`** (decision K1): the trusted kernel arithmetic is still only `Nat`'s. The division laws (`Int.divAddMod`, `Int.modNonneg`, `Int.modLtAbs`) are ordinary theorems. See [integers.md](proposals/integers.md).

Extracted JS uses native `bigint` arithmetic for these `Nat` definitions, and has separate natives for `Int` (DESIGN.md §12).

## Text

`Text` means `MkText (chars: List Char)`, and a `Char` is `MkChar code valid`. But a text literal's characters are stored as one range of an array (`Term::Chars`, `Value::Chars`; `crates/core/src/chars.rs`), following option B1 of [the proposal](proposals/compact-text.md#as-built-stage-2), whose meaning is its expansion, `Cons (MkChar c rfl) … Nil`:

- `"ab"` elaborates to `MkText` of a range, which has type `List Char`. `""` is `MkText Nil`; `['a', 'b']` and `'a'` are still constructors.
- Matching on a range takes the `Nil` branch if it's empty, and otherwise the `Cons` branch with fields `MkChar c rfl` and the rest of the range, without building the list. Evaluation never makes a list compact: `Cons` builds cons cells, so `"ab" ++ t` is two cons cells in front of `t`.
- Conversion compares two ranges by their characters, and a range against anything else by expanding it one cell. So `"a"` and `Cons (MkChar 97 h) Nil` are equal only if `h` and `rfl` are, which for a proof variable `h` they aren't. Unification does the same, but solves a metavariable against a range with the range.
- Quotation gives back a range (copied into its own array if it's less than half of the one it shares, so a short suffix doesn't keep a long literal alive), and hashing covers the characters and `List`'s and `Char`'s hashes, not the array.
- A range is never structurally smaller than anything: descent only comes from matching, where its rest is a `Cons` field.
- **Trust.** These rules are trusted (DESIGN.md §13). The representation is registered while the prelude loads, only if `List` and `Char` (and through `Char`, `Char.isScalar`) have the content hashes it was written for, since the expansion's `rfl: Char.isScalar c = True` relies on `Char.isScalar`'s definition and on each `c` being a Rust `char`. Otherwise literals are constructors, the kernel refuses a range (`E-MALFORMED`), and a test fails until the hashes are updated. `crates/driver/tests/compact_text.rs` compares complete results with the constructor form.

## Float

`Float` (`std/Float/Float.sw`, docs/proposals/float.md) is a library record, `{ bits: Nat, valid: Float.isValid bits = True }`: a double's 64 bits, with every NaN as the one NaN `0x7FF8000000000000`. Its values in the evaluator are that record with a number for `bits` and `rfl` for `valid`: no new kind of term or value. The kernel (`crates/core/src/float.rs`) adds:

- **Primitives.** `Float.add` and `Float.sub` are definitions without bodies, admitted only from the library and only with type `Float -> Float -> Float`, as `Delay`'s constants are. Applied to two records whose bits are known (after evaluation, not as written) and valid, the evaluator computes the IEEE result with Rust's `f64` (round to nearest, ties to even), makes a NaN canonical, and returns `{ bits = k, valid = rfl }`; otherwise the application is stuck, and conversion compares it structurally. This rule is always on: switching the natives off doesn't change it. A primitive's hash is its name, `FLOAT_CONTRACT` (the version of the rules' meaning) and its type, so `add` and `sub` hash differently and a change of meaning changes every dependent hash.
- **Natives.** `Float.neg`, `Float.abs`, `Float.isNaN` and `Float.decEq` are ordinary definitions with natives, which fire only on known, valid bits and give exactly what the definitions compute, proofs included: a record built by `Float.make`, whose witness `Bool.canonicalTrue (Float.isValid n) p` is `rfl` on known bits whatever `p` is; for `decEq`, `Yes (Float.bitsExt x y rfl)` or `No (Float.bitsNe x y (Nat.equalFalse m n rfl))`. They are off with the natives.
- **Trust.** Both are trusted (DESIGN.md §13). The reducer's result is well typed only if `Float.isValid` is the library's, so `Float` and each definition with a native are bound by content hash (`FLOAT_DATA_HASH`, `NATIVE_HASHES`): a library that doesn't match is refused with `E-BUILTIN`. The gate (`crates/driver/src/float_gate.rs`) compares whole normal forms with the natives on and with the float natives off, on the native and WebAssembly kernels; with every native off, `Float` can't be evaluated at all, since its bit patterns are 64-bit numbers that the `Nat` definitions would count down one at a time.

## Elaboration

The elaborator (`crates/elab`) checks surface syntax bidirectionally, following András Kovács' elaboration-zoo, and produces core terms for the kernel.

- **Metavariables.** An unknown, such as an implicit argument or a `_` hole, becomes a metavariable applied to the variables in scope (except variables a case branch has replaced by a constructor). Its solution is a closed function of those variables.
- **Inserting implicit arguments.** When a function's type starts with implicit parameters, the elaborator applies it to fresh metavariables, unless an argument names one with `f [x := e]`. When checking against an implicit function type, it inserts an implicit lambda.
- **Pattern unification.** `?m x₁ … xₙ = t` is solved when the `xᵢ` are distinct variables. The solution is `x₁ … xₙ => t`. There's an occurs check, so `?m` can't appear in `t`, and a scope check, so `t` may only mention the `xᵢ`. **Pruning:** if `t` contains another metavariable applied to variables outside the `xᵢ`, that metavariable is narrowed so it can't depend on them. **Fallback:** when the spine isn't a pattern (`?m … (f o) = g … (f o)`), the last arguments are unified and then the rest (`?m … = g …`). This finds *a* solution rather than the most general one, which is safe because the kernel re-checks everything.
- **Constructors.** A constructor's data parameters come from the expected type, or from fresh metavariables. An inferred constructor of a parameterised type is wrapped in a type annotation, so the kernel can infer it too.
- **Constructors of indexed families** (`crates/elab/src/families.rs`). A constructor's written result type must be the type applied to its own parameters (by unification, so exactly them), then indices, which become its result indices. Implicit fields are filled in by fresh metavariables, or by `[n := e]`; the result type is the type applied to the parameters and the result indices, with the fields substituted. Automatic implicit fields are bound first, each with a metavariable as its type, in the order of first use; if the constructor doesn't check that way, every other order is tried (up to four fields), and if one put after the written fields checks with a type mentioning one of them, that's `E-IMPLICIT-FIELD`.
- **Matching on an indexed family** (`families::check_case`). The pattern compiler splits as for any type, but a constructor no equation matches isn't an error yet. Checking the tree, each branch unifies the constructor's result indices with the scrutinee's using the kernel's own unifier (`unify_index::unify`, after substituting solved metavariables), then refines the context as the kernel will. A conflict makes the branch impossible: its equations are dropped unchecked, and one never reached elsewhere is `W-UNREACHABLE`. A stuck problem is `E-INDEX-STUCK`, with a hint for `n + 1`. A constructor with no equation that is possible is accepted only if one of the columns still to match has a type every one of whose constructors conflicts (one level deep): the branch is then a case on it with every branch impossible; otherwise `E-NONEXHAUSTIVE`. `()` on an indexed family builds that case too, or is `E-INDEX-STUCK` if a constructor is stuck. Implicit fields are wildcards in patterns unless named, `[n := p]`.
- **Zonking.** After a declaration is elaborated, solved metavariables are substituted in. Any left unsolved is an error (`E-UNSOLVED`) at the place it was created.
- **Auto arguments.** Inserting an `[auto x: P]` argument creates a metavariable and records an obligation. Once the declaration is elaborated, each obligation is proved (`crates/elab/src/auto.rs`):
  1. a hypothesis in scope whose type unifies with `P`;
  2. otherwise a **decision procedure**: a definition whose result type is `Decidable …`, trying the most recently defined first, so a file's own procedures take priority over the prelude's. Its arguments are found by unifying `Decidable …` with `Decidable P`. Arguments it still needs that are `Decidable` (like `Decidable.not`'s) are found recursively, up to depth 8, and auto arguments by proof search. It's evaluated at compile time:
     - `Yes` → the proof is `Decidable.fromYes d Trivial`. The kernel accepts this only if `Decidable.IsYes d` computes to `Unit`, so it re-checks the decision itself;
     - `No` → `E-AUTO-FALSE`;
     - stuck on unknown values → `E-AUTO-STUCK`, with a hint to use `if h: P then … else …`;
     - no procedure fits → `E-AUTO-NONE`.

  Failed attempts are undone, by restoring the metavariables from a snapshot.
- **`if`.** `if c then a else b` elaborates to `Bool.ifThenElse c (_ => a) (_ => b)`. `if h: P then a else b` finds a decision procedure for `P` (it must exist, but may be stuck: it runs at runtime) and elaborates to `Decidable.elim d (h => a) (h => b)`, with `h: P` in `a` and `h: Not P` in `b`.
- **Operators.** `a != b` is `Not (a = b)`. `a == b` is `Decidable.toBool d`, where `d` is a decision procedure for `a = b`, found as for `if h:`. `<`, `<=`, `+`, `-`, `*`, `/`, `%` are the prelude's `Nat.LessThan`, `Nat.LessEq`, `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`. `Nat.div` and `Nat.mod` take `[auto ok: d != 0]`.
- **Implicitly bound type variables.** An unknown lowercase name in a signature becomes an implicit parameter at the front if *every* use of it is where a type is expected: the domain or result of a function type, a binder's type, or an argument of a data type whose parameter is a type (`List a`, `Or p q`). A name used anywhere in an index of an indexed family (`Vec a (Succ n)`) is bound whatever its other uses, unless it's a name the module declares. Its own type is a metavariable, usually solved to `Type`, which is also the default. Any other use (`List.length xs` with `xs` unbound) stays an unknown name.
- **Equations.** Parameters are bound from the signature. Implicit ones are in scope by their signature names. Explicit ones are matched by the equation's patterns, so `length (Cons x xs)` has one pattern while `length` has two parameters. Equations compile to a case tree by the usual matrix method: split on the first constructor pattern in the first remaining equation, and in each branch replace that column by the constructor's fields (rows with a variable there get wildcards). The first equation whose patterns are all variables wins. A column with a number pattern in the first remaining equation compiles to a `NumCase`, unless some equation has `Zero` or `Succ` in that column: then it's split into `Zero` and `Succ` like any constructor column, and a number pattern `n` is `Succ` of the pattern `n - 1`. In a `NumCase`, the arm for each number keeps, in order, the equations with that number in the column and those with a variable or `_`; the default keeps only the latter, and there must be at least one (`E-NONEXHAUSTIVE`). In a column of the prelude's `Int` with a number pattern, `k` is the pattern `OfNat k` and `-k` is `NegSucc (k - 1)` (`-0` is `OfNat 0`), so the column splits into those two constructors, and each field column is a `Nat` column as above.

What the elaborator *doesn't* check is left to the kernel: `Prop` elimination, positivity, universe constraints on fields, and termination. Those errors come from the kernel, with source locations kept from the elaborated term.

## Abilities

Abilities are translated into ordinary data before the kernel sees them, so the kernel's existing checks (positivity and termination) are what show that handlers terminate. The design, and why, is in [docs/proposals/abilities.md](proposals/abilities.md). The translation is in `crates/elab/src/effects.rs`.

- **`ability A params where op: X -> {A params} Y …`** generates:
  - a data type `A params`, with a constructor `A.op (x: X)` for each operation;
  - `A.res: params -> A params -> Type`, giving each operation's result type;
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
  - An operation call becomes `Effect.Comp.Call (inject op) (r => Effect.Comp.Done r)`, injected into the row with `Effect.Plus.L`/`Effect.Plus.R`.
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
- **Different orders, fewer abilities.** An effectful function passed where a row lists its abilities in a different order, or lists more of them, is wrapped as `x => translate m (f x)`. Plain unification can't reorder or widen a `Plus` chain.
- **Unknown tails.** When a call needs abilities the context's row doesn't list, and the row ends in an unknown, the unknown is solved with them plus a fresh unknown, so later calls can add more. Two open rows `{A | ?f}` and `{B | ?t}` meet with a fresh `?r`: `?f := B∖A | ?r` and `?t := A∖B | ?r`.
- **Operations as values.** `op` on its own is `x => op x`, of type `(x: A) -> {Ability args} B`.
- **Timings.** Set `STITCHWORT_TIMINGS=1` and the CLI prints a table to stderr when it finishes. For the core prelude, each standard library file and each project namespace, in load order, it shows the elaboration time, the time inside the kernel's declare and define calls, the number of core term nodes (types and bodies, not counting source locations) and the number of declarations. A library file loads in the middle of the namespace that needs it, and its time and terms count against the file. The last line gives the wall time and what falls outside the units (parsing, printing, and for `run` the program itself). A second table lists declarations, slowest first, by full name (a group of mutually recursive declarations is one row): elaboration time, kernel time, evaluation steps and core term nodes, exclusive of any library file loaded while checking it. It shows the 20 slowest; `STITCHWORT_TIMINGS=decls` shows all of them ([proof-check-speed.md](proposals/proof-check-speed.md)). Unset, it costs one cached flag read per call. See [check-cache.md](proposals/check-cache.md#a5-as-measured-stage-0).
- **Long terms in messages** are cut off: a term longer than about 240 characters is shown with its inner parts as `…` (the outer layers stay), so one stuck computation can't fill the screen. Set the environment variable `STITCHWORT_FULL_TERMS=1` to see messages' terms in full. The REPL and `run` results are never cut off. A failed `rfl` shows the two sides as the declaration's type wrote them (`Range.repeated r k n` and `0`) and, in a note, what each side computes to. The written form is available when the `rfl` is the whole body of a `def` or `theorem` (after its parameters) whose type is the `=`; elsewhere (an `rfl` nested in a larger proof, an arm with patterns) the message shows the computed sides.
- **Messages** show computation types as rows (`{State Nat | e} a`) and the unit type as `()`.

The termination checker accepts recursion on `rest y` for a recursive function field `rest`, which is what makes folds over `Effect.Comp` structural ([Definitions](#definitions)).

## Partial computations

Stage 1 of docs/proposals/partial.md. The kernel's part is small and has no
computation rules (`crates/core/src/partial.rs`, trusted for consistency):

- `Effect.Delay: (op: Type) -> (res: op -> Type) -> Type -> Type`, and the
  constants `Effect.now`, `Effect.lift` (an `Effect.Comp` as an `Effect.Delay`), `Effect.bindD`, `Effect.mapSig` and
  `Effect.pfix: [op res A] [B: A -> Type] -> ((x: A) -> Effect.Delay (Effect.Plus (Effect.Rec A) op)
  (Effect.PlusRes (Effect.RecRes B) res) (B x)) -> (x: A) -> Effect.Delay op res (B x)`.
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
`main()`, performs operations, and counts ticks. Nothing it computes is
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
- **data types are nominal**, so their hash includes their name, their constructors' names, their fields' names, and whether they're records;
- **JS representation attributes are excluded from logical content hashes** (`@[js.tag …]`, `@[js.name …]`, docs/proposals/attributes.md, D598): they say how a type crosses to JavaScript, which the kernel never sees, so a logical hash doesn't identify a JS interface. They are kept beside the data type (`Data::js`), resolved by the elaborator, and cached with the unit that declares it;
- **indices**: a data type's index telescope and its constructors' result indices, and which branches of a `case` are impossible, are hashed. A type without indices, and a case without impossible branches, hash exactly as they did before indices existed.

Renaming a function or reformatting code changes no hashes. Changing a body changes its hash and the hash of everything that uses it.

**The test cache** stores each result under `.stitchwort/cache/tests/<compiler version>-<fingerprint>-<modes>-<test hash>`. A test runs again only when its hash changes. Failures are cached as well as passes. The fingerprint is a hash of the source of the syntax, core, elaborator (with the prelude) and driver crates, made when the compiler is built (`crates/driver/build.rs`), so a changed compiler doesn't reuse results even with the same version number; the modes say whether natives and compact text were on (`n1c1`), so a run with either switched off doesn't reuse results found with them on. The local cache is trusted. `--no-cache` ignores it.

**The check cache** (docs/proposals/check-cache.md, stage 1) keeps each standard library file's elaborated declarations and side tables under `.stitchwort/cache/check/`, keyed by the compiler build (the fingerprint also covers `Cargo.lock`), the modes and limits, and the file's text and dependencies. Loading an entry skips elaborating the file, not checking it: every declaration goes to the kernel again through `declare_*`/`define_*`, so a bad entry can't make anything false be accepted. `check`, `test`, `run`, `build` and `eval` use it; `--no-cache` turns it off. Tests and the benchmark never use it, except its own differential test.

## The prelude

`crates/elab/src/std/core/` (the always-loaded core: a folder of small files, checked as one module) and the library files under `crates/elab/src/std/` (checked when a program uses them; docs/proposals/std-library.md) define everything above that isn't built in: `Void`, `Unit`, `Not`, `Void.absurd`/`Void.exfalso`; `Nat` with `+ - *`, `Nat.pred`, `/`, `%`, `Nat.equal`; `Bool` with `not`, `Bool.ifThenElse`, `Nat.leq`, `Bool.decEq`; `<=` and `<` as propositions computed via `Nat.leq`; `List`, `List.length`, `List.append`, and a pure list toolkit (`map`, `filter`, `foldLeft`, `foldRight`, `sum`, `product`, `maximum`, `minimum`, `zip`, `zipWith`, `zipWith3`, `take`, `drop`, `get`, `any`, `all`, `count`, `find`, `filterMap`, `concat`, `concatMap`, `replicate`, `range`, `reverse`, `last`, `elem`, `partition`, `lookup`, usable as `xs.map f`) with `Nat.min`, `Nat.max`, `Nat.absDiff`, `Nat.pow` (examples/accept/list-toolkit.sw); `Eq.cong`, `Eq.sym`, `Eq.trans`; constructor disjointness and injectivity; and `Effect.Comp` (computations as trees of operations, docs/proposals/abilities.md) with `Effect.foldComp` and `Effect.bind`; the `IO` ability (`IO.print`, `IO.readLine`, `IO.readAll`) and `IO.simulate`, which runs a program against scripted input and records what it prints (docs/proposals/text-and-io.md); `Decidable` with `Decidable.IsYes`, `Decidable.fromYes`, `Decidable.toBool`, `Decidable.elim` and decision procedures for `=` on `Nat`, `<=`, `<`, `Not`, and `b = True`, and for `=` on `List`, `Pair` and `Option` given one for the elements (`List.decEq`, `Pair.decEq`, `Option.decEq`; `auto` fills that argument by searching under the binders, examples/accept/eqeq-containers.sw).

**Sorting** (examples/accept/sort.sw): `List.sort: List Nat -> List Nat`, `List.sortBy: (a -> a -> Ordering) -> List a -> List a` (with `Nat.compare`, `Text.compare`, ...) and `List.sortWith: (a -> a -> Bool) -> List a -> List a`, which takes a "may come before" test (`Nat.leq`); `sortBy` is `sortWith` with `Ordering.isLessEq (cmp x y)`, and `sort` is `sortWith Nat.leq`. It's a stable bottom-up merge sort whose runs are kept like a binary counter (slot `i` empty or a sorted run of 2^i elements), so every function is structurally recursive and it's O(n log n): 2,000 numbers sort in a few hundredths of a second under `stitchwort run`. Stability isn't proved. Correctness is `List.sortWithSorted`/`List.sortBySorted`/`List.sortSorted` and `List.sortWithPerm`/`List.sortByPerm`/`List.sortPerm` (and `List.sortLength`):
- `List.Sorted le xs` says each element may come before the next (`le x y = True`, as a conjunction `And`, the prelude's `type And (p q: Prop): Prop = Both ...`); for a transitive `le` that orders every pair. The sortedness proofs need only that `le` is total (`le x y = False -> le y x = True`; `Nat.leqTotal`, `Nat.compareTotal`), not transitivity, since adjacent pairs are all a merge compares.
- `List.Perm xs ys` is `(p: a -> Bool) -> List.occurrences p xs = List.occurrences p ys`: every test is passed by as many elements of each. Counting makes the proofs arithmetic on `+` (the count of a merge is the sum of the counts) instead of rearranging an inductive permutation with swap and transitivity steps, and it needs no equality on the elements; with decidable equality it's the usual meaning (test with `Nat.equal v`). `List.permRefl`, `permSym`, `permTrans`, `permLength` come with it.
- Proofs about `if le x y then ... else ...` case on the condition while remembering `b = True` or `b = False`. In programs that is `match h: Nat.leq x y with` (the AoC proofs, SW-26); the library's own lemmas still use `Bool.inspect b motive t f`, the same thing with the motive written by hand. A separate helper that matched on the `Bool` would lose the size-change evidence for the recursive call.

Division is defined by structural recursion on fuel (`n` steps is always enough when the divisor isn't zero). Its non-zero precondition is what makes `n / 0` a compile-time error rather than a convention.

## Erasure and JS extraction

What's erased:

- **Definitions:** a definition is erased (not emitted) if its type is a proposition or a type former.
- **Parameters:** a parameter is erased if its type is a proposition or a type former. Calls to definitions drop erased arguments. Lambdas keep all their parameters, and erased arguments passed to them become `undefined`.
- **Terms:** `Data`, `Sort`, `Pi`, `Eq` and `Refl` compile to `undefined`. `J P d p` compiles to `d`.
- **Case on a proof:** this is only possible for the subsingleton propositions above, so it compiles to its single branch.
- **Run bodies:** a definition with a run body (a `decreasing` one, [above](#recursion-on-a-measure-decreasing)) is emitted, and lowered for `stitchwort run`, from that instead of its body.
- **Impossible branches** (indexed families) have no body and generate no code. A case with no possible branch generates a `throw`, as does the fall-through after a switch; running such a case in the kernel with erasure panics with `unreachable`. Typing keeps well-typed programs from reaching either (`examples/extract/vec-inside.sw` runs `head` through the JS differential test).

Representations: `Nat` is `bigint` (`Zero` is `0n`, `Succ n` is `n + 1n`, a case on `Nat` tests `=== 0n`, and a `NumCase` is a `switch` whose arms each return, followed by the default). Other data types are `{ tag, …fields }`, omitting erased fields (an indexed family's computational fields are kept, forced implicit ones like `n` in `VCons` included, and its proof fields are erased: `Certified n` with `ok: IsPrime n` stores only the number); a record is `{ …fields }`, with no tag (docs/proposals/records.md §11). Inside generated code the tag is always the property `tag` and a field's key its own name; at the JS boundary the codec translates to the type's JS representation (`$tag`, or what `js.tag` and `js.name` say, DESIGN.md §12).

The exportability check, the boundary encodings and the decode → compute → encode contract are as described in DESIGN.md §12, restricted to `Nat`, `Bool`, `List` and parameterless data types built from them. An indexed family can't cross the boundary (`E-EXPORT`): not as an input or result, nor through a type synonym, inside a container (`List (Vec Nat 3)`), or in a record field (`Grid { height, width, rows: Vec (Vec Bool width) height }`), since decoding would have to check the indices. A function may use one internally (examples/reject/export-indexed-*.sw; the accepted counterpart is examples/extract/vec-inside.sw).

**Preconditions.** An export's proof parameters (like `[auto ok: percent <= 100]`) aren't passed by JS. For each one, the elaborator finds a decision procedure in the context of the earlier parameters. The kernel checks it has type `Decidable P` (`add_validator`), and that the data type used really is shaped like `Decidable`, with its first constructor carrying a proof of `P`. The generated wrapper decodes the inputs, runs each decision procedure on them, and throws `StitchwortInputError` unless it says `Yes`. A proof parameter with no decision procedure makes the export `E-EXPORT`.

Only definitions reachable from the exports (and their checks) are emitted, in the kernel's order, which is dependency order (a definition refers only to earlier ones and to members of its own group). Each definition has one calling convention, decided once and used at its declaration, every reference, application and first-class use, and in its export wrapper: a *function* if it has runtime parameters; otherwise a *thunk* (a function of no arguments, called as `f()`) if its body is a case tree (such as `absurd`, whose only parameter is an erased proof, so it only runs if it's reached) or it's a member of a group of two or more (so it never calls a sibling while the module loads, before the sibling is defined); otherwise a *value*, computed when the module loads. Only a function's tail calls to itself become loops: definitions in a group that tail-call each other use a stack frame per call, and running out is a `StitchwortResourceError`.

## Error codes

| Code | Meaning |
|---|---|
| `E-PARSE` | Syntax error |
| `E-UNKNOWN-NAME` | Name not in scope |
| `E-UNKNOWN-FIELD` / `E-RECORD-FIELD` / `E-NOT-A-RECORD` / `E-RECORD-UPDATE` | A record, or a constructor in a named-field pattern `C { … }`, has no such (explicit) field; a literal or pattern leaves a field out or gives one twice; a record operation on something that isn't a record; an update that replaces a field without the later fields whose types mention it, or that would change a type parameter a kept field mentions |
| `E-DUPLICATE` | Name defined twice, or a built-in name redefined |
| `E-MISSING-DEFINITION` | A `def` header with no body (only the prelude's primitives may) |
| `E-ARITY` | Wrong number of patterns or arguments |
| `E-NOT-A-CONSTRUCTOR` | A pattern that isn't a constructor |
| `E-TYPE-MISMATCH` | Types don't match |
| `E-UNIVERSE` | Universe mismatch, or a field or an index too large for its data type |
| `E-CANNOT-INFER` | Needs a type annotation |
| `E-NOT-A-TYPE` / `E-NOT-A-FUNCTION` / `E-NOT-A-SORT` | Wrong kind of thing |
| `E-NOT-A-PROP` | A `theorem` whose type isn't a proposition |
| `E-REFL` | `rfl` used for sides that don't compute to the same value |
| `E-NONEXHAUSTIVE` | Missing pattern-match case |
| `E-MATCH-MOTIVE` | A `match` whose scrutinees can't be generalised in this version (the same variable twice, one scrutinee part of another, one's type mentioning another) or whose generalised type is ill-formed |
| `E-MATCH-EQUATION` | The equation of `match h: e with` can't be formed (the types differ); not reported in the first version |
| `E-TERMINATION` | Recursion that can't be shown to terminate, or a recursive call not given all its arguments |
| `E-SYNONYM-CYCLE` | Type synonyms defined in terms of each other, so none of them has a meaning |
| `E-POSITIVITY` | Data type used in a negative position, inside another type, with other parameters, or in an index (for any member of its data group) |
| `E-MUTUAL-SIGNATURE` / `E-MUTUAL-CONSTRUCTOR` / `E-MUTUAL-PARAMETERS` / `E-MUTUAL-KIND` | A type or header mentioning something it's checked together with; a field using a constructor of its own group; data types defined together with different parameters or universes; a cycle mixing data types and definitions, or with an ability |
| `E-PROP-ELIM` | Matching on a proof to produce data, where that's not allowed |
| `E-EXPORT` | Export can't cross the JS boundary |
| `E-DECREASING` | A definition with `decreasing` whose recursion can't be compiled: a call `auto` can't prove smaller, a call under a lambda, a measure with no header parameter, a mutual group, or (an internal error) a generated definition the kernel refused |
| `E-UNSOLVED` | An implicit argument the elaborator couldn't work out |
| `E-AUTO-FALSE` / `E-AUTO-STUCK` / `E-AUTO-NONE` | An auto argument is false, can't be decided at compile time, or has no decision procedure |
| `E-NOT-EMPTY` | An absurd pattern `()` for a type that has values |
| `E-INDEX-STUCK` | A `case` on an indexed type where unifying a constructor's indices with the scrutinee's gets stuck: neither solved nor a conflict ([unifying indices](#unifying-indices)) |
| `E-IMPLICIT-FIELD` | An automatic implicit field of a constructor whose type would mention a written field: write it out, after that field |
| `E-RECORD-INDICES` | A record declared with indices |
| `W-UNREACHABLE` | A warning: an equation whose constructor can never match the indices there; it's dropped unchecked |
| `W-RECORD-ARGUMENT` | A warning: `C { f = … }` on a one-field constructor whose field holds a record that has a field `f` too names `C`'s own field; `C ({ … })` matches the record's |
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
