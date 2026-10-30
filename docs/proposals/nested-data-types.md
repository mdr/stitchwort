# Proposal: nested data types, `Packets (items: List Packet)`

**Status:** draft 2, 29 October 2026. Ticket SW-704 (D1820: rethink after the external review of
draft 1, SW-829). Draft 1 (28 October) proposed Rocq's old nested positivity rule; this draft
replaces it with the 2026 Lamiaux–Forster–Sozeau–Tabareau criterion, specialised to Stitchwort.
What changed and why is in [§11](#11-response-to-review). The decisions for Matt are in
[§13](#13-decisions). D1821 adopted the rule; **stages 1-3 are built**
([As built](#as-built-stage-1), [stage 2](#as-built-stage-2): derived `==`, `<`, `${…}`, D1840;
[stage 3](#as-built-stage-3): generated `T.size`, `T.induct`, `T.inductMem`, `D.All`, D1870,
which adopted D1823). Stage 4 (dogfood) is not done. Related: [mutual-recursion.md](mutual-recursion.md) (data groups,
size-change termination), [well-founded-recursion.md](well-founded-recursion.md) (`decreasing`,
`List.attach`), [parser-combinators.md](parser-combinators.md) §5.3, [map-equality.md](map-equality.md)
(why nesting through a quotient is refused), [indexed-families.md](indexed-families.md).

**The short answer.** Let a data type contain itself inside an earlier data type, such as `List`,
`Option`, a pair, `Vec` or an earlier mutual group, at a parameter that the earlier type only
*stores*. The kernel works out once, per data group, which of its parameters are like that
(*nestable*), with the rule from Lamiaux, Forster, Sozeau and Tabareau's paper (PLDI 2026,
"LFST" below). Then a field like `items: List Packet` is checked by looking up `List`'s table, not
by expanding `List`'s constructors. LFST have a machine-checked proof that every type their rule
accepts has a strictly positive *mutual* encoding (`Packet` with a private copy of `List`). Our
rule is their rule with a few extra restrictions (§5.5), so the proof covers us, under the
assumptions written out in §6. Termination needs no change: "is a part of" already means "is a
constructor field, at any depth, of this particular value" (§6.4). Two small additions: a field
may not depend on an earlier field that contains the type (LFST's "no inductive-inductive"
rule), and a proposition with a nested field can't be matched to produce data (as in Lean). A
scratch prototype (~200 lines, behind an environment variable, not merged) accepts every
example we want and refuses every one we don't (§7), and changes no verdict on the 1,075 files
in `examples/accept`, `reject` and `soundness` except `reject/nested-data.sw` **[run]**.

This note can be read without knowing type theory. Labels:

- **[checked]**: read in the Stitchwort source at commit `9a6a3d84`, or in a source listed at
  the end, at the place given;
- **[cited]**: what a source says, quoted, and not checked further by us;
- **[run]**: a program run on 29 October 2026 (Stitchwort at `9a6a3d84`, with the scratch
  prototype where stated; Lean 4.34.1 and Rocq 9.1.1 from nixpkgs). Programs are scratch files;
  each is quoted or described where used;
- **[inferred]**: our reasoning from checked or cited facts;
- **[unverified]**: believed, not confirmed.

## Contents

- [1. The problem](#1-the-problem)
- [2. Words this note uses](#2-words-this-note-uses)
- [3. How Stitchwort checks data types today](#3-how-stitchwort-checks-data-types-today)
- [4. How others do it](#4-how-others-do-it)
- [5. The rule for Stitchwort](#5-the-rule-for-stitchwort)
- [6. Why it is sound](#6-why-it-is-sound)
- [7. What we ran](#7-what-we-ran)
- [8. The translation test oracle](#8-the-translation-test-oracle)
- [9. Induction principles](#9-induction-principles)
- [10. Stages](#10-stages)
- [11. Response to review](#11-response-to-review)
- [12. Options considered](#12-options-considered)
- [13. Decisions](#13-decisions)
- [As built (stage 1)](#as-built-stage-1)
- [As built (stage 2)](#as-built-stage-2)
- [As built (stage 3)](#as-built-stage-3)
- [Sources](#sources)

## 1. The problem

Advent of Code 2022 day 13 gives lines like `[[1],[2,3,4]]`: a packet is a number or a list of
packets. The natural type is refused today **[run]**:

```
type Packet: Type =
  | Number (value: Nat)
  | Packets (items: List Packet)
```

```
[E-POSITIVITY] Error: `Packet` is used inside another type
   field `items` has `Packet` inside another type
```

The workaround is a `Tree` and a `Forest` defined together (`examples/accept/mutual-data.sw`). It
works, but the forest is a second list type: none of `List`'s functions or theorems apply to it.
The same shape comes up in 2021 day 18 (snailfish numbers), 2022 day 7 (file trees), expression
trees, JSON-like values, and whatever a recursive `{Parse}` grammar builds (parser-combinators.md
§5.3). It also comes up in proofs: a typing judgement for a language with `switch` wants "every
branch is well typed", `All (t => Typed t r) branches`, which is LFST's own motivating example.

What users want, in order of how often: the type itself, with a real `List` inside; functions
using the library (`items.map`, `sum`, `zip`); proofs by induction where the step for `Packets
items` may assume the property for every packet in `items`; and derived `==`, `<` and `${p}`.

## 2. Words this note uses

- **Nested occurrence.** The type being defined appears as an argument of another type in a
  field: `List Packet`. `Packet` is *nested* in `List`; `List` is the *outer type*.
- **Strictly positive.** The type never appears to the left of an arrow in a field.
  `Bad (f: Bad → Nat)` is not strictly positive, and would let a program loop and prove anything.
- **Uniform parameter.** A parameter every recursive use of the type passes on unchanged:
  `List a` uses `List a` inside, never `List (a, a)`. In Stitchwort *every* parameter is uniform:
  in its own fields a group's member may only be applied to the group's own parameters
  (`not_positive`, `check.rs:2733-2739`, `Occurrence::OtherParameters`) **[checked]**. Anything
  that varies is an index.
- **Nestable parameter.** LFST's "strictly positive uniform parameter": a parameter of type
  `Type` (or a function returning a type, `a → Prop`) that the type only stores, never takes as
  input and never uses in an index. `List`'s `a` is nestable; `Neg (a) = MkNeg (consume: a →
  Nat)` has a non-nestable `a`. Rocq's manual: "The inductive type `prod` has two
  uniform-parameters `A, B : Type` that are strictly positive, and hence nestable" [R2] **[cited]**.
- **Mutual encoding.** The same type written without nesting: `Packet` and a private copy of
  `List` specialised to packets, defined together. LFST's whole justification is that this exists.
- **Size-change termination (SCT).** Stitchwort's termination check: every recursive call is
  summarised by which arguments got smaller, and every way of repeating calls must make something
  smaller (mutual-recursion.md §3).
- **Recursor.** The built-in induction principle Lean and Rocq give each type. Stitchwort has
  none: functions and proofs are case trees plus the termination check (`docs/core.md`).

## 3. How Stitchwort checks data types today

Everything here was read at `9a6a3d84` **[checked]** unless marked.

**Positivity.** Each field type of each constructor of a data group is checked
(`check_type`, `check.rs:2205`), then passed to `not_positive` (`check.rs:2218`, defined at
`:2722`). It allows a member only applied to the group's own parameters and then to indices that
mention no member, possibly as the result of a function field whose inputs mention no member.
Anything else is an `Occurrence` (`:2705`): `Input`, `OtherParameters`, `InIndex`, or `Inside`,
which is where `List Packet` falls. Note that positivity runs on the *checked* field type, in
which every `Eq` carries its type: `Eq(None, a, b)` comes back as `Eq(Some(A), a, b)`
(`check.rs:355-376`). This matters in §5.3.

**Other guards** that stay:

- **Declared later** (`declared_later`, `check.rs:2631`, used at `:2190`): a field may only
  mention declarations made before its group. So the outer type is always final and fully known.
- **No constructors or `case` of the group in fields** (`admissible`, `check.rs:2534`, message at
  `:2596`): nothing that inspects a member exists while its fields are checked.
- **`case` only at the top of a definition** (`case_only_in_tree`), so a field's type can't
  compute by matching.
- **Field sizes**: a field's type must fit in the type's universe (`E-UNIVERSE`), and there is no
  cumulativity (`docs/core.md`, Universes).
- **`Prop` elimination** (`check.rs:915-922`): matching on a proof may produce data only if the
  proposition is alone in its group, has at most one constructor, and every field is a proof.
  The same rule is in `value.rs:1615` and `erase.rs:39`.

**Termination** (`termination.rs`, header at lines 1-55). "An argument's relation comes only from
the terms, never from types" (`:19`). A variable bound as a field of a constructor matched out of
a parameter, directly or through further matches, is smaller than it, whatever its type. A
*recursive function field* (a field whose declared type is a function returning a member of the
matched type's own group, `is_recursive_fn`, `:326`) applied to arguments is smaller too. Calls
under lambdas see lambda-bound variables as unknown, so `items.map (q => f q)` is refused and needs
`decreasing` with `List.attach` (well-founded-recursion.md).

**Quotients and primitives.** `Map` and `Set` are records over `Quot`
(`std/Map/Map.sw:22`). A quotient is `Term::Quot`, not a data type. `Effect.Delay` is a `def` with
no body (`std/core/Effect.sw:233`), not a data type either.

## 4. How others do it

### 4.1 Lean 4: translate to a mutual group in the kernel

Lean's kernel finds each nested occurrence `I Ds is` and copies *every* type of `I`'s mutual
declaration into the group as an auxiliary type ("We should copy all inductive datatypes `J` in
the mutual declaration containing `I` to the `m_new_types` mutual declaration as new auxiliary
types", `src/kernel/inductive.cpp`, `replace_if_nested`, around line 1080, master at `400f83a`)
[L4] **[cited]**. It then checks the whole thing as an ordinary mutual group, and builds the
recursor from the translated one. Requirements from the manual [L1] **[cited]**: occurrences
"must be nested directly under an inductive type's type constructor"; "Local variables such as
the constructor's parameters may not occur in the arguments to the nested occurrence"; "The
nested occurrences must occur strictly positively"; "Constructor parameters whose types include
nested occurrences may not be used in ways that rely on the specific choice of outer type
constructor"; and "Nested occurrences may not be used as parameters to the outer type
constructor that occur in the types of the outer type's indices." The local-variable rule is
`is_nested_inductive_app`: "nested inductive datatypes parameters cannot contain local
variables" (`inductive.cpp:1041`) **[checked]**.

Two consequences we ran **[run]**, Lean 4.34.1:

- `inductive ITree : Nat → Type | node (n : Nat) (children : List (ITree n)) : ITree (n+1)` is
  refused: "(kernel) invalid nested inductive datatype 'List', nested inductive datatypes
  parameters cannot contain local variables". So is LFST's `Typed` judgement with
  `All (fun t => Typed t r) bs`, and LFST's `Fnat` (nested through `Eq`, see §4.2).
- A proposition nested in `And` only eliminates into `Prop`: for
  `inductive P : Prop | mk (h : And P True)`, `#check @P.rec` shows `motive_1 : P → Prop` and a
  second motive for the auxiliary `And`. Lean's rule: "Mutually recursive inductive predicates
  only eliminate into Prop" (`inductive.cpp:517-519`), and the auxiliary types make the group
  mutual **[checked]**.

Lean accepts nesting through an earlier *mutual* group (`MTree`/`MForest`) **[run]**, and the
manual's `BRTree`, whose later field says `children.length < branches`, is refused because the
translated `children` has the auxiliary type [L1] **[cited]**.

### 4.2 Rocq before 9.2: substitute and re-check

The kernel rule, still the one in the Rocq 9.3 manual [R1] **[cited]**: a type is strictly
positive in `T` if, among other cases, "`T` converts to `(I a_1 … a_r t_1 … t_s)` where `I` is the
name of an inductive definition … (in particular, it is not mutually defined and it has `r`
parameters) and no `X_1 … X_k` occur in any of the `t_i` nor in any of the `a_j` for `m < j ≤ r`
where `m ≤ r` is the number of recursively uniform parameters, and the (instantiated) types of
constructor `C_i{p_j/a_j}_{j=1…m}` of `I` satisfy the nested positivity condition". Draft 1
proposed this rule.

LFST show two problems with it (§2.2 of [P1]) **[cited]**, and we reproduced both with Rocq 9.1.1
**[run]**:

- **Nestability decided by computation.** `Inductive depends_on_b (b : bool) (A : Type) := cst :
  (if b then A else (A -> bool)) -> depends_on_b b A.` Nesting in `depends_on_b true` is
  accepted, in `depends_on_b false` refused. The answer depends on reducing the outer type's
  constructors with the arguments in.
- **Inductive-inductive types slip through.** `Inductive Fnat : Type := Fnat_zero : Fnat |
  Fnat_succ : forall (n m : Fnat), n = m -> Fnat.` is accepted. Its mutual encoding would need a
  copy of `eq` *indexed by* `Fnat`, which is inductive-inductive. "The recursive dependency via
  eq introduces an inductive-inductive structure, but Rocq accepts it because the strict
  positivity checker does not reject such cases" [P1].

Also, nesting through a mutual group (`MTree`/`MForest`) is refused by Rocq 9.1.1 **[run]**, as
the rule says ("not mutually defined").

### 4.3 LFST 2026: nestable parameters

Thomas Lamiaux, Yannick Forster, Matthieu Sozeau, Nicolas Tabareau, "Nested Inductive Types:
Justified and Usable Nested Inductive Types in Lean and Rocq", PACMPL 10 (PLDI 2026), 1891–1914,
doi 10.1145/3808322 [P1]. We read the November 2025 preprint (HAL hal-05366368v1, via the Internet
Archive) in full; the published version was not reachable (ACM returned 403, HAL refused
connections), so differences between the two are **[unverified]**. We read the formalisation
[R4] (`MetaRocq/nested-eliminators`, commit `f9ca941`, 24 April 2026): the positivity condition
in full, the translation's top level and the theorem statement.

The abstract: "This paper introduces a novel validity criterion for nested inductive types that
guarantees that they can be elaborated into well-formed mutual inductive types. … Our condition
strictly generalizes Lean's current check while ruling out exactly the problematic cases
accepted in Rocq." **[cited]**

**The idea** (§3 of [P1]) **[cited]**: "The core idea is to only allow nesting on the parameters
that are arities—of the form ∀ X0 … Xn, Type—and that occur in strictly positive position, with
arguments that are themselves strictly positive. We call these parameters strictly positive
parameters." Each inductive type comes with a function `check_nestable` saying which parameters
those are; "The role of the strict positivity condition is to guarantee the correctness of this
function". Nesting is then checked *compositionally*: an occurrence `D args` looks up `D`'s
table instead of expanding `D`.

**The condition** (§3.2 of [P1], formalised as `positive_argument`, `Positivity_condition.v:911-976`)
**[cited, and checked against the Coq source]**. An argument (constructor field) is one of four
shapes, each `∀ largs, …`:

1. "a constant `arg_is_cst t` then `t` must not refer to the inductive blocks or strictly
   positive parameters";
2. "a recursive argument `arg_is_ind largs pos_block inst_indices` then: `largs, inst_indices`
   must nor refer to the inductive blocks and the strictly positive parameters";
3. "a strictly positive parameter `arg_is_sup largs k inst_args`, then: `largs, inst_args` must
   nor refer to the inductive blocks and k-th parameter does correspond to a strictly uniform
   parameter. To ensure the encoding is not inductive-inductive, we also need that recursive
   occurrences do not appear in in `largs, inst_indices`";
4. "a nested argument `largs ind inst_params inst_indices`, then `largs, inst_indices` must nor
   refer to the inductive blocks and the strictly positive parameters. Moreover, for each
   instantiation `(largs, arg)` … of a parameter, `llargs` must nor refer to the inductive blocks
   or the strictly positive parameter; and if the parameter is strictly positive then `arg` must
   be positive, otherwise it must not refer to the inductive blocks or the strictly positive
   parameters. To ensure the encoding is not inductive-inductive, we also need that recursive
   occurrences do not appear in `largs`, nor in `llargs` and `args`."

Plus: "An inductive block … is positive provided that all its constructors are positive, and
that the indices do not refer to the inductive blocks nor the strictly positive parameters. A
constructor … is positive provided that all its arguments are positive, and that the
instantiation of the indices … does not refer to the inductive blocks nor to the strictly
positive parameters." Non-uniform parameters must not mention the strictly positive ones
(`positive_mutual_inductive_body`, `:1141-1144`).

Three details from the Coq source that the prose doesn't spell out **[checked]**:

- **"Recursive occurrences" means earlier arguments that contain one.** The extra condition
  (marked `BEGIN ADDITION NO INDUCTIVE-INDUCTIVE`) is `rc_notin`: no argument may mention an
  earlier argument whose shape isn't a constant (`PosArgBool`, `:1111-1115`). So a constant field
  can't depend on an earlier recursive field at all.
- **The outer type may be a member of a mutual group.** The nested case looks up `D`'s whole
  block (`lookup_minductive E kname = Some mdecl`, `pos_ind < #|ind_bodies mdecl|`) and uses the
  block's per-parameter flags (`ind_uparams : list (context_decl * bool)`), `:946-973`. Rocq's
  old "not mutually defined" condition is gone: "this limitation is artificial" [P1, §2.2].
- **The flags are per block and assumed correct.** The theorem takes the flags as given and
  assumes every earlier block is positive with them (`E_pos`, `Nested_to_mutual_proof.v:1200`).
  The plugin computes them with `preprocess_strpos` (`strictly_positive_uniform_parameters.v:146`):
  a parameter starts as a candidate if its type reduces to an arity ending in a sort
  (`default_value`, `:54`), and stays one if it occurs only strictly positively in every
  argument (`preprocess_strpos_arg`, `:87`), not in non-uniform parameters' types
  (`check_nuparams`, `:134`) and not in index types (`check_indices`, `:137`). That function does
  not check `rc_notin` and does not look at later uniform parameters' types **[checked]**; the
  formal condition's `E_pos` would refuse some flags it computes (for a `Sigma`-like type, see
  §5.5) **[inferred, not run: no Rocq ≥ 9.2 available]**. We follow the formal condition.

**The translation** (§3.1 of [P1]) **[cited]**: each nested occurrence's outer block is copied
into the group, with the parameters replaced, "and the nested arguments are replaced with their
corresponding specialized instantiations". Unlike Lean's, it allows local variables: "we must
include the relevant arguments as indices to keep them available", leaving out recursive ones
(the strengthening `↑args_g`), so `List (Tree n)` becomes a forest *indexed by* `n`. The
specialised block's signature: `ind_l_mut params_g : ↑args_g → largs_g → σ(indices_l) → Type`.

**The theorem.** `pos_nested_to_mutual : positive_mutual_inductive_body mdecl ->
positive_mutual_inductive_body (nested_to_mutual mdecl)` (`Nested_to_mutual_proof.v:1417`)
**[checked]**: the encoding of a positive nested block is a positive *non-nested* mutual block.
What it does not say is in §6.1.

**Eliminators** (§4 of [P1]): "sparse parametricity" adds a predicate only for each nestable
parameter (`prod_all A PA B PB`), with a "local fundamental lemma" (`ind_all_forall`: if every
`PA` holds, `ind_all` holds). The eliminator for a nested type takes `All`-style hypotheses and
is built by `fix` and `match` using that lemma. This is in Rocq 9.2 as `Scheme All`
[R2] **[cited]**. LFST also say the eliminator's encoding via the mutual one is pen and paper:
"Although we are fairly confident this method succeeds, we emphasize that … absolute certainty
remains unattainable" [P1, App. F] **[cited]**.

**A caveat to "strictly generalizes Lean's check".** Lean 4.34.1 accepts
`structure Dep (α : Type) (x : List α) where y : α` followed by
`inductive UsesDep | leaf | node (d : Dep UsesDep [])` **[run]** (Rocq 9.1.1 too **[run]**).
Under the formal condition, `x` isn't an arity so it isn't nestable, and its argument `[]`, which
is `@List.nil UsesDep`, mentions the type: refused **[inferred]**. So the inclusion holds for the
cases the paper discusses, not for every declaration. Nothing in Stitchwort needs this case.

### 4.4 Agda

Agda analyses how a type uses its parameters, or takes `@++` polarity annotations; a polarity
that is *declared* rather than checked can prove `⊥`, so "Polarity pragmas are not allowed in
safe mode" [A1] **[cited]**. The lesson stands: nestability must be computed by the kernel from
the outer type's constructors, never trusted from an annotation.

### 4.5 Summary

| | Lean 4.34 | Rocq ≤ 9.1 kernel | LFST (Rocq 9.2 eliminators) | This proposal |
|---|---|---|---|---|
| How nesting is checked | translate, check the copy | substitute, re-check by conversion | per-type nestable flags | per-group nestable flags |
| `List (Tree n)` (earlier field in the index) | refused [run] | accepted [run] | accepted | accepted [run] |
| `All (t => Typed t r) bs` | refused [run] | accepted [cited] | accepted | accepted [run] |
| Through an earlier mutual group | accepted [run] | refused [run] | accepted | accepted [run] |
| `Fnat` (through `Eq`) | refused [run] | accepted [run] | refused | refused [run] |
| `depends_on_b` | accepted [P1] | `true` accepted [run] | refused | can't be written (§5.6) |
| `Dep UsesDep []` | accepted [run] | accepted [run] | refused [inferred] | refused (§5.5) |
| Nested `Prop` matched to make data | no [run] | yes (`P_rect` into `Type`) [run] | not discussed | no (§5.4) |
| Proved | no paper proof | no | encoding is positive (mechanised) | inherits LFST (§6) |

## 5. The rule for Stitchwort

### 5.1 Nestable parameters of a data group

Computed once per data group when it is admitted (or lazily when first needed; it depends only
on the group's final constructors, so it needs no hash and no cache). A group's parameters are one
telescope shared by its members, so the flags are per group. Parameter `p` of group `G` is
**nestable** when all of these hold:

1. **Its type is an arity**: `Type`, `Prop`, or a function type ending in one (`a → Prop`).
2. **No later parameter's type mentions it.** (`List.Member (a) (xs: List a)`: `a` is not
   nestable. `Map (k) (v) [auto ord: Ord k]`: `k` is not.) This is a restriction beyond LFST;
   see §5.5.
3. **No member's index types mention it**, and no constructor's result indices do.
4. **In every field of every constructor of every member, it occurs only strictly positively**,
   which means the field type, after any leading `(x: A) →` whose `A` doesn't mention `p`, is one
   of:
   - something that doesn't mention `p`;
   - `p` applied to arguments that don't mention `p`;
   - a member of `G` applied to `G`'s own parameters (which includes `p` itself, as in `tail:
     List a`) and then to indices that don't mention `p`;
   - an earlier data type `D args`, where every argument mentioning `p` is at a nestable
     parameter of `D` and, after stripping leading lambdas `x y => …`, satisfies this same
     condition; `D`'s indices don't mention `p`.
5. **No field mentions an earlier field whose type mentions `p`** (LFST's `rc_notin`, applied to
   the parameter).

Anything else (`p` left of an arrow, inside a `def` application, an `Eq`, a `Quot`, or a
non-nestable parameter of another type) makes `p` not nestable. In particular a quotient is not a
data type, so `Map`'s and `Set`'s parameters are never nestable, and no special case is needed for
them **[inferred from `std/Map/Map.sw:22`; the elaborator refuses first, §7]**.

Examples. Nesting through these was accepted by the prototype, so they are nestable **[run]**:
`List`'s `a`, `Option`'s `a`, `Pair`'s first parameter, `Vec`'s `a`, `Effect.Comp`'s `a`, a local
`All (a) (p: a → Prop)`'s `p`, and a mutual `Tree`/`Forest`'s `a`. Nesting through these was
refused, so they are not **[run]**: `Neg`'s `a`, `List.Member`'s `a`, `Exists`'s `a`. By the rule,
not run: `Pair`'s second, `And`'s and `Or`'s parameters are nestable; `Effect.Comp`'s `op` (in
`res`'s type) and `res` (an input of `rest`), and `Map`'s and `Set`'s parameters are not
**[inferred]**.

### 5.2 The new case in `not_positive`

In a field of group `G`, a member may now also occur:

3. **inside `D a₁ … aₙ t₁ … tₛ`**, where `D` is a data type outside `G` (so final and earlier,
   by the declared-later guard), and
   - no member occurs in the indices `t₁ … tₛ`;
   - every `aⱼ` that mentions a member is at a nestable parameter of `D`;
   - each such `aⱼ`, after stripping leading lambdas, is itself allowed by the whole rule
     (directly, as a function field's result, or nested again).

Cases 1 and 2 (directly, applied to the group's own parameters and member-free indices; as the
result of a function field whose inputs mention no member) are unchanged. So are the refusals of
a member left of an arrow, applied to other parameters, in an index, or under anything that is
not a data type: a `def` (`Children := List`), a type variable (`Fix f = MkFix (f (Fix f))`), a
quotient, `Effect.Delay`, `Eq`.

`List (List Packet)`, `Option (Packet, Nat)`, `Vec Packet n`, `Tree Big` with `Tree`/`Forest`
mutual, `List (Tree n)` with `n` an earlier field, and `All Term (t => Typed t r) bs` are
accepted; `Neg Bad`, `Option WithCheck → Bool`, `List.Member Q []` and `Exists E (x => x = x)`
are refused **[run, prototype]**.

### 5.3 No field depends on a recursive field

New, from LFST's `rc_notin`: **a field may not mention an earlier field of the same constructor
whose type mentions a member.** `Mk (children: List T) (lenOk: List.length children = 2)` is
refused. It is refused already by §5.2, because the checked `lenOk` is `Eq(Some(Nat), List.length
T children, 2)` and `T` is the type argument of `List.length`, a `def` **[run]**. Likewise LFST's
`Fnat`: `n = m` is checked to `Eq(Some(Fnat), n, m)` **[run]**.

So why add a rule? Because §5.2's argument rests on the member's *name* appearing in the term, and
Stitchwort's core terms don't always carry types the way Rocq's do: lambdas have no domain
(`Term::Lam(Name, Icit, body)`) and constructors take no parameters (`Term::Ctor(DataId, usize,
fields)`, `term.rs:151-162`) **[checked]**. We found no way to use a recursive field without the
member's name appearing (§6.2), but the explicit rule makes that argument unnecessary for
soundness. It costs nothing: with it the prototype gives the same verdict as today on every one of
the 1,075 example files **[run]**.

### 5.4 Propositions with a nested field

**A member of `Prop` with a nested occurrence in any of its fields counts as a group of two or more
for `E-PROP-ELIM`**: matching on its proofs only produces proofs. Today
`type P: Prop = | MkP (h: And P Unit)` followed by `def fromP (p: P): Nat := match p with | MkP h
=> 0` is accepted by the prototype **[run]**, because `P` is alone in its group, has one
constructor, and its field is a proof (`check.rs:917-922`). Its encoding is `P` with a copy of
`And`, a group of two, which may not eliminate into data. Lean agrees (§4.1); Rocq 9.1.1 gives
`P_rect` into `Type` **[run]**. We see no unsoundness in Rocq's choice for such types (they are
built only from single-constructor proofs, so a proof's depth can't be observed) **[inferred,
not proved]**, but the conservative rule keeps "accepted only if the encoding is accepted" true
without a separate argument, and no example needs the large elimination. The flag is three places
in the code (`check.rs:917`, `value.rs:1615`, `erase.rs`).

### 5.5 How this relates to LFST

LFST's setting is MetaRocq's PCUIC. Specialising it to Stitchwort:

| LFST | Stitchwort | Same, restriction, or not applicable |
|---|---|---|
| Uniform and non-uniform parameters | All parameters are uniform; indices do what non-uniform parameters do | N/A: LFST "do not distinguish indices from non-uniform parameters" [P1 §3]. Their rule for non-uniform parameters is our rule for indices |
| Strictly positive parameter: arity, strictly positive everywhere, not in non-uniform parameters' or indices' types | §5.1 conditions 1, 3, 4, 5 | **Same** |
| Later *uniform* parameters' types may mention a nestable one | Not nestable then (§5.1 condition 2) | **Restriction**, below |
| Four argument shapes; constants mention no block and no nestable parameter | §5.2 and today's cases 1-2; anything else refused | **Same**, with "mention" meaning a syntactic occurrence of the member's name in the *checked* term |
| `rc_notin` | §5.3 | **Same** (ours is the simpler form: no field mentions an earlier field containing a member; LFST exempt the indices of a direct recursive field, which can't mention such a field in Stitchwort anyway, because index types are fixed before the group and can't mention a member) **[inferred]** |
| Outer type: any block of an earlier mutual inductive | Any member of an earlier data group | **Same** |
| Instances may mention earlier constant arguments (local variables) | Allowed (`List (Tree n)`, `t => Typed t r`) | **Same** |
| Instances of arity parameters: `fun llargs => arg` | Leading lambdas stripped, body checked | **Same** |
| Indices of the nested occurrence must be constants | Same | **Same** |
| Truly nested types (a type as its own container) | Refused by declared-later | **Same** (LFST don't cover them either) |
| `Prop`, `SProp`, sort polymorphism | One `Prop`, subsingleton elimination, no cumulativity | **Restriction** for `Prop` (§5.4); universes as today |
| Quotients, primitive types (`array`) | `Quot` isn't data: never nestable; `Effect.Delay` isn't data | **Restriction** (LFST's Rocq integration allows registered `array_all` by hand [R2]; we don't) |
| Flags computed by `preprocess_strpos` (no `rc_notin`) | Flags by the formal condition (with `rc_notin`) | We follow the formalisation, which is what the theorem is about |

**Why the restriction to "no later parameter's type" is harmless and wanted.** LFST's formal
condition doesn't look at later uniform parameters' types. Take `Dep (a: Type) (xs: List a)` with
`a` nestable. To nest, the instance for `xs` must be a term of type `List T` that mentions neither
`T` nor a recursive field. In Rocq that is impossible (`nil` is `@nil T`), so the case is
vacuous. In Stitchwort it isn't: `Nil` is `Term::Ctor` with no parameters, and `_ => Nat` is a
lambda with no domain, so a term can have a type involving `T` without mentioning `T`. Refusing to
nest through such a parameter closes that gap. What we lose: nothing in the standard library
(`List.Member`, `Exists`, `Map`, `Effect.Comp` are the parameters affected, and none is a
container one nests in) **[checked, the std types listed in §5.1]**, and Lean's `UsesDep`, which
LFST refuse too.

**Why the flag approach, not draft 1's substitution, even though they agree here.** Under
Stitchwort's restrictions (uniform parameters, no computation in field types, syntactic
occurrence) substituting the arguments into `D`'s constructors and re-checking gives the same
verdict as the flags, except for nesting through a mutual outer group, where draft 1's rule was
incomplete (it would re-expand `Forest` inside `Tree` inside `Forest`, with no stopping case for a
sibling) **[inferred]**. The flags are what the theorem is about, terminate trivially, handle
mutual outer groups, give the error message its content ("`Neg`'s `a` is used as a function's
input in field `consume`"), and are exactly what stage 3's `All` predicates need.

### 5.6 Resolved questions

- **`lenOk: List.length children = 2`.** Refused, by Lean, LFST (`ind_notin` for constants, and
  `rc_notin`) and by us (§5.3) **[run]**. We shouldn't allow it: its encoding would need a
  translation of `List.length` to the copied list, and nothing proves such types sound. Draft 1
  said option A "need not" inherit Lean's refusal; that was wrong, as the reviewer suspected: draft
  1's own rule refused it too (`List.length T children` is a `def` application). Users write the
  invariant as a separate proposition about the value, or use an index.
- **An outer type in an earlier mutual group.** Allowed. LFST's formalisation covers it directly,
  Lean allows it, and the flags make it free (§5.5). The prototype accepts `Big` nested in
  `Tree Big`, with `Tree`/`Forest` mutual, and a structural count over all three types computes
  in `rfl` **[run]**. The reviewer suggested restricting stage 1 to non-mutual outer types; we
  think that is unnecessary (§11, point 4).
- **`children: List (Tree n)`, `n` an earlier field.** Allowed, as the reviewer recommends. LFST's
  encoding indexes the copied list by `n`; we wrote that encoding by hand (`Tree`/`Forest: Nat →
  Type` with `FCons (n) (t: Tree n) (rest: Forest n): Forest n`) and today's kernel accepts it,
  with a count that computes in `rfl` **[run]**. Lean refuses the nested form **[run]**.
- **Quotients.** Stay refused (`Map`, `Set`): automatically by the flags, and earlier by the
  elaborator's own message ("`M` is used inside a quotient type … built on a quotient type")
  **[run]**. Same reasons as before: no encoding, and no part-of relation through a quotient.
- **`depends_on_b`.** Can't be written: a field type can't contain `case`
  (`case_only_in_tree`), and a `def` that computes a type is not a data type, so the parameter
  used through it is not nestable.

## 6. Why it is sound

### 6.1 What we rely on

**The theorem** [R4, `Nested_to_mutual_proof.v:1417`] **[checked: the statement]**: for every
mutual block `mdecl` written in LFST's view (`argument`, `constructor_body`, `mutual_inductive_body`
of `Positivity_condition.v`), if `positive_mutual_inductive_body mdecl` then
`positive_mutual_inductive_body (nested_to_mutual mdecl)`, and the result has no nested arguments.
It assumes, in full:

- **A1 (environment).** Every block already in the environment is positive with its flags:
  `Parameter (E_pos : forall kname, if lookup_minductive E kname is Some mdecl then
  positive_mutual_inductive_body mdecl else False)` (`:1200`). The environment `E` and
  `lookup_minductive` are parameters too (`Positivity_condition.v:440-441`), as is
  `cdecl_to_arity` (`:894`).
- **A2 (the view).** The theorem is about the view, not about raw terms: that a declaration's
  view correctly describes it (`arg_of_term`) is not part of the theorem **[checked: the
  statement quantifies over views; we found no lemma linking views to terms in the files we
  read]**.
- **A3 (guard).** "Guard Checking is unset in the formalization in order not to have to reason by
  well-foundedness on the size of the environment" [R4 README] **[cited]**. The recursion is on
  earlier types, so it is well founded; the formal proof doesn't show it.
- **A4 (positivity only).** What is proved is that the encoding is *strictly positive*. That the
  encoding is *well typed* is not stated as a theorem; the paper's §3.1 explains the construction
  (strengthening, indices) that is meant to make it so **[cited]**.
- **A5 (eliminators).** That the nested eliminator can be derived from the mutual one is argued
  in [P1, App. F] on paper, with computation rules holding "only up to propositional equality",
  "fairly confident" **[cited]**.
- **A6 (the base theory).** A strictly positive mutual inductive type is consistent in CIC
  (standard; not part of the paper).

### 6.2 What we argue ourselves

- **B1 (our rule is inside theirs).** Every group our rule accepts, with our flags, satisfies
  LFST's `positive_mutual_inductive_body`, reading Stitchwort's data group as a block with only
  uniform parameters and our indices as their indices. The table in §5.5 is the argument, case by
  case **[inferred]**. Our flags are at most theirs (condition 2 refuses more), and a non-nestable
  parameter is treated as a constant, which is always allowed. By induction over declaration
  order, every earlier group is positive with its flags, which is A1 for us.
- **B2 (syntax).** LFST's conditions say "does not refer to the inductive blocks"; ours say "the
  member's name doesn't occur in the checked term". These agree if a term whose type involves a
  member must mention it or a field whose type does. In Stitchwort a type is introduced to a term
  only by: an explicit argument (a data type's parameters, a `def`'s implicit arguments, which are
  explicit in core terms), an `Eq`'s type (filled in by the checker before positivity runs,
  `check.rs:355-376`), a variable's type, or the expected type of a constructor or lambda. The
  first two mention the member by name; a variable whose type mentions a member is a recursive
  field, which §5.3 forbids mentioning; the last is closed by §5.1 condition 2 for parameters, and
  by index types being fixed before the group for indices **[inferred, not proved]**.
- **B3 (the encoding exists in Stitchwort).** LFST's encoding is a mutual group with uniform
  parameters and some new indices: exactly the shape Stitchwort's data groups allow (one
  parameter telescope, per-member indices, members applied to their own parameters). Universes:
  the copied type's fields keep their sorts after substitution, and `D args` fitting in the
  group's universe means `D`'s sort does, so the copy fits **[inferred]**. Per declaration, the
  test oracle (§8) checks this with today's kernel, which is stronger than A4.
- **B4 (Prop).** With §5.4, a nested proposition eliminates exactly like its encoding.
- **B5 (termination).** Below.

### 6.3 What remains open

- **C1.** No proof that a Stitchwort value of `T` corresponds one to one with a value of the
  encoding. It is the folklore relabelling (each `List T` value ↔ the copy's value, constructor
  for constructor), and the oracle can test it on generated values (§8), but nobody has proved it
  for Stitchwort.
- **C2.** B2 is an argument about the shape of core terms, not a proof; §5.3 and §5.1 condition 2
  are there so that we don't depend on it.
- **C3.** Stitchwort's own kernel (mutual groups, SCT, `Prop` rules) has no soundness proof. This
  proposal adds nothing to that gap beyond C1.
- **C4.** We read LFST's preprint, not the published version.

### 6.4 Termination

**The invariant**, to go in `termination.rs`'s header and `docs/core.md`: *SCT's "smaller than"
relates two variables only when, in every run, the first's value is a proper constructor
subvalue of the second's: a field of it, a field of a field and so on, or the result of applying
a recursive function field of it. It is the transitive closure of immediate field containment on
one particular value, never a relation computed from the data types' dependency graph.* So
`Packet → List Packet → Packet` repeating in the *types* is irrelevant: for values,
`p > items > q` and `q` can't be `p`.

**Checked against the code** **[checked]**: a variable becomes smaller only by being bound as a
field of a `case` on a variable that is a parameter or already smaller (`termination.rs`, the
`Term::Case` arm from line 442: `source = scrutinee.param.or(scrutinee.smaller_than)`), by
`let` of such a value, or as a recursive function field applied. The only type-directed step is
`is_recursive_fn` (`:326`): it reads the *matched* type's own declared field type and its own
group. For a nested type that is conservative: a field `kids: Nat → List Tree` returns `List`, not
a member, so `kids n` gains nothing, and `List`'s `head: a` is never a function field. Quotients
can't be matched ("A quotient form, `Quot.lift` included, gives no evidence of descent", `:407`). So nothing makes "part of" follow
types **[checked]**.

**Why that's enough** **[inferred]**: SCT is sound if "part of" is well founded on values. Values
of a nested `T` are finite trees (or well-founded trees, through function fields) because `T` is
isomorphic to its encoding (B3, C1), whose values are. An infinite descent through `T`, `List T`
and back would be an infinite descent in the encoding, which can't exist. This uses C1, and needs
positivity: `Bad`'s values would not be well founded.

## 7. What we ran

**The prototype** (scratch, ~200 lines in `check.rs` behind `STITCHWORT_NESTED_PROTO`, not
merged; kept as `dev/scratch/sw704-nested-positivity.patch` in a separate commit): §5.1 flags
computed on demand, §5.2's case, §5.3's rule. Not §5.4. **[run]**:

| Program | Prototype | Lean 4.34.1 | Rocq 9.1.1 |
|---|---|---|---|
| `Packet` with structural size, `rfl` | accepted | (draft 1: accepted) | |
| `Rose a`, `List (List (Option (Nest, Nat)))` | accepted | | |
| `Vec V n` (nested at `Vec`'s parameter) | accepted | | |
| `Effect.Comp Nat (_ => Nat) C` | accepted | | |
| `Big` in `Tree Big`, `Tree`/`Forest` mutual, count by `rfl` | accepted | accepted | refused |
| `Tree: Nat → Type` with `children: List (Tree n)`, count by `rfl` | accepted | refused | accepted |
| `Typed` with `All Term (t => Typed t r) bs` (and `Term` nested in `List`) | accepted | refused | |
| `Neg Bad` | refused | | |
| `WithCheck`, `f: Option WithCheck → Bool` | refused (negative) | refused | |
| `BRTree` with `ok: List.length children < branches` | refused | (manual: refused) | |
| `lenOk: List.length children = 2` | refused | | |
| `Fnat` (`same: n = m`) | refused | refused | accepted |
| `Fix f`, `unfold: f (Fix f)` | refused | | |
| `List.Member Q []` | refused | | |
| `Exists E (x => x = x)` | refused | | |
| `Map Nat M` | refused (elaborator, quotient message) | | |
| `P: Prop` nested in `And`, matched to make a `Nat` | **accepted** (§5.4 not in the prototype) | `P.rec` into `Prop` only | `P_rect` into `Type` |
| `Dep UsesDep []` | (not tried) | accepted | accepted |

**Regression sweep**: all 1,075 files in `examples/accept`, `examples/reject` and
`examples/soundness`, checked with and without the variable: one verdict differs,
`reject/nested-data.sw` (the nested `Rose` this proposal accepts) **[run]**.

**Runtime and induction**: with the prototype, `Packet` with a hand-written All-form induction
principle (§9) checks, `Packet.sizePositive` follows from it by `omega`, and `main` prints `size: 6`
under `run` and `run --js` **[run]**. Draft 1's runs (recursion through `items.attach.map` with
`decreasing`, day 13's comparison, mutual induction, the same output under `run --reference`) used
draft 1's prototype, which accepted a superset of this one on those programs; they don't depend on
the positivity rule and are not repeated here.

An aside: a first version of the hand-written induction principle wrote `List.All`'s proofs as
`()` and a pair; checking it ran for over 100 s at 2 GB before we stopped it. Written with
`Trivial` and `Both`, it checks at once. A pair against an `And` alone gives a prompt type
mismatch **[run]**. Not investigated further; worth a ticket.

## 8. The translation test oracle

A property test of the kernel rule against LFST's translation, run by today's kernel. It tests the
algorithm on many shapes, not a list of examples.

**Generator** (seeded, deterministic, in Rust, emitting source text):

- **Outer types**: a fixed library (`List`, `Option`, `Pair`, `Vec`, a mutual `Tree`/`Forest`,
  `Neg (a → Nat)`, `W (a → b)`, `Phantom`, `Dep (a) (xs: List a)`, `All (a) (p: a → Prop)`,
  an indexed `Idx (a): a → Type`), plus 0-2 randomly generated earlier groups (1-2 members, 1-2
  parameters of type `Type` or `a → Prop`, 0-1 index, 1-2 constructors, 0-3 fields).
- **The group under test**: 1-2 members, 0-1 parameters, 0-1 `Nat` index, 1-3 constructors, 0-3
  fields each. Field types from: `Nat`, a parameter, an earlier `Nat` field, a member (own
  parameters; index a literal or an earlier `Nat` field), `D τ…` for an outer type, `τ → τ'`, a
  lambda instance for an arity parameter, `x = y` on earlier fields.

**Translation** (LFST §3.1, on the generator's own small AST, so it never parses): repeatedly
replace the first nested occurrence `D σ` in field `f` by a fresh copy of `D`'s whole group,
parameters replaced by `σ`, indexed by the earlier constant fields that `σ` mentions (LFST's
`↑args`), and refer to it applied to those fields. Stop when nothing nested is left, or report
"no translation" (a member in an index, an instance mentioning a recursive field).

**Properties**, both checked with the real elaborator and kernel:

1. **Soundness (must hold):** if the nested group is accepted, its translation is accepted by the
   kernel *without* the nested case. A failure is a kernel bug or a translation bug; either way it
   blocks.
2. **Completeness (reported, not required):** if the translation is accepted, so is the nested
   group. Each kind of counterexample is either fixed or listed in the note with its reason (we
   expect the §5.5 restriction to show up here, and nothing else).
3. **Values (stage 1 if cheap, else later):** for accepted pairs, generate the two conversion
   functions (structural, one per copied type) and random closed values, and check
   `fromMut (toMut v) = v` by `rfl`. This tests C1 on instances.

**Tiers**: 50 cases in the lane tier (`AREA=core`), a few thousand in the daily tier. A failure
prints both programs as `.sw` files, ready to become `examples/soundness` pairs.

## 9. Induction principles

**What LFST generate**, and why we can't copy it directly. Their eliminator for `Packet` has the
hypothesis `List.All motive items` (sparse parametricity), proved by `fix` and `match` with a
generic lemma `allOf: ((x: a) → p x) → (xs: List a) → List.All p xs` applied to the eliminator
itself under a lambda. Rocq's guard checker accepts that because it unfolds `allOf` [P1 §4.2].
Stitchwort's SCT doesn't look inside other definitions: our version is refused, "the 4th argument,
`q`, isn't seen as smaller than `p`" **[run]**.

**What stage 3 generates instead**: the same statement, proved by a *mutual helper per nested
occurrence*, which is the encoding at the level of proofs. For `Packet` **[run, prototype]**:

```
theorem Packet.induct (motive: Packet → Prop)
    (number: (n: Nat) → motive (Number n))
    (packets: (items: List Packet) → List.All motive items → motive (Packets items)):
    (p: Packet) → motive p
  | Number n => number n
  | Packets items => packets items (Packet.inductList motive number packets items)

theorem Packet.inductList (motive: …) (number: …) (packets: …):
    (items: List Packet) → List.All motive items
  | Nil => Trivial
  | Cons p rest => Both (Packet.induct motive number packets p) (Packet.inductList motive number packets rest)
```

Both helpers are ordinary checked theorems; nothing is trusted.

**`All` versus "for every member".** The `All` form composes: `List (Option T)` gives
`List.All (Option.All motive) items`, and a container with two nestable parameters gets one
predicate per parameter (`Pair.All PA PB`). The membership form, `(q: T) → List.Mem q items →
motive q` (draft 1), reads better but needs a `Mem` for each container and doesn't compose.
Proposal: the generated `T.induct` uses the `All` form, as LFST do; for a field whose type is
`List T` or `Option T` directly, a corollary `T.inductMem` with the membership hypothesis is
generated from it with `List.All.mem` (a library lemma). `List.All` already exists as a
definition by recursion (`std/core/ListOptionPair.sw:89`, moved there from `List/Toolkit.sw` in stage 3); stage 3 generates `D.All` the same way for
a user's container (a `def`, one predicate per nestable parameter, `Prop`-valued only, since
Stitchwort has no sort polymorphism), and the helpers above per occurrence. That's D1823.

## 10. Stages

1. **Kernel and docs** (medium). §5.1-5.4 in `check.rs` (flags, the nested case, the
   recursive-field rule, the `Prop` rule in its three places); error messages that name the outer
   type's parameter and the field that makes it non-nestable; `docs/core.md` (data types, groups,
   the termination invariant of §6.4) and `docs/syntax.md:140`; the termination header comment;
   the JS codec's finiteness comment (`crates/js/src/lib.rs:1244-1251`, a nested occurrence is
   still the type applied to its own parameters). Must-reject pairs in `examples/soundness`:
   `Neg`/`List`, `Fnat`/`Tree` with `Eq` on a non-recursive field, `WithCheck`/`Option` stored,
   `List.Member`/`Option`, a nested `Prop` matched to data / matched to a proof, `Map`/`List`.
   The §8 oracle (properties 1-2), with these as seeds.
2. **Derived `==`, `<`, `${…}`** (medium), as in draft 1: a generated mutual helper over each
   nesting container the deriver knows (`List`, `Option`, tuples); others keep today's message.
   **Built** ([As built (stage 2)](#as-built-stage-2)); the others get a new message naming the
   container.
3. **Generated `D.All`, `T.induct`, `T.inductMem`, size and membership lemma** (medium), §9,
   with `auto` proving `decreasing T.size p` obligations from an `attach`ed element.
   **Built** ([As built (stage 3)](#as-built-stage-3)).
4. **Dogfood** (small). AoC 2022 day 13, 2021 day 18, a typing judgement with `All`.

Draft 1's option C (termination looking inside `map`) stays unstaged.

## 11. Response to review

| Reviewer's point | What changed |
|---|---|
| 1. Base the rule on LFST's nestable-parameter criterion, not old Rocq | **Adopted.** §4.3 quotes it, §5 specialises it, §5.5 maps it line by line. The flags are per group, as in the formalisation |
| 2. The soundness argument claims "iff the translation is accepted" but also that A accepts more than Lean (`lenOk`) | **Agreed; the draft was wrong.** `lenOk` is refused by draft 1's own rule, by Lean, by LFST and by this rule (§5.6) **[run]**. The claim is now one-directional: accepted ⇒ LFST-positive ⇒ positive encoding (mechanised), plus a per-instance check that the encoding is accepted (§6, §8). We do still accept more than Lean (local variables, `List (Tree n)`), because LFST's translation does |
| 3. Derive the parameter side condition from the nestable-parameter definition, or prove they coincide | **Derived** (§5.1). One condition is ours, not LFST's (a later parameter's type), kept for a Stitchwort-specific reason: untyped lambdas and parameterless constructors (§5.5) |
| 4. Earlier mutual outer types; maybe restrict stage 1 to non-mutual | **Allowed from stage 1, not restricted.** LFST's formalisation handles it directly with per-block flags, Lean allows it, and the prototype accepts it and computes over it **[run]**. Draft 1's substitution rule did have the gap the reviewer saw; the flags remove it |
| 5. Allow `List (Tree n)` | **Adopted** (§5.6), with the hand-written indexed encoding accepted by today's kernel **[run]** |
| 6. Termination is sound if "part of" is concrete subvalue containment; say so | **Adopted** as an invariant for `termination.rs` and `docs/core.md`, checked against the code (§6.4) |
| 7. Keep quotients refused | **Agreed**; now a consequence of the flags as well as the elaborator's message (§5.6) |
| 8. A over B2, with a property-style oracle; say which direction is the soundness check | **Adopted** (§8): "nested accepted ⇒ translation accepted" must hold; the converse is reported |
| 9. User-facing "for every member" built on `All` | **Adopted with a change**: LFST's construction is refused by SCT **[run]**, so stage 3 generates a mutual helper per occurrence; the `All` form is primary, the membership form a corollary (§9, D1823) |
| Not raised, found here | §5.3 (`rc_notin`), §5.4 (`Prop` elimination, a real mismatch with the encoding **[run]**), the `UsesDep` caveat to "strictly generalizes Lean" (§4.3), and that LFST's mechanised result is positivity of the encoding, not its typing or the eliminators (§6.1) |

## 12. Options considered

- **A′ (recommended): LFST's rule, specialised (§5).** Kernel: about 200 lines (the prototype is
  that size), no change to termination, conversion, evaluation, hashing or erasure.
- **A (draft 1): Rocq's old substitute-and-re-check rule.** Superseded: incomplete for mutual
  outer types, and its justification was the theorem for a different rule.
- **B2: Lean's translation in the kernel.** Builds the encoding, checks it, throws it away (we have
  no recursor to derive from it). More trusted code than A′ for the same verdicts, and Lean's
  translation refuses local variables. Kept as the test oracle (§8), outside the kernel.
- **C: termination looks inside `map`.** Not now (draft 1 §6, unchanged).
- **D: sized types.** Rejected (well-founded-recursion.md §5(D)).
- **E: keep refusing, generate `Forest` twins.** Strictly worse than A′.

## 13. Decisions

Earlier decisions this note relies on: D1820 (this rethink). Recommendations in brackets.

| # | Question | Options |
|---|---|---|
| D1821 | Adopt §5 (LFST's nestable parameters, specialised, with §5.3 and §5.4) as the kernel rule, with stages as in §10, including mutual outer types, earlier fields in nested instances, and arity parameters (`All (t => Typed t r) bs`) in stage 1? | [**yes, all in stage 1**]; or stage 1 without arity parameters and local variables (Lean's fragment), the rest later |
| D1822 | A proposition with a nested field: may matching on its proofs produce data? | [**no, as Lean: it counts as a group of two (§5.4)**]; or yes, as Rocq, with a separate argument that the encoding mismatch is harmless |
| D1823 | Shape of the generated induction principle | [**`T.induct` with `All` hypotheses, plus `T.inductMem` ("for every member") for direct `List`/`Option` fields (§9)**]; or membership form only (draft 1). **Adopted** with D1870 (Matt, 29 October): `All` primary, membership a corollary; built in stage 3 |

## As built (stage 1)

29 October 2026, SW-704, after D1821 (Matt: the §5 rule in stage 1, including earlier mutual
outer types, earlier fields in nested instances, and predicate parameters). D1822 is still
formally open; the stage takes its conservative option (§5.4), which the soundness argument
uses (B4).

**Kernel** (`crates/core`):

- `globals.rs`: `Data::nestable`, one entry per parameter of the group, `Ok(())` or the first
  reason it isn't nestable (`NotNestable`: not a type, a later parameter's type, an index type,
  a result index, or a field's `ParamUse`: a function's input, inside something that isn't a
  data type, at another type's non-nestable parameter, in an index, or depending on an earlier
  field that has it). Not hashed.
- `check.rs`: `nestable_params` (§5.1, conditions 1-5, with `stored_only` for condition 4),
  computed in `install_data_group` once the constructors are final, so on the checked path and
  the check cache's trusted path alike (the trusted test compares them). `not_positive` gains
  case 3 (`not_positive_nested`, §5.2): an argument of an earlier data type that mentions a
  member must be at a nestable parameter (not an index), and after stripping its leading
  lambdas is checked by the whole rule again. §5.3 runs in `admit_data_group` *before*
  positivity, so `Fnat` gets "field `same` depends on `n`, whose type contains `Fnat`" rather
  than the equation's message. §5.4 is `nested_field`, read by `E-PROP-ELIM`'s subsingleton
  test, with its own note. `value.rs` and `erase.rs` needed no change: they match an erased
  proof into data only where the checker allowed it, which is now strictly less often.
- An outer type that failed is skipped by positivity: the group fails anyway, with
  `E-FAILED-DEPENDENCY` (`admissible` saw it).
- Messages: "`Packet` is used inside `Neg`, and `Neg`'s field `consume` takes its parameter `a`
  as a function's input"; through two containers, "`Bad` is used inside `Wrap`, and `Wrap`'s
  field `inner` (of `MkWrap`) has its parameter `a` inside `Neg`, where `Neg`'s field `consume`
  takes its parameter `a` as a function's input"; "`Q` is used inside `List.Member`, and the
  type of `List.Member`'s later parameter `xs` mentions its parameter `a`"; inside a
  non-data-type, the label names it ("inside `Children`, which is a definition, not a data
  type", "a quotient", "an equality", "a type that's a variable"). The Tree/Forest workaround
  note is gone; the elaborator's quotient message (`Map`, `Set`) is unchanged and still comes
  first.

**What it accepts and refuses** (**[run]**, the stage's binary): accepted, in
`examples/accept/nested-data.sw` and `nested-data-shapes.sw`: `Packet` with `size`/`sizeList`,
`items.length` and a membership lemma (`size q < size (Packets items)` for `List.Mem q items`);
`Rose a`; `List (List Nest)`, `Option (Pair Nest Nat)`; `Vec Wide 2`; `Expr`/`Stmt` mutual, both in
lists; `Big` in `Tree Big` (`Tree`/`Forest` mutual); `Ranked: Nat → Type` with `kids: List
(Ranked n)`; `Typed` with `All Term (t => Typed t r) bs`; and the pairs' accepted halves. Refused,
in `examples/soundness/`: `nested-negative.sw` (`Neg Bad`, with the proof of `Void` written
out), `nested-recursive-field.sw` (`Fnat`), `nested-input.sw` (`Option WithCheck → Bool`),
`nested-member.sw` (`List.Member Q []`), `nested-prop-elim.sw` (`E-PROP-ELIM`),
`nested-in-quotient.sw` (`Map Nat M`); in `reject/`, `nested-through-definition.sw`
(`Children Tree`). `Packet`'s `main` prints `size: 6` under `run`, `run --js`, `run --reference`
and `run --native` (all three bodies native). An exported function taking and returning a
`Packet` extracts to JS with the type `{ $tag: "Packets"; items: Packet[] }` and round-trips.

**Regression** **[run]**: every file in `examples/accept`, `reject` and `soundness` (the daily
sample, which is all of them): one verdict changed, `reject/nested-data.sw` (now accepted; the
file is removed, its `Rose` is in `nested-data-shapes.sw`). Three messages changed:
`soundness/partial-nested.sw` (`Delay`, "a definition, not a data type"),
`quot-recursive-relation.sw` ("inside a quotient") and `cell-operation.sw` (now "`CellOp` is used
inside `Effect.Comp`, and the type of `Effect.Comp`'s later parameter `res` mentions its
parameter `op`": Landin's knot is refused by condition 2).

**Derived instances** (before stage 2, which replaced these; see [stage 2](#as-built-stage-2)): a
nested type got these messages, checked **[run]**:
"`==` isn't derived for `Packet`: the field `items` of `Packets` contains `Packet` inside
another type, which `==` isn't derived for yet", the same for `Show` and, through `==`, `Ord`.

**The oracle** (§8, properties 1-2; `crates/driver/tests/nested_oracle.rs`). Its library is
`OList`, `OOpt`, `OPair`, `OVec`, `OTree`/`OForest`, `ONeg`, `OW`, `OPhantom`, `ODep`, `OAll`
and `OIdx`, written in the test (not the standard library's, since the translation needs their
constructors), plus 0-2 random earlier groups. 19 hand-written seeds (the examples' shapes) get
their expected verdicts, and §5.5's `ODep` is the only seed where the translation is accepted
and the nested group isn't. Two choices the note didn't spell out: the generated group is split
into the groups the elaborator makes (members that refer to each other), each translated with
the earlier ones as containers; and each copy is declared in the group's universe, since a
Stitchwort group has one (positivity doesn't depend on it). Results **[run]**, seed `0x5eed0704`:

| Cases | Nested accepted (each translation accepted) | Refused by positivity | ... with an accepted translation | Ill-formed |
|---|---|---|---|---|
| 50 (lane) | 26 | 24 | 2 (both §5.5) | 0 |
| 400 (daily) | 214 | 186 | 21 (18 §5.5, 3 phantom) | 0 |
| 4000 (full) | 2148 | 1852 | 191 (146 §5.5, 45 phantom) | 0 |

**Property 1 held on every case.** Property 2's counterexamples are of two kinds: §5.5's
restriction (`ODep`, and generated groups with a predicate parameter on their first one,
`(r1: r0 → Prop)`, which makes `r0` not nestable), and *phantom* containers: a container that
doesn't use a parameter (`OPhantom`, or a generated one) loses the occurrence in its copy, so
something the rule refuses by where the name is written (`OPhantom (ONeg T)`, `OW Nat (R T)`
with `R`'s parameter unused) disappears from the translation. All 45 phantom cases at 4000 were
looked at (by a script checking for `OPhantom`, and the 10 others by hand: each had a
generated container with the parameter unused). Neither kind is a soundness question; a
phantom parameter could be made nestable everywhere if it ever matters.

**Not done in stage 1**: property 3 (values, `fromMut (toMut v) = v`), which needs
generated conversion functions; stages 2-4. One thing for a later decision, not changed here:
§5.3 is applied to fields, as the note says, not to constructors' result indices. A result index
that mentions a field holding a member without naming the member (only possible through an
index of type `Prop` or a type former, `(x => True) r`) is as allowed as it was before this
stage; LFST's condition refuses it ("the instantiation of the indices does not refer to the
inductive blocks"), and so would extending §5.3 to result indices **[inferred]**.

## As built (stage 2)

29 October 2026, SW-704, after D1840. Derived `==`, `<`/`compare` and `${…}` for a type nested
in `List`, `Option` and pairs, in the elaborator's derivers only (`crates/elab/src/derive.rs`,
`derive_ord.rs`, `derive_show.rs`); the kernel is unchanged.

**How.** `Elaborator::members` finds, for `T`, the containers it's in: each field's type that
mentions `T` and isn't `T` itself, evaluated with `T`'s parameters as variables, and then each
of *their* fields' types, until no new one turns up (`List (List T)` gives both lists, `Option
(T, Nat)` the option and the pair). Each is a *member*, numbered from 1 in the order found, and
gets the same generated functions as `T`, named `T.%m1%…`: `T.%m1%type` (a definition of `T`'s
parameters standing for the member's type, so the generated source can name it), `T.%m1%tag`,
the field projections `T.%m1%Cons%0`, `T.%m1%differ`, `T.%m1%decEq`; `T.%m1%compare`, `equal`,
`flip`, `unfold`, `trans`; `T.%m1%show` (and `T.%m1%items` for a list). They're made by the same
code as `T`'s, as for a data type whose constructors are the container's with its arguments,
where a field whose type is a member calls that member's function. Each kind (all `decEq`s, all
`compare`s, …) is admitted as one group (`Elaborator::definitions`), so `T.%decEq (Packets a0)
(Packets b0)` calls `T.%m1%decEq a0 b0`, which calls `T.%decEq` on the heads and itself on the
tails: every call is on a part of an argument, and termination accepts it as it accepts
`size`/`sizeList` (§6.4); no `decreasing`. The proofs (`J`s, `Eq.cong` of the projections,
`Ordering.thenTransBy`) are the ones generated for any type, checked by the kernel. A type
without nesting generates exactly what it did: no example's hashes changed except the nested
ones', which gained the new definitions.

**Behaviour** (**[run]**). `==` is structural. `Ord` is constructors in order, then fields;
a container's own derived order is the order of its library instance (`List.compareLex`:
`Nil` first, then head, then tail; `Option.compareWith`: `None` first; `Pair.compareWith`), so
`Ord.compare (Packets [Number 1, Number 9]) (Packets [Number 2]) == Ord.compare [1, 9] [2]`.
`Show` prints a list `[x, y]` and a pair `(x, y)` as `List.instShow` and `Pair.instShow` do,
and an option as `Option.instShow` does: `Packets [Packets [Number 1], Packets [Number 2,
Packets [Number 3]]]`, `Node 'a' [Node 'b' []]`, `Link (Some (Link None "b", 3)) "a"`.
`auto`, `if h:`, a proposition as a `Bool`, `List.sort`, `contains` and `Map` keys use them, and
they compute in proofs (`(Packets [Number 1] == Packets [Number 1]) = True := rfl`).

**Not derived**, with the note naming the container: `T` inside `Vec`, a type of the program
(`Box T`), or an earlier group (`Tree Big`): "the field `kids` of `Fork` contains `Branching`
inside `Vec`, and `==` is derived for a type inside `List`, `Option` and pairs only".
Unchanged: types defined together (`Expr`/`Stmt`), types with indices (`Ranked`).

**Tests** **[run]**: `examples/accept/nested-data-derived.sw` (34 tests: `Packet`, a rose
tree with a parameter, `List (List Table)`, `Option (Chain, Nat)`, `auto`, `rfl`, a
9,000-node value), whose `main` prints the same under `run`, `run --js`, `run --reference` and
`run --native`; `examples/reject/nested-data-derived-vec.sw` (`Vec`, and a user's `Box`).
`==`, `compare` and `${…}` on `Packet`s of 20,000 nodes and a 2,000-deep one take under 0.2 s
under `run` and `run --native`, 0.7 s under `run --reference`. Checking the accept examples
takes the same time as before (about 50 s for the whole folder, one file at a time).

## As built (stage 3)

29 October 2026, SW-704, after D1870 (Matt: stage 3 as in §9, which adopts D1823: `All`
hypotheses primary, the membership form a corollary). In the elaborator only
(`crates/elab/src/derive_induct.rs`, called after the derived instances for every data type
and record); the kernel's rules are unchanged. Labels as above; **[checked]** here means read in
`derive_induct.rs` or `auto.rs` on the stage's branch.

**What is generated**, for a nested type `T` (signatures as the REPL's `:t` prints them **[run]**;
it leaves out the names of binders nothing depends on, and shows `List.Mem q items` as what it
computes to, `List.Any (y => y = q) items`):

- `T.size`, structural: one more than the sizes of the fields that hold `T`, through a helper
  for each container (`T.%m1%size`, …: one more than the sizes of *its* fields that hold `T`).
  For `Packet`: `Packet → Nat`; `Number n` is 1, `Packets items` is `Succ (Packet.%m1%size
  items)`, `Nil` is 1 and `Cons y ys` is `Succ (Packet.size y + Packet.%m1%size ys)`, so
  `Packet.size (Packets [Number 1]) = 4` by `rfl`. With indices, they're implicit: `Ranked.size:
  [i0: Nat] → Ranked i0 → Nat`.
- `T.induct`, one case per constructor (named after it, lower case), taking the constructor's
  fields and then a hypothesis for each field that holds `T` (named after the field,
  `itemsIh`): `motive` of it for a field of type `T`, the container's `All` of the motive for a field inside a container. Nesting composes
  (`List.All (List.All motive) rows`, `Option.All (Pair.All motive (x => Unit)) next`):

  ```
  Packet.induct: (motive: Packet → Prop) → ((value: Nat) → motive (Number value)) →
      ((items: List Packet) → List.All motive items → motive (Packets items)) →
      (x: Packet) → motive x
  ```

  With indices the motive takes them: `Ranked.induct: (motive: (i0: Nat) → Ranked i0 → Prop) →
  motive 0 RLeaf → ((n: Nat) → (kids: List (Ranked n)) → List.All (motive n) kids → motive (Succ
  n) (RNode n kids)) → [i0: Nat] → (x: Ranked i0) → motive i0 x`. It's proved by a helper per
  container (`Packet.%m1%induct: … (x: List Packet) → List.All motive x`, §9's `inductList`),
  defined in one group with `T.induct` **[checked]**.
- `T.inductMem`, only when some field's type is `List T` or `Option T` itself (`T` applied to
  its own parameters): the same, with that field's hypothesis "for every member", and every
  other field's as in `T.induct`. It's `T.induct` with each such case adapted by
  `List.memOfAll` or `Option.memOfAll` **[checked]**:

  ```
  Packet.inductMem: (motive: Packet → Prop) → ((value: Nat) → motive (Number value)) →
      ((items: List Packet) → ((q: Packet) → List.Any (y => y = q) items → motive q) →
          motive (Packets items)) →
      (x: Packet) → motive x
  ```

  For an option the hypothesis is `(q: T) → next = Some q → motive q` **[run]**.
- `D.All` for a container `D` of the program: `Bag.All: [a: Type] → (a → Prop) → Bag a → Prop`
  **[run]**, one predicate for each parameter that is nestable and of type `Type` (`p`, `q`, …,
  at most eight), then `D`'s indices, implicit. By cases: the `And` of the predicates of the
  fields that hold a parameter, `Unit` for none, as `List.All` is written, so `Bag.All p (Many x
  [y])` is proved by `Both px (Both py ())`. It is generated the first time a nested type needs
  it, and named `D.All` only when `D` is declared in the same module, isn't in `Std`, and the
  module has no `D.All` of its own; otherwise it is hidden in the nested type's namespace,
  `T.%D%All` (`Wide.induct` has `Wide.%Vec%All motive kids` **[run]**). Since `D.All` doesn't
  exist until a nested type holding `D` is checked, a declaration that writes `D.All` depends
  on every data type of the module that mentions `D` (`module.rs`, a "speculative"
  dependency), so `bagAll` can be written above `Crate`.
- The size lemmas, for each field `i` of a constructor `C` whose type is `List T` itself:
  `T.%C%i%sizeMem` (`Packet.%Packets%0%sizeMem`, `Rose.%Bloom%1%sizeMem`, the record
  `Node`'s `Node.%%mk%1%sizeMem`). Its statement **[checked]**: given those fields of `C` its
  statement mentions, an element `q` and `h: List.Mem q f`, `T.size q < Succ (the sum of the
  sizes of C's fields that hold T)`, which is what `T.size (C …)` computes to. For `Packet`:

  ```
  Packet.%Packets%0%sizeMem: (items: List Packet) → (q: Packet) → (h: List.Mem q items) →
      Packet.size q < Succ (Packet.%m1%size items)
  ```

  It is proved from the list's own lemma, `Packet.%m1%sizeMem: (q: Packet) → (xs: List
  Packet) → List.Mem q xs → Packet.size q < Packet.%m1%size xs` (by recursion on `xs`), with `Nat.lessLe`,
  `Nat.leAddOfLeLeft` and `Nat.leAddOfLeRight`.

Names with `%` can't be written in source (the parser reads `Packet.%…` as a field access and
stops **[run]**); they're for the compiler. Each user-facing name (`T.size`, `T.induct`,
`T.inductMem`, `D.All`) is skipped when the module declares it itself, and then so is what
depends on it: no `T.size` means no size lemmas, no `T.induct` means no `T.inductMem`. A
module's own `T.size` is used as written (`Own.size OL` evaluates to the module's 7 **[run]**).
All of them are kernel terms (case trees), declared and defined through the kernel, which checks
their types, bodies and the termination of each group; nothing is trusted. If the kernel refuses
one, that's `E-INTERNAL`, "the induction principle generated for `T` was refused", a compiler
bug.

**`auto` and `decreasing T.size`.** When a goal isn't decided by computing, `auto` now also tries
`size_from_member` (`auto.rs`) before `omega`: for each membership fact in scope (a hypothesis
whose type is a call of `List.Mem` or of `List.Any`, what `List.Mem` computes to, or such a
field of a record in scope, as an `attach`ed element's `isIn`), whose element type is a data type `T`, it
tries each `T.%C%i%sizeMem`, all arguments but the membership left to unification with the
fact and the goal, and uses the first one that solves them all **[checked]**. That proves the
obligation of a recursive call on an element of a `List T` field:

```
def Packet.depth (p: Packet): Nat
    decreasing Packet.size p
:=
  match p with
    | Number n => 0
    | Packets items => 1 + (items.attach.map (e => Packet.depth e.value) |> .foldLeft 0 Nat.max)
```

**[run]**, also for a field after others (`TNode (left: List Two) (n: Nat) (right: List Two)`, a
call on an element of `right`), a parameter (`Rose a`), an index (`Ranked`) and a record (`Node`).
It proves an `[auto]` argument the same way: `[auto lt: Packet.size q < Packet.size (Packets
items)]` with `h: List.Mem q items` (or `h: q ∈ items`) in scope **[run]**, also for `Rose a`
and the record `Node` (`examples/accept/nested-data-induction.sw`). At first it didn't
(`E-AUTO-STUCK`, "can't decide `Packet.size q ≤ Packet.%m1%size items`"), and the goal wasn't
the reason: an `[auto]` goal and a `decreasing` one reach `size_from_member` in the same
computed form, `Packet.size q ≤ Packet.%m1%size items` either way **[run]**. The hypothesis
was: its type, as written, is a glued call of `List.Mem`, while `attach`'s `isIn` is stored as
the `List.Any` it computes to, and only `List.Any` was looked for **[checked]**. Now both are
(SW-704 follow-up, D1977).

When `auto` is stuck on such a goal anyway (the membership is in another list,
`examples/reject/nested-data-auto-other-list.sw`), `E-AUTO-STUCK` shows it as it computes,
with the hidden helper, and a note says what that is: "`Packet.%m1%size` is a helper the
compiler generates for `Packet` (part of `Packet.size`, `Packet.induct` or their lemmas); it
can't be written in source" **[run]**. It can't show the goal as written: `Packet.size (Packets
items)` takes its step at once when it is evaluated (its case tree starts on a constructor), so
even the obligation's unforced goal is `Packet.size q < Succ (Packet.%m1%size items)` **[run]**.
Showing `Packet.%m1%size items` in a user-facing form (as `Packet.size (Packets items)` minus
one, say) would be a readback rule in the pretty-printer, not done here.

**Which types get them** **[checked]**: a type of `Type` (not `Prop`, not a higher universe)
that is alone in its group, has at least one constructor, and holds itself, at its own
parameters, inside `List`, `Option`, a pair, or a data type that is alone in its group, in
`Type`, and not nested itself (`Vec`, a user's `Bag`), at any depth (`List (List T)`, `List
(Option T)`, `Option (T, Nat)`), with parameters and indices, and through a container whose
arguments mention earlier fields (`kids: List (Ranked n)`: the helpers then take those fields).
Fields that are erased (proofs) are skipped. Covered by the examples: `Packet`, `Rose a`,
`Nest` (`List (List Nest)` and `Option (Nest, Nat)`), `Sparse` (`List (Option Sparse)`),
`Crate` (`Bag Crate`), `Wide` (`Vec Wide 2`), `Ranked`, the record `Node`, and the shapes in
`nested-data-shapes.sw` and `nested-data-derived.sw` (hash snapshots list what each got).

**Not covered**: nothing is generated, silently, for types defined together (`Expr`/`Stmt`), a
type inside a member of a group (`Big` in `Tree Big`), a container that is nested itself
(`Weird (a) = W (x: a) (ys: List (Weird a))` holding `T`), a field that holds `T` inside a
function's result, at a container parameter that gets no predicate (one that isn't nestable or
isn't of type `Type`: `All (t => Typed t r) bs`), at other parameters than `T`'s own, or in an
index. One exception to "nothing": a `D.All` made for an earlier field stays when a later field
stops generation (with `(bag: Bag T) (w: Weird T)`, `Bag.All` exists and `T.induct` doesn't
**[run]**). `T.inductMem` covers direct `List T` and `Option T` fields only (`Nest`, `Sparse`
and `Crate` get none); the size lemmas `List T` fields only (no `auto` help for `Option T`,
`List (List T)`, `Vec` or a user's container: write the lemma by hand, as
`examples/accept/nested-data.sw` does). Types declared while the core loads get nothing (the
generator returns at once there).

**Library** (in the core, `crates/elab/src/std/core/`, since the generated terms name them):
`List.All`, `List.Any` and `List.Mem` moved there from `List/Toolkit.sw` (so `List.Mem` is
now a core built-in in `crates/core/src/registry.rs`, the stage's only change in `crates/core`);
new are `Option.All`, `Pair.All`, `List.memOfAll` (§9's `List.All.mem`), `Option.memOfAll`
(`ListOptionPair.sw`), `Nat.leAddOfLeLeft` and `Nat.leAddOfLeRight` (`Division.sw`). The
generator finds them by name; without them it generates nothing.

**Tests** **[run]**: `examples/accept/nested-data-induction.sw` (3 tests; proofs by
`Packet.induct`, `Packet.inductMem`, `Rose.inductMem`, `Ranked.induct`; the statements of
`Nest.induct`, `Sparse.induct`, `Crate.induct` written out and checked; `Bag.All`; recursion
by `attach` under `decreasing T.size` for `Packet`, `Rose`, `Ranked` and `Node`), whose `main`
prints the same under `run`, `run --js`, `run --reference` and `run --native`;
`examples/accept/nested-data.sw` gains `depth`, the same recursion beside its hand-written
lemma. Hash snapshots: only the nested examples' and the prelude's changed (their new
declarations); no other example's snapshot changed.

**Cost** **[run]**, 29-30 October, release builds of this branch and of `main` (6a3f4b19), runs
alternated, min/median of three. The whole std, loaded eagerly with no cache (`Session::eager`,
from a scratch binary): 4.40/4.45 s, `main` 4.39/4.43 s (load average 7-8). Every file of `main`'s
`examples/accept` (316), `check --no-cache` one at a time: 98.2/98.5 s, `main` 96.4/96.6 s,
2% more, none failing (load average 4-7). `aoc`, `check --no-cache`, CPU time (user + system;
the machine slept during some runs, so wall times were unusable): 33.0/33.1 s, `main`
32.9/33.3 s; runs without a sleep took 33-35 s wall either way, peak memory 1.39 GB either way.

## Sources

Read in full unless marked otherwise.

- [P1] T. Lamiaux, Y. Forster, M. Sozeau, N. Tabareau, "Nested Inductive Types: Justified and
  Usable Nested Inductive Types in Lean and Rocq", PACMPL 10 (PLDI 2026) 1891–1914,
  doi:10.1145/3808322 (bibliographic data from pldb). Read: the preprint, HAL hal-05366368v1
  (November 2025), from the Internet Archive's copy of
  https://hal.science/hal-05366368v1/file/main.pdf. Not accessible: the ACM version (403), HAL
  directly (connection refused), hal-05366368v2 (bot check).
- [R4] MetaRocq, nested-eliminators, https://github.com/MetaRocq/nested-eliminators, commit
  `f9ca941` (24 April 2026): `README.md`; `formalization/Positivity_condition.v` (all);
  `formalization/Nested_to_mutual.v` (lines 1-80, `nested_to_mutual` at 352);
  `formalization/Nested_to_mutual_proof.v` (lines 1195-1431: assumptions and the theorem, not the
  proof); `theories/Preprocess/strictly_positive_uniform_parameters.v` (all).
- [R1] Rocq 9.3.0 reference manual, "Inductive types and recursive functions": "Positivity
  Condition", "Strict positivity", "Nested Positivity":
  https://rocq-prover.org/doc/V9.3.0/refman/language/core/inductive.html (those sections).
- [R2] Rocq 9.3.0 reference manual, "Reasoning with inductive types", "Eliminators for Nested
  Inductive Types" (`Scheme All`, `prod_all`, `LeftTree`, `trie` over `array`):
  https://rocq-prover.org/doc/V9.3.0/refman/proofs/writing-proofs/reasoning-inductives.html (that
  section).
- [L1] Lean language reference, Inductive types, "Nested Inductive Types":
  https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/ (that section, read
  for draft 1).
- [L4] Lean 4 kernel, `src/kernel/inductive.cpp`, master at `400f83a` (29 October 2026):
  `is_nested_inductive_app`, `replace_if_nested`, `elim_only_at_universe_zero` (lines 505-580,
  1005-1100).
- [A1] Agda documentation, Positivity checking:
  https://agda.readthedocs.io/en/latest/language/positivity-checking.html (read for draft 1).
- Draft 1's other sources (Lean recursive definitions [L2, L3], Rocq guard checker [R3, R6],
  Agda polarity and termination [A2, A3]) are still the basis of option C and the `decreasing`
  material; see draft 1 in git history (`e2297587`).
- Stitchwort at `9a6a3d84`: `crates/core/src/check.rs`, `term.rs`, `termination.rs`;
  `docs/core.md`; `DESIGN.md` §13; `crates/elab/src/std/core/{Data,Logic,Effect}.sw`,
  `List/Toolkit.sw`, `Logic/Logic.sw`, `Map/Map.sw`, `Vec/Vec.sw`.
