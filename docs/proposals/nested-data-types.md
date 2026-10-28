# Proposal: nested data types, `Packets (items: List Packet)`

**Status:** draft 1, 28 October 2026, for review. Ticket SW-829 (from SW-704). No decisions are
taken here; the [open questions](#9-open-questions) are for Matt. Related:
[mutual-recursion.md](mutual-recursion.md) (data groups, size-change termination; it set nested
types aside as "a later step"), [well-founded-recursion.md](well-founded-recursion.md)
(`decreasing`, `List.attach`, congruence lemmas), [parser-combinators.md](parser-combinators.md)
§5.3 (the `recursive` combinator, which today can only sum a packet, not build one),
[map-equality.md](map-equality.md) (why nesting through a quotient is refused).

**The short answer.** Let a data type contain itself inside an *already defined* data type, such
as `List`, `Option`, a tuple or `Vec`, when that type only ever *stores* its parameter (never
takes it as a function's input, never uses it as an index). The kernel checks this by looking
inside the outer type's constructors with the parameter filled in, exactly as Rocq's kernel
does. Nothing else in the kernel changes: the termination checker already treats "a field of a
matched constructor" as smaller whatever its type, so a list of packets inside a packet, and a
packet inside that list, are already smaller. A prototype of the relaxed check (a scratch patch,
not committed) accepted the Packet type, and with it, unchanged: structural recursion through a
helper over the list, proofs by mutual induction, recursion through `items.attach.map` with
`decreasing`, day 13's comparison, `rfl` on a `decreasing` function over packets, and the same
output under `run`, `run --js` and `run --reference` **[run]**. Then, in later stages, the
compiler generates what Lean generates: `==`/`<`/`${…}` for such types, a size function, and an
induction principle whose hypothesis is "the property holds for every member of `items`".

This note can be read without knowing type theory. Labels, as in the other notes:

- **[checked]**: read in the Stitchwort source or docs at the `file:line` given (commit
  `39c6f838`), or in a source listed at the end ([L1], [R1] and so on), read in full unless
  marked otherwise;
- **[run]**: a Stitchwort or Lean program run on 28 October 2026 (Stitchwort's release CLI at
  `39c6f838`, with the scratch patch where stated; Lean 4.34.1 from nixpkgs). The programs are
  scratch files, not committed; each is quoted where it's used;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, not confirmed.

## Contents

- [1. The problem](#1-the-problem)
- [2. Words this note uses](#2-words-this-note-uses)
- [3. How Stitchwort checks data types and recursion today](#3-how-stitchwort-checks-data-types-and-recursion-today)
- [4. How others do it](#4-how-others-do-it)
- [5. What we ran](#5-what-we-ran)
- [6. Options](#6-options)
- [7. Recommendation: option A, in detail](#7-recommendation-option-a-in-detail)
- [8. Stages](#8-stages)
- [9. Open questions](#9-open-questions)
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
 6 │   | Packets (items: List Packet)
   │                     ╰─────── field `items` has `Packet` inside another type
   │ Note 1: a data type's fields can contain it only directly, or as the result of a function
   │ field: whether it's safe inside another type (such as a `List`) would depend on how that
   │ type uses it, which isn't checked
   │ Note 2: for a tree whose children are in a list, write two types defined together instead:
   │ a tree, and a forest of trees
```

The suggested workaround, a `Tree` and a `Forest` defined together (`examples/accept/mutual-data.sw`
**[checked]**), works, but the forest is a second list type: none of `List`'s functions
(`map`, `sum`, `zip`, `sort`, `attach`) or theorems apply to it, and every one a program needs
has to be written again for `Forest`. The same shape comes up in 2021 day 18 (snailfish
numbers, pairs of pairs), in expression trees, JSON-like values, file-system trees (2022 day 7),
and in whatever a recursive `{Parse}` grammar produces: parser-combinators.md §5.3 says its
example "sums the numbers because `type Packet = … | Packets (items: List Packet)` is refused"
**[checked]**.

What users want to write, in order of how often:

1. **The type itself**, with a real `List` inside.
2. **Functions using the library**: `items.map (q => depth q)`, `items.sum`, `List.zip`, a
   comparison that walks two lists of packets together.
3. **Proofs by induction**, where the step for `Packets items` may assume the property for every
   packet in `items`.
4. **`==`, `<` and `${p}`** derived, as for every other type.

## 2. Words this note uses

- **Nested occurrence.** The type being defined appears as an argument of another type in a
  field: `List Packet`. `Packet` is *nested* in `List`; `List` is the *outer type*.
- **Strictly positive.** A type occurs strictly positively in a field if it never appears to the
  left of an arrow (as a function's input). `Bad (f: Bad -> Nat)` is not strictly positive, and
  would let a program loop forever and prove anything (mutual-recursion.md §3 lists the bugs
  that came from getting this wrong).
- **Parameter that's only stored.** `List (a: Type)` uses `a` only as the type of a field
  (`head: a`) and in `List a` itself. A type like `type Neg (a: Type) = | MkNeg (consume: a -> Nat)`
  uses `a` as a function's input. Agda calls the first kind of parameter *strictly positive*
  (`@++`), Rocq a *nestable* uniform parameter. Nesting is safe exactly through stored
  parameters.
- **Size-change termination (SCT).** Stitchwort's termination check: every recursive call is
  summarised by which arguments got smaller than which parameters, and every way of repeating
  the calls must make something smaller (mutual-recursion.md §3).
- **Recursor / eliminator.** In Lean and Rocq, the built-in "induction principle" a data type
  comes with. Stitchwort has none: functions and proofs are case trees plus the termination
  check (`docs/core.md`) **[checked]**.

## 3. How Stitchwort checks data types and recursion today

**Positivity** (`crates/core/src/check.rs`). Each field type of each constructor of a data group
goes through `not_positive` (called at `check.rs:2149`, defined at `:2483`) **[checked]**. It
allows a group member only as itself applied to the group's own parameters (and indices that
mention no member), possibly as the result of a function field whose inputs mention no member.
Anything else is an `Occurrence`: `Input` (left of an arrow), `OtherParameters`, `InIndex`, or
`Inside`, the catch-all that `List Packet` falls into (`:2576`, the message above). The error
note already anticipates this note: "whether it's safe inside another type … would depend on how
that type uses it, which isn't checked".

Two other guards matter here and stay as they are:

- **Declared later** (`declared_later`, used at `check.rs:2121-2136`): a field may only mention
  declarations made before the group, so a definition can't hide an occurrence. So the outer type
  (`List`) is always final and fully known when a nested type is checked **[checked]**.
- **No constructors or `case` of the group in fields** (`admissible`, `Itself::DataGroup`): a
  later field can't compute anything from a packet, because nothing that inspects a packet exists
  yet **[checked]**.

**Termination** (`crates/core/src/termination.rs`, `docs/core.md:202`). The rule that decides
this note: "A field of a constructor matched out of a parameter is smaller than it, **whatever its
type**, so `size (Node n kids) = Succ (sizeForest kids)` is a smaller call" **[checked]**. The
order is "is a part of", across types, and transitive through further matches
(`termination.rs:20-24`). So in `size (Packets items)`, `items` is smaller than the packet, and
in a helper that matches `items` as `Cons p rest`, `p` is smaller still. Nothing about this
needs to know that `items` is a `List`.

What termination does *not* accept: "Every occurrence of a member is a call … under lambdas …
Occurrences of members must be saturated" (`termination.rs:42-50`) **[checked]**. In
`items.map (q => depth q)`, `q` is a lambda's variable, so nothing is known about its size, and
the call is refused (shown in §5). That is the job of `decreasing` with `List.attach`
(well-founded-recursion.md stage 3a/3b, built) **[checked]**.

**Derived instances.** `==` (`DecEq`), `<` (`Ord`) and `Show` are derived for every declared
type, except "the type is used inside another type of its own fields" (`docs/syntax.md:619`;
`crates/elab/src/derive.rs:336`, `derive_show.rs:160`) **[checked]**. The derivers already have
an error for this case, which is what a nested type gets until they learn it (§5).

**Quotients.** `Map` and `Set` are records over a quotient (`std/Map/Map.sw:22`: `{ raw: Quot
(Map.Raw k v [ord := ord]) Map.Raw.Equiv }`) **[checked]**. A recursive occurrence inside a
quotient has its own error (`crates/elab/src/quot.rs:401-470`, R10: "data types can't be
recursive through a quotient yet") **[checked]**, and stays refused under every option here (§7.1).

**Runtimes.** The JS boundary codec relies on "a data type's fields can only mention it, and the
types defined together with it, applied to their own parameters (the positivity check) … so a
boundary type has finitely many types inside it" (`crates/js/src/lib.rs:1244-1251`)
**[checked]**. A nested occurrence is still the type applied to its own parameters, so the set
stays finite **[inferred]**; the comment needs a word changed.

## 4. How others do it

### 4.1 Lean 4: translate to a mutual group, inside the kernel

The reference manual [L1, §4.4.5.4 "Nested Inductive Types"]:

> "Nested inductive types that satisfy certain requirements can be translated into mutual
> inductive types; this translation demonstrates that they are sound. Internally, the kernel
> performs this translation; if it succeeds, then the original nested inductive type is accepted.
> This avoids performance and usability issues that would arise from details of the translation
> surfacing."

The requirements it lists: occurrences "must be nested directly under an inductive type's type
constructor. Terms that reduce to such nested occurrences are not accepted" (so `abbrev Children
:= List` fails); "Local variables such as the constructor's parameters may not occur in the
arguments to the nested occurrence"; "The nested occurrences must occur strictly positively";
"Constructor parameters whose types include nested occurrences may not be used in ways that rely
on the specific choice of outer type constructor"; and "Nested occurrences may not be used as
parameters to the outer type constructor that occur in the types of the outer type's indices."

The translation: "Nested occurrences of the inductive type are translated into new inductive
types in the same mutual group … These new inductive types have the same constructors as the
outer inductive type, except the original parameters are instantiated by the translated version
of the type", repeated "if the resulting type is also a nested inductive type (e.g. a type nested
under Array becomes a type nested under List …)". Conversions both ways are generated and
"proved to be mutual inverses", and "The recursor for the nested inductive type is constructed
from the recursor for the translated type." Lean's kernel source agrees: `elim_nested_inductive_fn`
creates "an auxiliary type `Iaux` in the (mutual) inductive declaration" for each nested
occurrence `I Ds is`, and afterwards `restore_nested` puts the real `I Ds` back
(`src/kernel/inductive.cpp:966-1039`) [L4]. Note what this means for positivity: Lean has no
separate "how does `List` use its parameter" analysis. Copying `List`'s constructors into the
group, with `Packet` for `a`, and running the ordinary mutual positivity check on the copy *is*
that analysis; a bad use (`check (f : Option WithCheck → Bool)`) fails the ordinary check
[L1].

One consequence is visible to users: a later field may not apply a `List`-specific function to
the nested field. The manual's `BRTree` (`children.length < branches`) is refused with "argument
has type `_nested.List_1` but function has type `List (BRTree branches α) → Nat`", because "a
translation of List.length to the translated types" would be needed [L1].

**The recursor** has a second motive for the list [run]:

```
@Packet.rec : {motive_1 : Packet → Sort u_1} → {motive_2 : List Packet → Sort u_1} →
  ((value : Nat) → motive_1 (Packet.number value)) →
  ((items : List Packet) → motive_2 items → motive_1 (Packet.packets items)) →
  motive_2 [] →
  ((head : Packet) → (tail : List Packet) → motive_1 head → motive_2 tail → motive_2 (head :: tail)) →
  (t : Packet) → motive_1 t
'Packet.rec' does not depend on any axioms
```

**Structural recursion** over nested types arrived with mutual structural recursion in Lean
4.11: "This feature supports both mutual recursion over a non-mutual data type, as well as
recursion over mutual or nested data types", with the example `Tree.size`/`Tree.list_size` over
`inductive Tree where | node : List Tree → Tree` [L2]. The manual's rule: "All the types of all
the decreasing arguments must be from the same inductive type, or more generally from the same
mutual group" [L3, §7.6.2.2] (the group includes the auxiliary `List Tree`).

**Recursion through `map`** is well-founded recursion. Every inductive type gets a `SizeOf`
instance ("For inductive types, a SizeOf instance is automatically derived by Lean"), and the
elaborator rewrites `xs.map f` on a parameter into `xs.attach.unattach.map f` so that `f`
sees `x ∈ xs` (`wfParam`, the `wf_preprocess` simp set; "This feature requires special setup
for the higher-order function under which the recursive call is nested") [L3, §7.6.3]. The
default `decreasing_tactic` knows `sizeOf_list_dec`, "that the size of list elements is less
than the size of the list" [L3]. The manual's worked example is exactly this case for a custom
container (a `Pair`): a membership predicate, "a theorem that relates the size of a member to the
size of the containing pair", `attach`/`unattach`, two `wf_preprocess` rules and a
`decreasing_trivial` extension [L3]. What we ran **[run]**:

```
def Packet.depth : Packet → Nat
  | .number _ => 0
  | .packets items => 1 + (items.map Packet.depth).foldl max 0
```

is accepted with no annotation, and `#eval` gives 2 on `[1,[2]]`; but `by decide` and `rfl` on
the same fact fail ("reduction got stuck"), and `#print axioms Packet.depth` says `[propext,
Quot.sound]`. The size facts it used: `Packet.packets.sizeOf_spec : sizeOf (Packet.packets items)
= 1 + sizeOf items` and `List.sizeOf_lt_of_mem : a ∈ as → sizeOf a < sizeOf as`.

**Induction.** The plain tactic refuses nested types **[run]**: "The `induction` tactic does not
support the type `Packet` because it is a nested inductive type. Hint: Consider using the `cases`
tactic instead". Functional induction does work, and gives the hypothesis users want **[run]**:

```
Packet.depth.induct : ∀ (motive : Packet → Prop),
  (∀ (value : Nat), motive (Packet.number value)) →
    (∀ (items : List Packet), (∀ (x : Packet), x ∈ items → motive x) → motive (Packet.packets items)) →
      ∀ (a : Packet), motive a
```

**Day 13's comparison**, written as most solutions write it (a number against a list is
compared as a one-element list), is refused **[run]**: "Could not find a decreasing measure",
with the call `compareList [number a] ys` failing every structural candidate. Rewritten with a
separate number-against-list helper, Lean's structural recursion still refuses it ("Skipping
arguments of type List Packet, as Packet.cmp has no compatible argument") because each function
must pick one decreasing parameter of the group's types, and the helper's is its second.

### 4.2 Rocq: a nested positivity rule, guard checking that looks inside `map`

**Positivity** [R1, "Positivity Condition", "Strict positivity", "Nested Positivity"]. The
constants occur strictly positively in `T` when, among other cases, "`T` converts to `(I a_1 …
a_r t_1 … t_s)` where `I` is the name of an inductive definition … (in particular, it is not
mutually defined and it has r parameters) and no `X_1 … X_k` occur in any of the `t_i` nor in
any of the `a_j` for `m < j ≤ r` where `m ≤ r` is the number of recursively uniform parameters,
and the (instantiated) types of constructor `C_i{p_j/a_j}` of `I` satisfy the nested positivity
condition". So Rocq does not translate anything: it *substitutes* the arguments into the outer
type's constructors and checks those. Within that check, an occurrence of the outer type itself
is fine as long as the nested types don't appear in its indices or non-uniform parameters (the
first bullet of "Nested Positivity"), which is what stops the check expanding forever.

**Recursion.** A fixpoint's recursive call must be on a subterm of the decreasing argument
[R1, "Fixpoint"]. Recursing through `map` used to need a local copy of `map` written with its
function "lambda-dropped" (a `fix` inside a `fun f`), because "The natural definition of
`List.map` with a `Fixpoint` doesn't pass the guard condition" (Rocq issue #16040, with the
`tree`/`lmap` example) [R3]. Since PR #17986, merged 7 May 2024, the guard checker "computes the
parameters of inner fixpoints that are stable across recursive calls and extrudes them for the
computation of guard through these inner fixpoints" [R3]: it looks *inside* `map`'s definition
and sees that the function passed in is only ever applied to parts of the list. That is a
change to the trusted kernel, made after decades of users asking.

**Induction principles.** Until recently Rocq generated no useful induction principle for nested
types; Rocq 9.2 adds one [R2, "Eliminators for Nested Inductive Types"]: "When generating
eliminators for a predicate P, if an argument is nested with reference, the All predicate and
its theorem will be looked up … and used to enforce P holds on the nested argument", and "If they
are not registered, no induction hypothesis is created for the nested argument." `Scheme All for
prod` generates `prod_all` (the property holds of both components) and `prod_all_forall`; the
resulting `LeftTree_ind` has the hypothesis `prod_all (LeftTree A) P nat (fun _ => unit) p -> P
(Lnode A p)` [R2]. This comes from the MetaRocq `nested-eliminators` project, whose README
claims a "New positivity condition for nested inductive types, and proof that any positive nested
inductive type has a mutual encoding", and says "The plugin has been adapted and merged into
Rocq, and is part of Rocq 9.2" [R4]. The accompanying talk, "Nested Inductive Types for Rocq and
Lean" (Lamiaux, Forster, Sozeau, Tabareau, RocqPL 2026): "neither Rocq nor Lean currently
provides adequate support for them, both positivity and generation of elimination principles
being insufficient", and "we introduce a new positivity condition for nested inductive type that
is neither too lax nor too strict" [R5, abstract only: I found no public full text].

The guard checker itself is acknowledged to be intricate: "All the mentioned features like
mutuality and nesting introduce mostly orthogonal complexity in the definition of Rocq's guard
checker, which is defined in the kernel/inductive.ml file of Rocq's code in about 1000 lines of
OCaml code", with a history of relaxations and restrictions (2012, 2014, 2022, 2024) [R6].

### 4.3 Agda: polarity of parameters

Agda's positivity checker "analyses how functions use their arguments. For instance, Agda can
tell that D in the following code is strictly positive, because Vec uses its Set argument in a
strictly positive way" [A1]; the example nests `D` in a `Vec` defined by a *function* (`Vec A
(suc n) = A × Vec A n`). An alternative is to write the polarity: `data _×_ (@++ A B : Set)`,
where `@++` means "Anywhere except in the domain of a pi/function type" [A1, A2]. The
documentation's warning is the lesson for us: a polarity that is *declared* rather than checked
can prove `⊥`. Its example postulates `_⇒_` with `{-# POLARITY _⇒_ ++ #-}`, defines `data D :
Set where c : D ⇒ ⊥ → D`, and derives `bad : ⊥`; "Polarity pragmas are not allowed in safe
mode" [A1]. mutual-recursion.md §3 records Idris 2 #1771, `Fix f = MkFix (f (Fix f))` with a
negative `f`, looping under `%default total` "because nested occurrences were allowed without
checking how the outer type uses its parameter" **[checked]**.

Agda's termination page describes structural recursion on subterms and the call-matrix method
("Foetus") [A3]; it says nothing specific about recursion through `map`, and I didn't test it
**[unverified]**.

### 4.4 What to take

| | Lean 4 | Rocq | Agda |
|---|---|---|---|
| Is the outer type's use of its parameter checked? | yes: by translating and running the mutual check | yes: by substituting into its constructors | yes: occurrence analysis, or `@++` annotations |
| Outer type defined by a function (`abbrev`, Agda's `Vec`)? | no | only if it *converts* to an inductive | yes |
| Structural recursion through a helper over the list | yes, since 4.11 | yes (mutual `fix`) | yes |
| Recursion through `map` | well-founded: `sizeOf` + automatic `attach`; doesn't compute in `rfl`/`decide` | structural, the guard looks inside `map` (since 2024) | [unverified] |
| Induction hypothesis "for every member" | functional induction (`f.induct`); plain `induction` refuses | `Scheme All` (Rocq 9.2) | by hand |

## 5. What we ran

A scratch patch to `not_positive` (an extra arm: a member inside any argument of another data
type is checked recursively, with **no** check of how that type uses its parameter; behind an
environment variable, never committed) to see what else would break. The programs:

```
type Packet: Type =
  | Number (value: Nat)
  | Packets (items: List Packet)

def Packet.size: Packet → Nat
  | Number n => 1
  | Packets items => 1 + Packet.sizeList items

def Packet.sizeList: List Packet → Nat
  | Nil => 0
  | Cons p rest => Packet.size p + Packet.sizeList rest

def sample: Packet := Packets [Number 1, Packets [Number 2, Number 3], Packets []]
theorem sizeSample: Packet.size sample = 6 := rfl
```

**Accepted with no other change [run]:**

1. **The type**, and `size`/`sizeList` (structural, a mutual pair, as for Tree/Forest).
2. **Proofs by mutual induction**: `Packet.numbersLe: (p: Packet) → Packet.numbers p ≤
   Packet.size p` with its list twin `numbersListLe`, each arm closed by `omega` with the other's
   result in a `let`.
3. **A membership lemma**: `Packet.memLe (q): (items: List Packet) → List.Mem q items →
   Packet.size q ≤ Packet.sizeList items`, by structural recursion on `items`.
4. **Recursion through `map`**, with `decreasing` and `attach`; `auto` finds the obligation by
   `omega` from the lemma in scope:

   ```
   def Packet.depth (p: Packet): Nat
       decreasing Packet.size p
   :=
     match p with
       | Number n => 0
       | Packets items =>
         1 + (items.attach.map (e =>
           let below := Packet.memLe e.value items e.isIn
           Packet.depth e.value) |> .foldLeft 0 Nat.max)

   theorem depthSample: Packet.depth sample = 2 := rfl
   theorem depthStep (items: List Packet): Packet.depth (Packets items) = 1 + (items.attach.map (e => Packet.depth e.value) |> .foldLeft 0 Nat.max) :=
     Packet.depth.unfold (Packets items)
   ```

   Unlike Lean's, this one computes in `rfl` (well-founded-recursion.md's design reason for
   proof-carrying fuel).
5. **Day 13's comparison**, as three structural functions: `cmp` (packet against packet),
   `cmpList` (list against list, calling `cmp` on the heads), and `cmpNumberList`/`cmpNumber` (a
   number against a list or a packet, so that the "wrap the number in a list" case never calls
   `cmp` on a rebuilt packet). Both of the puzzle's sample comparisons give `Less`.
6. **The induction principle Lean generates, written by hand** and accepted by the ordinary
   termination check: the recursive call is on a field (`items`), and the lambda's own variables
   are only passed along:

   ```
   theorem Packet.induct (motive: Packet → Prop)
       (number: (n: Nat) → motive (Number n))
       (packets: (items: List Packet) → ((q: Packet) → List.Mem q items → motive q) → motive (Packets items)):
       (p: Packet) → motive p
     | Number n => number n
     | Packets items => packets items (q h => Packet.inductList motive number packets items q h)

   -- (`number` and `packets` as above; shortened here)
   theorem Packet.inductList (motive: Packet → Prop) (number: …) (packets: …):
       (items: List Packet) → (q: Packet) → List.Mem q items → motive q
     | Nil, q, h => Void.exfalso h
     | Cons p rest, q, Inl e => rewrite <- e in Packet.induct motive number packets p
     | Cons p rest, q, Inr h => Packet.inductList motive number packets rest q h
   ```

   and used: `Packet.induct (p => Packet.numbers p ≤ Packet.size p) (n => omega) (items ih => …)`.
7. **Tests and runtimes**: `stitchwort test` passes all four tests; `main` prints `size: 6`,
   `depth: 2`, `numbers: 3` identically under `run`, `run --js` and `run --reference`.

**Refused, as expected [run]:**

- **Recursion through `map` without `decreasing`**: `| Packets items => 1 + (items.map (q =>
  Packet.count q) |> .sum)` is `E-TERMINATION`, "the 1st argument, `q`, isn't seen as smaller".
- **Day 13 written the usual way** (a number against a list calls `cmp (Number a) y` again):
  `E-TERMINATION`, "going round `Packet.cmp` → `Packet.cmpNumberList` → `Packet.cmp` → …, no
  argument is known to get smaller". It does terminate (the total size goes down), so it needs
  `decreasing`, or the shape in item 5. Lean refuses the same program (§4.1).
- **Derived instances**: `sample == sample` is `E-INSTANCE-NONE`, "`==` isn't derived for
  `Packet`: the field `items` of `Packets` contains `Packet` inside another type, which `==`
  isn't derived for yet"; `"${sample}"` the same for `Show`.

**Accepted by the prototype, and must not be [run]:**

```
type Neg (a: Type): Type =
  | MkNeg (consume: a → Nat)

type Bad: Type =
  | B (inside: Neg Bad)
```

`Neg` uses its parameter as a function's input, so `Bad` hides a negative occurrence, the
Idris #1771 shape. The prototype checks it; `main` refuses it (`E-POSITIVITY`). This is why the
real rule must look inside the outer type (§7.1).

## 6. Options

### Option A: a nested positivity check in the kernel (Rocq's rule)

`not_positive` gains one case: a member may appear inside `D args`, where `D` is an earlier,
final data type (not a quotient, not a primitive like `Effect.Delay`), if the arguments that
mention a member are in parameter positions of `D` (never indices), and `D`'s constructor fields,
with those arguments substituted for `D`'s parameters, pass the same check. Everything else in
the kernel stays.

- **Kernel changes.** About 100 lines in `check.rs`: the new case, the substitution of arguments
  into `D`'s field types (the kernel already instantiates constructor types when it checks a
  `Ctor` or a `Case` **[inferred; not located in the source]**), a guard so that `D`'s own recursive occurrence (`tail: List a`) isn't
  expanded again, and new error messages. No change to termination, conversion, evaluation,
  hashing or erasure **[inferred from §3, and §5's run]**.
- **Soundness argument.** Two parts. (1) *The type exists*: every type the rule accepts has a
  translation into a mutual group the kernel already accepts, made by copying the outer type's
  constructors into the group with the parameter replaced, as Lean's kernel does [L1, L4], and
  the values of the two correspond one to one. The rule's recursive check on the substituted
  fields is exactly the ordinary group check run on that copy, so it accepts exactly the types
  whose translation the existing check accepts **[inferred]**. The nested-eliminators project
  claims a mechanised proof that "any positive nested inductive type has a mutual encoding" for
  its (Rocq-style) condition [R4] (I haven't read the proof). (2) *Termination stays sound*: the
  SCT order is "is a part of a value", and the parts of a `Packet` in the nested form are
  exactly the parts of the corresponding value in the mutual form, list cells included, so any
  call sequence that descends forever in one descends forever in the other **[inferred]**.
  Tree/Forest is already accepted on that basis (`docs/core.md:202`).
- **Recursion through `items.map (p => f p)`.** Not by the termination check (§5). Three
  routes, all available on day one: a helper over the list (structural, no proof); `decreasing`
  with a size and `List.attach` (needs a size function and its membership lemma, §5 items 3-4);
  or the guard style. Stage 3 generates the size and the lemma so the second route needs no
  user proof.
- **Proofs by induction.** Mutual theorems, as for Tree/Forest (§5 item 2), or a generated
  `T.induct` with "for every member of `items`" (§5 item 6), or `decreasing` on a theorem.
- **Runtime, JS, native.** No change to representation: a packet's `items` is an ordinary list
  value **[run: `run`, `--js`, `--reference`]**. Native code was not run **[unverified]**; it
  uses the same erased program as `run` **[inferred]**. The JS codec's finiteness comment holds
  (§3); exporting a nested type across the boundary wasn't tried.
- **Effort.** Kernel stage small to medium (the check, messages, docs, about 15 accept/reject
  examples). Derivers medium. Generated size/induction medium.

### Option B: translate to a mutual group (Lean's approach)

Two variants.

- **B1, in the elaborator, visible to users.** `List Packet` becomes a generated
  `Packet.List` type. This *is* today's Tree/Forest workaround, generated: `items.map` and the
  `List` library don't apply to it, which is the whole point of the request. Not useful.
- **B2, in the kernel, for checking only** (what Lean's kernel does). The kernel builds the
  auxiliary group, checks it, and keeps the real `List` in the accepted type. In Lean the
  translation earns its keep because the kernel then derives the *recursor* from the translated
  one [L1]. Stitchwort's kernel has no recursors: after the check, the auxiliary group would be
  thrown away. So B2 is option A with a more roundabout implementation of the same check (build
  types, admit them, discard them) **[inferred]**, and it would inherit Lean's restriction that
  no later field may apply a list function to the nested field (§4.1, `BRTree`).
- **Its real use here: a test oracle.** For every nested type in the tests, a test can build the
  translated group, admit it with the existing kernel, and check that A accepts exactly the
  types whose translation is accepted (a cheap, independent check of A's code).

### Option C: let the termination check look inside `map` (Rocq since 2024)

When a member is passed to a known structural function over a list (`List.map`, `sumBy`, …), the
termination check would inline that function and see that the callback is only applied to
elements of the list. `items.map (q => depth q)` would then pass without `decreasing`.

- **Kernel:** a substantial change to trusted code that mutual-recursion.md §3 lists bugs in
  (Rocq's own history of guard relaxations and fixes [R6]), and it interacts with
  `case_only_in_tree` and lifted matches. **Effort:** large.
- **Gain:** one annotation saved in a pattern that `decreasing` already covers and stage 3 makes
  annotation-free in the common case. Not now; reconsider if AoC ports show many `decreasing`
  clauses whose only purpose is this.

### Option D: sized types

Rejected for the reasons in well-founded-recursion.md §5(D): Agda's sized types are not allowed
with `--safe` because of soundness bugs, and sizes would show in every signature. Nothing here
changes that.

### Option E: keep refusing, improve the workaround

Generate `Forest`-style twins plus conversions to and from `List`. Every use pays a conversion,
and proofs must move facts across it. Strictly worse than A.

### Side by side

| | A: nested positivity | B2: kernel translation | C: guard through `map` | E: generated twins |
|---|---|---|---|---|
| `items: List Packet` is a real `List` | **yes** | yes | needs A or B2 | no |
| Kernel change | **one case in positivity** | larger: build, check, discard | large, in termination | none |
| `items.map (q => f q)` | `decreasing` + `attach` (stage 3: automatic) | same | **structural** | n/a |
| `rfl`/`test` on such functions | **yes** [run] | yes | yes | yes |
| Induction "for every member" | generated `T.induct` (stage 3) | same | same | per twin |
| Runtimes | unchanged [run] | unchanged | unchanged | conversions |
| Effort | **small-medium** | medium | large | medium, no gain |

## 7. Recommendation: option A, in detail

### 7.1 The rule

In a field of a data group, a member may occur:

1. directly, applied to the group's own parameters, then to indices that mention no member (as
   today);
2. as the result of a function field whose inputs mention no member (as today);
3. **new:** inside `D a₁ … aᵣ t₁ … tₛ`, where
   - `D` is a data type declared before the group and final (the "declared later" guard
     already ensures this), and is *not* a record or type with a quotient field (`Map`, `Set`) and
     not a primitive (`Effect.Delay`): those keep today's refusal and messages;
   - no member occurs in the indices `t₁ … tₛ` (Lean: nested occurrences "may not be used as
     parameters … that occur in the types of the outer type's indices"; Rocq: none in the `t_i`);
   - no member occurs in a parameter `aⱼ` whose position appears in the type of a later
     parameter or of an index of `D` (`List.Member (a) (xs: List a)`: `a` can't be nested
     through), nor in an `auto` dictionary parameter's position (so `Map`'s `k` is excluded twice
     over);
   - every field type of every constructor of `D`, with `a₁ … aᵣ` substituted for `D`'s
     parameters, passes this same check for the group, where `D`'s own occurrence applied to the
     same arguments counts as direct (so `tail: List Packet` in `List`'s `Cons` is fine and isn't
     expanded again), and `D`'s constructor result indices mention no member.

   Each argument that mentions a member must itself be an allowed occurrence (so `List (List
   Packet)`, `Option (Packet, Nat)` and `Vec Packet n` are fine; `List (Packet → Nat)` is not).

Because `D` is always declared earlier, the check only ever looks at earlier types, and the
"counts as direct" case stops it re-expanding `D` inside itself, so it ends **[inferred]**
(nested-eliminators makes the same argument for its formalisation: "a nested inductive type can
only refer to previously defined inductive types" [R4]). A computed type in a field (a `def`
that unfolds to `List Packet`, a `match` in a type) stays refused, as in Lean ("Terms that reduce
to such nested occurrences are not accepted" [L1]); the declared-later guard means such a `def`
couldn't mention `Packet` anyway, only a type variable, so this only loses aliases like
`Children := List`.

What stays exactly as it is: occurrences left of an arrow, other parameters, member constructors
or `case` in fields, universes (`List Packet` is in `Type` like `Packet`), `Prop` elimination
rules (a `Prop` can't contain a `List` of itself: the field would be in `Type`, `E-UNIVERSE`),
and the termination check. A function field returning a *nested* type (`children: Nat → List
Tree`) isn't a recursive function field for termination (`termination.rs:24-30` only counts
fields returning a member itself); that is conservative and can stay **[inferred]**.

A cached "which parameters of `D` can be nested through" table per data type is an optimisation
of the same rule, not a different rule; it would also make the error message easy to write. The
error for a refused nested occurrence should name the field of `D` that breaks it: "`Packet` is
used inside `Neg`, and `Neg`'s field `consume` takes its parameter `a` as a function's input".

### 7.2 What users write

```
type Packet: Type =
  | Number (value: Nat)
  | Packets (items: List Packet)
```

**Functions.** With a helper over the list (structural), or with `decreasing` and `attach` (§5).
After stage 3 the size measure and its membership lemma are generated, so

```
def Packet.depth (p: Packet): Nat
    decreasing Packet.size p
:=
  match p with
    | Number n => 0
    | Packets items => 1 + (items.attach.map (e => Packet.depth e.value) |> .foldLeft 0 Nat.max)
```

has its obligation found by `auto` (§8 stage 3).

**Proofs.** By the generated principle:

```
theorem Packet.sizePositive: (p: Packet) → 0 < Packet.size p :=
  Packet.induct (p => 0 < Packet.size p) (n => omega) (items ih => omega)
```

where `ih: (q: Packet) → List.Mem q items → …`, or by mutual theorems, or by `decreasing` on a
theorem.

**Day 13**, after stage 2's derived `Ord` and the parser: `parse` builds `Packet`s with
`recursive` (parser-combinators.md §5.3 already shows the grammar), and `solvePart1` compares
pairs with the hand-written `cmp` (the puzzle's order isn't the derived one).

### 7.3 Effect on the rest

- **Hashes.** None to the scheme: `Packet`'s hash covers its constructors, and a reference to
  `List` is a reference to an earlier declaration, as `Nat` is.
- **Erasure and runtimes.** None (§5 item 7).
- **JS boundary.** Update the finiteness comment (`crates/js/src/lib.rs:1244-1251`); add a test
  that exports a function taking a `Packet`, since a list of packets crosses as an array of
  objects, which the codec builds lazily per type (`data`, `list` memoise by instance)
  **[checked: the memoisation; inferred: that it suffices]**.
- **Elaborator.** The `quot.rs` R10 message keeps quotients' own wording; the
  Tree/Forest note on `E-POSITIVITY` goes, replaced by the new message; `docs/syntax.md:138`
  ("or inside another type (`List Tree`)") changes.
- **Derivers** (`derive.rs`, `derive_ord.rs`, `derive_show.rs`): stage 2.

## 8. Stages

Each is one lane-sized piece of work; each ends with its acceptance examples.

1. **Kernel and docs** (small-medium). The rule of §7.1 in `check.rs`, the new error message,
   `docs/core.md` (groups of data types) and `docs/syntax.md`. Examples: accept `Packet`, a
   rose tree, nesting in `Option`, a tuple, `Vec` (parameter, not index), `List (List T)`, a
   mutual group nested in a list, and §5's programs 1-7 (minus derived instances); reject `Neg`
   (§5), a member in an index of the outer type, through `List.Member`'s `a`, through `Map`
   (quotient message unchanged), through a `def` alias, through `Effect.Delay`, and `type Fix (f:
   Type → Type) = | MkFix (unfold: f (Fix f))` (a variable isn't a data type). The translation
   test oracle of option B as a kernel test. Lean's `WithCheck` (nested under `Option`, left of an
   arrow) as a soundness example.
2. **Derived `==`, `<`, `${…}`** (medium). Each deriver generates a mutual helper over the
   nesting container instead of calling the container's instance with an unsaturated recursive
   function (which termination would refuse, as `map` is refused): `Packet.decEq` with
   `Packet.decEqList`, and so on. Only for containers it knows (`List`, `Option`, tuples); others
   keep today's message.
3. **Generated size, membership lemma and induction principle** (medium). For each nested type:
   `T.size` (structural, through generated helpers, as Lean's `sizeOf`), `T.sizeMem…` (a member of
   a nested list is smaller than its node), registered so that `auto` proves `decreasing T.size p`
   obligations from an `attach`ed element's `isIn` without a `let`, and `T.induct` with "for every
   member" hypotheses (§5 item 6 shows the shape is accepted). Names and shapes in an open
   question.
4. **Dogfood** (small). AoC 2022 day 13 and 2021 day 18 programs and proofs, through the parser's
   `recursive`; anything they expose is filed then.

Option C is not staged; it's reconsidered only if stage 4 shows many `decreasing` clauses whose
only purpose is recursion through a library function.

## 9. Open questions

Each is one decision; the recommendation comes first.

1. **Which approach?** Recommended: option A, Rocq's nested positivity rule in the kernel, with
   Lean's translation used only as a test oracle. The alternative worth weighing is B2 (build the
   translated group inside the kernel, as Lean does), which reuses more of the existing check but
   does more work for the same result and refuses list functions in later fields.
2. **Generate an induction principle `T.induct` for each nested type?** Recommended: yes, in stage
   3, shaped like Lean's functional induction (§4.1): one case per constructor, and for a field
   `items: List T` the hypothesis `(q: T) → List.Mem q items → motive q`. The alternative is to
   leave proofs to mutual theorems and `decreasing`, which work today (§5).
3. **Should `auto` find "this element is smaller" obligations by itself?** Recommended: yes, in
   stage 3, through a generated size and membership lemma, as Lean's `decreasing_tactic` does with
   `sizeOf_list_dec`. Without it, each `decreasing` recursion through `attach` names the lemma or
   brings it into scope with a `let` (§5 item 4).
4. **Nesting through `Map` and `Set`** (quotients). Recommended: stay refused for now, with
   today's message suggesting ids into a separate table; neither Lean nor Rocq nests through a
   quotient. Revisit if a puzzle needs a tree keyed by name.
5. **A member nested with a constructor's own field as an index** (`children: List (Tree n)`,
   where `n` is an earlier field). Lean refuses this ("parameters cannot contain local variables"
   [L1]); Rocq's rule allows it when the variable is in an index of the member, not a parameter
   of the outer type. Recommended: allow it, since a direct occurrence `Tree n` is already allowed
   and the rule treats the substituted occurrence the same way; the conservative choice is
   Lean's refusal.

## Sources

Read in full unless marked otherwise.

- [L1] Lean language reference, Inductive types, §4.4.5.4 "Nested Inductive Types" and §4.4.3.2.2
  "Strict Positivity": https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/
  (the nested section and the positivity section read in full; the rest of the page skimmed)
- [L2] Lean 4.11.0 release notes, "Recursive definitions":
  https://lean-lang.org/doc/reference/latest/releases/v4.11.0/
- [L3] Lean language reference, Recursive definitions (§7.6.2 structural recursion, §7.6.3
  well-founded recursion, preprocessing, the `Pair` example):
  https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/ (those sections;
  not the partial-fixpoint and coinduction parts)
- [L4] Lean 4 kernel source, `src/kernel/inductive.cpp`, `elim_nested_inductive_fn` and
  `restore_nested` (lines 871-1039 read):
  https://github.com/leanprover/lean4/blob/master/src/kernel/inductive.cpp
- [R1] Rocq reference manual, Inductive types and recursive functions ("Positivity Condition",
  "Strict positivity", "Nested Positivity", "Fixpoint"):
  https://rocq-prover.org/doc/master/refman/language/core/inductive.html (those sections)
- [R2] Rocq reference manual, Reasoning with inductive types, "Eliminators for Nested Inductive
  Types": https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/reasoning-inductives.html
  (that section)
- [R3] Rocq issue #16040, "Guard condition should recognize fixpoint parameters", and PR #17986,
  "Extrude uniform parameters of inner fixpoints in guard condition check" (merged 7 May 2024):
  https://github.com/rocq-prover/rocq/issues/16040, https://github.com/rocq-prover/rocq/pull/17986
  (descriptions read; the code not read)
- [R4] MetaRocq, nested-eliminators, README: https://github.com/MetaRocq/nested-eliminators (README
  only; the formal proofs not read)
- [R5] T. Lamiaux, Y. Forster, M. Sozeau, N. Tabareau, "Nested Inductive Types for Rocq and Lean",
  RocqPL 2026 (POPL 2026 workshop):
  https://popl26.sigplan.org/details/rocqpl-2026-papers/9/Nested-Inductive-Types-for-Rocq-and-Lean
  (abstract only; no public full text found)
- [R6] Y.-J. Tan and Y. Forster, "Towards Formalising the Guard Checker of Rocq", TYPES 2025
  abstract: https://msp.cis.strath.ac.uk/types2025/abstracts/TYPES2025_paper15.pdf
- [A1] Agda documentation, Positivity checking (occurrence analysis, polarity pragmas):
  https://agda.readthedocs.io/en/latest/language/positivity-checking.html
- [A2] Agda documentation, Polarity annotations:
  https://agda.readthedocs.io/en/latest/language/polarity.html
- [A3] Agda documentation, Termination checking:
  https://agda.readthedocs.io/en/latest/language/termination-checking.html
- Lean's manual cites no paper for its translation; the closest current research is [R4, R5].
  The containers paper Agda cites for strict positivity (Abbott, Altenkirch, Ghani, "Containers:
  constructing strictly positive types", TCS 342(1), 2005) was not read.
- Stitchwort: `crates/core/src/check.rs`, `crates/core/src/termination.rs`, `docs/core.md`,
  `docs/syntax.md`, `crates/elab/src/derive.rs`, `derive_show.rs`, `quot.rs`,
  `crates/js/src/lib.rs`, `crates/elab/src/std/Map/Map.sw`, `List/Attach.sw`;
  `docs/proposals/mutual-recursion.md`, `well-founded-recursion.md`, `parser-combinators.md`.
