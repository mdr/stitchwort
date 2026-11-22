# Sealed theorems: a proof's body never affects another declaration (SW-4656)

**Status:** design note, Fable paper lane SW-4656, 22 November 2026, asked for by Matt after
SW-4645's count ("it seems sensible that proofs are encapsulated and that you can't break
another proof by changing [one] ... maybe you can help me understand why you might want to
unfold a proof or whether that's just a bad idea in general"). Nothing was built. The code and
`docs/core.md` were read at `cb436c8bf`; the web sources on 22 November 2026; seven small
programs were run on `main`'s release binary (section 3.1, files in
[`sealed-theorems/`](sealed-theorems/)). The end state is Matt's decision: the questions are in
[section 6](#6-decisions-for-matt).

Marks: **[verified]** read today in the primary source cited; **[earlier]** verified in an
earlier note of ours, not re-read today; **[run]** a program I ran today; **[measured]** a
number from SW-4645 or another lane's run; **[estimated]** my judgement; **[not verified]** I
believe it but found no source or ran nothing.

## 1. Summary

**What "sealed" means.** A theorem has a statement ("for every list, reversing twice gives it
back") and a proof. Sealed means: once the proof is checked, every other declaration sees only
the statement. Nothing else can look inside the proof, so replacing it with a different correct
proof of the same statement cannot change whether anything else checks, what anything else
means, or what anything else hashes to. The proof is still checked, stored, and counted when we
ask which axioms or open goals a result relies on.

**What happens today.** Stitchwort's theorems are not sealed. A theorem's proof is kept as a
term, and three things look inside it when they meet a call of the theorem: moving something
along an equation (`J`, which is what every `rewrite` and `calc` step becomes), taking a proof
apart (`match h with | Both l r`), and comparing two proofs. The count (SW-4645) found this is
constant, not rare: 63,049 unfoldings of theorem proofs in one check of `tools/fmt`, 12,394 in
std, 47,607 across all of AoC **[measured]**. Almost all of it is the same few one-line lemmas:
`Eq.flipped` alone is 37% of `tools/fmt`'s, because `rewrite <- h` is a `J` on `Eq.flipped h`
and the checker opens `Eq.flipped` to see whether a `byComputing` is inside.

**Is any of that unfolding needed?** Mostly not. I sealed copies of `Eq.flipped`, `Eq.trans`,
a lemma by induction and `And.left` (using the mechanism that exists today for opaque
definitions) and tried the common shapes **[run]**:

- A proof that rewrites with a sealed lemma, chains sealed lemmas, or takes a sealed
  conjunction apart **still checks**. The result is itself a proof, and nobody needs to know
  what is inside it. This is the bulk of the count.
- Three shapes **stop checking**, all of them cases where something other than a proof depends
  on the inside of a proof:
  1. *Data moved along a proof, then computed while checking.* `castNat 3 5 = 5` by computing,
     where `castNat` carries a number across the equation `n = n + 0`: the checker has to open
     the lemma to see that the equation is trivially true for `3`.
  2. *A proof taken apart to produce data* (`match bothProof with | Both l r => x`), then
     computed while checking.
  3. *Two different proofs compared directly* (a statement `proofA = proofB`, or a function
     that computes with its proof argument).

**Is depending on how B was proved ever good engineering?** No, with one honest exception. In
shapes 1 to 3 the user never *wants* the content of the proof: the answer is the same whatever
the proof is (any proof of `3 = 3 + 0` moves `5` to `5`; a conjunction has only one shape). The
checker opens the proof only because it has no other way to find that out. The right fix is to
teach the checker those facts directly, which is what Lean does, and then no proof ever needs
opening. The one real use of a proof's inside in other systems is Rocq's recursion over an
"accessibility" proof, where the proof is what the function recurses on; Stitchwort's
`decreasing` doesn't work that way (it counts down a number), so we don't have that case
**[verified in `docs/core.md`]**.

Every system I checked agrees with Matt's instinct. Rocq's manual: "what matters in a
mathematical development is the sequence of lemma statements, not their actual proofs", and a
proof ended with `Qed` is "irreversibly opaque". Lean's new module system puts every proof in a
module's private part, so that changing a proof doesn't rebuild the modules that use it.
Isabelle's logic has no way to mention a proof at all.

**What it would buy.**

- *Encapsulation as a rule the kernel enforces*, not a habit.
- *Editing a proof stops invalidating everything after it.* Today a theorem's hash covers its
  proof and every user's hash covers the theorem's, so a changed proof changes the hash of
  everything downstream, and a std edit re-checks every namespace that lists the file. With
  sealing a user's hash covers the statement only.
- *Proofs can be checked in parallel and loaded lazily*: a sealed theorem and a promise of one
  look the same to everything else (parallel-checking.md's option B2), and a session that only
  uses a theorem needs only its statement in memory.
- *The unfolding work itself goes away* (the 63,049). I expect that to be a small direct
  saving; it was counted, not timed.

**Recommendation.** Make theorems sealed by default (option B in section 5), in stages, with a
measurement first:

1. A switch that seals every theorem, run over std, `tools/fmt`, AoC, the roguelike and the
   examples by Overmind, listing every declaration that stops checking and which of the three
   shapes it is. I expect few, but nobody knows: the count says how often proofs are opened,
   not how often opening them was needed.
2. Seal by default, with `transparent theorem` (Rocq's `Defined`) on the lemmas stage 1 found,
   so nothing that checks today stops checking.
3. Hashes and the check cache follow the statement only.
4. Two kernel rules that remove the need for the opt-outs: a cast along any proof of `a = a`
   computes (Lean's "K-like" rule), and a `match` on a proof with one possible shape takes its
   branch without opening the proof. These change what the kernel accepts, and the first
   reverses a position taken in the proof-irrelevance note (which kept the rule out because of
   a known contrived looping term), so each needs its own soundness review and Matt's yes.

## 2. How other systems do it

### 2.1 Lean 4

- **Any two proofs of one proposition are equal by definition**, checked by type: the kernel's
  `is_def_eq_proof_irrel` infers `t`'s type, and if that type is a proposition, compares the
  two types and answers from that alone **[verified, L1]**. So Lean never opens a proof to
  compare it with another.
- **K-like reduction.** For "datatypes that support K-axiom" (equality is the main one), the
  recursor's major premise is replaced by the constructor when its type matches
  (`to_cnstr_when_K`, called from `inductive_reduce_rec` when `rec_val.is_k()`) **[verified,
  L2, in a summarising read; the exact code was read line by line for
  `docs/proposals/proof-irrelevance.md` on 19 October]**. So a cast along any proof of `a = a`
  computes without looking at the proof.
- **A match on a proof of a one-constructor proposition.** `to_cnstr_when_structure` turns a
  stuck `p` into `mk p.1 … p.n` for non-recursive structures. Today's source says "We do not
  perform eta for non-singleton propositions" and skips it when the recursor has as many
  universe parameters as the type, that is, when it cannot eliminate into data **[verified,
  L2]**. I read that as: for a proposition that *can* be matched into data (`And`), Lean now
  does take the branch on a stuck proof. Our October read of the same function saw
  `if (is_prop(e_type)) return e;` (never for propositions) **[earlier]**, so this changed in
  between or one of the reads is wrong: **least certain fact in this note**.
- **Theorems are not opaque to Lean's kernel.** `is_delta` unfolds any constant for which
  `has_value()` holds, and `constant_info::has_value` is `is_theorem() || is_definition() ||
  (allow_opaque && is_opaque())`; a theorem's reducibility hint is "opaque", which makes it
  the last thing unfolded **[verified, L1, L3, L4]**. (A comment in the same header says
  theorems "are treated like opaque declarations", which contradicts the code beside it
  **[verified, L3]**.) The elaborator's side is stricter: `getUnfoldableConst?` returns `none`
  for a theorem **[verified, L5]**. With proof irrelevance and the two rules above, the
  kernel's permission is rarely if ever used; I did not find a statement of how often.
- **Module system: proofs are private.** "proofs of theorems are in the private scope. This is
  the case both for public and private theorems", and "Changes to files that affect only
  non-exported information" such as proofs do not trigger rebuilds outside those files
  **[verified, L6]**.

### 2.2 Rocq

- `Qed` adds the proof "as an opaque constant"; `Defined` is the same "except the proof is made
  transparent, which means that its content can be explicitly used for type checking"
  **[verified, R1]**.
- "constants defined by proofs ending with Qed are irreversibly opaque; Transparent will not
  make them transparent", with the rationale "what matters in a mathematical development is
  the sequence of lemma statements, not their actual proofs", against definitions "whose actual
  values are of course relevant in general" **[verified, R2]**. `Opaque`/`Transparent` on
  ordinary constants only steer tactics and delay unfolding **[verified, R2]**.
- **Why `Defined` is used.** Rocq's ordinary `Prop` has no definitional proof irrelevance and
  no K-like rule, so anything that computes *through* a proof needs the proof transparent.
  The standard case is well-founded recursion: `Fix_F` recurses on an accessibility proof
  through `Acc_inv`, and `Acc_inv` ends with `Defined.` in the standard library **[verified,
  R3]**. The other case, casts along equality proofs that must compute, I know from practice
  and did not find stated in the manual **[not verified]**.
- Opaque proofs are what let Rocq skip or delay them (`-vos`, asynchronous proofs)
  **[earlier, parallel-checking.md R1, R2]**.

### 2.3 Agda

- `opaque` blocks: "opaque definitions will not unfold in general, but unlike abstract
  definitions, opacity can be selectively controlled at use-sites", through `unfolding`
  clauses, which are transitive; "Opaque definitions do not reduce in type signatures, even
  inside opaque blocks" **[verified, A1]**. Stitchwort's `opaque def` and `unfolding` are this
  design. In Agda opacity is opt-in for everything; there is no theorem/definition
  distinction.
- With `--prop`, "all elements of a type in Prop are considered to be (definitionally) equal",
  and matching a `Prop` into data "is restricted to the absurd pattern", so an equality in
  `Prop` cannot move data at all **[verified, A2]**. Proofs are irrelevant by giving up casts,
  where Lean keeps casts and adds the K-like rule.

### 2.4 Isabelle/HOL

- A theorem is a value of the abstract type `thm`, which "guarantees that its values have been
  constructed by basic principles of the Thm module"; "Proof terms are irrelevant in the Pure
  logic, though; they cannot occur within propositions"; recording them is a runtime option
  (`Proofterm.proofs`) **[verified, I1]**. So "depending on how B was proved" cannot be
  expressed. HOL has no dependent types, so there are no casts along proofs to compute.

### 2.5 What the survey says

Nobody treats a proof's body as part of a theorem's interface. The systems differ in how they
make that workable for dependent types: Isabelle has nothing that could depend on a proof;
Agda's `Prop` forbids the dependence; Rocq allows it and makes the author choose `Defined`
case by case; Lean allows it and makes the kernel smart enough (irrelevance, K-like) that the
proof's body is never the thing depended on. Stitchwort today is none of these: it allows the
dependence and gets it by opening proofs everywhere, by default.

Not verified: how often Lean's kernel actually unfolds a theorem in practice; Rocq's `Defined`
for casts (above); anything about Idris or F\*.

## 3. Stitchwort: what replaces each kind of unfolding

### 3.1 What exists already, and the seven programs

The kernel already has sealing: an opaque definition "has a type and no body" while others are
checked, and "a theorem with `unfolding` stays folded even under `case` and `J`"
(`docs/core.md`, "Opaque definitions"; `docs/syntax.md`). `value.rs` even calls a call that
can't unfold `sealed`. What is missing is only the default (`opaque theorem` is refused today
as unnecessary) and what to do about the programs that needed the body.

The programs ([`sealed-theorems/sealed.sw`](sealed-theorems/sealed.sw), and
[`transparent.sw`](sealed-theorems/transparent.sw), the same with the seals off, which checks
entirely) **[run]**:

| # | Shape | Sealed, today's kernel |
|---|---|---|
| 1 | `rewrite h`, `rewrite <- h`, `Eq.trans` chains with sealed lemmas, in a theorem | checks |
| 2 | data cast along a sealed proof, then `byComputing` on a closed instance | `E-REFL`: stuck on `J … (flippedS (addZeroS 3))` |
| 2b | the same with `unfolding flippedS, addZeroS` on the user | checks |
| 3 | `match` on a sealed conjunction, or `And.left` of it, in a theorem | checks |
| 4 | `match` on a sealed conjunction producing data, then `byComputing` | `E-REFL` |
| 5 | a function that casts along its proof argument, called with two different sealed proofs, compared | `E-REFL` |
| 6 | two records that differ only in a proof field holding different sealed proofs | checks (proof fields are skipped) |
| 7 | the statement `proofA = proofB` by `byComputing` | `E-REFL` |

One more **[run]**: with theorems transparent as today, `castTo n 5 = 5` for a *variable* `n`
fails (`J` is stuck on `Eq.flipped n.addZero`, whose proof is by induction), though it holds
for every `n`. Unfolding only ever helped on closed instances.

### 3.2 The count, site by site

Sites and counts are SW-4645's **[measured]**: `tools/fmt` / std / all of AoC.

| Site | Counts | Why it unfolds today | Sealed: what happens | Replacement needed |
|---|---|---|---|---|
| `J` on a theorem's proof | 50,468 / 6,936 / 31,695 | every `rewrite`, `rewrite <-` and `calc` step is a `J` on a proof built from `Eq.flipped`, `Eq.cong`, `Eq.trans` or a lemma; evaluation opens it looking for `byComputing` | the `J` stays stuck on the call. When the result is a proof (nearly always: a rewrite inside a theorem), nothing more is asked of it (program 1) | only for a `J` that produces **data the checker must compute** (program 2): rule K below, or the lemma chain transparent |
| `case` on a theorem's proof | 6,702 / 2,521 / 7,594 | `And.left`/`right` and `match h with \| Both l r` on a lemma's result; `Decidable.andSound`, `Bool.andReads`, `List.memContains` results taken apart; `Bool.falseNotTrue` refuted | stuck on the call; fine when the result is a proof (program 3). A `case` with no possible branch never computes anyway | only for a `case` producing **data** (program 4): rule S below |
| a call returned by a body | 5,312 / 2,655 / 7,500 | a by-product: an unfolded proof ended in a call of another theorem, opened in turn | never starts | none |
| conversion (incl. over-applied) | 80 / 182 / 763 | two proofs compared outside a proof position; in AoC mostly the kernel comparing `Map`s built by `insert`, whose `ordered` and `sized` proof fields are calls of `Map.Tree.insertWithWithin` and `insertWithSized` (438 each, kernel only), in the *shortcut mode* that compares proof fields | two calls of one sealed theorem are compared by their arguments, as for any hidden body (`docs/core.md`, shortcut mode); if that fails the shortcut gives up and the outer calls are unfolded and compared with proof fields skipped, so the `Map` case still checks **[estimated from the rules, not run]** | rule P below for proofs compared where nothing is skipped (programs 5, 7) |
| unify (incl. over-applied) | 487 / 100 / 55 | the elaborator's side of the same | as conversion | rule P |

So about 99% of the unfoldings (`J`, `case`, returned calls) happen at sites where, when the
result is a proof, sealing needs no replacement at all. What the count cannot say is how many
of the `J` and `case` unfoldings fed *data* that a `byComputing` or a type then needed. That
is stage 0's measurement.

### 3.3 The opt-out

- **`transparent theorem name …`** on the declaration (Rocq's `Defined`): the theorem is
  checked, folded and unfolded exactly as every theorem is today, and its hash covers its
  proof. The author states that the proof is part of the interface. A `def` whose type is a
  proposition is already this, minus the folding **[not run]**.
- **Not** an `unfolding B` on the user's side for theorems. That exists for opaque definitions
  (and worked in program 2b because a theorem with a list is an opaque definition to the
  kernel), but for theorems it is the reaching-into-internals Matt's rule is meant to end: B's
  author would not know that A depends on the proof. I recommend the kernel refuse a sealed
  theorem in an `unfolding` list. Nothing uses one today: the only `unfolding` clauses in std,
  `tools/fmt`, AoC and the roguelike are six in the roguelike, each naming an opaque
  definition (`RoomsFit`, `generateLevel`, `layOut`, `Dice.upTo`) **[verified by grep]**.
- Without rules K, S and P, a cast needs the *whole chain* transparent: `flippedS (addZeroS n)`
  needs `flippedS`, `addZeroS` and the `Eq.cong` inside its induction. That is why option C
  (opt-outs only) scales badly if stage 0 finds many casts: the opt-outs spread down through
  std's basic lemmas.
- **Which programs, how many:** unknown until stage 0. Sizes for scale: 4,301 theorems in std,
  5,578 in `tools/fmt`, 2,869 in AoC, 174 in the roguelike **[counted by grep]**.

### 3.4 Rule K: `J` computes when its endpoints are already equal

**Rule.** `J P d p ⟶ d` when `p: x = y` is not `byComputing` after its head is computed, and
`x ≡ y`. (Today: only on `byComputing`; "with any other proof it's stuck".)

**Kernel changes** (`docs/core.md`: "Terms", "Typing" for `J`, "Equality", "The equality
rule" (rule E for `J`), "Running a program"): evaluation is untyped, so `J` must carry its
endpoints, filled in by the checker as `Eq`'s type is; the machine compares them when the
proof's head is rigid; the reference evaluator and the elaborator's unifier get the same rule
(in the elaborator a `J` whose endpoints mention an unsolved unknown waits). The test of
record (`proof_equivalence.rs`) gains wrapping cases.

**Soundness.** In the set model every proposition has at most one element, and `x = y` is
inhabited only when the two are the same; a cast along it is the identity. The kernel already
commits to this model three times: axiom K holds through index unification's deletion rule
("That's consistent, and rules out only univalent and higher-dimensional readings of
equality"); comparison skips proofs at proof positions; and the runtime erases equality proofs
and "`J` on an erased proof takes its base". Rule K makes the checker compute what the runtime
already computes, in the cases where the checker can see the endpoints agree. It is Lean's
rule **[verified, L2]**.

**Consistency with what's there.**
- *Univalence-style axioms:* already excluded by K; nothing changes.
- *`Quot.sound`:* the one axiom. A proof made by it has endpoints `Quot.mk a` and `Quot.mk b`;
  rule K fires only if those are convertible, where the cast is the identity in the model.
  Otherwise `J` stays stuck as today. `Quot.funext` is derived from it and is the same case.
- *Assumptions (`?`) and stand-ins:* a `J` on an assumed proof of `a = a` would now compute.
  That is the model's answer too, and what the runtime does.
- *Subject reduction:* `J P d p: P y p` steps to `d: P x byComputing`; the types agree only if
  `p ≡ byComputing` where `P` mentions its proof argument. The kernel doesn't equate those
  (no general proof irrelevance), so a term can compute to one the checker wouldn't accept at
  the same type: the gap `docs/proposals/proof-irrelevance.md` §5.7 already documents, not a
  new kind.
- **The known cost (Abel and Coquand).** "Normalization fails in type theory with an
  impredicative universe of propositions and a proof-irrelevant propositional equality"
  **[verified, AC, abstract]**. Stitchwort has the impredicative `Prop`; rule K supplies the
  rest. Under the false hypothesis `h: (a b: Prop) -> a = b` there is a term that computes
  forever. Our proof-irrelevance note ran it: it is accepted and checks quickly today because
  `J` is stuck on `h Top a`, and that note concluded "**So: no K-like rule.** This is a
  must-keep test" **[earlier, proof-irrelevance.md §5.2]**. With rule K that one program
  (`omegaUnfolds`) would stop with `E-RESOURCE`: inconclusive, never a wrong answer. It is the
  only program I know of that rule K takes from "checks" to "doesn't", it needs a
  contradictory hypothesis, and Lean accepts the same trade. I found no restriction of the
  rule that keeps the program and is still simple: limiting it to proofs headed by a theorem
  fails (pass `h` to a theorem), and limiting it to equations at data types fails (box the
  propositions in a record). Limiting it to *closed* proofs would keep it, but then open
  casts that unfold to `byComputing` today would be lost.

**What it accepts that today doesn't:** casts along any proof with equal endpoints, including
open ones (`castTo n 5 = 5`), `Quot.ind`-made proofs and hypotheses.

### 3.5 Rule S: a `case` on a one-shape proof takes its branch

**Rule.** `Case(x, D, [b])` with `D: Prop`, no indices, exactly one constructor, and a
scrutinee that is a neutral proof takes its branch, with each field bound to a stand-in for
"that field of the proof". It is [record eta](../core.md#record-eta)'s rule 2 for the
propositions `E-PROP-ELIM` already lets into data.

**Why it terminates and is sound.** `E-PROP-ELIM` allows a proposition to be matched into
data only if it has at most one constructor, every field is a proof, and no field mentions the
type itself (D1980). So the branch receives only proofs, which can themselves only be passed
on or taken apart by this rule or rule K, and there is no recursive proposition to unfold
without end (Lean's `Acc` problem, which D1980 removed). The runtime already does exactly
this: "a `case` on an erased proof takes its only branch". Lean's kernel appears to do the
same for such propositions today (section 2.1, least certain).

**Scope.** Needed only when the result is data; into a proposition the stuck `case` is itself
a proof. Indexed one-constructor propositions other than `=` (a user's `Same x y`) would need
their indices checked as rule K checks endpoints; I'd leave them stuck (transparent opt-out)
until one turns up. A `case` with no constructors stays stuck, as now.

**Kernel changes:** `value::branch`, the unfolding policy ("can take a step"), a neutral form
for a proof's field (`Proj` is deliberately only for data records), rule E; reference
evaluator and unifier alike.

### 3.6 Rule P: two sealed proofs are equal

**Rule.** In conversion and unification, two neutrals each headed by a sealed theorem (any
two theorems, any arguments) are equal.

**Soundness.** Comparison is only ever asked about two values of one type (the precondition
the proof-position skips already rest on). A term headed by a theorem is a proof whatever its
arguments, since a theorem's type is a proposition and a function into a proposition is one.
So both sides are proofs of one proposition, equal in the model. It needs no type inference,
which is why Stitchwort's position-based design can afford it.

**What it replaces.** Today's comparison by unfolding both proofs (programs 5 and 7, where
both sides are theorem calls), and the inert-parameter marks for theorems, which today leak a
theorem's body into its users ("a caller's `byComputing` … can come to depend on the body
ignoring a proof", `docs/core.md`): with rule P a theorem's arguments are never compared, so
nothing about its body is consulted.

**What it doesn't do.** A sealed proof against a variable `h`, a `byComputing` or a `Both l r`
written out is still "different", where today unfolding sometimes made them equal. Making
those equal one-sidedly would break transitivity (`p ≡ T ≡ q` with `p ≢ q` for two
hypotheses), which the test of record checks. The complete answer is Lean's typed rule for
all of `Prop`, option D of the proof-irrelevance note, which Matt declined in October in
favour of proof positions; this note doesn't reopen it. With rules K and S in place, nothing
*computes* differently on two proofs any more, so such a comparison can only arise from a
statement about proofs themselves (program 7), which I expect stage 0 to show is rare.

### 3.7 `Decidable` and other things that look like proofs

A decision is data: `Decidable p` is a record with a `Bool` test and two proof fields, and
its procedures are `instance`s, which are definitions. They stay transparent, and `if`,
`==`, `auto` and `byDeciding`-style proofs compute with `holds` as now. The count's
`Decidable.andSound` and `Bool.andReads` entries are *theorems about* decisions whose result
(a conjunction, an `↔`) is taken apart inside another proof: the site "`case` on a proof",
result a proof, no replacement needed. `decreasing` recursion counts down a number and only
passes its proofs along (`f.%go`, "Recursion on a measure"), so it needs nothing either.
Generated theorems (`f.unfold`, `T.induct`, `%respects`, `%irrel`) are sealed like any other;
`f.unfold`'s own list (`[f]`) is unchanged.

### 3.8 Hashes

Today "a definition's hash covers whether it's a theorem, its type and its body", and a
reference is hashed as the referent's hash. Proposed: two hashes per theorem.

- **Interface hash**, used wherever another declaration refers to it: tag `theorem` and the
  statement. A transparent theorem's is its full hash. This is what users' hashes cover, so
  a changed proof changes no dependant's hash. (`proofless_hash` in `hash.rs` is close, but
  it also blanks proof arguments inside definitions, which the kernel can still compare; the
  interface hash must not.)
- **Full hash**, today's: statement and proof, with references by interface hash. It
  identifies the checked proof itself.

Two things must not ride on the interface hash, because they depend on proofs' insides:
*which axioms and open goals a result relies on* (`relied_on`, `stitchwort axioms`, `audit`),
which are walks over bodies and stay so; and any cached verdict of "finished". If B's proof
gains a `?`, A's interface hash doesn't move, so A's "relies on an open goal" must come from
the walk (or a stored per-declaration reliance set), never from a hash-keyed cache. The test
cache's key (the test's hash) needs the reliance set added for the same reason, or to keep
using full hashes for tests. A proof that *fails* is replaced by a stand-in, whose hash tag
differs, so failure still reaches every user.

Two theorems with the same statement get the same interface hash. That is harmless (with
rule P they are also equal to the checker), and it is the same choice as hashing no names.

Hash snapshots: every hash downstream of a theorem changes once; no migration concern.

### 3.9 Check cache, editor, parallel checking, performance

- **Check cache.** An entry's key covers "the unit's text and its dependencies' keys", so any
  edit to a file re-checks everything that needs it. With sealed theorems the key can cover
  each dependency's *interface digest* (the interface hashes and side tables of what it
  declares) instead of its text key: editing a proof in std then re-checks that file only.
  This is the early cut-off Lean's module system advertises **[verified, L6]**. It is a
  separate stage; sealing makes it correct, not automatic. The elaborator's side tables
  (names, instances, `@[walk]` and `@[reading]` lemmas) must be in the digest; they read
  statements, not proofs **[not verified for every table]**.
- **Editor.** Same mechanism, per namespace; within a namespace, declarations after an edited
  proof need no re-check if the editor tracks interface hashes per declaration **[not
  verified how the editor re-checks within a namespace today]**.
- **Parallel checking.** Sealing is Lemma B of `parallel-checking.md` as a rule: a later
  declaration cannot tell a finished theorem from a promise of one, so proof bodies can be
  checked in any order after their statements (option B2), where theorem bodies are at least
  60% of `tools/fmt`'s check time **[measured there]**. The process experiment found workers
  spend most of their time reloading dependencies (233 s of 329 s); a session that needs only
  statements can skip decoding proof bodies, which I'd expect to be most of an entry's bytes
  **[estimated; not measured]**.
- **Performance.** The 63,049 unfoldings disappear, and the kernel's `J` stops re-walking
  `Eq.flipped`. Against 1.89 billion steps for a `tools/fmt` check that is probably well
  under 1% of steps **[estimated: unfoldings were counted, not costed]**. Rule K adds a
  comparison of endpoints at each `J` stuck on a rigid proof; rule P makes the shortcut mode
  succeed more often (the `Map` proof fields). Net effect unknown until measured; I would not
  sell sealing on direct speed.

## 4. What stays the same

- Proofs are checked by the kernel exactly as now; sealing only changes what *later*
  declarations may see.
- Running a program: "while a program runs every definition unfolds", and proofs are erased
  anyway.
- Definitions, instances, `opaque def`, `unfolding` for definitions.
- A theorem with an `unfolding` list (to see inside opaque definitions) is already sealed.

## 5. Options for the end state

**A. Keep theorems transparent.** No work. A changed proof can break or change any later
declaration (rarely in practice, but nothing prevents it), every dependant's hash moves on
every proof edit, proof-level parallelism needs blocking on demand, and the leak through
inert marks stays. Stitchwort would remain the only system in the survey where a proof's
body is part of a theorem's interface by default.

**B. Sealed by default, kernel rules K, S and P, `transparent theorem` as the escape.**
The end state Lean has, by Stitchwort's position-based means. Proof bodies matter to nothing
else; the opt-out is expected to be unused, kept for what the rules don't reach (indexed
one-constructor propositions, statements about proofs).
- *Costs:* three kernel rules with soundness reviews (K is the significant one), `J` carrying
  endpoints, the same rules in the reference evaluator and the unifier, two hashes, a new
  keyword (guide, `docs/syntax.md`, both formatters), `docs/core.md`.
- *Risks:* rule K gives up normalisation under contradictory hypotheses (budget catches it;
  one known program); a mistake in K or S is a soundness bug, so Fable-reviewed; the cost of
  endpoint comparisons.

**C. Sealed by default, no new kernel rules, opt-outs where needed.** Rocq's `Qed`/`Defined`
world. The kernel change is small (theorems submitted opaque; refuse theorems in `unfolding`
lists; hashes).
- *Costs:* every cast or data-producing match along a lemma needs that lemma *and everything
  its proof calls* transparent, chosen by the lemma's author in advance; open casts still
  never compute; the inert-mark leak stays unless rule P is taken anyway.
- *Risk:* if stage 0 finds many such uses, the transparent set spreads through std's basic
  lemmas and the encapsulation is lost exactly where it's used.

**Recommendation: B as the end state, reached through C.** Seal first with whatever opt-outs
stage 0 shows are needed (C is then a waypoint, and nothing stops checking), then add P, S
and K, each removing opt-outs, K last and only after its own review. If stage 0 finds the
opt-outs would be many (I'd say more than a few dozen declarations, or any spread into
`Eq.*`), do the rules before sealing instead.

### Stages, and how each is measured

| Stage | What | Measure | Who |
|---|---|---|---|
| 0 | A test-only switch (`STITCHWORT_SEAL_THEOREMS=1`): every theorem submitted opaque with an empty list. No language change | Overmind runs std, `tools/fmt`, AoC, roguelike, examples with it: the declarations that fail, classed as cast / match-into-data / comparison; the lemmas they would need transparent, with the closure through their proofs | Sonnet, small |
| 1 | `transparent theorem`; theorems sealed by default; theorems refused in `unfolding` lists; messages ("`B` is a theorem, so its proof isn't used here"); guide, syntax, both formatters, `docs/core.md` | everything checks; `STITCHWORT_THEOREM_UNFOLDS` reports unfoldings only of transparent theorems; steps before and after on `tools/fmt` | Opus (kernel, syntax) |
| 2 | Interface and full hashes; reliance kept on the walk; test-cache key | edit a proof in std: no dependant's hash changes (a test); hash snapshots re-recorded once | Opus |
| 3 | Check-cache keys by interface digest | edit a proof in a low namespace of `tools/fmt`: number of namespaces re-checked, before and after | Opus, after a short note |
| 4 | Rule P | opt-outs removed; test of record extended (transitivity) | Opus + Fable review |
| 5 | Rule S | opt-outs removed; soundness examples | Opus + Fable review |
| 6 | Rule K, after a soundness note of its own (the Abel-Coquand term, `Quot.sound`, the unifier) | remaining opt-outs removed; `omegaUnfolds` recorded as `E-RESOURCE`; cost of endpoint comparisons on `tools/fmt` | Fable note, Opus build, Fable review |

Parallel proof checking (parallel-checking.md B2) can start after stage 1.

## 6. Decisions for Matt

1. **End state:** should a theorem's proof be sealed by default, enforced by the kernel, with
   users' hashes covering the statement only and `transparent theorem` as the declared
   exception (no use-site unfolding of theorems)? This is user-visible language and a change
   to what the kernel accepts by default. **[rec: yes, starting with stage 0's measurement,
   which commits to nothing.]**
2. **Later, when stage 0's numbers are in:** may the kernel gain the K-like rule for `J` (and
   the smaller rules S and P), so that sealing needs no opt-outs? It reverses the
   proof-irrelevance note's "no K-like rule", at the cost of one known contrived program going
   from "checks" to "out of budget". **[rec: no decision now; I lean yes, after a dedicated
   soundness note, since without it casts along lemmas force transparent chains or stay
   stuck.]**

## 7. Sources

All read on 22 November 2026 unless marked.

- [L1] Lean 4 kernel, `src/kernel/type_checker.cpp`, `master` (`is_delta`,
  `unfold_definition_core`, `is_def_eq_proof_irrel`, `lazy_delta_reduction_step`):
  <https://raw.githubusercontent.com/leanprover/lean4/master/src/kernel/type_checker.cpp>
- [L2] Lean 4 kernel, `src/kernel/inductive.h`, `master` (`to_cnstr_when_K`,
  `to_cnstr_when_structure`, `inductive_reduce_rec`):
  <https://raw.githubusercontent.com/leanprover/lean4/master/src/kernel/inductive.h>
- [L3] Lean 4 kernel, `src/kernel/declaration.h`, `master` (`constant_info::has_value`, the
  reducibility hints comment):
  <https://raw.githubusercontent.com/leanprover/lean4/master/src/kernel/declaration.h>
- [L4] Lean 4 kernel, `src/kernel/declaration.cpp`, `master` (`constant_info::get_hints`):
  <https://raw.githubusercontent.com/leanprover/lean4/master/src/kernel/declaration.cpp>
- [L5] Lean 4, `src/Lean/Meta/GetUnfoldableConst.lean`, `master`:
  <https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Meta/GetUnfoldableConst.lean>
- [L6] The Lean Language Reference, "Source Files and Modules", §5.4 "Modules and Visibility"
  ("Proofs are Private"): <https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/>
- [R1] Rocq reference manual 9.1, "Proof mode" (`Qed`, `Defined`, `Admitted`):
  <https://rocq-prover.org/doc/V9.1.0/refman/proofs/writing-proofs/proof-mode.html>
- [R2] Rocq reference manual 9.1, "Reasoning with equalities" (`Opaque`, `Transparent`, the
  note on `Qed`):
  <https://rocq-prover.org/doc/V9.1.0/refman/proofs/writing-proofs/equality.html>
- [R3] Rocq core library, `theories/Corelib/Init/Wf.v`, `master` (`Acc_inv … Defined.`,
  `Fix_F`): <https://raw.githubusercontent.com/coq/coq/master/theories/Corelib/Init/Wf.v>
- [A1] Agda documentation, "Opaque definitions":
  <https://agda.readthedocs.io/en/latest/language/opaque-definitions.html>
- [A2] Agda documentation, "Prop": <https://agda.readthedocs.io/en/latest/language/prop.html>
- [I1] Wenzel, *The Isabelle/Isar Implementation* (dated 24 October 2026), §2.4 on `thm` and
  the Pure logic, §2.5 "Proof terms": <https://isabelle.in.tum.de/doc/implementation.pdf>
- [AC] Abel and Coquand, "Failure of Normalization in Impredicative Type Theory with
  Proof-Irrelevant Propositional Equality", LMCS 16(2), 2020 (abstract read today; §1 read
  for `proof-irrelevance.md`): <https://arxiv.org/abs/1911.08174>

The web pages were read through a fetch tool that summarises and quotes; the quotations above
are as it returned them, and the Isabelle manual was read as extracted text.

### What I could not verify

- Whether Lean's kernel today takes the branch of `And.rec` into data on a stuck proof
  (section 2.1): today's read and October's disagree.
- How often Lean's kernel unfolds a theorem in practice; Rocq's use of `Defined` for casts.
- In Stitchwort: how many declarations need a proof's body once theorems are sealed (stage
  0); that the `Map` proof-field comparisons still check when sealed (argued from the
  shortcut-mode rules, not run); that every elaborator table reads statements only; what the
  unfoldings cost in steps or time; how the editor re-checks within a namespace.
- Normalisation with rule K restricted in any way; I know of no result either way.
