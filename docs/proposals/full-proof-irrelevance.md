# Full proof irrelevance: "which proof you have never matters" as the end state (SW-4662)

**Status:** design note, Fable paper lane SW-4662, 23 November 2026, asked for by Matt in D3720
("we care about the best end state ... if an escape hatch would go unused, why don't we go to
full proof irrelevance?"). Nothing was built. It reopens a decision of 19 October (D1′, in
[proof-irrelevance.md](proof-irrelevance.md), which did not recommend "option D2, full Lean")
in the light of [sealed-theorems.md](sealed-theorems.md) and its measurements. The code and
`docs/core.md` were read at `6e5fe356d`; four probe files were run on `main`'s release binary
([`full-proof-irrelevance/`](full-proof-irrelevance/)). The choice between the end states is
Matt's: [section 10](#10-decisions-for-matt).

Marks: **[verified]** read today in the source cited; **[earlier]** verified in one of our two
earlier notes, not re-read today; **[run]** a program I ran today; **[measured]** a number from
another lane's run; **[inferred]** my reasoning from those, not stated in a source;
**[estimated]** a size or cost I judged; **[not verified]** believed, no source found or nothing
run.

## 1. Summary

**The question.** A theorem has a statement and a proof. Everyone agrees the statement is what
other code should depend on. The open question is how far the checker goes in treating two
proofs of the same statement as the same thing. There are two coherent places to stop.

**E1: sealed theorems, and proofs ignored in the places the checker knows about (today's rule).**
The checker skips a proof when it sits in a record's proof field, in a data type's proof
parameter, or in an argument that a function only passes along. Everywhere else two proofs are
compared like data. A cast along a proof computes only if the checker can see the proof is
literally "both sides are the same"; with theorems sealed it can't see inside a lemma, so such
casts stay stuck unless the lemma is declared `transparent theorem`. This is roughly Rocq's
world.

**E2: sealed theorems, and proofs ignored everywhere.** The checker treats every proof as a
blank. Two proofs of one statement are always equal; a cast along a proof of `a = a` always
computes; taking apart a proof with one possible shape always takes its branch. Nothing the
checker does can depend on how something was proved. This is Lean's world, and it is also what
a running Stitchwort program already does: `run` erases every proof, takes the base of every
cast and the only branch of every such match (`docs/core.md`, "Running a program")
**[verified]**. Under E2 the checker computes with exactly what the program computes with.

**What I found, against what was believed when this lane started.**

1. *"The checker's values don't carry types" is not a blocker.* Confirmed. Rocq does it with a
   one-bit mark on every binder; Stitchwort has unique sorts and an impredicative `Prop`, the
   two facts the trick needs (section 4).
2. *E2 needs the cast rule (K).* Confirmed, and it also needs the match rule (S), for every
   proposition that can be matched into data, including a user's own indexed ones. That last
   case is accepted today and needs a decision (section 4.4, Q2).
3. *Abel and Coquand's looping program would hit the budget.* Better than that: every term in
   the loop is itself a proof, and under E2 the checker never computes inside a proof, so the
   loop never starts and the program still checks. A 2023 paper proves decidable checking for a
   system of this kind by exactly that argument (section 5.3). Stitchwort's own calculus has no
   such proof, today or under either end state.
4. *The kernel gets simpler.* In ideas, yes: three mechanisms (the inert-parameter analysis, the
   shortcut mode, unfolding theorems to look for a literal proof) are replaced by one rule. In
   lines, about even. Two things believed removable stay: the limit on record eta (Rocq has the
   same limit, for the same reason), and `rewrite`'s search still has to skip proofs (it
   becomes one instance of the general rule instead of a special case) (section 6).
5. *Std's Hedberg lemmas become one-liners today.* Confirmed by a probe, with theorems sealed.
   This matters for the staging: with `Prop.irrel` in std, **sealing every theorem needs no
   `transparent theorem` anywhere in std, `tools/fmt`, AoC or the roguelike** (section 9). One
   accept example (`omega-basics`'s `transportComputes`) would wait for rule K.

**Recommendation: E2.** Three reasons, in order of weight.

- *It is the only one of the two where "a proof's body never matters" is true without
  exceptions.* Under E1 sealing is a flag with an escape hatch, and the checker's answers still
  depend on what a function's body does with a proof (the inert marks) and on which of two
  comparison modes it is in. Under E2 there is nothing an escape hatch could expose: no rule
  looks inside a proof, so `transparent theorem` has no meaning and is not needed.
- *It removes E1's known oddities instead of documenting them.* Today a statement can check
  for every `n` and be refused at `n = 1` (probe 8); a well-typed term can compute to one the
  checker refuses (the "subject-reduction gap"); and with theorems sealed, two equal maps built
  two ways differ under a stuck call because a mode compares their proof fields (SW-4659). None
  of these can be stated under E2.
- *The risks that made October's note say no have shrunk.* Recursive propositions into data
  are refused since D1980; the looping program does not loop a checker that leaves proofs
  alone; and the "values don't carry types" cost is a mark per binder, not a rewrite of the
  comparison.

**What E2 costs.** The largest kernel change since D1′: a mark on every binder (a term-format
change), casts that carry their two ends, an evaluator that asks "are these two ends equal?"
while computing, the same in the reference evaluator and the elaborator's unifier, and a
rewrite of `docs/core.md`'s proof paragraphs. A wrong mark that calls data a proof would be a
soundness bug, so the marks are computed by the kernel from sorts alone and re-derived by the
reference evaluator. One thing is lost: the elaborator will no longer learn an unknown by
looking inside two proofs (it already doesn't at proof positions); nobody has measured how
often that helps today.

**Stages** (section 9): seal now with no new keyword (both end states want this); then marks
with counters and no change of behaviour; then rules K and S; then the full skip and the
deletions together.

## 2. The two end states, side by side

| | E1: sealed + positional (D1′) | E2: sealed + full |
|---|---|---|
| In a sentence | proofs in fields, and in arguments a function only passes along, don't matter | which proof you have never matters |
| Two proof variables `p q: a` | different (equal only as a theorem, `piViaBox`) | equal |
| `f p` and `f q`, `f` a local function | different | equal |
| Cast along a proof of `a = a` that isn't literally `byComputing` | stuck; along a lemma, needs the lemma and everything it calls `transparent` (or rule K added) | computes |
| Match on an unknown one-shape proof, producing data | stuck (or rule S added) | takes its branch |
| Two proofs of `∃ x, p x` with different witnesses | different (`soundness/proof-irrelevance-04`) | equal (the witness can't be got out into data: `E-PROP-ELIM`) |
| Does `f p ≡ f q` depend on `f`'s body? | yes (the inert marks) | no |
| Comparison modes | two (normal, shortcut) | one |
| A term accepted at a type can compute to one refused at it | yes (§5.7 of the October note) | no **[inferred]** |
| `transparent theorem` | needed as the escape hatch | meaningless; not added |
| Can a proof's body affect another declaration? | not when sealed, except through marks of *definitions* and through `transparent` | no rule reads one |
| What the checker computes with | data, plus proofs where something inspects them | data only, as `run` does |
| Kernel work | small: default flag, keyword | large: marks, K, S, deletions |
| Closest system | Rocq (`Qed`/`Defined`, relevant `Prop`) | Lean 4 |

**Sealed-theorems.md's option B is E1 with rules K, S and P added.** It gets most of E2's
user-visible gains, and it was that note's recommendation. It differs from E2 in three ways:
rule P is one-sided (a sealed proof against a hypothesis `h` is still "different"); K under
positional masks keeps the subject-reduction gap, as that note says; and the positional
machinery (inert marks, shortcut mode) all stays, next to the new rules. E2 is the same three
rules done uniformly, after which the positional machinery has nothing left to do.

**A third end state, briefly: a separate sort of strict propositions** (Rocq's `SProp`; option
C of the October note). Proofs in the new sort are all equal; ordinary `Prop` stays as it is.
It has a published decidability proof, but it splits the logic in two, `rewrite` can't use a
strict equation (no cast out of the sort), and std's 4,301 theorems would each have to pick a
side. Not recommended, for the reason October gave: "propositions are types" stops being one
story.

**Typed comparison instead of marks** (Lean's implementation of E2: infer the type of what is
being compared) is a way to build E2, not another end state. It would also lift the record-eta
limit of section 6.2. It needs types during comparison, which Stitchwort's values don't have;
October's verdict ("a rewrite of `conv` and the unifier") still holds, and marks get nearly
all of it.

## 3. E2: the rules

Write `|t|` for `t` with every proof replaced by a blank `□`. E2 in one line: **two values of
one type are equal exactly when their normal forms are equal after blanking**, with the eta
rules as today. Four rules give that.

- **Rule I (irrelevance).** In conversion and unification, if both sides are proofs, they are
  equal, and nothing inside them is looked at. (Precondition, as today: both sides have one
  type. If one side is a proof and the other visibly is not, that precondition has been
  broken: an internal error in test builds, "different" otherwise.)
- **Rule K (casts).** `J P d p`, where `p: x = y` and the result is data, has the head of `d`
  whenever `x ≡ y`. The proof `p` is never inspected. (`x ≡ y` always holds when `p` is
  `byComputing`, so today's rule is a special case.)
- **Rule S (one-shape matches).** A `case` on a proof of a proposition with one constructor,
  producing data, takes its branch whatever the proof is, each field bound to a stand-in "that
  field of the proof" (itself a proof). For an indexed proposition the constructor's result
  indices must be `≡` the scrutinee's (rule K is the instance for `=`); see section 4.4.
- **Rule F (proofs are frozen).** A `J` or `case` whose result is a proof, and a call of a
  definition or theorem whose type is a proposition, is a neutral value. It is never computed,
  because rules I, K and S leave nothing that would read the result.

K and S fit the frame `docs/core.md` already has ("The equality rule"): each is a new *lazy
form*. A cast whose ends are equal is a lazy form of its base; a one-shape match on a proof is
a lazy form of its branch. Rule E (eliminations decide on the head) and rule C (comparison)
then apply unchanged.

**What this does to each construct.**

- `byComputing` (`Refl` checked by comparison): proves `p = q` for any two proofs, and
  everything it proves today **[inferred: every rule above only adds equalities, section 7]**.
- `J`: into a proposition, frozen; into data, rule K. It needs its two ends at hand, so a `J`
  whose result is data carries them (filled in by the checker; `rewrite` and `calc` steps
  inside theorems are `J`s into propositions and carry nothing).
- `case` on a proof: into a proposition, frozen; into data, rule S; with no possible branch,
  stuck as today, and two such are equal as today.
- Record eta: unchanged, including the limit to records with a field that isn't a proof
  (section 6.2).
- Index unification: an equation between two proofs is always deleted, so `E-INDEX-STUCK` no
  longer arises from one. Proofs are still never taken apart to find a conflict (D137).
- Theorems: never unfolded by anything. "Sealed" stops being a flag and becomes a consequence.
  A `def` whose type is a proposition is the same to the kernel.
- Erasure and `run`: unchanged. The checker now agrees with them.
- Termination check: unchanged. It reads descent from the terms and never through a proof
  (`docs/core.md`, "Relevant data only") **[verified]**.
- Hashes: a term's hash still covers its proofs (it identifies the checked term). The marks
  are a function of the checked term, so they needn't be hashed if the kernel recomputes them
  on replay, as it does for inert marks today; a data-`J`'s ends are part of the term and are
  hashed. The interface hash of sealed-theorems.md §3.8 (a user's hash covers a theorem's
  statement only) is then justified by the kernel's rules, not by a flag. `hash.rs`'s
  `proofless_hash`, which that note set aside because it "blanks proof arguments inside
  definitions, which the kernel can still compare", becomes exactly the identity the kernel
  sees **[inferred]**: a candidate for the interface hash of *definitions* too.
- Check cache: stores the marks or recomputes them; nothing else changes beyond
  sealed-theorems.md's stage 3.

## 4. How the checker knows "this is a proof" without types

### 4.1 Why one bit per binder is enough

Three facts about Stitchwort's core **[verified in `docs/core.md`, "Universes"]**:

1. Every type has exactly one sort: no cumulativity, no universe polymorphism.
2. `Prop` is impredicative: `(x: A) → B` is a proposition exactly when `B` is.
3. A theorem's type is a proposition (`E-NOT-A-PROP`).

From 2: `f a` is a proof exactly when `f` is. So whether an application is a proof is decided
by its head, whatever the arguments. From 1: "its type is a proposition" survives substitution,
so a mark set once stays right. This is the argument Rocq's `SProp` rests on (Gilbert et al.
§4.5, Prop. 4.4 **[earlier]**), and Rocq's kernel does it with marks cached on binders, "used
to efficiently implement proof irrelevance" **[verified, R1]**.

### 4.2 Where the marks live

A mark is one bit: "the type here is a proposition".

| Where | Mark | Who sets it |
|---|---|---|
| `Lam` binder, `Pi` binder, `let` | the bound variable is a proof | the kernel, when it checks the binder's type (it computes that type's sort already) |
| variable in the checker's context; a variable made during a comparison (going under a `Lam` or `Pi`) | copied from the binder | the kernel |
| constructor field, data-type parameter | exists today (`Ctor::field_sorts`, `Data::proof_params`) | the kernel |
| a data type itself | its sort is `Prop`, so its constructors' values are proofs | exists |
| definition, theorem, assumption, axiom | its type is a proposition | the kernel, from the signature's sort |
| `case` and `J` | the result is a proof (the motive's sort) | the kernel; it compares that sort today for `E-PROP-ELIM` |
| `Quot.lift` | the result type's sort (`Quot.ind`'s result is always a proof) | the kernel |
| metavariable (elaborator only) | from its type when created; "unknown" while that type's sort is unsolved | the elaborator |

The marks on `Lam` are the one real addition to the term format: a lambda has no domain in
the core, and two lambdas are compared by going under them with no type at hand. They are what
closes the hole October's "stage 3" left ("variables bound inside the comparison have no
mark").

### 4.3 The test

`is_proof(v)`, constant time, no forcing:

- a neutral: the mark of its last elimination that isn't an application (`.i` → that field's
  mark; a stuck `case`, `J` or `Quot.lift` → its result mark), or, with none, its head's mark
  (variable, definition, assumption, metavariable);
- a glued or folded call: the definition's mark (so a proof call is never forced);
- a constructor: its data type's sort; `Refl`: yes;
- a lambda: not decided here; the comparison goes under it and asks about the bodies;
- a sort, a function type, a data type: no.

Conversion's first step is "both `is_proof`? equal". The elaborator's unifier does the same,
with today's proof-position rule kept: if one side is a bare solvable unknown it is solved
with the other; otherwise nothing inside is looked at or solved. An unknown whose mark is
"unknown" is compared as data; that can only fail to find an equality or solve from inside a
proof, and the kernel re-checks. Where the unifier pairs arguments whose types needn't agree
(`?m a` against `f b`, `docs/core.md` "Record eta", `NO_ETA`), the skip needs both sides
marked. The reference evaluator gets the same test and the same four rules, written
independently, as it has the inert validator today.

**The kernel computes the marks; it never trusts them.** A mark that wrongly says "proof" on
data would make the kernel call two different numbers equal. Rocq's manual says of marks made
outside its kernel only that they "may generate incorrect marks resulting in bugs", typically
a conversion that wrongly fails **[verified, R1]**; I take the conservative reading and have
the kernel derive every mark from a sort it computed itself, refusing (`E-MALFORMED`) a term
whose stored mark differs.

### 4.4 Rule S and a user's own indexed propositions (needs a decision)

`E-PROP-ELIM` lets a proposition be matched into data if it has at most one constructor, all
of whose fields are proofs, and isn't self-referential (D1980). Besides `=`, that admits a
user's own indexed proposition **[run, `indexed-prop.sw`]**:

```
type Same (a: Type) (x: a): a → Prop = | MkSame: Same a x x
def carry (x y: Nat) (h: Same Nat x y) (n: Nat): Nat := match h with | MkSame => n
```

Today `carry x x MkSame 4` computes and `carry x x h 4` is stuck. Under E2 that can't stay: `h`
and `MkSame` are equal proofs, so the two calls are equal by their arguments and different by
their unfoldings, which is the non-transitivity Lean has for `Acc` (Carneiro §3.1.1
**[earlier]**). Two ways out: (a) rule S covers indexed propositions, checking the
constructor's result indices against the scrutinee's as rule K checks `=`'s two ends, so the
`case` carries the scrutinee's indices as a data-`J` carries its ends; Lean does this for
propositions with one constructor and no fields beyond the parameters (`to_cnstr_when_K`
**[earlier]**). (b) `E-PROP-ELIM` refuses indexed propositions other than `=` into data unless
every branch is impossible. I recommend (a): it accepts strictly more than today and makes `J`
the one built-in instance of a general rule. How many such matches std, `tools/fmt` and AoC
contain was not counted.

## 5. Soundness and decidability, honestly

### 5.1 Soundness: the model argument

The model is the one the kernel already leans on three times (axiom K through index
unification's deletion rule; the proof-position skips; `run`'s erasure): every proposition is
a set with at most one element (Carneiro's model of Lean, §6, Corollary 6.8 **[earlier]**).

- Rule I is that model's defining property, given that both sides have one type.
- Rule K: `x = y` has an element only if `x` and `y` are the same, and then the cast is the
  identity. It is Lean's rule **[earlier, L2]**.
- Rule S: a proposition that passes `E-PROP-ELIM` has at most one proof, and its fields are
  proofs; the branch receives proofs, which are all equal.
- Rule F computes nothing.

So every equation E2 adds holds in the model, and E2 is sound **if the rest of the kernel is
sound in that model**, which is the same condition D1′ rests on (October's note §5.6, its
review §1: "sound") **[earlier; the extension to I, K, S is inferred]**. Nothing here is
mechanised, as nothing in the kernel's metatheory is.

**The precondition carries more weight.** Today "both sides have one type" matters at masked
positions. Under E2 a caller that hands `conv` two values of different types gets "equal"
whenever both are proofs. October's audit of every caller (§7.4) is 19 days and many kernel
changes old; it must be redone. E2 does supply a tripwire D1′ can't: one side marked a proof
and the other visibly data means a caller broke the precondition.

### 5.2 Transitivity, stability, subject reduction

Under E2 the relation is "equal after blanking proofs", and blanking is a function of the
term, so the relation is an equivalence **provided evaluation commutes with blanking**: no
step may depend on what a proof is. Rules K, S and F are exactly that proviso; D1′ fails it at
`Box.unbox` and at every `J` (hence the shortcut mode and the inert marks). **[inferred]**

- *Stability* (property 5 of the test of record): a pair equal with `n` unknown stays equal
  once `n` is known. Fails today for proof fields: `depth (MkBox p) n = depth (MkBox q) n`
  checks for every `n` and is refused at `n = 1` **[run, `underStuck` and `atOne`]**. Holds
  under E2.
- *Subject reduction:* a K step takes `J P d p: P y p` to `d: P x byComputing`; those types
  are equal because `x ≡ y` (the rule's condition) and `p ≡ byComputing` (rule I). The §5.7
  example (`castViaBox … byComputing` computing to an `x` the checker refuses at `f q`) is
  accepted: `f p ≡ f q` by the marks on `p` and `q` **[run today as refused, probe 6;
  inferred for E2]**.
- *Opaque definitions:* "being transparent only ever adds equalities" holds without the
  shortcut mode, for the same reason.

### 5.3 The Abel-Coquand program

"Normalization fails in type theory with an impredicative universe of propositions" and "a
proof-irrelevant propositional equality" **[verified, AC abstract]**. Their term `Ω h`, under
the false hypothesis `h` that all propositions are equal, reduces to itself through a cast
that fires without looking at its proof. Stitchwort accepts the program today, because `J` is
stuck on `h Top a` **[run, `abel-coquand.sw`]**. October concluded "no K-like rule";
sealed-theorems.md expected rule K to turn it into `E-RESOURCE`.

Under E2 neither happens, because **every term in the loop is a proof**: `delta: Top`,
`omega h: Bot`, and the cast's result has type `a: Prop`. Rule K is for casts that produce
data; this cast is frozen by rule F, and `omegaUnfolds` (an equation between two proofs of
`Bot`) holds by rule I without evaluating either side. To make the *checker* loop, data would
have to demand the proof's value, and the only doors from a proof into data are rules K and
S, which don't open the proof **[inferred]**.

This is not only my reading. Pujet and Tabareau (POPL 2023) asked whether Abel and Coquand's
result "stems from a fundamental incompatibility between UIP and impredicativity" or whether
"a more suitable algorithm could decide type-checking", and proved "decidability of conversion
for the resulting system ... by harnessing proof-irrelevance to avoid computing with
impredicative proof terms" **[verified, PT abstract]**. Their system is not Stitchwort's (its
cast computes by the structure of the two types), so this is support for the approach, not a
proof about E2. Rocq's own non-terminating example for its "Definitional UIP" flag needs an
impredicative *proof-relevant* sort **[verified, R1]**, which E2 doesn't have: its impredicative
sort is the irrelevant one.

What remains unproved is what is unproved today: that *data-level* evaluation of well-typed
terms terminates ("Assumed" in October's table). E2 adds K and S steps to it. A fired cast
between two equal types can be deleted from the term without changing its type, and a fired
one-shape match is a `let`; so I see no new way to loop **[inferred, a sketch]**. If one
exists, the budget reports `E-RESOURCE`; a wrong answer would need a soundness failure, which
is section 5.1's question, not this one.

### 5.4 Carneiro's undecidability

His construction needs a recursive proposition matched into data (`Acc`), so that a function
can be unfolded one more step at any time **[earlier, L4 §3.1]**. D1980 refuses exactly that
(`E-PROP-ELIM`: no field's type mentions the proposition) **[verified, `docs/core.md`]**. His
second source, a quotient of a proposition, is `E-UNIVERSE` **[earlier]**. Lean has a third
that E2 would not: it leaves a match on a stuck proof of a structure like `And` stuck (or did
in October; sealed-theorems.md's later read disagrees, its "least certain fact"), so `f h` and
`f ⟨h.1, h.2⟩` are equal by arguments and not by unfolding; rule S computes both. So E2 would
be Lean's design without `Acc` and with eta for one-shape proofs. I know of nothing
Carneiro-like left, and I did not find a published decidability result for this exact
combination **[not verified]**.

### 5.5 `Quot.sound`, assumptions, stand-ins

- `Quot.sound a b r: Quot.mk a = Quot.mk b` is a proof by its head. A cast along it fires only
  if `Quot.mk a ≡ Quot.mk b`, where it is the identity in the quotient model; otherwise stuck,
  as today. `Quot.lift`'s proof argument is never inspected, today or under E2.
- An assumption (`?`) or a failed proof's stand-in whose type is a proposition is a proof by
  its head, equal to any other proof of that proposition, and casts along it fire when their
  ends agree. That is the model's answer and `run`'s. Whether a result *relies on* an
  assumption is a walk over checked terms, not a comparison, and is unchanged: a proof that is
  never evaluated is still walked.

### 5.6 Soundness bugs in other systems' irrelevance

| Bug | Cause | What prevents it here |
|---|---|---|
| Agda #2170 (proof of `⊥`, 2.5.3) **[earlier]** | a *data* field marked irrelevant, then matched | marks come only from sort `Prop`, never from "erased" (`field_sorts`, not `field_erased`); matching a proof into data is still `E-PROP-ELIM`. `soundness/proof-irrelevance-01`, `-02`, `-03`, `-06`, `-09` stay refusals |
| Agda #8699 (`--safe` proof of `⊥`, fixed Aug 2026) **[earlier]** | the termination checker counted descent through an irrelevant argument | termination reads real matches on relevant data only; `-07` and `-14` stay refusals. Rule S's stand-ins are evaluator values the termination check never sees |
| Rocq: marks made outside the kernel **[verified, R1]** | a binder marked wrongly | the kernel derives every mark from a sort it computed; the reference evaluator re-derives them |
| Rocq: "conversion checking through bytecode or native code compilation currently does not understand proof irrelevance" **[verified, R1]** | a second evaluator without the rule | every mode (kernel, glued, reference, plain, unifier) gets rules I, K, S, F; the test of record holds each to the plain one |
| Rocq Definitional UIP loops **[verified, R1]** | the cast rule with an impredicative relevant sort | no such sort (5.3) |
| Lean: comparison not transitive, subject reduction fails (not unsound) **[earlier, L4]** | `Acc`; no eta for one-shape proofs | D1980; rule S |
| Any system: a term with two sorts | cumulativity or sort polymorphism across `Prop` | none today; **a constraint on later work**: never add either across `Prop` (Rocq forbids it for `SProp`) |

## 6. What E2 removes and adds

Sizes are **[estimated]** from file sizes and greps (`inert.rs` 277 lines; "shortcut" appears
44 times in `value.rs`, 30 in `unify.rs`, 6 in `reference.rs`), not from a design.

### 6.1 Goes

| What | Why it exists | About |
|---|---|---|
| Inert-parameter analysis (`inert.rs`, `Def::inert_params`, the reference validator, the fixed point over groups, the marks of opaque bodies) | a definition may compute with its proof | 400-500 lines |
| Shortcut mode in `conv`, the unifier (U1-U5) and the reference evaluator; `CallMemo` and the tree memo keyed by mode | unfolding could tell apart what the masks equated | 300-500 lines |
| Unfolding a theorem for `J`, `case` and comparison ("Theorems stay folded", `unfold_folded_head` for proofs, known gap G12) | finding the literal `byComputing` or constructor | 200-400 lines |
| The opaque flag as the means of sealing theorems; `transparent theorem` (never added) | | small |
| `E-INDEX-STUCK` from an equation between proofs | | small |
| The char-arm regression accepted in stage 2 of D1′ (`reject/char-arm-opaque-call.sw`), `Bool.canonicalTrue` in `Float` | shortcut mode | small, user-visible |
| About 15 of the 26 `examples/soundness/proof-irrelevance-*.sw` become accept examples (`-04`, `-05`, `-12`, `-13`, `-15`, `-17` to `-19`, `-21` to `-25`, `-27`): they record D1′'s chosen limits, not unsoundness **[inferred from their header comments]** | | |

### 6.2 Stays, contrary to what was hoped

- **Record eta's limit (D1981)**: a record in `Type` whose fields are all proofs gets no eta.
  With eta, two unknowns of such a type would have to be equal, and the comparison can't tell
  from marks that a *data* value has that type. Rocq, with the same untyped comparison, has
  the same rule: such records "are allowed but do not have η-conversion" **[verified, R1]**.
  Lifting it needs a third mark ("its type has only one value") or typed comparison.
- **SW-4661** (`rewrite`'s search compares proof fields syntactically): still needed, but as
  an instance of one rule: every syntactic matcher in the elaborator compares modulo proofs,
  using the same marks, which are now in the terms.
- **The same-type precondition** (5.1).

### 6.3 Arrives

| What | About |
|---|---|
| Marks: on `Lam`, `Pi`, `let`, `case`, `J`, definitions; on context and comparison variables; set and checked in `check.rs`; `is_proof` | 300-500 lines in the kernel; a mechanical change wherever the elaborator builds a binder |
| Rule K: ends on a data-`J`, the lazy form, the evaluator calling the comparison | 200-300 |
| Rule S, with indices (4.4) and a stand-in for a proof's field | 150-300 |
| The same in the reference evaluator and the unifier (metavariable marks, re-reading a waiting cast when an unknown is solved) | 300-500 |
| Test of record: K and S as wrapping cases; stability over proof fields; the tripwire | tests |

**Net:** about even in lines **[estimated]**; fewer ideas. `docs/core.md`'s "Proof
irrelevance" paragraph (about 600 words of positions, inert conditions and modes) becomes
section 3's four rules and 4.2's table, perhaps a third of the length; "Theorems stay folded"
shrinks to a sentence; the shortcut-mode clauses leave "Glued calls" and rule C; `J`'s typing
and the lazy-form list grow.

**The one new kind of thing:** computing a head can now call the comparison (rule K's
`x ≡ y`). In the kernel there are no unknowns, so a cast that didn't fire is re-read like any
lazy form when something inspects it. In the elaborator it must be re-read after an unknown in
its ends is solved, as kept unfoldings are (`meta_epoch`). How the kernel's branch refinement
(index solutions "substituted throughout the context and the goal") interacts with a cast that
was stuck before the substitution I did not trace **[not verified]**; getting it wrong loses
an equality, not soundness.

## 7. What users would see

Probe files, run today **[run]**; the E2 column is a prediction **[inferred]**, since nothing
is built.

| Program ([`e2-only.sw`](full-proof-irrelevance/e2-only.sw) unless named) | Today and E1 | E2 |
|---|---|---|
| 1. `p = q := byComputing` for `p q: a` | `E-REFL` | checks |
| 2. `f p = f q` for a local `f: a → Nat` | `E-REFL` | checks |
| 3. `cast a a h x = x` for a variable `h: a = a` | `E-REFL` | checks (K) |
| 4. `castNat n 5 = 5` for every `n`, a cast along `Eq.flipped (addZero n)` | `E-REFL`; sealed, also at `n = 3` (sealed-theorems.md, program 2) | checks (K) |
| 5. `pick a b h 3 = 3`, a match on an unknown `h: Both a b` into data | `E-REFL` | checks (S) |
| 6. `x: f q` where `x: f p` | `E-TYPE-MISMATCH`, though `castOk` computes to it | checks |
| 7. `Box.unbox (MkBox p) = Box.unbox (MkBox q)` | `E-REFL` | checks |
| 8. `depth (MkBox p) 1 = depth (MkBox q) 1` | `E-REFL`, though it checks for an unknown `n` | checks |
| 9. `secret (MkBox p) = secret (MkBox q)`, `secret` opaque | `E-REFL` (shortcut mode) | checks |
| `carry x x h 4 = 4` ([`indexed-prop.sw`](full-proof-irrelevance/indexed-prop.sw)) | `E-REFL` | checks, if Q2 is (a) |
| Hedberg's statements by `Prop.irrel` ([`checks-today.sw`](full-proof-irrelevance/checks-today.sw)), sealed or not | checks | checks; `Prop.irrel` itself is `byComputing` |
| [`abel-coquand.sw`](full-proof-irrelevance/abel-coquand.sw) | checks | checks (5.3) |
| `PrefixSums.atOf` with theorems sealed (SW-4659) | fails without a two-line edit | checks unedited |

**Checks today, might not under E2:**

- A program where the elaborator solves an unknown only by matching two proofs structurally
  (`lemma ?n` against `lemma 3` where no type mentions `?n`). E2 doesn't look inside. This is
  already the rule at proof positions; under E2 it is the rule everywhere. Lean's unifier
  compares the two proofs' *types* at this point, which Stitchwort can't. I know of no
  instance; stage 2's counter measures it. **[not verified]**
- If Q2 is answered (b): matches of a user's indexed proposition into data.
- Nothing else: rules I, K and S only add equalities, and a proof that computes to
  `byComputing` today has ends that are equal **[inferred]**.

**The mental model.** E1: "proofs in fields, and in arguments the function only passes along,
never matter for equality, but still compute". E2: "which proof you have never matters". The
error "computing both sides gives `p` and `q`" disappears from the language.

## 8. Performance (all estimated)

- *Sealing alone changed nothing:* whole `tools/fmt`, 103.9 s unsealed and 102.9 s sealed
  **[measured, SW-4657]**. E2's rule F removes the same unfoldings, so expect the same: none.
- *Saved:* comparisons stop at a proof instead of walking it; the shortcut mode's second pass
  and second memo go; proof arguments needn't be evaluated at all (a later optimisation).
- *Added:* one bit test per comparison; a comparison of two ends at each data-producing cast
  whose proof isn't literal, usually of two identical values. Such casts are rare: `rewrite`
  inside a theorem is a cast into a proposition and is frozen.
- *Term size:* a bit per binder; two terms on each data-`J`.
- I expect no measurable change either way on today's corpora, and would not sell E2 on speed.
  The speed case is sealed-theorems.md's: interface hashes, the check cache and parallel proof
  checking, which E1 and E2 both allow.

## 9. Stages

| Stage | What | Measure | Who |
|---|---|---|---|
| 1 | **Seal every theorem now, with no new keyword** (D3719, changed). Add `Prop.irrel` to std (the `Box` construction, a theorem since D1′); prove `Decidable.symThenSelf` and `Bool.symThenSelf` by it, or delete the Hedberg chain in favour of it; apply SW-4659's two-line edit to `PrefixSums.atOf`; refuse a theorem in an `unfolding` list; and the five accept examples stage 0 lists: three exist to test theorem unfolding and are rewritten, `omega-basics`'s `transportComputes` (a cast along `arithmetic`'s proof, computed) waits for rule K, and `and-guard-proof-in-induct` needs the equation generator to read a proof's statement, not its body. Right under E1 and E2 alike | std, `tools/fmt`, AoC and the roguelike check sealed with an empty exception list; the examples as listed | Opus |
| 2 | Interface hashes and check-cache keys (sealed-theorems.md stages 2, 3). Independent of the rest | as there | Opus |
| 3 | Marks, with no change to what's accepted. Counters under a switch: unknowns solved inside a proof (the inference E2 gives up), casts and one-shape matches into data on a proof that isn't literal, indexed propositions matched into data | the counts over std, `tools/fmt`, AoC, roguelike; the reference evaluator re-derives every mark | Opus + Fable review |
| 4 | Rules K and S as lazy forms. They only add equalities, so they can land under D1′ | test of record with K and S wrapping cases; `soundness/-05`, `-17`, `-21` move to accept | Opus + Fable review, after a redo of October's §7.4 audit |
| 5 | Rule I everywhere and rule F, **together with** deleting the shortcut mode and the inert analysis (deleting them before K and S would break transitivity; keeping them after is dead weight). `docs/core.md`, the guide, the remaining examples | test of record: equivalence, stability over proof fields, plain agreement; `e2-only.sw` checks | Opus + Fable review |
| 6 | Remove the opaque flag from theorems (rule F does its job) | no hash depends on a proof body | Sonnet |

If Matt chooses E1 instead: stage 1 as above, plus `transparent theorem` (so far unused by
any library code), stage 2, and stop; K, S and P remain available as sealed-theorems.md
describes them.

**Is `transparent theorem` needed?** Under E2, no, and it couldn't mean anything. Under E1 it
is the only way to compute a cast along a lemma, but after stage 1 nothing in std,
`tools/fmt`, AoC or the roguelike uses one **[measured for the corpora by SW-4657 and the
orchestrator's whole-AoC run; the Hedberg replacement run on a probe only]**. So stage 1 can
ship without the keyword whichever way Q1 goes. Under E1 the keyword (or rule K) would be
added later, when a program first needs a computed cast along a lemma; `transportComputes` in
`examples/accept/omega-basics.sw` is the one we have.

## 10. Decisions for Matt

**Q1 (suggested D3721): which end state?**
*The problem:* today the checker ignores which proof you have only in some places, and has to
track which places; sealing theorems on top of that leaves an escape hatch and a few odd
refusals. *The change:* E2: the checker ignores which proof you have everywhere, as a running
program already does, built in stages 3 to 6 with a soundness review at each. *What it should
do:* the nine probe programs check; nothing can depend on a proof's body, with no keyword to
opt out; three kernel mechanisms go and one rule replaces them; no speed change expected
(estimated). *Risk:* a big kernel change whose soundness rests on an argued model, not a
machine-checked one, like the rest of the kernel; termination of checking remains assumed, as
today. **[rec: E2.]**

**Q2 (suggested D3722), only if Q1 is E2: a user's own indexed one-shape proposition matched
into data** (`Same x y`, section 4.4).
*The problem:* it is accepted today and computes only on a literal proof, which E2 can't keep.
*The change:* (a) the kernel computes it whenever the indices agree, as it will for `=`; or
(b) refuse such matches and have people use `=`. *What it should do:* (a) accepts more than
today; (b) accepts less. **[rec: (a).]**

**Q3 (suggested D3723): seal theorems now, without a `transparent theorem` keyword** (stage 1,
replacing D3719's held stage 1).
*The problem:* D3719 planned a keyword as the escape hatch; the measurements say library code
needs it for two proofs, and those two have a one-line proof that needs no hatch. *The
change:* seal by default; no keyword; `Prop.irrel` in std. *What it should do:* a changed
proof can no longer break another declaration, in everything we have, starting now, whichever
way Q1 goes. *What it costs:* one example declaration (a cast along `arithmetic`'s proof,
computed on numbers) stops checking until rule K lands; under E1 it would need the keyword
after all. **[rec: yes.]**

Not Matt's, noted for the orchestrator: marks rather than typed comparison (4.1); the order of
K and S before I (stage table); a `def` whose type is a proposition is treated as a theorem.

## 11. What I could not verify

- **No proof** that E2's comparison is decidable or that data-level evaluation terminates.
  The nearest published results are for other calculi (Gilbert et al.: no cast out of the
  strict sort; Pujet and Tabareau: cast by type structure). Sections 5.2 to 5.4 are argued.
- That the evaluator can freeze every proof-typed elimination cheaply (rule F), and that
  nothing but `case`, `J` and comparison reads a proof's value today: taken from
  `docs/core.md` ("only three things look inside a proof ... Natives never take a proof"),
  not from the code.
- How branch refinement in the kernel treats a cast that was stuck before an index was solved
  (6.3).
- How often the elaborator solves an unknown from inside two proofs today (section 7).
- How many indexed propositions are matched into data in our code (4.4).
- October's audit that every caller of `conv` and `unify` passes one type: not redone.
- Whether Lean's kernel today takes the branch of `And.rec` into data on a stuck proof (the
  two earlier notes disagree); the Lean and Agda facts marked **[earlier]** were not re-read.
- The E2 column of section 7's table: predictions. The sizes in section 6: greps.
- The Hedberg replacement was run on a probe file, not on std itself; a sealed run of all of
  std with it is the verifier's or Overmind's.
- Rocq's non-terminating example was read in the manual's words through a summarising fetch
  tool, as were all web sources; quotations are as it returned them.

## Sources

Read on 23 November 2026:

- **[R1]** Rocq reference manual, "SProp (proof irrelevant propositions)": records with only
  strict fields, Definitional UIP and its non-termination, relevance marks, bytecode
  conversion. <https://rocq-prover.org/doc/master/refman/addendum/sprop.html>
- **[AC]** Abel and Coquand, "Failure of Normalization in Impredicative Type Theory with
  Proof-Irrelevant Propositional Equality", LMCS 16(2), 2020 (abstract today; §1 for the
  October note). <https://arxiv.org/abs/1911.08174>
- **[PT]** Pujet and Tabareau, "Impredicative Observational Equality", POPL 2023 (PACMPL 7,
  article 74), abstract as given on the conference page; the paper itself not read.
  <https://popl23.sigplan.org/details/POPL-2023-popl-research-papers/74/Impredicative-Observational-Equality>
- `docs/core.md` at `6e5fe356d`: "Universes", "Data types" (`E-PROP-ELIM`, D1980), "Theorems
  stay folded", "Proof irrelevance", "Running a program", "Record eta", "The equality rule".

From the earlier notes, not re-read (**[earlier]**): Lean's kernel (L1, L2) and Carneiro's
thesis (L4), Gilbert et al. (G), Agda #2170 and #8699 (A3), as listed in
[proof-irrelevance.md](proof-irrelevance.md#sources) and
[sealed-theorems.md](sealed-theorems.md#7-sources).

**Decided:** Q1 as D3721 (Matt, 22 Nov 2026): "D3721, yes." The end state is E2.
