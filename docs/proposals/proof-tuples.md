# Proof tuples: a short way to build and take apart "exists/and" facts

Fable paper lane, SW-3514 (D3630, Matt, 16 November 2026: short proofs
become a language goal; this note is the first step). No builds or tests
were run and no code was changed. Code read at `2b3cc6532`. Migration cost
is not counted (D2303).

How claims are marked:

- **[measured]**: counted here with `grep` and one script over
  `tools/toyfmt/src` (58 files, 29,612 lines at this commit, after the
  SW-3490 tidy; the script is described in [§7](#7-what-it-saves-on-the-toy));
- **[read]**: read in this repo, with file and line;
- **[cited]**: from a page fetched for this note (sources at the end, each
  with what was quoted from it);
- **[not rechecked]**: from memory, not confirmed today;
- **[estimated]**: mine; nothing was tried.

## In plain words

**The problem.** A fact such as "there is a start column such that the
token is allowed there and was seen there" is built today as `Witness start
(Both allowed seen)` and taken apart by matching the same shape. The toy
formatter's proof writes those two constructor names 3,980 times and opens
2,620 brackets just to hold them [measured]. The deepest pattern is 28
constructors inside one another (`declarationsRun`,
`tools/toyfmt/src/Toy/Syntax/FileProofs.sw:162-177`); the lanes' own notes
say every error in that part of the proof was a bracket miscount (friction
86, `tools/toyfmt/NOTES.md:2766`).

**The change.** Let the tuple Stitchwort already has do this job. Where a
proof of an `∃` or an `∧` is wanted, `(start, allowed, seen)` builds it;
as a pattern, `(start, allowed, seen)` takes one apart, in `match`, `let`,
lambda parameters and clause lambdas. Tuples already nest to the right
(`(a, b, c)` is `(a, (b, c))`, `docs/syntax.md:1625`), which is exactly
how `∃ x => A ∧ B` is nested, so the flattening needs no new rule. No new
bracket, no new keyword, no kernel change: the checker writes the same
`Witness`/`Both` term as before, so a proof rewritten this way keeps its
hash. Named propositions with several parts that are used in many places
should instead be records with named fields, which Stitchwort already has;
that is a style rule for the guide, not a language change.

**What it should do.** On the toy [measured by rewriting every pattern
with a script, and counting; the rest estimated]:

- all 3,980 constructor names and their 2,620 bracket pairs go (the names
  alone are 3% of the proof's 144,000 words);
- the 673 match arms that open such a fact shrink from 1,105 pattern lines
  to about 770, and the deepest nesting goes from 28 to 2;
- 286 one-arm matches become a `let`, a line and four columns of
  indentation each;
- in all about **600 to 1,100 lines, 3-5% of the proof** [estimated].
  Patterns get much shorter; built proofs get flatter but not shorter.

That is well under the 2,500 to 4,000 lines that toy-proof-complexity.md
§4.3 guessed for this feature, and the note should be corrected: taking
the five largest proofs apart by hand shows that their height is mostly
calls written one argument per line and the same arm written three times,
which are that note's ranks 6 and 4, not this one. What this change buys
is mainly that the proofs read as an argument and that bracket-counting
errors stop; it is still worth doing first because it is small (about two
hours of lane time [estimated]) and everything later (a simplifier,
`cases h`) will want to print and accept the short form.

**Two things found on the way** that cost nothing:

- People already write it. `(rfl, h)` for a proof of `a = a ∧ a = 1` came
  up in AoC 2021 day 6, and the checker now has a special note saying
  "write `Both`" (SW-3419, `crates/elab/src/check.rs:5699-5709`,
  `examples/reject/and-tuple-not-both.sw`). The proposal turns that error
  into the feature.
- `let Witness x (Both a b) := lemma …` is documented as working today
  (`docs/syntax.md:2491-2513`: in a proof a pattern `let` is the one-arm
  `match`), but the toy never uses it: 0 uses against 286 one-arm matches
  on these constructors [measured]. The proving guide doesn't mention it.
  That is a guide fix and a sweep, whatever is decided here.

**Decisions for Matt:** two, in [§9](#9-decisions-for-matt): the bracket
(round, as proposed, or Lean's angle brackets), and whether the short form
is for `∃` and `∧` only or for every type with one constructor.

## Contents

1. [Stitchwort today](#1-stitchwort-today)
2. [What the toy's proofs do with these facts](#2-what-the-toys-proofs-do-with-these-facts)
3. [Other languages](#3-other-languages)
4. [The proposal](#4-the-proposal)
5. [What the elaborator needs](#5-what-the-elaborator-needs)
6. [Error messages](#6-error-messages)
7. [What it saves on the toy](#7-what-it-saves-on-the-toy)
8. [Deferred](#8-deferred)
9. [Decisions for Matt](#9-decisions-for-matt)
10. [Lanes](#10-lanes)

## 1. Stitchwort today

All [read].

**The types** (`crates/elab/src/std/core/Logic.sw`):

```
type And (p: Prop) (q: Prop): Prop = | Both (left: p) (right: q)        -- line 18
type Iff (p: Prop) (q: Prop): Prop = { forward: p → q, backward: q → p } -- line 25
type Exists (a: Type) (p: a → Prop): Prop =                              -- lines 36-37
  | Witness (value: a) (proof: p value)
```

So `∧` is a data type with one constructor whose fields have names, `↔`
is already a record, and `∃` is a data type with one constructor.

**Statements** are short already: `∃ (x y: Nat) => P` nests one `Exists`
per name, `∧` groups to the right, so `∃ (x: T) => A ∧ B ∧ C` is
`Exists T (x => And A (And B C))` (`docs/syntax.md:2138-2165`).

**Building** is by constructor: `Witness x (Both a (Both b c))`. For `↔`,
by record literal: `{ forward = …, backward = … }`.

**Taking apart** is by `match`, with the constructors nested in the
pattern; by a pattern `let`, which in a proof is the one-arm `match`
(`docs/syntax.md:2491-2513`); by a lambda's pattern parameter, `(Witness x
h) => …`; or by a clause lambda (`match | Witness x h => …`,
`docs/syntax.md:2379`).

**Projecting.** `h.left` and `h.right` work on a proof of `∧`, since the
fields are named; the toy uses them 180 times [measured], and std core
uses them (`crates/elab/src/std/core/Equality.sw:115-116`). So friction 27
("no projections for `∧`", `tools/toyfmt/NOTES.md:1284`) was a lane not
knowing them, and what it asks for is a guide line, not a feature. Chains
read badly, though: the third part of four is `h.right.right.left`. `∃`
has no projections and can't have them: a proof may not hand out its
witness as data (`E-PROP-ELIM`), and the type of `h.proof` would have to
mention `h.value`.

**Tuples** (`docs/syntax.md:1625`): `(a, b)` is `MkPair a b`, `(A, B)` is
`Pair A B`, the pattern `(p, q)` is `MkPair p q`, "by identity", and three
or more nest to the right. Their parts must be data, never propositions
(`examples/reject/tuple-prop-component.sw`). The parser's tuple node has
exactly two children (`crates/syntax/src/ast.rs:164`, `:918`), so `(a, b,
c)` reaches the checker as `(a, (b, c))`.

**Records** can be propositions. A proof field gets a projection; a data
field doesn't (`docs/proposals/records.md:831-832`). A record proposition
is built with `{ name = …, … }` (a bare `name` means `name = name`) and
opened with `{ name, .. }` (`docs/syntax.md:487-512`). They have no eta
rule (`records.md:135`), which doesn't matter for proofs, since any two
proofs of a proposition are already equal.

**What doesn't exist.** No anonymous constructor, no `obtain`, and neither
has been proposed or rejected before: `grep` over `docs/` and the board
finds Lean's `⟨…⟩` only in quotations of other people's code. The nearest
things are after-the-toy-proof.md §2.3 ("propositions as records with
named fields") and toy-proof-complexity.md §4.3 rank 2, which this note
answers.

## 2. What the toy's proofs do with these facts

[measured] unless marked.

| What | Count |
|---|---|
| `Witness` written | 980 |
| `Both` written | 3,000 |
| Brackets opened straight onto one of them, `(Witness` or `(Both` | 2,620 |
| Lines holding only the constructor name (the rest didn't fit) | 316 |
| Match arms with one of them in the pattern | 673, on 1,105 lines |
| Of those, one-arm matches (what a `let` would say) | 286 |
| `let Witness …` or `let Both …` | 0 |
| Deepest nesting in one pattern | 28 |

(toy-proof-complexity.md counted 4,157 before the SW-3490 tidy deleted 118
theorems.)

Three shapes cover nearly all of it.

**Shape 1: open a lemma's result, build a similar one.**
`declarationsRun`'s arm for a comment line
(`tools/toyfmt/src/Toy/Syntax/FileProofs.sw:149-161`): the recursive call
gives "there are steps such that joined and runs and values", and the arm
returns the same four parts with the last one adjusted.

**Shape 2: open a big hypothesis that a definition unfolds to.**
`Events`, `Spelled` and `SpelledDeclarations` are defined by cases on the
syntax tree; each case is a chain of `∃` and `∧`. The arm for `let name =
body` in `declarationsRun` opens 5 witnesses and 13 facts (lines 162-177,
16 lines of pattern); `declarationsOut`'s opens 19 parts in two levels
(`tools/toyfmt/src/Toy/Fmt/BlockSpellProofs.sw:1870-1889`).

**Shape 3: build a named proposition's proof.** `Spells`
(`tools/toyfmt/src/Toy/Fmt/SpellProofs.sw:613-619`) is two `∃`s and four
facts; `exprSpells` builds one in every arm (lines 661-690 and on).

In shape 3 the parts are large expressions, so each sits on its own line
whatever the syntax. In shapes 1 and 2 the parts are names, and the cost
is all brackets and constructor names.

## 3. Other languages

For each: how a proof of `∃ x, A x ∧ B x` is built, taken apart and
projected, how nesting is flattened, and what it costs.

### Lean 4

- **Build.** `⟨x, a, b⟩`, the *anonymous constructor*. "The anonymous
  constructor `⟨e, ...⟩` is equivalent to `c e ...` if the expected type is
  an inductive type with a single constructor `c`", and "If more terms are
  given than `c` has parameters, the remaining arguments are turned into a
  new anonymous constructor application. For example, `⟨a, b, c⟩ : α × (β
  × γ)` is equivalent to `⟨a, ⟨b, c⟩⟩`" [cited: L1]. It works for every
  type with one constructor, structures included [cited: L5].
- **Take apart.** The same brackets as a pattern ("This works in both
  pattern and expression contexts" [cited: L1]) in `match`, `let` and
  `fun`; and in tactic proofs `obtain ⟨x, a, b⟩ := h`, `rcases` and
  `rintro`, whose patterns add `p | q` for the cases of an `∨`, `rfl` to
  substitute an equation at once, `-` to drop a hypothesis, and the same
  flattening: "If there are too many arguments, such as `⟨a, b, c⟩` for
  splitting on `∃ x, ∃ y, p x`, then it will be treated as `⟨a, ⟨b, c⟩⟩`,
  splitting the last parameter as necessary" [cited: L2].
- **Project.** `h.left`, `h.right` for `∧` [cited: L3]; any structure's
  fields by number, `h.1`, `h.2`, "numbered beginning with `1`" [cited:
  L5]. `Exists` is a plain inductive type, not a structure, so it has
  neither; `Iff` is a structure [cited: L6].
- **Records as propositions.** `structure … : Prop` with named fields;
  `Iff` is one [cited: L6]. Built with `{ x := e, … }` or the angle
  brackets [cited: L5].
- **Cost.** The expected type must be known: the notation is for "when
  the relevant type is an inductive type and can be inferred from the
  context" [cited: L3], and otherwise it is an error asking for the type
  [not rechecked: the exact wording]. For `∃` the predicate is read off
  the expected type; *Theorem Proving in Lean* shows the trouble when it
  isn't given: "`Exists.intro` has implicit arguments: Lean has to infer
  the predicate `p : α → Prop`" and several predicates fit [cited: L4].
  A wrong count of parts shows up as a type mismatch on the last part,
  not as "too many parts" [not rechecked]. The brackets are Unicode only
  (`\<` `\>` in an editor) [not rechecked].

### Rocq

- **Build.** In tactics, `exists x` then `split`: `exists` is "Equivalent
  to `constructor 1 with bindings`" and applies "when the conclusion is an
  inductive type with a single constructor"; `split` "is typically used to
  split conjunctions in the conclusion such as `A /\ B` into two new goals"
  [cited: R2]. As a term, `ex_intro _ x (conj a b)` [not rechecked]; there
  is no anonymous constructor for arbitrary types.
- **Take apart.** *Intro patterns*, after `destruct … as`, `intros` or
  `assert`: `[ p1 … pn | … ]` "splits an inductive type that has multiple
  constructors"; `( p1 , … , pn )` "matches a product over an inductive
  type with a single constructor"; and `( p1 & … & pn )` "matches a
  right-hand nested term that consists of one or more nested binary
  inductive types", so "`(H1 & H2 & H3)` matches `A /\ B /\ C`" [cited:
  R1]. So Rocq has both forms: the comma form is one constructor with many
  fields, the `&` form is the flattened right-nested chain, and `destruct
  h as (x & a & b)` opens `∃ x, A x ∧ B x`. SSReflect folds the same into
  its `=>`: "`move=> [a b].` `case=> [a b].` `case=> a b.` are all
  equivalent", nesting as `move=> [[a b] c]`, and in terms `let: exist (x,
  y) p_xy := Hp in …` [cited: R3].
- **Project.** `proj1 h`, `proj2 h` [not rechecked]. Records in `Prop`
  exist [not rechecked].
- **Cost.** Two spellings for almost the same thing (`[x [a b]]`, `(x & a
  & b)`), and a pattern with too few names is silently padded: "If there
  are not enough names, Rocq picks fresh names" [cited: R2], which is how
  Rocq scripts come to depend on generated names.

### Agda

- **Build.** `∃` is a library definition over the dependent pair `Σ`, a
  record: "`∃ = Σ _`", with `∃[ x ] B` as syntax, and `A × B` is the
  non-dependent case of the same type [cited: A3]. So one infix
  constructor `_,_` builds pairs of data, `∧` and `∃` alike: `x , a , b`.
  `-, y` is `_ , y`, for a witness the checker can work out [cited: A3].
  Records can also be built by `record { f = e; … }` or by copatterns
  [cited: A1].
- **Take apart.** The same `(x , a , b)` as a pattern in a function
  clause, in a pattern lambda `λ { (a , b) → a }` or `λ where …` [cited:
  A2], and in `let (x , y) = p in …`, which since Agda 2.9.0 "requires
  records with eta-equality" [cited: A1].
- **Project.** `proj₁`, `proj₂` (renamings of the built-in `fst`, `snd`)
  [cited: A3]; any record's fields by name.
- **Cost.** Little in inference, since `_,_` is an ordinary constructor of
  one type. But there is no separate world of propositions, so nothing
  like `E-PROP-ELIM` to explain. Pattern lambdas are compared by where
  they were written: "two pattern lambdas with the same body are not
  considered equal by Agda" [cited: A2].

### Idris 2

- **Build, take apart.** A dependent pair is `(x ** p)`, its type `(x : a
  ** p)`; "`( x ** p )` constructs a value of this type", `_` may stand
  for the first part where it can be worked out (`(_ ** [3, 4])`), and
  the pattern is the same (`(_ ** xs')` in a `case`) [cited: I1]. Plain
  tuples use the comma and "are represented as nested pairs" [cited: I1].
  So Idris keeps two brackets-with-separators: `,` where the parts are
  independent and `**` where the second part's type mentions the first.
- **Cost.** The writer chooses the separator, so the checker never has to;
  the reader can see dependency at a glance.

### Isabelle/Isar

- **Take apart.** `obtain x where a: "A x" and b: "B x" by …`: it "states
  a generalized elimination rule with exactly one case", after which the
  variables and the named facts are in scope [cited: Is1]. Nothing is
  matched by position: the writer *states* the facts they want, with
  names, and automation shows they follow. `consider` is the same for
  several cases [cited: Is1].
- **Build.** By stating the goal and letting a rule or automation find the
  witness, or `show "∃x. …"` with an explicit `exI` [not rechecked].
- **Cost.** It depends on automation to connect the stated facts to the
  hypothesis, and each fact is written out in full. It reads best of all
  of these; it is also the longest.

### F*, Dafny

- **F\*** has sugar that names the connective: `introduce exists x. q x
  with a and f`, `eliminate exists (x:t). p x returns q with pf_p. k x
  pf_p`, `introduce p /\ q with … and …`, and usually none of it is
  written, because one can "rely entirely on the SMT solver to discover a
  proof of `p /\ q`" [cited: F1].
- **Dafny** has `var x :| P;`: choose an `x` such that `P`, where "Dafny
  will report an error if it cannot prove that values exist that satisfy
  the condition" [cited: D1]. Conjunctions are never built or opened by
  hand; the solver does it.
- Both show the far end of the road: with a solver the question
  disappears. Stitchwort's proofs are terms, so it doesn't apply here.
  Liquid Haskell was not looked at.

### What the comparison says

| | Build | Take apart | Flattening | Needs the expected type |
|---|---|---|---|---|
| Lean 4 | `⟨x, a, b⟩` | `⟨x, a, b⟩` in `match`/`let`/`fun`, `obtain` | extra parts nest to the right | yes |
| Rocq | `exists x; split` | `(x & a & b)`, `[x [a b]]` | `&` form only | tactic sees the goal |
| Agda | `x , a , b` | `(x , a , b)` | `,` is right-associative [not rechecked: its fixity is in a file not read] | no |
| Idris 2 | `(x ** a)` and `(a, b)` | the same | nested pairs | no |
| Isabelle | by rule or automation | `obtain x where …` | none needed: facts are named | no |
| **Stitchwort today** | `Witness x (Both a b)` | the same | none | no |

1. **Everyone has a short form, and it is one form for building and
   taking apart.** Stitchwort is the outlier.
2. **Flattening to the right is the common rule** (Lean, Rocq's `&`,
   Agda), and it matches how statements are written.
3. **Agda uses one comma for pairs of data and for proofs alike**, and
   Lean's angle brackets build both too; Idris and Rocq use a different
   mark where the parts aren't plain independent data (`**`, `&`).
4. **The costs are small and known**: the expected type must be known,
   and a wrong number of parts gives a poor message unless the checker
   counts.
5. **Naming the facts** (Isabelle's `obtain … where`, Lean's structures
   in `Prop`) is the answer where position stops being readable.
   Stitchwort's records are that.

## 4. The proposal

One recommendation per question. The end state, written out:

```
-- build: where an ∃ or ∧ proof is wanted
theorem small: ∃ (n: Nat) => n > 2 ∧ n * n = 49 := (7, byDecision, rfl)

-- take apart: match, let, lambda parameter, clause lambda
match lemma xs with
  | (n, big, square) => …

let (n, big, square) := lemma xs

hs.map ((n, big, square) => …)

Exists.elim h (match | n, (big, square) => …)

-- two facts make an ∧ with nothing expected
let both := (big, square)

-- project
both.left
```

### 4.1 Building

**Recommendation: a tuple, checked against the expected type.** `(e1,
e2)` where a proof of `P ∧ Q` is expected is `Both e1 e2`, with `e1`
checked against `P` and `e2` against `Q`. Where a proof of `∃ (x: T) => P
x` is expected it is `Witness e1 e2`, with `e1` checked against `T` and
`e2` against `P e1`. Longer tuples follow from the nesting the parser
already does: `(x, a, b)` is `(x, (a, b))`, so against `∃ x => A x ∧ B x`
it is `Witness x (Both a b)`.

The expected type is looked at after computing it, so a definition that
unfolds to a chain (`Spells layout pending head expr events`) takes a
tuple directly, as it takes `Witness` today.

**With nothing expected,** a tuple whose first part is a proof is an `∧`:
`(h1, h2)` has type `P ∧ Q` when `h1: P` and `h2: Q`. This can't be
confused with a pair, because a pair's parts are never propositions. An
`∃` can't be worked out this way (many statements have the same witness
and proof), so it needs the expected type; §6 has the message.

`Witness` and `Both` remain, as the constructors' names, for the places
where a function is wanted (`hs.map (Witness x)`), as `Cons` remains
beside `[x, ..xs]`.

### 4.2 Taking apart

**Recommendation: the same tuple as a pattern, read by the type of what
it matches.** On a pair it is `MkPair p q` as now; on a proof of `∧`,
`Both p q`; on a proof of `∃`, `Witness p q`. It works wherever a tuple
pattern works today, with no new forms:

| Place | Today | Proposed |
|---|---|---|
| `match` arm | `\| Witness x (Both a b) => …` | `\| (x, a, b) => …` |
| `let` in a proof | `let Witness x (Both a b) := h` | `let (x, a, b) := h` |
| lambda parameter | `(Witness x (Both a b)) => …` | `(x, a, b) => …` |
| clause lambda | `match \| Witness x (Both a b) => …` | `match \| (x, a, b) => …` |
| definition by arms | `\| Witness x (Both a b), ys => …` | `\| (x, a, b), ys => …` |

`_` skips a part: `(_, _, b)`. A part that is itself a chain on the left
side nests visibly: a proof of `(A ∧ B) ∧ C` is `((a, b), c)`.

This is Lean's `obtain ⟨x, a, b⟩ := h` spelled `let (x, a, b) := h`. No
separate `obtain` word is needed, because in a proof Stitchwort's pattern
`let` already is the one-arm `match` and already refines the goal.

Taking a witness out of a proof to compute with stays an error
(`E-PROP-ELIM`), exactly as with `Witness` today.

### 4.3 Projecting

**Recommendation: nothing new.** `h.left` and `h.right` exist; for a
chain, a pattern `let` names the part wanted (`let (_, _, c) := h`); for
a proposition whose parts deserve names, a record gives `h.spelled`. The
proving guide gains a paragraph saying all three.

Lean's numbered fields (`h.2.2.1`) are deferred: they are no more
readable than `h.right.right.left`, and a flattened `h.3` would have to
guess where the chain stops.

### 4.4 Flattening

**Recommendation: only what tuples already do.** `(a, b, c)` is `(a, (b,
c))`, each two-part tuple is read against the type it meets, and that is
all. So a tuple pattern can stop early and name the rest as one fact:
on `∃ x => A ∧ B ∧ C`, `(x, a, rest)` gives `rest: B ∧ C`. That is Lean's
rule and Rocq's `&` rule [cited: L1, L2, R1].

### 4.5 Records instead of chains: when

**Recommendation: a house rule, in the proving guide.** Use a record
proposition when all of these hold:

- the proposition has a name of its own and is used in more than a couple
  of theorems;
- it has four or more parts, or parts easily confused (two facts of the
  same shape);
- it isn't defined by cases on a value (a record is one type; `Spelled`,
  which is a different chain for each kind of expression, has to stay a
  definition, though each case may *name* a record).

In the toy, `Spells` and `DeclarationsSpell` qualify:

```
type Spells (layout: Layout) (pending: List Trivia) (head: Option Nat → Prop)
    (expr: Expr) (events: List Event): Prop =
  { first: TokenView
  , others: List TokenView
  , seen: Seen pending events [first, ..others]
  , spelled: ∀ (from: Nat) (tokens: List (Parse.Located Token)) => …
  , headed: head first.start
  , above: first.above = (waiting pending expr.firstAbove).reverse
  }
```

built with `{ first = …, others = [], seen, spelled = …, headed = allowed,
above = rfl }` and opened with `{ seen, spelled, .. }`. A reader no longer
needs the definition open beside the proof to know which `Both` is which,
and adding a field breaks each use with a message naming the field,
instead of shifting every position by one (friction 11,
`tools/toyfmt/NOTES.md:830`).

Use a tuple for everything else: a lemma's own `∃ … ∧ …` conclusion, the
cases of a definition by recursion, and facts that live for three lines.

A tuple does **not** build or open a record: named things are used by
name. (Lean allows `⟨…⟩` on structures; the price is that reordering
fields silently changes meaning where the types happen to agree.)

One thing to confirm when this is tried: a record proposition whose proof
fields mention its data fields (`seen` mentions `first`) can't have
projections for those fields, for the same reason `∃` can't, so it is
opened by pattern only. I haven't run one; the trial lane in §10 checks it
and the message a `h.seen` gives.

### 4.6 How it fits the rest of the language

- **Operators for propositions, brackets for data** is the existing
  style: `∧` not `And`, `[x, ..xs]` not `Cons x xs`. `(x, a, b)` not
  `Witness x (Both a b)` is the same move, and the constructor names stay
  for use as functions, as `Cons` does.
- **Read by type, not by identity.** Today's tuple is `Pair` "by
  identity". The list bracket already left that rule once: on a
  `NonEmptyList`, `[p, ..q]` is that type's record
  (`crates/elab/src/lib.rs:5010` on). This is the second such case, and
  the rule becomes: a bracket form is read against the type it meets, and
  means the plain data type when there is none.
- **Statements and proofs line up.** `∃ (x: T) => A ∧ B` is proved by
  `(x, a, b)`: one part per binder and per conjunct, in the order written.
- **`↔` stays a record**: `{ forward = …, backward = … }` says which
  direction is which, and a pair of functions would not.
- **`∨` is untouched**: it has two constructors, `match` splits it.

## 5. What the elaborator needs

All [read] for where; the work is [estimated].

- **The parser: nothing.** `Expr::Tuple` and `Pattern::Tuple` exist with
  two children each (`crates/syntax/src/ast.rs:164`, `:918`).
- **Checking a tuple against a type**
  (`crates/elab/src/check.rs:5693-5709`): there are arms for `Pair` and
  for a universe, and a third that catches `∧` only to give SW-3419's
  note. That third arm becomes the construction, and a fourth is added
  for `Exists`. Each builds the constructor application the hand-written
  form would have, so everything downstream (the kernel, erasure, hashes)
  sees nothing new.
- **Inferring a tuple** (`check.rs:2206`, `infer_tuple`): if the first
  part's type is a proposition, build `Both`; otherwise as now. The same
  function already looks at the first part to tell a tuple type from a
  tuple value (`docs/syntax.md:1625`).
- **A tuple whose type isn't known yet** (an argument whose parameter
  type is still an unknown): today it becomes a pair at once. It should
  wait, as a record literal does (`docs/syntax.md:515`,
  postponement.md stage 2), and fall back to a pair if nothing says
  otherwise. This is the one part with any subtlety; if it proves awkward
  it can be left out at first, at the cost of an occasional type
  annotation.
- **Patterns** (`crates/elab/src/lib.rs:4997`): the tuple pattern picks
  `MkPair` unconditionally. It should pick the constructor from the type
  of the column it matches, as the `NonEmptyList` case a few lines below
  does. The other passes that walk tuple patterns (`equations.rs:618`,
  `redundant.rs:195`, `module.rs:3788`, `autobind.rs:629`, `nav.rs`) treat
  it structurally and need a look, not a redesign.
- **Pattern `let`** (`crates/elab/src/patlet.rs`): outside a proof, a
  tuple pattern is turned into projections. That shortcut must not apply
  when the value is a proof of `∃`; the code already asks whether the
  type is a proposition (`patlet.rs:103`, `:153`).
- **Printing.** Where the tool writes a proof term or a pattern for the
  user (the `stitchwort goal` search, the "add the missing arms" fix,
  `E-NONEXHAUSTIVE`'s list), it should write the tuple.
- **The formatter.** A tuple is a "comma bracket": one line, or one item
  per line with the closer on its own line (formatter-style.md S31; S22
  for patterns). A pattern of 18 short names would then take 20 lines,
  worse than today's 16. Tuple *patterns* whose items are all names or
  `_` should fill their lines instead (as many per line as fit). The
  figures in §7 assume that.
- **Not needed:** any kernel change, any new unification. Because the
  expected type is required for `∃`, the predicate is read from it, never
  guessed; the higher-order guess that *Theorem Proving in Lean* warns
  about [cited: L4] doesn't arise.

## 6. Error messages

The wording is a sketch; the content is what matters.

**Too many parts.** The surplus shows up at the innermost tuple, checked
against something that isn't a chain. The message should count from the
outside:

```
E-TUPLE-PARTS: this gives 4 parts, but the goal takes 3
  ∃ (n: Nat) => n > 2 ∧ n * n = 49
    1. a value for `n`
    2. a proof of `n > 2`
    3. a proof of `n * n = 49`
```

**Too few parts** is not an error by itself (the last part stands for
the rest), so when the last part fails to check, the note says what it
stood for: "the last of these 2 parts must prove all of `n > 2 ∧ n * n =
49`".

**No expected type, for an `∃`.**

```
E-CANNOT-INFER: can't tell which statement `(7, rfl)` proves
  note: a witness and a proof fit many `∃` statements. Give the type:
        `((7, rfl): ∃ (n: Nat) => n * n = 49)`, or use it where a goal is known.
```

**A pair where a proof was wanted, or the reverse**, found late (the
tuple was taken for a pair, then met `P ∧ Q`): the mismatch names both
readings, "this was read as a pair of data because nothing said what it
proves when it was checked".

**A tuple pattern on something else.** As today's mismatch, with the
three types a tuple pattern can open listed.

**Taking a witness out as data.** `E-PROP-ELIM` as now; its note should
show the tuple form.

**Gone:** SW-3419's "write `Both <left> <right>`".

## 7. What it saves on the toy

### The script [measured]

A short Python script read every `.sw` file under `tools/toyfmt/src`,
found each match arm whose pattern holds `Witness` or `Both`, rewrote the
pattern to tuples (flattening to the right, keeping left-nested chains as
inner tuples), and counted the lines the new pattern needs at 120
columns, filling lines. It also counted the lines that hold nothing but a
constructor name, and the one-arm matches. It doesn't rewrite
expressions, so the saving in built values is estimated from the
before/after examples below.

### Three real proofs, before and after

**1. `declarationsRun`, the comment-line arm**
(`tools/toyfmt/src/Toy/Syntax/FileProofs.sw:149-161`). Before, 13 lines:

```
    | [{ blankBefore, line = DeclarationNote comment }, ..more], Both lineShaped moreShaped, spelled =>
      match declarationsRun isFirst
        (pending ++ [{ blankBefore, line = DeclarationNote comment }])
        more
        tokens
        endTrivia
        moreShaped
        spelled with
        | Witness steps (Both joined (Both runs values)) =>
          Witness steps
            (Both joined
              (Both runs
                (Eq.trans values (List.appendAssoc pending [{ blankBefore, line = DeclarationNote comment }] more))))
```

After, 15 lines (the last part is too long for the tuple to sit on one
line, by 6 columns, so it breaks as any comma bracket does):

```
    | [{ blankBefore, line = DeclarationNote comment }, ..more], (lineShaped, moreShaped), spelled =>
      let (steps, joined, runs, values) :=
        declarationsRun isFirst
          (pending ++ [{ blankBefore, line = DeclarationNote comment }])
          more
          tokens
          endTrivia
          moreShaped
          spelled
      (
        steps,
        joined,
        runs,
        Eq.trans values (List.appendAssoc pending [{ blankBefore, line = DeclarationNote comment }] more)
      )
```

Two lines *longer*. The nesting is 1 deep, not 4, and the arm reads top
to bottom: get four things, give four things back; but a built proof
that doesn't fit one line pays for the bracket's own two lines. (The base
case just above it, lines 147-148, fits and goes from 2 lines to 1: `([],
Eq.sym noTokens, declarationDeclines [] rfl, Eq.trans notes (Eq.sym
(List.appendNil pending)))`.)

**2. `declarationsRun`, the pattern of the `let name = body` arm**
(lines 162-177). Before, 16 lines:

```
    | [{ blankBefore, line = Value letComments name nameComments equalsComments inner }, ..more], Both innerShaped
          moreShaped, Witness first
        (Witness named
          (Witness equals
            (Witness bodyTokens
              (Witness later
                (Both split
                  (Both atMargin
                    (Both isLet
                      (Both isName
                        (Both nameAllowed
                          (Both isEquals
                            (Both equalsAllowed
                              (Both letCommented
                                (Both nameCommented
                                  (Both equalsCommented (Both noted (Both innerSpelled laterSpelled)))))))))))))))) =>
```

After, 4 lines:

```
    | [{ blankBefore, line = Value letComments name nameComments equalsComments inner }, ..more],
        (innerShaped, moreShaped), (first, named, equals, bodyTokens, later, split, atMargin, isLet, isName,
        nameAllowed, isEquals, equalsAllowed, letCommented, nameCommented, equalsCommented, noted, innerSpelled,
        laterSpelled) =>
```

The same arm in `declarationsOut`
(`tools/toyfmt/src/Toy/Fmt/BlockSpellProofs.sw:1870-1889`) goes from 20
lines to 4 [measured by the script], and the `if` arm at line 597 from 22
to 5.

**3. `exprSpells`, the arm for a name**
(`tools/toyfmt/src/Toy/Fmt/SpellProofs.sw:661-690`). Before, 30 lines:
the pattern, a 10-line `match tokenSeen … with`, the inner pattern, and
an 18-line `Witness (…) (Witness [] (Both seen (Both (…) (Both allowed
rfl))))` of which 13 lines are one call of `leafSpells` with 11
arguments. After, 31 lines: a `let (start, allowed, seen) := tokenSeen
…`, then a six-part tuple whose fourth part is the same 13-line call.
Nothing saved: the height is the two tall calls. This arm is then repeated twice more for numbers and
strings (lines 691-750). Those 60 lines are an or-pattern's to save, and
the 11 arguments are implicit parameters' (toy-proof-complexity.md §4.3
ranks 4 and 6).

### The estimate

| Where | Lines saved | Basis |
|---|---|---|
| Patterns: 1,105 lines to 772 | 333 | [measured], script, filling at 120 columns |
| One-arm matches to `let` (286) | 150-290 | [estimated]: a line each where the call fits one line, none where it doesn't (example 1) |
| Built values: the 316 lines that hold only a constructor name go, but each tuple that still breaks adds its opening and closing lines | -100 to +150 | [estimated] from examples 1 and 3: about even |
| Shallower nesting lets more calls fit on a line (each chain level costs 2 columns; many chains are 4 to 8 deep) | 150-400 | [estimated], the weakest figure: I couldn't run the formatter |
| **Total** | **about 600-1,100** | 3-5% of the 21,770 theorem lines (SW-3490's count) |

Records for `Spells` and `DeclarationsSpell` change few lines either way
(a field name per part where there was a constructor name); their gain is
that the proofs can be read without the definition.

**So the earlier estimate was too high.** toy-proof-complexity.md §4.3
put this feature at 2,500 to 4,000 lines and said the five largest proofs
"are mostly this". By count they are mostly tall calls and repeated arms
with this on top. What the feature does deliver, and what Matt's reaction
to reading the proofs was about:

- 3,980 constructor names and 2,620 bracket pairs gone [measured];
- no pattern nested more than two deep, where 28 was reached;
- the class of error that friction 86 says was *every* error in the
  1,400-line mutual induction (a bracket miscount) mostly gone, which
  saves checking rounds rather than lines;
- a short form for the simplifier and `cases h` to print when they come.

The real formatter's proof is put at 3 to 5 toys, so the same shares
apply to 3 to 5 times the text.

## 8. Deferred

- **Numbered projections** (`h.1`, `h.3`): §4.3.
- **Lean's extra `rcases` patterns**: `rfl` (substitute the equation at
  once) and `p | q` inside a tuple (split an `∨` in place) are both real
  savings in Lean proofs. The first belongs with `match`/`rewrite`
  refinement, the second with or-patterns in proofs
  (toy-proof-complexity.md §4.3 rank 4). Neither is needed for this.
- **Every one-constructor type** (Lean's rule): decision 2 below.
- **Tuple patterns in a theorem's header**, `theorem t ∀ ((x, a): ∃ …)`:
  no use found in the toy.
- **Record update on a proposition**, `{ got | seen = better }`, where the
  new record is an instance of the type with different parameters. Shape 1
  in §2 is this, and it is the one place where records could beat tuples
  on lines. Today's update keeps the type; a design of its own.
- **Isabelle's stated `obtain x where "A x"`**: only worth having with
  automation to justify the stated facts; revisit with the simplifier.
- **The data-and-proof pairs in `Type`** (a value with a proof about it):
  those are records today and should stay so.

## 9. Decisions for Matt

Two, for the orchestrator to number. Both are user-visible syntax.
Everything else in this note (messages, the formatter's fill rule, the
guide's house rule for records, the order of lanes) is the orchestrator's.

**Q1. Which bracket builds and takes apart `∃`/`∧` proofs?**

*The problem:* the toy writes `Witness` and `Both` 3,980 times, up to 28
deep, and its bracket miscounts were the main error in its largest
proofs.
*The options:*

- **(a) The round tuple, read by type**: `(x, a, b)`. Nothing new to
  learn or type; it is what people already write by mistake (SW-3419);
  Agda does the same with its comma. The cost: `(a, b)` no longer always
  means a pair of data. A reader tells which from where it stands (after
  a theorem's `:=`, or matching a hypothesis), and the checker tells by
  type.
- **(b) Lean's angle brackets**: `⟨x, a, b⟩`. Says "a proof, not data" at
  a glance, and Lean users know it. The costs: a second bracket for the
  same idea; every other Stitchwort symbol has an ASCII spelling and this
  one has no good one (`<x, a>` collides with comparisons); and `(rfl,
  h)` stays an error with a note.
- **(c) No new syntax**: teach pattern `let` and `.left`/`.right` in the
  guide, and move named propositions to records. Fixes the one-arm
  matches and the worst-named chains, leaves the 3,980 names.

*What it should do:* (a) or (b) remove all 3,980 names and about 600 to
1,100 lines of the toy [estimated] and cap nesting at 2; (c) perhaps a
third of the lines and none of the nesting. **[rec: (a)]**

**Q2. For `∃` and `∧` only, or for every type with one constructor?**

*The problem:* Lean's short form builds any one-constructor type,
`⟨3, 4⟩ : Point` included. Should Stitchwort's?
*The change, if yes:* `(3, 4)` where a `Point` is expected would be `{ x
= 3, y = 4 }`.
*What it should do:* shorter literals for small data types, at the price
of position instead of names, in a language whose style rules ask for
names at call sites (D2367) and which already has record literals with
punning. For proofs it adds nothing: `↔` is the only other
one-constructor proposition in the core, and it reads better with its
field names. **[rec: `∃` and `∧` only; pairs as now]**

## 10. Lanes

Estimates are agent time, already scaled (a human-style estimate times
about 0.3).

| # | Lane | Model | Estimate | Notes |
|---|---|---|---|---|
| 1 | Tuples as `∃`/`∧` proofs: checking and inferring (§5), patterns in `match`, `let`, lambdas, clause lambdas and arms, the `patlet` guard, the messages of §6; accept and reject examples (`and-tuple-not-both.sw` becomes an accept); `docs/syntax.md` (the tuple row, "Patterns in `let` and lambdas", "Logic notation"), the language guide, and the proving guide's paragraph on building, opening and projecting (pattern `let`, `.left`/`.right`, tuples) | Opus (it writes kernel terms and touches patterns: D2506) | 60 min | Tests by name only: the new examples, the tuple and let-pattern examples, hash snapshots unchanged. No kernel change, so no `docs/core.md` change |
| 2 | Opus review of lane 1's diff (D2364: it generates kernel terms) | Opus, paper | 20 min | Especially: does a tuple ever get read as a proof where a pair was meant, and the postponed case |
| 3 | The tool's own output: `stitchwort goal` search results, missing-arm fixes and `E-NONEXHAUSTIVE` lists write tuples; the formatter fills tuple patterns made of names (§5) | Sonnet | 40 min | The fill rule is a formatter-style change; small, but it re-lays-out existing tuple patterns in `aoc/` |
| 4 | Sweep the toy: every `Witness`/`Both` to a tuple, every one-arm match on one to a `let`; then count lines again against §7 | DeepSeek | 45 min | The check is strong and cheap: every theorem's hash must be unchanged for the tuple rewrite, since the terms are the same. (The `let` rewrite is the same `match`, so it should hold there too; if a hash moves, stop and report) |
| 5 | Trial of §4.5: `Spells` and `DeclarationsSpell` as record propositions; confirm how a record with data fields and dependent proof fields is opened and what `h.seen` reports; write the house rule into the proving guide | Sonnet | 40 min | Reports whether the rule in §4.5 survives contact; if the projection message is poor, a ticket |
| 6 | Correct toy-proof-complexity.md §4.3 rank 2 and after-the-toy-proof.md §2.3 with the measured figure | orchestrator, with lane 4's count | 5 min | |

Lanes 1 and 2 first; 3, 4 and 5 can run together after lane 1 merges.
About 3.5 hours of lane time in all.

Whatever Q1's answer, two things can start now: the proving guide's
paragraph on pattern `let` and `.left`/`.right` (part of lane 1), and the
one-arm-match half of lane 4, which needs no new feature.

## Sources

Fetched 16 November 2026. Each entry says what was quoted from it.

- **[L1]** The Lean Language Reference, "Inductive Types", §4.4.1.3
  "Anonymous Constructor Syntax":
  <https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/>.
  The definition, "both pattern and expression contexts", and the rule
  for extra arguments.
- **[L2]** Lean 4 source, `src/Init/RCases.lean` (doc comments of
  `rcases`, `obtain`, `rintro`):
  <https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/RCases.lean>.
  The pattern forms and the "too many arguments" rule.
- **[L3]** *Theorem Proving in Lean 4*, "Propositions and Proofs":
  <https://lean-lang.org/theorem_proving_in_lean4/Propositions-and-Proofs/>.
  `And.intro`, `⟨hp, hq⟩`, `h.left`, and "can be inferred from the
  context".
- **[L4]** *Theorem Proving in Lean 4*, "Quantifiers and Equality", §4.4:
  <https://lean-lang.org/theorem_proving_in_lean4/Quantifiers-and-Equality/>.
  `⟨t, h⟩` for `Exists.intro`, and the implicit-predicate remark. The end
  of the section (`match`, `let`, `fun` with `⟨…⟩`) was cut off in the
  fetch; [L1]'s "pattern and expression contexts" covers it.
- **[L5]** The Lean Language Reference, same page as [L1], §4.4.2
  "Structure Declarations": fields by index, structure instances, the
  anonymous constructor on structures.
- **[L6]** Lean 4 source, `src/Init/Core.lean`:
  <https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Core.lean>.
  `inductive Exists … | intro (w : α) (h : p w)`; `structure Iff (a b :
  Prop) : Prop`.
- **[R1]** Rocq reference manual, "Tactics", intro patterns:
  <https://rocq-prover.org/doc/master/refman/proof-engine/tactics.html>.
  The grammar of `or_and_intropattern` and the three forms.
- **[R2]** Rocq reference manual, "Reasoning with inductive types":
  <https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/reasoning-inductives.html>.
  `exists`, `split`, `constructor`, `destruct … as`, "Rocq picks fresh
  names".
- **[R3]** Rocq reference manual, "The SSReflect proof language":
  <https://rocq-prover.org/doc/master/refman/proof-engine/ssreflect-proof-language.html>.
  The destructing intro pattern and its equivalents; `let:`.
- **[A1]** Agda documentation, "Record Types":
  <https://agda.readthedocs.io/en/latest/language/record-types.html>.
  Building, record patterns, eta, the `let` pattern and the 2.9.0 note.
- **[A2]** Agda documentation, "Lambda Abstraction":
  <https://agda.readthedocs.io/en/latest/language/lambda-abstraction.html>.
  Pattern lambdas and their generativity.
- **[A3]** Agda standard library, `Data.Product.Base`:
  <https://raw.githubusercontent.com/agda/agda-stdlib/master/src/Data/Product/Base.agda>.
  `∃ = Σ _`, `∃-syntax`, `_×_`, `-,_`, `proj₁`/`proj₂`.
- **[I1]** Idris 2 documentation, "Types and Functions":
  <https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html>.
  Dependent pairs and tuples.
- **[Is1]** The Isabelle/Isar Reference Manual, "Proofs" (HTML of the
  current distribution), `obtain` and `consider`:
  <https://isabelle.in.tum.de/dist/library/Doc/Isar_Ref/Proof.html>.
- **[F1]** *Proof-Oriented Programming in F\**, "Constructive & Classical
  Connectives":
  <https://fstar-lang.org/tutorial/book/part2/part2_logical_connectives.html>.
- **[D1]** Dafny Reference Manual, §8.5.5 "Such-that assignment" and
  §8.7: <https://dafny.org/latest/DafnyRef/DafnyRef>.
