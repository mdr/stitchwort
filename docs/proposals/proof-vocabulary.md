# Proof vocabulary: names that say what happens

**Status:** draft 1, 16 November 2026 (SW-3565, Opus paper lane, D3649).
No builds or tests; code read at `132bb7c22`. Decisions for Matt are in
[§5](#5-decisions-for-matt), to be brought one at a time. Migration cost
is not counted (D2303).

Related: [simp.md](simp.md) and D3647 (`rewrite repeatedly`, a name that
says what happens), SW-3564 and D3648 (`then` replaces `in` after
`rewrite`/`cases`), [proof-tuples.md](proof-tuples.md) and D3631 (`(x, a,
b)` replaces most `Witness`/`Both`), [constructor-names.md](constructor-names.md)
and D3615 (one name, one meaning per file).

How claims are marked:

- **[counted]**: `git grep` over the 3,253 tracked `.sw` files today (word
  matches, comments included, so a few per cent high);
- **[read]**: read in this repo, with the file;
- **[probed]**: tried on a scratch file with the release CLI today;
- **[cited]**: from a page fetched today (sources at the end);
- **[not rechecked]**: from memory of the other system, not fetched today;
- **[inferred]**: my reasoning, not tried.

## 1. In plain words

**The problem.** The words a proof is written with were mostly borrowed
from Lean as Stitchwort grew: `rfl`, `omega`, `ring`, `Inl`/`Inr`,
`Void.exfalso`, `Eq.sym`. Each is a fossil of somebody else's history:
`rfl` is Lean's spelling of "reflexivity", `omega` is the name of a 1991
algorithm (Pugh's Omega test) that the user never sees, `ring` is a
term from abstract algebra, `Inl` is "inject left", `exfalso` is Latin.
A newcomer can't guess any of them, and they don't match the house rule
the rest of the language follows: whole everyday words that say what
happens (`rewrite repeatedly`, `cases`, `.read`, `byDecision`,
`.forward`). Lean isn't the reference: the other systems use different
words for the same things (table in §3), so a Lean-shaped name is
familiar to one audience and as strange as any other to the rest.

**The change.** Rename the handful of words that are both common and
opaque, to words that say what the step does:

| Today | Proposed | Uses [counted] | What it does |
|---|---|---:|---|
| `rfl` | `byComputing` | 8,908 | both sides compute to the same value |
| `omega` | `arithmetic` | 3,118 | linear arithmetic over `Nat`/`Int` from the facts in scope |
| `Inl` / `Inr` | `Left` / `Right` | 1,426 / 1,484 | which side of an `∨` holds |
| `Void.exfalso` | `Void.impossible`, mostly `h.impossible` | 1,212 | anything follows from a contradiction |
| `Eq.sym` | `Eq.flipped`, mostly `h.flipped` | 1,760 | `y = x` from `x = y` |
| `Eq.trans` | `Eq.chain`, mostly `ab.chain bc` | 1,913 | `a = c` from `a = b` and `b = c` |
| `Eq.cong` | `Eq.map` | 1,449 | `f x = f y` from `x = y` |
| `ring` | `algebra` | 308 | multiply out both sides and compare |

Keep the rest (§4): `cases`, `calc`, `rewrite`, `byDecision`, `.forward`
/ `.backward`, `.read`, `auto`, `decreasing`, `?`, `matches`, `match x:`,
`at`, `Finite.check`, `Void`, `Unit`/`Trivial`, `Iff`, `DecEq`,
`Decidable.yes`/`no`, `Both`/`Witness` (going anyway with tuples), and
std's lemma-name suffixes (`Comm`, `Assoc`, `Cong`, `Injective`, …).

**What it should do.** A proof reads as an argument a newcomer can
follow without a glossary: `| Inl zero => Inl omega` becomes `| Left zero
=> Left arithmetic`; `Void.exfalso (Bool.falseNotTrue (Eq.sym h))`
becomes `(Bool.falseNotTrue h.flipped).impossible`. About 22,000 word
changes across the repo [counted, sum of the table], all mechanical. The
cost is unfamiliarity to people and agents arriving from Lean (and,
for `refl`/`cong`/`trans`, from Agda, Idris and Isabelle too); the
mitigation is an `E-UNKNOWN-NAME` hint that maps each other system's word
to ours (§6), which agents need anyway, because they will write `rfl`
and `omega` from training whatever we choose [inferred].

## 2. Ranking: clarity gained × uses

Clarity gained is my judgement on a 0-3 scale: 3 means a newcomer can't
guess the old word at all and will guess the new one; 1 means a modest
improvement over a word that is jargon but widely shared.

| Rank | Rename | Uses | Gain | Value | Hash change? |
|---:|---|---:|---:|---:|---|
| 1 | `rfl` → `byComputing` | 8,908 | 2 | 17,800 | no [inferred, below] |
| 2 | `omega` → `arithmetic` | 3,118 | 3 | 9,400 | no (keyword) |
| 3 | `Inl`/`Inr` → `Left`/`Right` | 2,910 | 2 | 5,800 | **yes** |
| 4 | `Void.exfalso` → `Void.impossible` | 1,212 | 3 | 3,600 | no |
| 5 | `Eq.sym` → `Eq.flipped` | 1,760 | 2 | 3,500 | no |
| 6 | `Eq.trans` → `Eq.chain` | 1,913 | 1 | 1,900 | no |
| 7 | `Eq.cong` → `Eq.map` | 1,449 | 1 | 1,400 | no |
| 8 | `ring` → `algebra` | 308 | 3 | 900 | no (keyword) |

Not renames, but sweeps to an existing better form (no decision needed,
the orchestrator's call): `And.left h` → `h.left` (450 + 471 uses;
the dot form already works [read, `docs/guide/10-proofs.md` §Taking a
fact apart]); `Exists.elim h (x a => …)` → `let (x, a) := h` (236 uses,
D3631's tuples); `Void.exfalso (Bool.falseNotTrue (Eq.sym h))` on `h:
True = False` → `match h with | ()`, which already works on a `Bool`
constructor clash [probed: `theorem b1 ∀ (h: False = True): 3 < 2 :=
match h with | ()` checks].

**Hashes** [read, `docs/compared.md` §4: "hashes each definition by
content ... but no names", "Nominal types include their module and name
in the hash"]. A renamed *lemma* or *function* (`Eq.sym`, `Void.exfalso`)
leaves every hash alone, since a reference is by hash, not name
[inferred from that]. A renamed *keyword* (`omega`, `ring`) changes
nothing the kernel sees. `rfl` is a built-in name elaborated straight to
the kernel's `Refl` term (`crates/elab/src/builtin_docs.rs:51`, `("rfl",
2) => Some(Term::Refl)`) [read], so renaming it changes no hash
[inferred]. Renaming `Or`'s *constructors* changes `Or`'s hash and so
every hash downstream of it, which is nearly all of std [inferred:
history.md says a data type's hash includes its field names; constructor
names are in it too, I have not checked the hasher]. Migration cost
doesn't count, so this is noted only so the sweep regenerates the
snapshots and repins.

## 3. Word by word

Each entry: what it does; what a newcomer would guess; what others call
it; candidates on real lines; clashes; recommendation.

### 3.1 `rfl` (8,908 uses; 3,809 as a whole proof or arm, about 3,600 as an argument [counted])

**Does:** proves `a = b` when both sides compute to the same value.
`E-REFL` already explains it in those words: "`rfl` proves `a = b` only
when both sides compute to the same value" (`docs/guide/10-proofs.md`).

**Newcomer's guess:** nothing; it isn't a word. Those who know it read
"reflexivity", which names a property of `=`, not what the checker does.

**Others:**

| System | Name |
|---|---|
| Lean 4 | `rfl` (term, `def rfl : Eq a a := Eq.refl a`), `rfl` and `decide` tactics [cited] |
| Rocq | `eq_refl` (constructor), `reflexivity` tactic [cited]; SSReflect `erefl`, `by []` [not rechecked] |
| Agda | `refl` (constructor of `_≡_`), `erefl` [cited] |
| Idris 2 | `Refl` (constructor of `Equal`) [cited] |
| Isabelle/HOL | `refl` rule (`t = t`) [cited]; in practice `by simp` [not rechecked] |
| F*, Dafny, Liquid Haskell | no name: equalities that compute go to the SMT solver or `assert`; Liquid Haskell's `trivial` for the empty proof [not rechecked] |

So "refl" in some spelling is near-universal, but always as jargon.

**Candidates, on real lines:**

```
theorem doubleFour: double 4 = 8 := rfl                                  -- today (guide)
theorem doubleFour: double 4 = 8 := byComputing
theorem doubleFour: double 4 = 8 := refl

| Times => { forward = member => rfl, backward = same => Inr (Inl rfl) }  -- AoC
| Times => { forward = member => byComputing, backward = same => Right (Left byComputing) }

let fits: ticket.values.length = candidates.length := Eq.trans (lengths ticket (Inl rfl)) (Eq.sym wide)
let fits: ticket.values.length = candidates.length := (lengths ticket (Left byComputing)).chain wide.flipped
```

- `byComputing`: says exactly what the checker does, pairs with
  `byDecision` (140 uses) so the two "the checker does it" proofs have one
  shape, and reads as a reason in argument position (`d.sound
  byComputing`: "d is sound, by computing"). Longer: 11 letters for 3.
  No std name or keyword clashes [counted: 0 uses]. After `then`:
  `rewrite h then byComputing`, though a bare `rewrite h` already ends by
  computing.
- `refl`: familiar to Agda, Idris, Isabelle and Rocq users; still jargon.
- `same`: reads well (`:= same`) but is std's most common hypothesis name
  (1,015 word uses in std alone [counted]), so a local `same` would shadow
  it.
- `computes`: reads well as a whole proof, badly as an argument (`d.sound
  computes`).

**Recommendation: rename to `byComputing`.** The gain is clarity at the
point where every newcomer starts (chapter 10's first example), times the
most common proof word in the repo.

### 3.2 `omega` (3,118 uses; 1,067 as `omega [facts]`, 102 as `omega: P` [counted])

**Does:** proves `≤`, `<`, `=` (and their `∧`, `∨`, `¬`) on `Nat` and
`Int` from every arithmetic fact in scope, treating calls and products of
unknowns as opaque numbers (`docs/proving-guide.md` §3) [read].

**Newcomer's guess:** nothing, or "the last thing". The name is the 1991
Omega test, an algorithm the user never meets; Stitchwort's procedure
isn't even only that algorithm (it splits disjunctions, reads `x / k` by
bounds).

**Others:** Lean 4 `omega` [cited, named in the tactic reference]; Rocq
`lia`, "a decision procedure for linear integer arithmetic" [cited], which
replaced Rocq's own `omega` [not rechecked]; Isabelle `arith`,
`linarith`, `presburger` [not rechecked]; Mathlib `linarith` [not
rechecked]; HOL4 `intLib.ARITH_TAC`, `DECIDE_TAC` [not rechecked]; F*,
Dafny, Liquid Haskell, ACL2: automatic, no name (SMT or ACL2's built-in
linear arithmetic) [not rechecked]. Two of six use a word with "arith" in
it; only Lean uses `omega`.

**Candidates:**

```
theorem roomForOne ∀ (x y: Nat) (before: x < y) (limit: y ≤ 10): x + 1 ≤ 10 := omega   -- guide
theorem roomForOne ∀ (x y: Nat) (before: x < y) (limit: y ≤ 10): x + 1 ≤ 10 := arithmetic

rewrite <- made in Eq.trans (Eq.cong Int.toNat (omega: i.toInt + 1 - 1 = i.toInt)) (Int.toNatToInt i)   -- AoC
rewrite <- made then (Eq.map Int.toNat (arithmetic: i.toInt + 1 - 1 = i.toInt)).chain (Int.toNatToInt i)

| [] => Eq.cong (Cons Free) (fillFrontFreeLast rest [] count (omega))      -- AoC
| [] => Eq.map (Cons Free) (fillFrontFreeLast rest [] count arithmetic)
```

- `arithmetic`: says what it knows. Reads "by arithmetic" after `:=`, and
  `cases then arithmetic`, `arithmetic [Nat.divModEq x 2]`. No std name
  [counted: 16 uses, all in comments]; becomes a keyword, so it can't be a
  variable name (it isn't one anywhere today [inferred from the count]).
- `linear`: precise but the word "linear" needs explaining; and
  `linear arithmetic` as a two-word keyword (like `rewrite repeatedly`) is
  long for 3,000 uses.
- `arith`: Isabelle's; an abbreviation, against house style.

The error code follows: `E-OMEGA` → `E-ARITHMETIC` (8 + 2 sites in
`crates/` [counted]).

**Recommendation: rename to `arithmetic`.**

### 3.3 `ring` (308 uses)

**Does:** "multiplies both sides out, collects like terms, and checks that
they match", over `Nat` and `Int` (`docs/guide/10-proofs.md` §Algebra)
[read].

**Newcomer's guess:** something about circles or jewellery. A ring is an
algebraic structure; the name tells only a mathematician which laws it
uses.

**Others:** Lean/Mathlib `ring`; Rocq `ring` [not rechecked]; Isabelle
`algebra` (Gröbner bases) and `simp add: algebra_simps` [not rechecked];
Agda `solve` from the ring solver [not rechecked]; SMT-based systems: automatic.

**Candidates:**

```
_ = c * a - c * b := ring                                          -- AoC
_ = c * a - c * b := algebra
let lengths: Succ position + rest.length = position + Succ rest.length := ring
let lengths: Succ position + rest.length = position + Succ rest.length := algebra
```

- `algebra`: reads "by algebra", the school word for exactly this (expand
  and collect). Pairs with `arithmetic`: arithmetic for inequalities on
  numbers, algebra for equations with unknowns multiplied together. No
  std clash [counted: 0].
- `expand` or `multiplyOut`: say the mechanism but not what it proves.

**Recommendation: rename to `algebra`**, in the same decision as
`omega`. `E-RING` → `E-ALGEBRA`.

### 3.4 `Inl` / `Inr` (1,426 / 1,484)

**Does:** the two constructors of `Or`: `Inl p` proves `p ∨ q` from `p`,
`Inr q` from `q`; as patterns, which side held. Their fields are already
called `left` and `right` (`type Or (p: Prop) (q: Prop): Prop = | Inl
(left: p) | Inr (right: q)`, `crates/elab/src/std/core/Logic.sw`) [read].

**Newcomer's guess:** "in-L"? "inline"? It's "injection left", type-theory
jargon.

**Others:** Lean `Or.inl`/`Or.inr`, tactics `left`/`right` [cited];
Rocq `or_introl`/`or_intror`, tactics `left`/`right` [not rechecked];
Agda `inj₁`/`inj₂` (for `_⊎_`) [cited]; Idris `Left`/`Right` (for
`Either`) [not rechecked]; Isabelle `disjI1`/`disjI2` [cited]; Haskell
and Liquid Haskell `Left`/`Right` [not rechecked]. The tactic layer of
Lean and Rocq already says `left`/`right`.

**Candidates:**

```
| Inl zero => Inl omega                                  -- guide, emptyOrTooBig
| Inr big => Inr big.read
| Left zero => Left arithmetic
| Right big => Right big.read

| Inr (Inr (Inr (Inl same))) =>                          -- AoC
| Right (Right (Right (Left same))) =>
```

- `Left`/`Right`: what every programmer from Haskell, Idris, Scala or
  Rust's `Either` crate expects, and the same as the fields.
  **Clash:** `aoc/src/Aoc/Common/Grid.sw:22`, `type Direction = | Up |
  Right | Down | Left`, used in 54 AoC files [counted]. Under D3615 a
  file may not use one name with two meanings, so grid days that also
  prove disjunctions would hit `E-AMBIGUOUS` [inferred from D3615 and
  SW-3397's warning]. Fix in the same sweep: `Direction` becomes `North |
  East | South | West` (grid puzzles' own words, and `turnLeft` /
  `turnRight` keep reading right). No std type has `Left`/`Right`
  constructors [counted].
- `First`/`Second`, `This`/`That`: avoid the clash, but say less than the
  field names already do.
- With tuples, an `∨` still needs a constructor: there is no
  bracket-only spelling for "which side", so this name stays common.

**Recommendation: rename to `Left`/`Right`**, and Grid's `Direction` to
compass points. Hash change (§2).

### 3.5 `Void.exfalso` (1,212) and `Void.absurd` (18)

**Does:** from a proof of `Void`, any proposition (`exfalso`) or any data
type (`absurd`; two functions because there is no universe polymorphism,
`Logic.sw`) [read]. Used as "this case can't happen".

**Newcomer's guess:** `exfalso` is Latin ("from falsehood"); most
programmers won't know it. `absurd` is closer to a word.

**Others:** Lean `False.elim`, `absurd h nh`, tactic `exfalso`, `nomatch`
[cited]; Rocq `False_ind`, tactics `exfalso`, `contradiction` [not
rechecked]; Agda `⊥-elim`, absurd pattern `()`
[not rechecked]; Idris `void : Void -> a` [cited], `absurd` from
`Uninhabited`, and the clause keyword `impossible` [not rechecked];
Isabelle `FalseE`, `notE` [cited].

Method form already works: `v.exfalso` and `(k h).exfalso` check
[probed], with 0 uses so far [counted].

**Candidates:**

```
(zero => Void.exfalso (notZero (Eq.trans decimal zero.read)))           -- AoC
(zero => (notZero (decimal.chain zero.read)).impossible)

| [line, ..lines], [one, ..ones], [], means, alsoNone => Void.exfalso alsoNone
| [line, ..lines], [one, ..ones], [], means, alsoNone => alsoNone.impossible

forward = h => Void.exfalso (Bool.falseNotTrue (Eq.sym h)),
forward = h => (Bool.falseNotTrue h.flipped).impossible,
```

- `impossible`: what the arm means ("this case is impossible"); Idris
  uses the same word for impossible clauses. No std definition [counted:
  5 comment uses]. Postfix on a name (`alsoNone.impossible`) reads best;
  prefix `Void.impossible (…)` stays for long expressions.
- `anything`: says what you get, not why.
- `absurd`: Lean's and Idris's word for a two-argument variant; reusing
  it for the one-argument form would mislead those readers.

**Recommendation: rename `Void.exfalso` to `Void.impossible`**, and
prefer the method form in the guide and the sweep where the argument is
a name. Leave `Void.absurd` (18 uses, data only) until universe
polymorphism lets the two merge under `impossible`.

### 3.6 `Eq.sym` (1,760; 46 already as `h.sym` [counted])

**Does:** `y = x` from `x = y`.

**Newcomer's guess:** "symbol"? "symmetric" if they know the term.

**Others:** Lean `Eq.symm`, `h.symm`, tactic `symm` [cited]; Rocq
`eq_sym`, tactic `symmetry` [cited for the tactic]; Agda `sym` [cited];
Idris `sym` [not rechecked]; Isabelle `sym` [cited].

**Candidates:**

```
let closed: Unclosed [top, ..below] = Unclosed [] := Eq.trans (Eq.sym e) (balancedScanNil line balanced)   -- AoC
let closed: Unclosed [top, ..below] = Unclosed [] := e.flipped.chain (balancedScanNil line balanced)

(Eq.sym h)
h.flipped
```

- `flipped`: everyday, says what happens to the equation. A postfix
  adjective reads like `.read`. std uses "flip" for other types' own
  operations (57 word uses [counted]); dot resolution is by the
  receiver's type, so `Eq.flipped` doesn't clash with them [inferred]. As
  a method it removes a pair of brackets at most sites.
- `reversed`, `swapped`: also fine; "reversed" suggests lists.

**Recommendation: rename to `Eq.flipped`**, written `h.flipped`.

### 3.7 `Eq.trans` (1,913; method form works, 0 uses [probed, counted])

**Does:** `a = c` from `a = b` and `b = c`.

**Others:** Lean `Eq.trans`, `h₁.trans h₂`, `calc` [cited]; Rocq
`eq_trans`, tactic `transitivity` [cited for the tactic]; Agda `trans`,
`begin … ≡⟨ ⟩ … ∎` [cited for `trans`]; Idris `trans` [not rechecked];
Isabelle `trans`, `also … finally` [cited for `trans`]; Dafny `calc`
[not rechecked]. The near-universal spelling, and the least opaque of the
set.

**Candidates:**

```
Void.exfalso (Nat.equalFalse j k hc (Eq.trans (Eq.sym (Nat.equalSound i j hb)) (Nat.equalSound i k hd)))   -- AoC
(Nat.equalFalse j k hc ((Nat.equalSound i j hb).flipped.chain (Nat.equalSound i k hd))).impossible
```

- `chain`: the guide already calls a `calc` "a chain of `=`, `<=`, `<`
  steps" [read], so one word covers both. `ab.chain bc`.
- `then`: reads best (`ab.then bc`) but is a keyword [read,
  `crates/syntax/src/lexer.rs`], and after D3648 it also separates a
  tactic from its continuation; overloading it would confuse both.
- keep `trans`: shared by every system; but an abbreviation.

**Recommendation: rename to `Eq.chain`**, the weakest of the eight;
fine to keep `trans` if Matt prefers the shared name. Both should
be written as methods in the sweep.

### 3.8 `Eq.cong` (1,449)

**Does:** `f x = f y` from `x = y`: apply the same function to both
sides.

**Others:** Lean `congrArg` [cited]; Rocq `f_equal` [cited for the
tactic]; Agda `cong` [cited]; Idris `cong` [cited]; Isabelle `arg_cong`
[cited]. "cong" in some form almost everywhere.

**Candidates:**

```
| [x, ..xs], Succ n => Eq.cong (Cons x) (List.takeAdd xs n m)      -- std
| [x, ..xs], Succ n => Eq.map (Cons x) (List.takeAdd xs n m)
| [x, ..xs], Succ n => Eq.onBothSides (Cons x) (List.takeAdd xs n m)
```

- `map`: std's word for "apply inside", with a precedent in the same file
  (`Exists.map f h`, `Logic.sw`) [read]; agents know it from every
  functor.
- `onBothSides`: the most literal; long.
- Method form isn't possible either way: the function comes first, and
  dot notation passes the receiver as the first explicit argument
  [probed: `h.cong (n => n + 1)` is `E-DOT-NO-RECEIVER`].

std's `…Cong` lemmas (25 definitions, `List.mapCong` and friends, the
lemmas `rewrite` goes through [read]) are a separate pattern: keep that
suffix, since it names a family, not a step a reader writes often.

**Recommendation: rename to `Eq.map`**, low priority; keep `cong` if Matt
weighs cross-system familiarity higher here.

## 4. Keeps, and why

| Word | Uses | Why keep |
|---|---:|---|
| `cases` | 811 | Universal (Lean `cases`, Rocq `case`/`destruct`, Isabelle `cases`) and plain English: "by cases". |
| `calc` | 273 | Lean and Dafny `calc` [not rechecked for Dafny]; a common English abbreviation; reads as "calculation". |
| `rewrite` | 5,639 | Says what happens. |
| `byDecision` | 140 | Says what happens; the model for `byComputing`. Not `decide`: that is `DecEq`'s field (`crates/elab/src/std/core/DecEq.sw:14`) [read]. |
| `.forward` / `.backward` | 257 / 244 | Already whole words; better than Lean `mp`/`mpr` or Isabelle `iffD1`/`iffD2` [cited]. |
| `Both`, `Witness` | 7,955 / 2,831 | Good words, and mostly disappearing behind tuples (D3631). |
| `Void` | 1,938 | Idris's word for the empty type [cited]; `False` is taken by `Bool`. `Never` (Swift, TypeScript) is an option but the gain is small once `Void.exfalso` becomes `.impossible`. |
| `Unit` / `Trivial` | 290 / 427 | `Trivial` says what it is (Lean's `trivial` term); `True` is taken by `Bool`. |
| `.read`, `@[reading]` | 32 | Chosen recently, plain. |
| `auto` | 1,365 | Means "filled automatically", not proof search as in Rocq or Isabelle [not rechecked]. A Rocq user writing `:= auto` gets a hint (§6); renaming it would cost the very common `[auto h: P]`. |
| `decreasing` | 399 | Plain; Dafny says `decreases` [not rechecked]. |
| `?` | — | Agda and Idris holes are `?` [not rechecked]. |
| `matches`, `match x:`, `at` | 168 / — / — | Plain; `at h` matches Lean and Rocq. |
| `Finite.check` | 20 | Says what it does. |
| `Iff` | 112 | Written `↔` almost everywhere; its fields are already plain. |
| `DecEq`, `Decidable.yes`/`no`, `DecEq.sound` | 62 / 105 | Agda `yes`/`no`, Idris `Yes`/`No`, Idris `DecEq` [not rechecked]. `DecEq` is an abbreviation; `DecidableEquality` would be the whole-word form. Low value; not proposed. |
| `Bool.falseNotTrue` | 301 | Says what it states. Most uses are the `Void.exfalso (Bool.falseNotTrue (Eq.sym h))` idiom, which becomes `match h with \| ()` or `(Bool.falseNotTrue h.flipped).impossible`. |
| `Exists.elim` | 236 | "elim" is jargon, but the sweep to `let (x, a) := h` retires most uses; not worth a name. |
| Lemma suffixes `Comm`, `Assoc`, `Refl`, `Irrefl`, `Antisymm`, `Cong`, `Injective`, `Elim`, `Intro` | 3,244 std theorems | Shared by every library (Lean `add_comm`, Isabelle `add.commute`/`add.assoc` [not rechecked]); std already prefers the long form where it matters (`Injective`, not `inj`; `lessIrrefl`). A glossary line in the proving guide's "Finding lemmas" covers the rest. |

## 5. Decisions for Matt

One at a time, in this order (value first). Each is a keyword or name
change only; none touches the kernel.

**D(a): name the two arithmetic procedures for what they do: `omega` →
`arithmetic`, `ring` → `algebra` (3,426 uses; no hash change). [rec:
yes]** The two words Matt called out; the largest clarity gain per use.

**D(b): `rfl` → `byComputing` (8,908 uses; no hash change). [rec: yes]**
Alternative: `refl`, the shared jargon of Agda, Idris, Isabelle and
Rocq. The most uses of any word; pairs with `byDecision`.

**D(c): `Void.exfalso` → `Void.impossible`, written `h.impossible` (1,212
uses; no hash change). [rec: yes]**

**D(d): `Or`'s constructors `Inl`/`Inr` → `Left`/`Right`, and AoC Grid's
`Direction` to `North`/`East`/`South`/`West` to keep D3615's one name,
one meaning (2,910 + the grid uses; hashes change). [rec: yes]**

**D(e): the equation helpers as methods with plain names: `Eq.sym` →
`Eq.flipped` (`h.flipped`), `Eq.trans` → `Eq.chain` (`ab.chain bc`),
`Eq.cong` → `Eq.map` (5,122 uses; no hash change). [rec: yes for
`flipped`; `chain` and `map` weaker, keep `trans`/`cong` acceptable]**
Could be split into three if Matt wants to keep the shared names.

The keeps in §4 need no decision unless Matt wants to reopen one.

## 6. The sweep

One sweep lane, together with SW-3564's `then` (D3648), so the repo moves
once and the guide is rewritten once:

1. **Keywords** (no hash change): `omega` → `arithmetic`, `ring` →
   `algebra` in the lexer, elaborator, error codes (`E-OMEGA`, `E-RING`
   and their `-INTERNAL` forms), LSP completion, formatter, together with
   `in` → `then`. Rejected-example snapshots that quote the words are
   regenerated.
2. **std names** (no hash change): `rfl` → `byComputing` (the built-in
   table in `builtin_docs.rs`, `E-REFL`'s text), `Void.exfalso` →
   `Void.impossible`, `Eq.sym/trans/cong` → `Eq.flipped/chain/map`. A
   word-boundary rewrite, then `stitchwort fmt`; where the argument is a
   name or a call, rewrite `Eq.sym h` to `h.flipped`, `Void.exfalso h` to
   `h.impossible` and `Eq.trans a b` to `a.chain b` (a small syntax-aware
   script, since brackets move).
3. **Constructors** (hashes change, in its own commit): `Inl`/`Inr` →
   `Left`/`Right`, Grid's `Direction` → compass points first so no file
   is ambiguous mid-sweep; regenerate the hash snapshots and repin std's
   native pins.
4. **The opportunistic sweeps** in the same lane: `And.left h` →
   `h.left`, `Exists.elim` → tuple `let`, the `falseNotTrue` idiom →
   `match h with | ()` where it type-checks.
5. **Hints for arrivals** (new, small): `E-UNKNOWN-NAME` with a note
   "`rfl` is `byComputing` in Stitchwort" for a fixed table of other
   systems' words: `rfl`, `refl`, `Refl`, `reflexivity`, `omega`, `lia`,
   `linarith`, `ring`, `exfalso`, `absurd` (when not `Void.absurd`),
   `False.elim`, `Or.inl`, `inl`, `inj₁`, `Eq.symm`, `symm`, `sym`,
   `congrArg`, `cong`, `f_equal`, `trans`, `decide`, `trivial`. This is
   what makes the unfamiliarity cheap for agents, which write Lean from
   training [inferred].
6. **Docs:** `docs/syntax.md`, the guide's chapter 10, the proving guide's
   tool table, `web/guide/`, and `Logic.sw`'s doc comments; the
   comparison page (`docs/compared.md`) gets a row mapping the words.

Stages 1-2 and 4-6 are mechanical; stage 3 is the only one that touches
hashes. A Sonnet or DeepSeek lane with a script, reviewed by sampling,
fits [inferred]; tests per the verifier's usual hash-snapshot set.

## Sources

Fetched today (16 Nov 2026):

- Lean 4 core, `src/Init/Prelude.lean` (GitHub `leanprover/lean4`
  master): `inductive Or … | inl … | inr`, `theorem Eq.symm`, `theorem
  Eq.trans`, `theorem congrArg`, `def absurd`, `def False.elim`, `def
  rfl`.
- Lean reference manual, Tactic Reference
  (lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/):
  `rfl`, `exfalso` ("converts a goal ⊢ tgt into ⊢ False"),
  `contradiction`, `symm`, `calc`, `left`/`right` ("Applies the first
  constructor …"), `omega` and `decide` named.
- Rocq 9.0 reference manual, equality tactics
  (rocq-prover.org/doc/V9.0.0/refman/proofs/writing-proofs/equality.html):
  `reflexivity` ("by applying eq_refl"), `symmetry`, `transitivity`,
  `f_equal`.
- Rocq 9.0 reference manual, micromega
  (…/refman/addendum/micromega.html): "`lia` is a decision procedure for
  linear integer arithmetic".
- Agda standard library, `Relation.Binary.PropositionalEquality.Core` and
  `Data.Sum.Base` (agda.github.io/agda-stdlib/master/): `refl`, `sym`,
  `trans`, `cong`, `subst`; `inj₁`, `inj₂`.
- Idris 2 tutorial, "Theorem Proving"
  (idris2.readthedocs.io/en/latest/tutorial/theorems.html): `Refl`,
  `cong`, `Void`, `void : Void -> a`.
- Isabelle/HOL theory `HOL` (isabelle.in.tum.de/library/HOL/HOL/HOL.html):
  `refl`, `sym`, `trans`, `arg_cong`, `conjI`, `disjI1`, `disjI2`,
  `FalseE`, `notE`, `iffD1`, `iffD2`.

Not rechecked today (from memory): SSReflect's `erefl`, Rocq's
`or_introl`/`eq_sym`/`False_ind`, Isabelle's `arith`/`linarith`/
`presburger`/`algebra` methods, Mathlib's `linarith`/`ring`, HOL4's
tactic names, Dafny's `calc`/`decreases`, F*'s and Liquid Haskell's proof
vocabulary, Idris's `impossible` clauses, `Either`'s `Left`/`Right`.
