# How a theorem's variables are written (SW-2640)

Status: options note, for Matt's decision. Nothing is built. Counts come from
a header parser run over the tree (a scratch script, not committed), and
hashes from the probe in §7. Each number is marked **measured** or
**estimated**.

## 1. The problem

After the `∀` sweep (D3458, SW-2587, SW-2588) a theorem's variables are
written in three ways:

```
theorem Nat.lessLe (m: Nat) (n: Nat) (h: m < n): m ≤ n := …          -- before the colon
theorem Nat.leRefl: ∀ (n: Nat) => n ≤ n                              -- ∀ after it
theorem Abort.orElseNeed (d: a): ∀ (o: Option a) => Abort.orElse …   -- both
```

Matt (10 Nov 2026): "I'm wondering if we should support forall symbol before
the colon as well, really it's an idea about readability closer to
logic/maths. I suspect move ∀ variables before the colon is a sensible house
style rule as long as we're not relying on it for the match syntax etc."

**The short answer: we do rely on it for the match syntax.** Of the 1,983
theorems that start with `∀` after the colon, 1,958 (99%) are proved by arms,
and arms can only take apart what comes after the colon. But the same proofs
can be written with `:= match x with` on parameters before the colon, and
that gives **the same term and the same hash** (measured, §7). So moving
every variable before the colon is possible; what it costs is one line and
one level of indentation per proof by cases.

### The real counts (measured)

Every `theorem` declaration, multi-line headers included:

| | std | aoc | games | total |
|---|---|---|---|---|
| parameters only, no `∀` at the top | 1,649 | 2,071 | 134 | **3,854** |
| `∀` after the colon, no parameters | 580 | 231 | 6 | **817** |
| both (84 of them have only `[a: Type]`-style parameters) | 684 | 449 | 33 | **1,166** |
| no variables at all | 163 | 117 | 1 | 281 |
| total | 3,076 | 2,868 | 174 | 6,118 |

The brief's grep (2,260 / 240 / 430) saw only one-line headers. How the
1,983 `∀` theorems are proved:

| | count |
|---|---|
| arms, and the first arm column is matched (nothing can move without a `match`) | 1,710 |
| arms, but some leading `∀` variables are plain names in every arm | 224 |
| arms, and no `∀` variable is matched at all | 24 |
| `:=` body (a lambda, a lemma, a tactic) | 15 |
| only implicit `∀ [a: Type] =>` | 8 |

Of the 1,958 arm proofs, 1,095 also have columns for premises (`a ≤ b →`):
770 name them with plain names in every arm, 325 match one with a pattern
(`Refl`, `Both l r`, `()`).

So the three ways aren't random. They are the `def` rule applied to
theorems: "named parameters, then arms" (docs/syntax.md, "Definitions in
detail"). A variable sits after the colon because the arms match on it.
Only about 270 theorems (224 + 24 + 15 + 8) break that rule.

## 2. What depends on the form (question 1)

Parameters before the colon and a leading `∀` after it are **the same type**.
The parser lowers both to the same function type (header:
`lower_header`, crates/syntax/src/parser/declarations.rs:763; `∀`:
`forall_expr`, crates/syntax/src/parser.rs:3589-3596, "the same term
(D3458)"). Binder names aren't hashed (crates/core/src/hash.rs:609-618). So
everything that reads the *type* sees no difference. What differs is how the
*body* is elaborated, and a few places that read the header.

**Things that depend on the form:**

1. **Arms match only arguments after the colon.** The parser turns a header
   into equations whose first patterns are the header's names, and records
   how many (`arm: Some(header.len())`); the elaborator refuses a pattern
   there with `E-ARM-PARAMETER`, "named parameters can't be matched in arms:
   move … after the colon, or use `match … with`" (crates/elab/src/lib.rs:3388-3420;
   the parser's own note, declarations.rs:351). `:= match | …` (a clause
   lambda) is lowered to the same equations (declarations.rs:317-332), so it
   needs the arguments after the colon too. **This is what 1,958 theorems
   rely on.**
2. **`decreasing` needs its variables before the colon.** The measure may
   only use header parameters: `E-DECREASING`, "`halfLeD`'s measure needs
   the parameters it uses named in its header" (crates/elab/src/decreasing.rs:1013-1039).
   Checked: `theorem halfLeD: ∀ (n: Nat) => half n ≤ n decreasing n` is
   refused.
3. **Default values only before the colon.** `∀ (n: Nat := 1) =>` is
   `E-PARSE`, "a `forall` parameter can't have a default"
   (parser.rs:3620-3630). Theorems hardly use defaults.
4. **A `:=` body sees header parameters by name; after the colon it must
   bind them.** `theorem t (n: Nat) (h: 0 < n): 1 ≤ n := omega`, but
   `theorem t: ∀ (n: Nat) => 0 < n → 1 ≤ n := n h => omega`. Implicit and
   `auto` parameters are the exception: they are in scope by name wherever
   they are written (lib.rs:3336-3345). `cases` introduces leading binders
   itself (docs/proving-guide.md §3).
5. **Exact arity of arms.** Arms need one pattern per argument after the
   colon, counted after unfolding, so `o ≠ Some 3` adds a column
   (`E-ARITY`, with a note, lib.rs:3374-3387). A `:=` body has no arity rule.
6. **The header as written.** `stitchwort doc` prints the header from the
   source (checked: `theorem plusZeroA (n: Nat): n + 0 = n` and
   `theorem plusZeroB: ∀ (n: Nat) => n + 0 = n`), so docs and hover show
   whichever was written.
7. **The first goal.** A `?` as the whole body shows `∀ (n: Nat) => …` for
   the `∀` form and `n` in context for the header form. Once the arms or a
   lambda bind `n` the goals are the same.

**Things that don't depend on it** (checked or read):

- **Recursion and induction hypotheses.** Induction is recursion, and a
  recursive call may pass anything to any parameter, before the colon or
  after. Checked: `theorem sumFromGe (acc: Nat) (xs: List Nat): acc ≤ sumFrom acc xs`
  with the recursive call `sumFromGe (acc + x) rest` (the accumulator
  changes) is accepted. So a `∀` after the colon never gives a stronger
  induction hypothesis, unlike Lean's `induction` tactic, where variables
  before the colon are fixed unless generalised.
- **`f.induct`, `match induct` and `f.eqK`.** Theorems have neither
  equations nor `f.induct` ("a theorem's arms have no equations: nothing
  unfolds a proof", crates/elab/src/equations.rs:2153). For a `def`,
  `f.induct`'s fixed prefix is chosen by what the recursive calls pass on
  unchanged, not by the colon (crates/elab/src/equations/induct.rs:546-575).
- **Named arguments.** `plusZeroB (n := k)` works on the `∀` form too
  (checked), since the type keeps the binder names.
- **Implicits at a use, `rewrite`, `apply`, proof search, `auto`, `search`,
  the counterexample search.** All work from the type, which is the same.
- **Signature help.** It walks the type's binders
  (`global_signature`, crates/elab/src/nav.rs:1298-1325; used by
  crates/driver/src/at.rs:444), so both forms give the same parameters.
- **Hover and goal printing of the type.** The REPL's `:t` prints both
  `plusZeroA` and `plusZeroB` as `∀ (n: Nat) => …` (checked).
- **Hashes**, with the exceptions in §7.

## 3. The options

The judge is the end state (D2303). Six real statements, each in every
option. The proofs are shortened to their first lines.

**(a) The `def` rule: variables before the colon, except from the first one
the arms match.** Of the 1,983 theorems with `∀` at the top, 86% already follow it (96% of all theorems).

**(a+) Every variable before the colon; a proof by cases is
`:= match x with`.** Premises that the arms name move into the header as
named hypotheses, which keeps the hash (§7). `∀` stays only where §4 says.

**(b) `∀` after the colon for every statement.** Named hypotheses become
premises (`m < n →`) and the proof binds them.

**(c) New syntax: `∀` before the colon**, a spelling of header parameters:
`theorem Nat.lessLe ∀ (m n: Nat) (h: m < n): m ≤ n`. It can sit on top of (a)
or (a+); below it's shown on (a+).

### `Nat.leRefl` (std, proof by cases)

```
(a), today   theorem Nat.leRefl: ∀ (n: Nat) => n ≤ n
               | Zero => rfl
               | Succ n => Nat.leRefl n

(a+)         theorem Nat.leRefl (n: Nat): n ≤ n :=
               match n with
                 | Zero => rfl
                 | Succ n => Nat.leRefl n

(b)          as (a)

(c)          theorem Nat.leRefl ∀ (n: Nat): n ≤ n :=
               match n with …
```

### `Nat.leTrans` (std, cases with premises)

```
(a), today   theorem Nat.leTrans: ∀ (a b c: Nat) => a ≤ b → b ≤ c → a ≤ c
               | Zero, b, c, h1, h2 => rfl
               | Succ a, Zero, c, h1, h2 => Void.exfalso (Bool.falseNotTrue h1)
               …

(a+)         theorem Nat.leTrans (a b c: Nat) (h1: a ≤ b) (h2: b ≤ c): a ≤ c :=
               match a, b, c with
                 | Zero, b, c => rfl
                 | Succ a, Zero, c => Void.exfalso (Bool.falseNotTrue h1)
                 …

(b)          as (a)

(c)          theorem Nat.leTrans ∀ (a b c: Nat) (h1: a ≤ b) (h2: b ≤ c): a ≤ c := …
```

### `Bool.andRight` (std, implicit parameters and a hypothesis)

```
(a), (a+)    theorem Bool.andRight [a: Bool] [b: Bool] (h: (a ∧ b) = True): b = True :=
               match e: a with …

(b)          theorem Bool.andRight: ∀ [a b: Bool] => (a ∧ b) = True → b = True := h =>
               match e: a with …

(c)          theorem Bool.andRight ∀ [a b: Bool] (h: (a ∧ b) = True): b = True := …
```

### `memCellsOfCellAt` (aoc, a record pattern and a premise)

```
(a), today   theorem memCellsOfCellAt (rows: List (List a)): ∀ (position: Position) (x: a) =>
                 cellAt rows position = Some x → (position, x) ∈ cells rows
               | { row, column }, x, found => …

(a+)         theorem memCellsOfCellAt (rows: List (List a)) (position: Position) (x: a)
                 (found: cellAt rows position = Some x): (position, x) ∈ cells rows :=
               match position with
                 | { row, column } => …

(b)          theorem memCellsOfCellAt: ∀ (rows: List (List a)) (position: Position) (x: a) =>
                 cellAt rows position = Some x → (position, x) ∈ cells rows
               | rows, { row, column }, x, found => …
```

### `noHitsAbove` (aoc, long, a matched column after unmatched ones)

```
today        theorem noHitsAbove (x: Nat) (d: Nat): ∀ (r c: Nat) (ls: List (Vec Bool w)) =>
                 x < r → List.any (timelinesFrom r c ls) (hitIn x d) = False
               | r, c, [], h => rfl
               | r, c, [row, ..rest], h => …

(a)          theorem noHitsAbove (x d r c: Nat): ∀ (ls: List (Vec Bool w)) =>
                 x < r → List.any (timelinesFrom r c ls) (hitIn x d) = False
               | [], h => rfl
               | [row, ..rest], h => …

(a+)         theorem noHitsAbove (x d r c: Nat) (ls: List (Vec Bool w)) (h: x < r):
                 List.any (timelinesFrom r c ls) (hitIn x d) = False :=
               match ls with
                 | [] => rfl
                 | [row, ..rest] => …

(b)          theorem noHitsAbove: ∀ (x d r c: Nat) (ls: List (Vec Bool w)) =>
                 x < r → List.any (timelinesFrom r c ls) (hitIn x d) = False
               | x, d, r, c, [], h => rfl
               …
```

### `settleKeeps` (aoc, `decreasing`)

```
(a), (a+)    theorem settleKeeps (wire: Wire) (values: Values) (waiting: List Gate)
                 (there: values.contains wire = True): (settle values waiting).contains wire = True
                 decreasing waiting.length
             := …

(b)          not possible today (§2, item 2): `decreasing` needs a language change
```

### How they compare

| | (a) `def` rule | (a+) all before | (b) all after | (c) `∀` before |
|---|---|---|---|---|
| statement shapes a reader sees | two: `∀` at the top means "proved by cases" | one | one, plus named-hypothesis theorems turned into premises | one, with a `∀` keyword |
| reads like logic | half the time | like Lean/mathlib: `(n: Nat): …` | yes | yes, but `∀ … (h: m < n)` reads oddly |
| proofs | unchanged: arms | proofs by cases gain `match x with` (one line, one indent) | every `:=` proof gains `n h =>` | as (a+) |
| call sites | unchanged | unchanged; premises gain names, so `(h1 := …)` works | unchanged | unchanged |
| statement tied to proof technique | yes: switching arms ↔ `match` moves the binders | no | no | no |
| language cost | none | none | `decreasing` over `∀` variables (decreasing.rs:1013) | parser, formatter, docs (below) |
| theorems that change (measured) | about 270 | about 1,980 | about 3,850 | every theorem with variables (about 5,800) |

**What (c) would mean.** Parser: `definition()` accepts an optional
`∀`/`forall` after a theorem's name, before the header parameters
(declarations.rs:236-239), about ten lines. It changes no term or hash. The
formatter keeps every token, so it needs only a spacing rule. `doc` and
hover print the header as written, so they show it as it is. The printer
(goals, `:t`) is untouched. docs/syntax.md's grammar (line 311), the guide
(docs/guide/10-proofs.md) and the proving guide change. The catch: if it is
optional it is a fourth spelling, and the drift this note is about gets
worse. If it is required on theorems, every theorem gains a token that
`def`s don't have, and `∀ (h: m < n)` says "for all proofs that m < n",
which is right in type theory but odd to most readers.

**Matt's other spelling**, `theorem plusZero: ∀ (n: Nat) => n + 0 = n` kept
as written but meaning parameters, already means the same term. What would
change is scoping: `n` would be in scope in a `:=` body without `n =>`. That
hides a binding, breaks the 15 `:=` proofs of `∀` statements (a written
`n =>` would bind the next argument, and a lemma passed whole would no longer
fit), and premises would still need a lambda. Not
recommended.

## 4. Where `∀` must stay (question 3)

Under every option:

- **Inside a hypothesis**: `(all: ∀ (x: a) => x ∈ xs → p x)`. It is the
  hypothesis's statement, not the theorem's variable.
- **After a premise**: `n < m → ∀ (k: Nat) => …`. Moving `k` before the
  colon is a different (equivalent) statement with a different hash. Change
  it by hand when it reads better; a sweep doesn't.
- **Nested in the conclusion**: `(∀ x => p x) ∧ q`, `¬∀ …`, `∃ y => ∀ x => …`.
- **In a `def` that returns `Prop`**: `def Sorted (xs: List Nat): Prop :=
  ∀ (i j: Nat) => …`. The `∀` is the definition's value; parameters would
  make `Sorted` take more arguments.
- **Under (a) only**: from the first variable the arms match onwards, and
  the premises after it.

Implicit and `auto` binders at the top move like the others:
`Nat.addDivSelf (d: Nat) (n: Nat): ∀ [auto ok: d ≠ 0] => …` becomes
`(d n: Nat) [auto ok: d ≠ 0]: …` at the same hash (measured).

## 5. The sweep (question 4)

**How.** A tool that works on the parsed tree, not on text with regular
expressions, since it must split arm patterns into columns, re-indent arms
under a `match`, and give `∀ n =>` binders without a written type their
type from the checker. For each theorem whose statement starts with `∀`:

1. Take the `∀` binders (and, under (a+), the premise columns that every arm
   names with a plain name) out of the statement into the header, after the
   existing parameters. Under (a), only the leading binders that every arm
   names with a plain name.
2. Arms: drop the moved columns; under (a+), turn the rest into
   `:= match v1, …, vk with`, the scrutinees being the moved variables some
   arm matches.
3. A `:= x y => body` lambda: drop the binders that moved.
4. A body that is a lemma or tactic (`:= Nat.addZero`): add the arguments
   (`:= Nat.addZero n`).

**Verifying it with the trial check.** `LiveProject::trial` with
`Promise::SameMeaning` and no renames (crates/driver/src/live/trial.rs:49-55)
checks the edited project and lists every declaration whose content hash
moved, so a sweep that keeps hashes can be checked exactly. Three gaps:

- Only `rename` calls it today (crates/cli/src/rename_cmd.rs:111). The sweep
  needs an entry point that takes arbitrary edits: a small dev command or a
  test harness, estimated half a day.
- It refuses edits to library files (`Refusal::Library`, trial.rs:100), so
  it can't check std, which holds two thirds of the `∀` theorems. For std,
  load the library before and after with `--std-dir` and compare every
  declaration's `def_hash` in order, as `fmt_hashes`
  (crates/driver/tests/library/fmt_hashes.rs) does for formatted files.
  Estimated half a day. The prelude snapshot in `hash_stability` already
  catches a change in std core.
- Some conversions keep the statement but not the proof term (below). For
  those the right promise is "same statement": compare a theorem's type
  hash instead of its full hash, and accept a change in a declaration only
  when the trial's `uses` field (trial.rs:132) points at a theorem whose
  statement held. A new `Promise` variant, estimated half a day.
- Definitions embed proofs (Map's invariants and `Quot.lift`
  respects-proofs, the Graph searches' `decreasing` proofs), so a
  re-proved theorem moves the hash of every definition that mentions it,
  and the hash of every statement that mentions one of those. For these
  the promise is "proofs only" (`--proofs-only`, SW-2698): compare each
  declaration's hash without proofs (`hash::proofless_hash`), its content
  hash with every proof position hashed as one marker and every reference
  hashed by this hash in turn. The proof positions are what a run never
  computes (crates/core/src/erase.rs): arguments at parameters whose type is
  a proposition, calls of definitions whose result is a proof, constructors'
  proof fields, data types' proof parameters, `J`'s proof, `Quot.lift`'s
  respects-proof, `Quot.ind` and `Quot.sound`. A theorem's hash without
  proofs is its statement's; in a recursive group, a member whose result is
  a proof stands apart from those that compute. Statements are kept, so a
  declaration passes only if it computes the same and its statement says
  the same, up to the proofs inside what it mentions. The kernel still
  checks everything in full: the promise only decides which edits the tool
  calls safe.

**Forms it can't convert at the same hash** (measured where marked):

1. A body that is a lemma or tactic with no lambda, `:= Nat.addZero`
   (measured: the hash moves). At most 13 in std and aoc (measured), a few
   in examples; a tactic body such as `:= cases` keeps its hash (measured). Same statement, so "same statement" accepts it.
2. `:= xs => match xs with …` (measured: the hash moves, because the `match`
   is lifted into a helper instead of being the case tree). After the
   sweep it is the case tree, which is better.
3. A premise column left inside the `match` branches instead of moving to
   the header (measured: the hash moves). This is the case for columns that
   come from unfolding `¬` or `≠` in the conclusion, which can't be named in
   the header without restating the conclusion. Count not measured;
   estimated a few dozen.
4. A premise column matched by a pattern (`Refl`, `Both l r`, `()`): 325
   theorems (measured). Becomes a scrutinee of the `match`; whether the hash
   holds isn't measured, and the trial says.
5. Arms that call a moved variable by different names (`| n, … | m, …`): 15
   theorems (measured). The body needs a rename to one name; the rename
   machinery can do it.
6. `∀ n =>` with no written type: needs the type from the checker.
7. Statements with `∀` after a premise (§4): left alone.

Estimated effort: the tool and its checks 1.5 to 2 days; the run itself an
hour or two of a lane, mostly reviewing the refusals.

## 6. Keeping it (question 5)

This belongs with D3462 (docs/proposals/forall-style-enforcement.md), which
recommends a `check` warning with a quick fix for `->` written where `∀` is
meant. The same warning family can carry this rule, since both are "how a
statement is written" and both need the checker (which columns arms match,
which types are propositions). The formatter can't do it: it has no types
and doesn't rewrite arms into a `match`.

- **The warning.** Under (a+): a theorem whose statement starts with `∀`.
  Under (a): a leading `∀` variable that no arm matches, or any leading `∀`
  with a `:=` body.
- **The quick fix: "Move `∀` variables before the colon"**, which makes the
  sweep's edit for that one theorem. It can run the trial check before it is
  offered, so a fix that would change the hash isn't offered silently.
- **The order.** Sweep first, so the trees start with no warnings, as D3462
  says for its own rule.

Built (SW-2658): `W-THEOREM-FORALL` on a theorem whose statement starts
with `∀` that the sweep would convert (a `∀` after a premise doesn't warn),
and the quick fix "Move ∀ variables before the colon". The quick fix is the
sweep's edit for that theorem, offered without the trial check, since the
checked project is on the checker thread; the sweep's trial remains the
guarantee for a whole folder.

## 7. The hash probe (measured)

`stitchwort` has no command that prints a hash, so the probe uses the test
cache: a test result is reused only when the content hashes of everything
the test uses are unchanged (docs/proposals/check-cache.md §4.5, and
`def_ref` in hash.rs:484-504 hashes references by their hash). A scratch
project has `test "probe" := let p := target; True`. Run it, swap
`target`'s form, run it again with `--json`, and read `cached`. Controls: a
comment added, cached; the statement changed, not cached; the variable
renamed, cached. Release build of `main` at 08:39, 10 Nov 2026.

| first form | second form | same hash |
|---|---|---|
| `(n: Nat): n + 0 = n := Nat.addZero n` | `∀ (n: Nat) => n + 0 = n := n => Nat.addZero n` | yes |
| same | `∀ (n: Nat) => n + 0 = n := Nat.addZero` | **no** |
| `(b: Bool): … := cases` | `∀ (b: Bool) => … := cases` | yes |
| `(n: Nat) (h: 0 < n): 1 ≤ n := omega` | `∀ (n: Nat) => 0 < n → 1 ≤ n := n h => omega` | yes |
| same | `(n: Nat): 0 < n → 1 ≤ n := h => omega` | yes |
| `∀ [a: Type] (xs: List a) => …` with arms | `[a: Type] (xs: List a): … := match xs with` | yes |
| same | `[a: Type]: ∀ (xs: List a) => … := match` (clause lambda) | yes |
| same | `∀ … := xs => match xs with` | **no** |
| `∀ (acc: Nat) (xs: List Nat) => …`, arms `\| acc, [] …` | `(acc: Nat): ∀ (xs: …) => …`, arms `\| [] …` | yes |
| same | `(acc: Nat) (xs: List Nat): … := match xs with` | yes |
| same | `… := match acc, xs with` | yes |
| `Nat.leTrans` with arms and premise columns `h1, h2` | `(a b c: Nat) (h1: a ≤ b) (h2: b ≤ c): a ≤ c := match a, b, c with` | yes |
| same | `(a b c: Nat): a ≤ b → b ≤ c → a ≤ c := match a, b, c with \| … => h1 h2 => …` | **no** |
| arms with a record pattern `{ row, column }` | `match p with \| { row, column } => …` | yes |
| arms with a guard `\| n if n == 0` | `match n with \| n if n == 0 => …` | yes |
| arms with a column from `o ≠ Some 3` | that column as `o3 =>` in each branch | **no** |
| `(d n: Nat): ∀ [auto ok: d ≠ 0] => …` | `(d n: Nat) [auto ok: d ≠ 0]: …` | yes |

So parameters versus a leading `∀` is never itself a change in meaning; the
hash moves only when the body's shape changes (an eta-expansion, a `match`
that is lifted instead of being the case tree, a premise bound inside a
branch).

## 8. Recommendation

**(a+): every variable before the colon, proofs by cases with `:= match x
with`, `∀` only where §4 says.** It is the end state Matt described, and the
one where a statement has one shape whatever its proof: a reader deciding
what was proved (the proving guide's reader) never has to read past the
proof technique, and changing a proof from arms to a lemma never moves the
statement's binders. It needs no language change, and the probe says the
conversion keeps the hash in every shape tried where the variables and
named premises all move. Its cost is in proofs: about 1,960 proofs by cases
gain a `match … with` line and an indent, and the guide's "a proof by cases
is like a function with arms" (docs/guide/10-proofs.md, "Induction is
recursion") becomes "like a function's `match`". Arms stay in the language
for `def`s, and stay legal on theorems, with the warning of §6.

If the arms are worth more than one shape of statement, (a) is the fallback:
it is the `def` rule, already followed by 96% of theorems, and changes about
270.

Not (b): it needs a language change for `decreasing`, turns 3,850 named
hypotheses into premises, and adds a lambda to every `:=` proof. Not (c):
an optional spelling makes the drift worse, and a required one is a token on
every theorem that `def`s don't have.

Order: the decision, then the sweep tool with its two hash checks (§5,
estimated 1.5 to 2 days), the sweep, then the warning with D3462's.

## 9. Open questions for Matt

1. **(a+) or (a)?** One shape for every statement, with proofs by cases
   written `:= match x with`; or the `def` rule, which keeps arms on
   theorems and leaves `∀` at the top of about 1,700 statements.
   *Recommendation: (a+).*
2. **Under (a+), do premises that the proof names move into the header?**
   `theorem Nat.leTrans (a b c: Nat) (h1: a ≤ b) (h2: b ≤ c): a ≤ c`
   rather than `(a b c: Nat): a ≤ b → b ≤ c → a ≤ c`. It is what keeps the
   hash (§7), it matches the 3,850 theorems that already name their
   hypotheses, and callers can then write `(h1 := …)`. Premises the proof
   doesn't name stay as `→`. *Recommendation: yes.*
3. **Add `∀` before the colon as a spelling (option c)?**
   *Recommendation: no.*
