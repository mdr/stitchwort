# SW-2707: porting Software Foundations to Stitchwort (Basics, Induction)

**Status:** lane report, 10 November 2026. Ports chapters 1 and 2 of
*Software Foundations*, Volume 1: *Logical Foundations* (LF), to the `sf/`
project, and records what made the port hard. Matt's question (10 Nov
2026): "Is that practical, could we start porting a chapter or two and see
what might be lacking that makes it hard to port cleanly?"

How claims are marked: **[measured]** run today with the release CLI built
from this branch; **[read]** read in the book's sources or this repo;
**[estimated]** my judgement.

## 1. Summary

- **The licence allows it.** The release's LICENSE file is the MIT licence
  (§2). The port keeps the book's prose as comments, with the licence in
  `sf/LICENSE-SF` and a header line in every file. Exercises are stated
  and left unsolved, as the authors ask.
- **Both chapters ported, and check.** `stitchwort check` in `sf/` checks
  7 namespaces in 0.38 s cold; `stitchwort test` passes 11 tests;
  `stitchwort audit` passes **[measured]**. Every definition and example
  of the two chapters is there, and every theorem the book proves, except
  two that differ from another only in Rocq's bullet style (§3).
- **The core language fits the book well.** Data types, `match`,
  or-patterns, structural recursion, `rfl`, `rewrite`, case analysis and
  induction as recursion all translate line for line. Several of the
  book's points come out *better*: the counterexample search says why
  `lower_letter_lowers` is unprovable, and a proof term has the shape of
  the book's informal proof.
- **What hurts is the reader's experience, not the language.** In order
  (§6): there is no way to leave an exercise unproved and still have the
  project check; Stitchwort's automation and library give most exercises
  away (`omega`, `ring`, `cases`, `search --at`, std's `Nat.addComm`); the
  library's `+` computes on its second argument, which removes the
  examples the book uses to motivate case analysis and induction; and the
  book's habit of stepping through a tactic proof to watch the goal change
  has only a partial counterpart (`?` holes).
- **The whole of LF looks practical**, at about 40 to 45 lane-hours more
  **[estimated]** (§8). The chapters about tactics (Tactics, Auto,
  AltAuto) and about Rocq's own machinery (IndPrinciples, Imp's
  notations) would need rewriting more than porting; IndProp meets two
  gaps found today (§7).

## 2. Licence

Downloaded `https://softwarefoundations.cis.upenn.edu/lf-current/lf.tgz`
(files dated 24 August 2026) into a fresh scratch directory. Its `LICENSE`
file, exactly **[read]**:

```
Copyright (c) 2026

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
```

It is the MIT licence. The copyright line names a year and no holder; the
Preface (`Preface.v:500-524`) says copyright is assigned to an "Author of
Record" per volume, Benjamin C. Pierce for LF. `sf/LICENSE-SF` reproduces
the file exactly, after a paragraph naming the book, the Author of Record
and the release, and each ported file starts with a line naming its
chapter and pointing at `sf/LICENSE-SF`.

The Preface also asks (`Preface.v:418-424`): "Please do not post solutions
to the exercises in a public place ... We especially request that readers
not post solutions to the exercises anyplace where they can be found by
search engines." The port states every exercise and solves none. I solved
them in the scratchpad only, to find what is hard (§5); nothing of that is
committed or quoted here.

## 3. What was ported

| | Basics.v | Induction.v |
|---|---|---|
| Book: lines, exercises | 2,052, 20 | 764, 12 |
| Book: proved theorems (`Qed`) | 30 | 6 |
| Port: files, lines | 6, 1,272 | 1, 451 |
| Data types | 12 (`bool` and `comparison` are std's) | 0 (`bin` is imported) |
| Definitions (not exercises) | 28 | 1 (`double`) |
| Worked theorems | 31 | 7 |
| `Compute` results as tests | 11 | 0 |
| Exercises stated | 20: 43 statements, 8 functions | 12: 23 statements, 3 functions |

- **Worked theorems.** Every theorem the book proves is ported, except
  `andb_commutative'` and `add_assoc''`, which repeat a proof with braces
  or bullets in place of another layout; the comments say so. Extra
  theorems show what is different: `plus1Neq0FirstTry` (holds by `rfl`
  here), `andb3Exchange'` (one word, `cases`), `add0RFirstTry` and
  `plusN0`.
- **Library types used for the book's own.** `bool` is std's `Bool`
  (`True`, `False`), with the book's `negb`, `andb`, `orb` written out
  over it; `nat` after `NatPlayground` is std's `Nat` (`Zero`, `Succ`);
  `comparison` (`Eq`, `Lt`, `Gt`) is std's `Ordering` (`Equal`, `Less`,
  `Greater`). `NatPlayground`'s own type is `Nat'` with `O` and `S`.
- **The book's modules** are namespaces, each in its own file, because a
  namespace has a file of its own (§6, item 6).
- **Names** go from `snake_case` to `camelCase` (`test_orb1` is
  `testOrb1`, `plus_O_n` is `plusON`); primes are allowed, so
  `plus_O_n'` is `plusON'`.
- **Exercises.** How they are stated, and why, is §4.

## 4. How the exercises are stated

Rocq's `Admitted` accepts a theorem or a definition without proof, so a
chapter with unsolved exercises still compiles, and the definitions after
an admitted function can still use it. Stitchwort's nearest form is `?`,
but a project with a `?` in it fails `stitchwort check`, and so would the
tiers if `sf/` were registered **[read, syntax.md "Goals"]**. Stitchwort
has no axiom declaration either. So the port states:

- **a theorem to prove** as a definition of a `Prop`, named as the book
  names the exercise: `def plusIdExercise: Prop := ∀ (n m o: Nat) => n =
  m → m = o → n + m = m + o`. The reader turns it into `theorem
  plusIdExercise (n m o: Nat) (h1: n = m) (h2: m = o): n + m = m + o :=
  …`. It checks, it can't be used as a fact by mistake, and the statement
  is visible.
- **a function to write** with a placeholder body (`def lowerGrade (g:
  Grade): Grade := g`), with a `--|` doc saying "Exercise: replace this
  placeholder". The definitions after it that use it (`applyLatePolicy`)
  still check.

Both are workarounds, and the first friction item (§6, item 1).

## 5. Each chapter

### 5.1 Basics: what ported cleanly

- **Data types and matching**, including `color`'s `primary` with an
  argument, nested patterns (`Bits B0 B0 B0 B0`), matching on two values
  (`minus`), and the or-patterns of `letter_comparison` (`C, (A | B)`),
  all character for character.
- **Examples**: `Example … Proof. simpl. reflexivity. Qed.` is `theorem
  … := rfl` every time.
- **`destruct`** is a `match`, and the book's bullets are its arms. The
  nested `destruct`s of `andb3_exchange` are nested matches, and `intros
  [] []` is `match b, c with`.
- **`rewrite`** with a hypothesis or a library lemma is the same idea,
  written `rewrite h in rfl`.
- **The test-backed `≤` (D3479) reads well against the book.** The book's
  `late_days <? 9 = true` hypotheses become `lateDays < 9`, which *is*
  the test giving `True`, so the program's `if lateDays < 9` and the
  hypothesis are one term: in the scratchpad, `noPenaltyForMostlyOnTime`
  is `rewrite onTime in rfl`, and `cases` proves it alone **[measured]**.
  The comments use `eqb`/`leb` to explain the difference from Rocq, where
  the proposition and the test are separate and joined by lemmas.
- **The counterexample search adds to the book.** The book's
  `lower_letter_lowers` first try (an `Abort`) asks "do you see why?".
  Stitchwort's `cases` closes four cases and answers: "this statement is
  false; a counterexample: l = F" **[measured]**. The port quotes the
  message.

### 5.2 Basics: what didn't port cleanly

- **`Compute` and `Check`** have no in-file form. `Compute` became a
  `test` stating the result (11 of them), with `stitchwort eval` and the
  REPL named for printing a value; `Check` became a comment quoting the
  REPL's `:t` (§6, item 5).
- **`Notation`** has no counterpart (D1200: a fixed set of operators). The
  book's `&&`, `||`, `+`, `*`, `-`, `=?`, `<=?` map to std operators
  already defined the same way, so this chapter loses nothing but the
  explanation of levels and scopes (§6, item 7).
- **`if` on any two-constructor type** (`invert`'s `if x then bw_white`)
  isn't Stitchwort's: `if` takes a `Bool` or a decidable proposition. A
  `match` instead, said in a sentence. Deliberate, and harmless here.
- **A constructor named like its type** (`Inductive grade := Grade …`)
  makes every later use of `Grade` as a type ambiguous (`E-AMBIGUOUS`,
  "`Grade` could mean `…LateDays.Grade` or `…LateDays.Grade.Grade`"),
  even in positions where only a type can go **[measured]**. The port
  names the constructor `MkGrade` (§6, item 8).
- **`plus_1_neq_0_firsttry` doesn't get stuck**, because std's `+`
  computes `n + 1` to `Succ n` (§6, item 3). The port proves it by `rfl`,
  says why, and makes the book's point with `eqb 0 n` and the book's own
  `plus`.
- **Modules** became files, so the chapter is read across six files
  (§6, item 6).

### 5.3 Induction: what ported cleanly

- **Induction as recursion** is closer to the book's informal proof than
  Rocq's script is. `add_assoc'` is three lines whose arms are the
  informal proof's two cases. The port keeps the book's "Formal vs.
  Informal Proof" section and says so.
- **`replace e1 with e2`** maps to `rewrite (proof: e1 = e2) in …`, and
  **`plus_rearrange_firsttry`** reproduces exactly: `rewrite Nat.addComm`
  with no arguments rewrites the outer `+`, as in Rocq **[measured]**; with
  its arguments, `rewrite Nat.addComm n m`, it rewrites the right one.
  That is Stitchwort's answer to the book's `replace`.
- **Separate compilation** disappears: `import Sf.Lf.Basics (..)` and a
  project, with the check cache, replace `_CoqProject`, `rocq makefile`
  and the "inconsistent assumptions" troubleshooting. The book's 130
  lines on it become one paragraph.
- **`bin`'s stubs**: the book repeats `bin`, `incr` and `bin_to_nat` so
  that the chapter can be graded alone. The port imports them from Basics.

### 5.4 Induction: what didn't port cleanly

- **The chapter's opening example is gone.** `add_0_r_firsttry` (`n + 0
  = n`) is `rfl` with std's `+`. The port shows that, then makes the
  book's case with the book's own `plus` from `NatPlayground2`, whose
  `plus n 0` is stuck, and quotes the error and the goal of the second
  try **[measured]** (§6, item 3).
- **The exercises' lemmas are in std, and the automation proves them.**
  `mul_0_r`, `plus_n_Sm`, `add_comm`, `add_assoc`, `mult_1_l`,
  `mult_plus_distr_r`, `mult_assoc` and `mul_comm` are `Nat.mulZero`,
  `Nat.addSucc`, `Nat.addComm`, `Nat.addAssoc`, `Nat.oneMul`,
  `Nat.mulDistribRight`, `Nat.mulAssoc`, `Nat.mulComm`; `omega` proves
  `add_comm`, `add_shuffle3` and even `mul_comm`; `ring` proves
  `mul_comm` and `mult_assoc` **[measured]** (§6, item 2). The worked
  theorems `mult_0_plus'` and `plus_rearrange` use the book's exercise
  `add_comm`; the port uses std's and says so.
- **Goal display while stepping** (§6, item 4): the book's "step through
  and watch the goal" has to become "write `?` and look", once per state.

### 5.5 Solving the exercises (scratchpad only)

I solved the 28 exercises of both chapters that give a statement or a
function to write (the other four ask for an informal proof, a theorem of
your own, or a function the checker rejects), in the scratchpad, in under
10 minutes **[measured, by
`date`]**, to see what a reader meets. Nothing
blocked. What I noticed, without the solutions:

- **Most are a word.** `cases` proves `andb_true_elim2` and the
  "tricky" optional `andb_eq_orb`; `omega` proves `mult_n_1`;
  `zero_nbeq_plus_1`, `zero_neqb_S`, `S_neqb_0`, `mult_1_l` and
  `double_incr` are `rfl` because of std's `+`.
- **Term proofs make the book's hints moot.** For `andb_true_elim2`, a
  `match` on both booleans leaves the hypothesis computed in each case,
  so the impossible case's hypothesis is already the proof; the book's
  hint ("simplify the hypothesis", "rewrite using the contradiction")
  doesn't apply. For `lower_grade_lowers` (3 stars), matching on the same
  patterns as `lowerGrade` left the hard case's goal as `Less = Less`,
  closed by `rfl`, without the letter split and the `lower_grade_F_Minus`
  rewrite the hint describes.
- **`cases` failed once where it might have worked.** On
  `lower_grade_lowers` it split the stuck call `letterComparison …` into
  its three results before the modifier underneath, and was left with
  goals like `Equal = Less` where the modifier was still unknown
  **[measured]** (§6, item 10).
- **The advanced `bin` exercises went through first time**, including the
  4-star `bin_nat_bin`, with `rewrite` finding a lemma's `natToBin (2 *
  n)` in a goal that shows `natToBin (k + k)` (it compares up to
  computation). `omega [ih]` did the arithmetic of `binToNat`.
- **`search --at` gives the answer.** At a `?` for `mul_comm` it listed
  the reader's own lemma, `Nat.mulComm m n` from std, and "omega, cases,
  Std.byDecision alone closes it". It took 18 s on this small project
  **[measured, once]**.

## 6. Friction, ranked by how much it hurts a reader of the book

1. **No `Admitted` that still checks.** A reader's file always has
   unfinished exercises, and the book's grading assumes that a chapter
   with `Admitted`s compiles and later chapters build on it. In
   Stitchwort a `?` makes `check` fail, everything using it is
   "unfinished", and an unfinished *definition* (an exercise function)
   leaves the definitions after it unchecked. The port's workaround (§4)
   checks, but it isn't how a reader works: they will write `?`, and then
   `check` fails.
   **Proposal:** a way to mark a declaration as deliberately unproved that
   checks with a warning, never silently. Options: (a) a project setting
   in `stitchwort.yaml`, `goals: allowed`, under which `check` reports
   open goals as warnings and still exits 0, while `audit` keeps failing
   every theorem that depends on one (Rocq's model: the `.vo` builds,
   `Print Assumptions` tells the truth); (b) an `admitted` proof term,
   reported by `check` as a warning and by `audit` as a failure. (a) is
   smaller and keeps `?` the one way to leave a hole. Matt's decision
   (trust and language). Either needs the unfinished definition case to
   work: a `def f … := ?` used by later definitions.
2. **The library and the automation give the exercises away.** About a
   third of the exercises (10 of the 28 with a statement, by my count) are one word or one std
   lemma (§5.5). Rocq
   readers have `lia`, `ring` and the standard library too, but the book
   hides them until later chapters, and it defines its own copies of
   things to keep the reader working by hand.
   **Proposal:** for the port, define the book's own `nat` and `bool`
   copies where it matters for the exercises, as the book does in
   `NatPlayground`: a `Sf.Lf.Nat` with its own `plus`, `mult`, and no
   lemmas, used by the exercises of Basics and Induction. That restores
   item 3 too. It costs the library's fast numbers, which these chapters
   don't need. The automation needs no change: say in the port which
   exercises it solves, and that doing them by hand is the point.
   Stitchwort deliberately has strong decision procedures (D2541:
   computing decides), and that is the right default.
3. **Std's `+` computes on its second argument** (nat-add-recursion.md),
   so `n + 0 = n`, `(n + 1) =? 0 = false` and `0 =? (n + 1) = false` are
   `rfl`. These are the book's chosen examples of "computing gets stuck",
   in both chapters. The port keeps the lesson with the book's own `plus`
   and `eqb 0 n`, but a reader following along with std's `+` won't see
   the problem the book is solving. Stitchwort deliberately differs; the
   fix for the port is item 2's own `nat`.
4. **No step-by-step proof state.** Rocq's pedagogy is to step through a
   script and watch the context and goal change after each tactic ("It is
   worth stepping through these proofs to observe how the context and the
   goal change", Basics.v:1033), and the later chapters' proofs are long
   enough that this is how a reader follows them. In
   Stitchwort a reader sees a goal by writing `?`, and the editor's
   "Show Goals" panel follows the cursor between holes, but a finished
   proof has nothing to step through: `rewrite a, b in rfl` shows no state
   between `a` and `b`, and a finished arm shows no goal.
   **Proposal:** in the language server, show the goal at any point of a
   proof, not only at `?`: hover on an arm shows its goal, hover on each
   rule of a `rewrite` chain shows the goal before and after it
   (lsp-goal-holes.md is the place to extend). This is the single largest
   gain for a reader of SF, or of any proof textbook.
5. **`Compute` and `Check` have no in-file form.** The book uses them
   25 times in these two chapters to show a value or a type
   inline (all in Basics). Tests cover `Compute` well (and are checked), but a type can't
   be asserted in the file, and `:t` in the REPL prints only the type,
   not `e: T`.
   **Proposal:** small: the REPL's `:t` prints `e: T` as Rocq's `Check`
   does. Larger, and Matt's decision: an in-file `#eval e` / `#check e:
   T` whose output the editor shows inline. Otherwise "Stitchwort
   deliberately differs: tests and the REPL".
6. **Modules become files.** Each `Module X … End X` is a namespace, and a
   namespace has its own file, so Basics reads across six files and the
   reader has to jump. The book uses modules to reuse names (`nat`,
   `plus`, `foo`) for the rest of LF too.
   **Proposal:** a nested `namespace X … end` block inside a file. Small
   to medium in the elaborator; it would also suit tests and examples.
   Otherwise "deliberately differs", with the README's reading order.
7. **No `Notation`.** Harmless in these chapters: the book's notations
   are std's operators. It matters later: Lists (`[x; y]`, `::`, `++`,
   map to Stitchwort's own list syntax, fine), Maps (`x !-> v ; m`), and
   above all Imp, whose 33 notations make programs like `X := 1; while
   …` readable. Stitchwort deliberately has a fixed operator set (D1200).
   For Imp the port would write programs as constructor terms or parse
   them from text (ImpParser does that already), with a cost to
   readability that is the largest of any chapter.
8. **A constructor with its type's name is ambiguous where a type is
   expected** (§5.2). Rocq, Lean and Haskell allow it, and SF does it often
   (`grade`'s `Grade`, later `Some`-like single constructors).
   **Proposal:** a small elaborator fix: in a type position, prefer the
   type (a constructor is never a type); keep `E-AMBIGUOUS` in value
   positions. Ticket-sized.
9. **`if` takes only a `Bool`** (§5.2). Deliberate; one sentence in the
   port.
10. **`cases` splits a stuck call before the variable under it** (§5.5).
    On `lower_grade_lowers` it generalised `letterComparison l1 l2` into
    its three results instead of splitting `g`'s modifier, and failed.
    **Proposal:** ticket for `cases`: when a case can't close, retry with
    the variables the stuck call is stuck on split first. Low for SF.
11. **Exercise-only items, small.** `stitchwort audit` reports "161
    theorems" for a project with 38, because it counts generated lemmas
    (the record update lemmas of `Grade`, `….Grade.l.update.l`); a reader
    checking "how many did I prove" is misled. `search --at` took 18 s
    here.

## 7. Two gaps found probing later chapters

On a scratch file, for the estimate in §8 **[measured]**:

- **Inductive propositions work.** `type Ev: Nat → Prop = | EvZero: Ev 0
  | EvSS (h: Ev n): Ev (Succ (Succ n))`, a proof of `Ev 4`, inversion by
  `match h with | EvSS e => e`, induction on evidence with `[n := m]`,
  an inductive `Le`, `injection` as `Eq.cong Nat.pred h`, `discriminate`
  as `cases`, Church numerals at `Type 1`, and excluded middle as a
  statement all check.
- **An impossible hypothesis of an inductive family can't be dismissed
  in the house style.** `theorem t: Ev 1 → Void | ()` checks, but with the
  hypothesis before the colon (D3470), `match h with | ()` is `E-PARSE`
  ("expected `=>`"), and `match h with` with no arms is `E-PARSE` too.
  `cases` doesn't invert families either: on `h: Ev 1` it finds "nothing
  to split on", and on `h: Ev (Succ (Succ n))` it can't produce `Ev n`.
  IndProp does this dozens of times (`inversion` is one of its main
  tools). **Proposal:** accept an arm `| ()` without a right side in a
  `match` expression (Lean's `nomatch h`), and teach `cases` to split a
  hypothesis whose type is an inductive family. The first is small and
  probably wanted anyway, since D3470 moved theorems to `match`.
- **No named induction principle for a data type.** `Nat.rec`,
  `Nat.induct`, `Tree.induct` don't exist (only functions get
  `f.induct`, and nested types `T.induct`). IndPrinciples is built on
  `Check nat_ind`; the port would state each principle as a theorem
  proved by recursion, which works but changes the chapter's subject.

## 8. Is the whole of LF practical?

Yes, with the friction above. These two chapters took about 25 minutes
of writing after reading them, plus 10 of solving in the scratchpad, for
2,800 lines of `.v`, and 40 minutes for this note **[measured]**; the rest of LF is about 23,000 lines including test
scripts. Per chapter, for an Opus lane, with exercises stated as here
**[estimated]**:

| Chapter | Lines | Exercises | Estimate | Main difficulty |
|---|---|---|---|---|
| Lists | 1,207 | 19 | 1.5 h | the book's own `natlist` and notation; std `List` lemmas give exercises away |
| Poly | 1,246 | 20 | 1.5 h | implicit arguments (`Arguments`, `@`) map to `[a: Type]` and `f [a := T]`; Church numerals need `Type 1` (measured fine) |
| Tactics | 1,301 | 19 | 2.5 h | a chapter about tactics (`apply`, `injection`, `discriminate`, `generalize dependent`, `specialize`): each becomes a term idiom, and the chapter is rewritten more than ported |
| Logic | 1,841 | 32 | 3 h | `Prop` vs `bool` (`even` vs `Even`, reflection): Stitchwort's answer is D3479's tests-first, and the chapter's "bool vs Prop" section should be rewritten from bool-and-prop.md; no `propext` (D3481); funext is a theorem from `Quot.sound`; classical axioms only as statements |
| IndProp | 2,945 | 53 | 5 h | `inversion` everywhere (§7), regular expressions and the pumping lemma are long; the largest chapter |
| Maps | 380 | 6 | 1 h | `string` equality is `Text`'s; maps as functions need funext (`Quot.funext`) |
| ProofObjects | 946 | 18 | 1.5 h | Stitchwort's natural ground: proofs are terms already, so the chapter shortens |
| IndPrinciples | 980 | 10 | 2.5 h | no generated `T.rec`/`T.induct` for plain types (§7): principles become theorems proved by recursion |
| CurryHoward | 1,320 | 16 | 2 h | fits, as ProofObjects |
| Rel | 412 | 12 | 1 h | plain `Prop` relations |
| Imp | 2,088 | 18 | 5 h | 33 notations (§6, item 7); big-step evaluation as an inductive relation (IndProp's gaps again) |
| ImpParser | 466 | 0 | 1.5 h | fuel-based parser on `Text`; Stitchwort's `Parse` could replace it, but a port keeps the book's |
| ImpCEvalFun | 398 | 4 | 1 h | fuel, fine |
| Extraction | 134 | 0 | 0.5 h | rewritten for `stitchwort build` and `--js` |
| Auto, AltAuto | 3,141 | 15 | 5 h | about tactic automation (`auto`, `eauto`, `Ltac`): rewritten around `omega`, `cases`, `auto` arguments and `search --at`; much of it has no counterpart |
| Preface, Postscript, Bib | | | 1 h | prose |
| **Total** | | | **about 37 h**, plus 15% for review: **40 to 45 h** | |

**Hardest:** IndProp (size, and inversion), Imp (notations, and
inversion on evaluation), Auto/AltAuto and Tactics (their subject doesn't
exist), and IndPrinciples (no generated principles). Logic is the most
interesting rather than the hardest: its "Prop vs bool" section is where
Stitchwort most deliberately differs from Rocq, and it bears directly on
D3479 to D3482. With D3482 (a `Bool` where a proposition is expected means
`b = True`), the chapter's reflection lemmas mostly disappear.

Fixing §6 items 1, 2 (the port's own `nat`) and 8, and §7's empty match,
before porting more would save rework across every later chapter.

## 9. What would help a reader follow along

- **Goals in the editor everywhere** (§6, item 4): the largest gain.
- **The playground**: `web/bundle-projects.sh` bundles `aoc/` and
  `games/rogue/` into the playground; `sf/` would be one more entry, with
  the same `sources: [src]` rule (D112). A reader could then read and
  edit the chapters in the browser with no install, as the book's own
  site offers HTML.
- **The guide**: a page "Coming from Rocq or SF" mapping tactics to terms
  (`intros` → parameters, `destruct` → `match`, `induction` → recursion,
  `rewrite` → `rewrite … in`, `replace` → `rewrite (proof: …)`,
  `inversion` → `match` on the evidence, `discriminate` → `()` or
  `cases`, `injection` → `Eq.cong`, `Admitted` → `?`, `Compute` →
  `test`/`eval`, `Check` → `:t`/hover). The port's comments already say
  most of this; the guide's proofs chapter would link it.
- **An HTML rendering of the port** (comments as prose, code as code), as
  `rocq doc` gives the book; the doc-comment tooling (`stitchwort doc`)
  could grow into it.

## 10. Registering `sf/` with the tiers (not done)

Like `aoc/` and `games/rogue/`, it would need, if wanted:

- `Taskfile.yml`: `cd sf && {{.SW}} audit --no-search` in `test:gate`;
  `Sf*) cd sf ;;` in `audit:touched`; `sf/.stitchwort` in the cache copy
  of `worktree:new`;
- `flake.nix`: `./sf/stitchwort.yaml` and `./sf/src`'s `.sw` files in the
  source fileset, if a flake check is to run it;
- `web/bundle-projects.sh`, for the playground (§9).

A whole-`sf/` check takes 0.4 s cold today **[measured]**, so it costs the
tiers nothing.

## 11. Findings worth tickets

1. A deliberately-unproved form that checks with a warning (§6, item 1):
   Matt's decision first.
2. The port's own `nat`/`bool` for the exercises (§6, items 2 and 3):
   Matt's decision on the port's direction.
3. Goals at any point of a proof in the language server (§6, item 4).
4. `E-AMBIGUOUS` for a constructor named like its type, in type positions
   (§6, item 8): small elaborator fix.
5. `match h with | ()` without a right side in a `match` expression, and
   `cases` inverting inductive-family hypotheses (§7).
6. The REPL's `:t` prints `e: T` (§6, item 5): small.
7. `cases` retries with the variables under a stuck call split first
   (§6, item 10).
8. `audit`'s count includes generated lemmas; say "38 theorems (and 123
   generated)" (§6, item 11).
9. Nested `namespace … end` blocks in a file (§6, item 6): design first.
10. Add `sf/` to the playground bundle (§9).
11. A "Coming from Rocq" guide page (§9).
