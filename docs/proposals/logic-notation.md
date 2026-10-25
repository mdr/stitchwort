# Notation for logic and sets: `x in xs`, `<->`, `exists`?

**Status:** design note, 25 October 2026 (SW-461). Nothing is implemented.
The decisions are D1200–D1208 (§9). The counts are in §3; the survey of other
languages is in §4, with a link for every claim.

## 1. The short answer

The trigger was D1199 (propositions stay predicate-first): `List.Mem x xs`
reads as "x ∈ xs", and Lean, Agda and Rocq all write it with `∈`. The
question is whether Stitchwort should have notation for membership,
quantifiers and connectives, and whether it should be Unicode, ASCII or both.

**The recommendation: ASCII only, as today, with three additions and a
change of house style.**

1. **`x in xs`** for membership (`List.Mem x xs`, and `Set`/`Map` keys), and
   `x !in xs` for its negation, as Kotlin and Dafny write them (§4.7, §4.11).
   Like `<=`, it's a proposition that is decided where a `Bool` is expected,
   so `if x in seen` and `xs.filter (x => x in seen)` work too.
2. **`p <-> q`** for `Iff p q`, as Lean and Rocq write it in ASCII.
3. **`exists (x: T) => P`** for `Exists T (x => P)`.
4. **House style: write the operators that already exist.** `&&`, `||`, `!`
   and `!=` already mean `And`, `Or`, `Not` and `Not (a = b)` where a
   proposition is expected (docs/syntax.md, "`&&`, `||` and `not`"), but the
   library and AoC still mostly write `Not (…)`, `And (…) (…)` and
   `Not (a = b)` (§3). The printer and a migration lane fix that.

No Unicode in source, no renderer that swaps `<=` for `≤`, no
user-definable notation, and no set operators (`∪ ∩ ⊆`). A Unicode
character pasted from Lean or a paper gets an error that names the ASCII to
write instead.

Here is one real statement (Day 9, `largestInList`) today and after:

```
-- today
theorem largestInList: (areas: List Nat) -> Or (List.Mem (largest areas) areas) (And (areas = Nil) (largest areas = 0))

-- proposed
theorem largestInList: (areas: List Nat) -> largest areas in areas || (areas = Nil && largest areas = 0)
```

The reasons, in brief:

- **Most of the notation is already there.** `->` is implication and
  `(x: T) -> P` is "for all", `&&`/`||`/`!` work on propositions, and `<=`,
  `>=` and `!=` exist. The gaps are membership, "there exists" and "if and
  only if" (§2).
- **ASCII keeps every tool working unchanged**: plain editors, the terminal,
  `grep`, diffs and the playground's `<textarea>`, which has no input method
  (§6.3). Lean and Agda need an editor that turns `\in` into `∈`; Isabelle
  needs its own editor to show `\<in>` as `∈` (§4).
- **It matches the mainstream languages Matt wants the surface to feel
  like.** Scala deprecated its Unicode arrows (§4.11), Dafny (a
  verification language with C-like syntax) is all ASCII, and Kotlin and
  Python have `in`.
- **Mathematical readers lose little.** `<=`, `!=`, `->`, `&&` are the forms
  every programmer already reads; `in` is the word for `∈`; `<->` is Lean's
  and Rocq's own ASCII.

## 2. What exists today

All from docs/syntax.md ("Expressions" and "`&&`, `||` and `not`") and the
library sources.

| Idea | Maths | Stitchwort today | Operator? |
|---|---|---|---|
| implies | `P → Q` | `P -> Q` | yes |
| for all | `∀ x : T, P` | `(x: T) -> P` (a dependent function type) | yes |
| bounded for all | `∀ x ∈ xs, P x` | `(x: T) -> List.Mem x xs -> P x`, or `List.All P xs` | no |
| there exists | `∃ x : T, P` | `Exists T (x => P)` (`import Std (Exists)`), built with `Witness x proof` | **no** |
| and | `P ∧ Q` | `P && Q`, or `And P Q` (constructor `Both`) | yes, printed as `&&` |
| or | `P ∨ Q` | `P \|\| Q`, or `Or P Q` (`Inl`, `Inr`) | yes, printed as `\|\|` |
| not | `¬P` | `!P`, `not P`, or `Not P` (which is `P -> Void`) | yes, but printed as `Not P` |
| iff | `P ↔ Q` | `Iff P Q`, a record of `forward` and `backward` | **no** |
| not equal | `a ≠ b` | `a != b` (it *is* `Not (a = b)`; printed as `!=`) | yes |
| order | `≤ ≥ <` | `<= >= <` (`>=` is `<=` flipped) | yes |
| membership | `x ∈ xs` | `List.Mem x xs` (defined as `List.Any (y => y = x) xs`) | **no** |
| membership (sets) | `k ∈ s` | `Set.contains k s = True` (a `Bool` equation) | **no** |
| subset | `A ⊆ B` | `Set.isSubset a b = True`; for lists, `(e: T) -> List.Mem e xs -> List.Mem e ys` | no |
| union etc. | `A ∪ B` | `Set.union a b`, `Set.difference a b` (functions) | no |

Other facts that matter:

- **Names are ASCII** (syntax.md, "Layout"): `def café` is "unexpected
  character". Text, characters and comments may hold any Unicode.
- **Operators are fixed.** There is no `infix` or `notation` declaration.
  Some operators go through interfaces (`+` is `Add.add`, `<` is `Ord`'s;
  `examples/accept/operators.sw`), so a user's type can *have* `+`, but no
  one can add a new symbol.
- **`&&`, `||` and `!` already have two readings**, chosen by what's
  expected: `And`/`Or`/`Not` where a proposition is expected, `Bool`
  operations otherwise (with a proposition operand decided). `x in xs` would
  follow the same pattern (§5.2).
- **`in` is taken, in one place.** It ends a `rewrite`:
  `rewrite h1, h2 in body`, used throughout the proofs (452 lines of `.sw`
have both `rewrite` and the word `in`, and more have the `in` on a later
line). It isn't a keyword:
  the parser checks for the word, and `(in)` is an ordinary name today
  (`crates/syntax/src/parser.rs`, `ends_rewrite_rule`). There's no
  `let … in`; blocks use layout.
- **Messages already use some Unicode**: goals print `⊢`, and failing tests
  print `✗`.
- **The playground editor is a `<textarea>` over a highlighted copy**
  (`web/index.html`): the two must have the same characters at the same
  widths, so anything that *displays* different characters from the ones
  typed doesn't fit it (§6.3). Its font is Recursive, whose "Rec Mono for
  Code" cut has code ligatures behind the `dlig` feature
  ([Recursive README](https://github.com/arrowtype/recursive)).

## 3. How often these appear

Counted by a script over `theorem` statements (from `theorem` to its `:=`)
and over all code, comments and text removed: 805 statements in `std`
(`crates/elab/src/std`), 326 in `aoc`, 712 in `examples/accept` and
`examples/projects`. The counts are by pattern, so treat them as
approximate: `&&`, `||` and `!` also count `Bool` uses inside statements,
and the binder count is "a `(name: T) ->` in the statement".

| Token | std: statements / all code | aoc | examples |
|---|---|---|---|
| `Mem` (`List.Mem`, …) | 81 / 102 | 69 / 94 | 6 / 6 |
| `And` (by name) | 31 / 53 | 7 / 28 | 3 / 9 |
| `Or` (by name) | 9 / 11 | 3 / 6 | 10 / 14 |
| `Not` (by name) | 73 / 103 | 6 / 9 | 12 / 13 |
| `Iff` | 12 / 15 | 1 / 4 | 0 / 4 |
| `Exists` | 10 / 13 | 1 / 2 | 3 / 3 |
| `&&` | 41 / 302 | 51 / 172 | 13 / 203 |
| `\|\|` | 31 / 59 | 11 / 38 | 6 / 22 |
| prefix `!` | 25 / 101 | 6 / 29 | 2 / 65 |
| `not` | 3 / 22 | 2 / 12 | 3 / 63 |
| `(x: T) ->` binders | 1413 / 1633 | 246 / 296 | 64 / 134 |
| `<=` | 261 / 290 | 146 / 234 | 132 / 173 |
| `<` | 127 / 177 | 87 / 147 | 71 / 164 |
| `!=` | 60 / 81 | 20 / 24 | 2 / 38 |
| `>=` | 0 / 0 | 0 / 0 | 3 / 12 |

What this says:

- **Membership is the one frequent gap**: 150 statements in std and aoc
  mention `Mem`, against 13 for `Iff` and 11 for `Exists`. In Day 8 and
  Day 9's proofs it is in most hypotheses (`(ma: List.Mem a tiles)
  (mb: List.Mem b tiles)`).
- **"For all" is everywhere and already reads well enough.** 1,700 binders
  are written `(x: T) -> …`. A `forall` keyword would change every one of
  them for no gain in meaning (§6.1).
- **The named connectives survive although the operators exist**, mostly
  `Not` (73 in std). `Not (h1 = h2)` appears where `h1 != h2` means the
  same term. One reason is likely that the printer shows `Not P` rather than
  `!P`, so code copied from goals keeps the name (speculative: not checked
  against history).
- **`<=` and `!=` are common and already ASCII**; a `≤` would only change
  how they look.

## 4. Survey

Every claim has a link to a page read for this note. Where a page couldn't
be read (403s from mailing-list archives, for example), the claim is marked
*unverified*.

### 4.1 Lean 4: Unicode first, partial ASCII, notation is user-definable

- **Both spellings are declared together**, with `unicode("…", "…")`:
  `infixr:35 unicode(" ∧ ", " /\\ ") => And`,
  `infixr:30 unicode(" ∨ ", " \\/ ") => Or`,
  `infix:50 unicode(" ≤ ", " <= ") => LE.le`
  ([Init/Notation.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Notation.lean)).
  The parser does the same for `∀`/`forall`, `λ`/`fun` and `→`/`->`
  (`unicodeSymbol "∀" "forall"`;
  [Lean/Parser/Term.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Parser/Term.lean)).
- **Some have no ASCII form at all**: `¬`, `∈` and `∉`
  (`notation:50 a:50 " ∈ " b:50 => Membership.mem b a`; Notation.lean), `≠`,
  and the set operators `⊆ ∪ ∩`
  ([Init/Core.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Core.lean)).
  `↔` and `<->` are both declared, with a comment saying to prefer `↔`
  (Core.lean).
- **The ASCII and Unicode forms can mean different things**: `≠` is the
  proposition `Ne`, while `!=` is "boolean not-equal" (Core.lean).
  (Stitchwort's `!=` is already the proposition, decided where a `Bool` is
  wanted, so it has no such split.)
- **`∈` comes from an interface**: `class Membership (α : outParam (Type u))
  (γ : Type v) where mem : γ → α → Prop`, "the typeclass behind the notation
  `a ∈ s : Prop`"
  ([Init/Prelude.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Prelude.lean)).
- **Bounded binders**: `∀ x ∈ y, …` is `∀ x, x ∈ y → …`, and `∃ x ∈ y, …` is
  `∃ x, x ∈ y ∧ …`
  ([Init/BinderPredicates.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/BinderPredicates.lean)).
- **Notation is user-definable**: `notation`, `infix` and macros; "operator
  declarations are translated into notation declarations"
  ([reference manual](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Notations/)).
- **Typing**: in VS Code, "typing a backslash followed by an abbreviation
  identifier… `\forall` will yield `∀`", and "hovering over the symbol will
  also provide all available abbreviation identifiers"
  ([vscode-lean4 manual](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md)).
  The book teaches `→` as `\to` "or the ASCII alternative `->`"
  ([Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html)).
- **Mathlib's style** encourages Unicode "where they help develop good
  notation and improve readability", but bans duplicate spellings: `λ` is
  "disallowed in mathlib in favor of the `fun` keyword", and `$` in favour of
  `<|` "for consistency"
  ([Mathlib style guide](https://leanprover-community.github.io/contribute/style.html)).
  A linter keeps an allowlist of characters and rejects invisible and
  direction-changing ones, noting that "some characters overlap in some
  fonts"
  ([UnicodeLinter.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Linter/TextBased/UnicodeLinter.lean)).

### 4.2 Agda: Unicode everywhere, mixfix

- **Mixfix operators** mark argument places with `_` (`if_then_else_`,
  `infix 4 _≡_`)
  ([Agda docs](https://agda.readthedocs.io/en/latest/language/mixfix-operators.html)).
- **Typing** is by an Emacs input method: `\all` for `∀`, `\to` for `→`,
  `\in` for `∈`; to find out how to type a character you see, "type
  `M-x describe-char`"
  ([Emacs mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)).
  The textbook PLFA lists the key sequence for every symbol it uses
  ([PLFA, Lambda](https://plfa.github.io/Lambda/)), which shows the burden.
- **Complaints**: "Years ago, I had a lot of trouble as a new user of Agda
  because it wasn't clear how to type the operators I needed"
  ([Python forum](https://discuss.python.org/t/using-math-symbols-for-operators/14700?page=2));
  "users have struggles simply copying their Agda code snippets to LaTeX"
  ([swift-evolution](https://lists.swift.org/pipermail/swift-evolution/Week-of-Mon-20170828/039354.html)).
  A 2012 thread on `:` versus the lookalike `∶` ("You cannot tell from
  looking at the code whether your code is syntactically correct or not")
  is *unverified* (archive returned 403;
  [link](https://lists.chalmers.se/pipermail/agda/2012/004810.html)).

### 4.3 Idris 2: ASCII by decision

- The FAQ answers "Will there be support for Unicode characters for
  operators?" with no: "It's hard to type (this is important if you're
  using someone else's code…)", "as soon as people start using it in their
  library code, others have to deal with it", "Too many characters look too
  similar"
  ([Idris FAQ](https://docs.idris-lang.org/en/latest/faq/faq.html)).
- Membership is a type, `Elem x xs`
  ([Data/List/Elem.idr](https://github.com/idris-lang/Idris2/blob/main/libs/base/Data/List/Elem.idr)),
  and negation is a function into `Void`
  ([tutorial](https://idris2.readthedocs.io/en/latest/tutorial/theorems.html)),
  as Stitchwort's `Not p` is `p -> Void`.

### 4.4 Rocq (Coq): ASCII by default, Unicode as an opt-in library

- ASCII: `~` (level 75), `/\` (80), `\/` (85), `<->` (95), `->` (99),
  `forall x : T, P`, `exists x, P`; list membership is the plain function
  `In a l`
  ([library](https://rocq-prover.org/doc/V9.0.0/refman/language/coq-library.html),
  [List](https://rocq-prover.org/doc/V8.19.0/stdlib/Coq.Lists.List.html)).
- Unicode is a library of notations over the ASCII ones:
  `Notation "x ∧ y" := (x /\ y)`, and so on for `∨ → ↔ ¬ ≠ ∀ ∃ λ`
  ([Utf8_core](https://rocq-prover.org/doc/V8.19.0/stdlib/Coq.Unicode.Utf8_core.html)).
  RocqIDE enables it with `Require Import Unicode.Utf8`, and "you of course
  need to use a character font which supports them"
  ([RocqIDE](https://rocq-prover.org/doc/V9.0.0/refman/practical-tools/coqide.html)).

### 4.5 Isabelle: ASCII on disk, Unicode on screen

- Files hold ASCII; symbols are written `\<forall>`, `\<in>`, and the jEdit
  editor shows them as `∀`, `∈`. Typing shortcuts: `!` for `∀`, `:` for `∈`,
  `-->` for `⟶`. In another editor, "verbatim "\alpha" will be shown". It
  ships its own font so every symbol displays, and says "Raw Unicode
  characters within formal sources compromise portability and reliability"
  ([JEdit.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/Doc/JEdit/JEdit.thy)).
  This is option (d) taken all the way: it works, at the price of a
  dedicated editor.

### 4.6 F*

- `/\`, `\/`, `~p` (defined as `p ==> False`), `==>`, `forall`, `exists`,
  and "every logical connective comes in two flavors" (a `bool` one and a
  `prop` one)
  ([F* book](https://fstar-lang.org/tutorial/book/part2/part2_logical_connectives.html)).
  That's Stitchwort's `&&` situation, with two spellings where Stitchwort
  has one.

### 4.7 Dafny: ASCII, mainstream syntax, and Unicode removed

- Logic: `<==>`, `==>`, `<==`, `&&`, `||`, `!`, `==`, `!=`; quantifiers
  `forall x: nat | x <= 5 :: x * x <= 25` and `exists p :: …`; sets have
  `e in s`, `e !in s`, `<=` (subset), `+` (union), `*` (intersection), `-`
  (difference), `!!` (disjoint)
  ([Dafny reference](https://dafny.org/latest/DafnyRef/DafnyRef)).
- "In some past versions of Dafny, non-ASCII, unicode representations of
  some mathematical symbols were permitted"; they no longer are, and
  "Unicode letters are not allowed in Dafny identifiers" (same page).

### 4.8 Liquid Haskell

- Refinements are ASCII: `{v:Int | 0 <= v}`; predicates use `&&`, `||`,
  `=>`/`==>`, `<=>`, `not`
  ([specifications](https://ucsd-progsys.github.io/liquidhaskell/specifications/),
  [tutorial](https://ucsd-progsys.github.io/liquidhaskell-tutorial/Tutorial_02_Logic.html)).

### 4.9 TLA+: ASCII canonical, typeset and now Unicode too

- ASCII `\A`, `\E`, `/\`, `\/`, `\in`, typeset as `∀ ∃ ∧ ∨ ∈`. Unicode
  source support was added to the tools in 2024; converting is "more
  complicated than search & replace since some TLA⁺ syntax depends on
  vertical alignment", and editor plugins translate as you type
  ([Helwer, 2024](https://ahelwer.ca/post/2024-05-28-tla-unicode/)). One
  symbol can have several ASCII spellings (`<=`, `=<`, `\leq` all become
  `≤`)
  ([tlaplus-standard/unicode](https://github.com/tlaplus/tlaplus-standard/tree/main/unicode)).

### 4.10 Haskell

- The `UnicodeSyntax` extension allows `∷ ⇒ → ← ∀` in place of
  `:: => -> <- forall`
  ([GHC guide](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/unicode_syntax.html)).
  It's opt-in per file; how widely it's used wasn't checked.

### 4.11 Scala, TypeScript, Kotlin: the mainstream

- **Scala deprecated its Unicode arrows** `⇒ ← →` in 2.13 (PR merged January
  2019), prompted by a precedence bug between the two spellings; a
  maintainer preferred "to not go the Unicode-symbol path at all, rather
  than maybe have it piecemeal", and ligatures were suggested instead
  ([scala/scala#7540](https://github.com/scala/scala/pull/7540)). Users
  agreed: "hard to type on most keyboards", "there are always two
  possibilities for arrows" (to search for), "I just want to see what I
  type" ([Scala forum](https://users.scala-lang.org/t/unicode-arrows/3509)).
- Scala's style guide says of symbolic method names: "Avoid!", except for
  DSLs and "Logically mathematical operations"
  ([naming conventions](https://docs.scala-lang.org/style/naming-conventions.html)).
- **Kotlin** has `a in b` (`b.contains(a)`) and `a !in b`
  ([operators](https://kotlinlang.org/docs/operator-overloading.html)).
- **JavaScript's `in`** means something else: `"key" in obj` "returns
  `true` if the specified property is in the specified object or its
  prototype chain"
  ([MDN](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/in)).
  A TypeScript reader may first read `x in xs` that way; Python, Kotlin and
  Dafny readers read it as membership.

### 4.12 Fonts, rendering, accessibility, lookalikes

- **Ligatures** draw `->`, `<=`, `!=` as one glyph: "This is just a font
  rendering feature: underlying code remains ASCII-compatible"
  ([Fira Code](https://github.com/tonsky/FiraCode)).
  Emacs's `prettify-symbols-mode` and Vim's `conceal` (which replace the
  displayed characters) weren't checked for this note, nor whether VS Code
  has an equivalent built in.
- **Accessibility**: a blind Julia user: "Fortunately, Julia can be written
  in ASCII only", and "It is such a pain to input Unicode characters
  besides ASCII"
  ([Julia Discourse](https://discourse.julialang.org/t/julia-and-braille/77002)).
- **Lookalikes**: Idris ("too many characters look too similar"), Scala
  ("102 rightward arrows in Unicode and many look alike"; forum above), the
  Mathlib linter, and Rust's `confusable_idents` lint, which uses Unicode's
  confusables data
  ([rustc source](https://doc.rust-lang.org/stable/nightly-rustc/src/rustc_lint/non_ascii_idents.rs.html)).

### 4.13 What the survey says

- **Languages whose surface is ASCII-first kept or went back to ASCII**:
  Idris refused Unicode operators, Dafny removed them, Scala deprecated its
  arrows. Liquid Haskell and F* are ASCII.
- **Two spellings of one thing cause trouble**: Scala's precedence bug,
  searches that must try both, Mathlib banning synonyms, Lean's `!=` and
  `≠` meaning different things.
- **Unicode-first systems need editor support** (Lean's and Agda's input
  methods, Isabelle's own editor and font), and their users report the
  cost when copying code elsewhere.
- **Membership is usually a library proposition behind an interface or a
  name** (Lean's `Membership`, Idris's `Elem`, Rocq's `In`); the ASCII
  infix `in` comes from Dafny, Kotlin and Python.

## 5. The options

The statements used throughout, all real:

| | Where | Today |
|---|---|---|
| S1 | Day 9 `largestInList` | `(areas: List Nat) -> Or (List.Mem (largest areas) areas) (And (areas = Nil) (largest areas = 0))` |
| S2 | Day 8 `joinedMore` (hypothesis) | `(more: (e: (Nat, Nat)) -> List.Mem e xs -> List.Mem e ys)` |
| S3 | Day 8 `occurrencesAbsent` | `(ys: List Nat) -> Not (List.Mem x ys) -> List.occurrences (z => q z && (z == x)) ys = 0` |
| S4 | Day 8 spec `LastNeeded` | `And (OneCircuit n (firstConnections (Succ k) points)) (Not (OneCircuit n (firstConnections k points)))` |
| S5 | Day 8 `lastNeededExists` | `(two: 2 <= points.length): Exists Nat (LastNeeded points)` |
| S6 | Day 7 `headsDistinct` (hypothesis) | `(ne: Not (h1 = h2))` |
| S7 | Day 9 `keyLinesHas` | `(m: Or (List.Mem v values) (List.Mem v (List.map Succ values))): List.Mem v (keyLines values)` |
| S8 | std `Map.memToList` | `Iff (List.Mem (key, value) (Map.toList m)) (Map.get key m = Some value)` |
| S9 | std `Exists.example` | `Exists Nat ((n: Nat) => n * n = 49)` |
| S10 | std `Nat.lexKeepsFirst` | `Nat.LexLess a1 a2 b1 b2 -> Not (a1 < b1) -> b1 < k -> a1 < k` |

(In S4, `points.length` is shortened to `n` to fit.)

### 5.1 (a) Status quo, with the operators that exist

No language change. Write `&&`, `||`, `!`, `!=` instead of the names, and
teach the printer to show `!P`.

```
S1  (areas: List Nat) -> List.Mem (largest areas) areas || (areas = Nil && largest areas = 0)
S2  (more: (e: (Nat, Nat)) -> List.Mem e xs -> List.Mem e ys)
S3  (ys: List Nat) -> !List.Mem x ys -> List.occurrences (z => q z && (z == x)) ys = 0
S4  OneCircuit n (firstConnections (Succ k) points) && !OneCircuit n (firstConnections k points)
S5  (two: 2 <= points.length): Exists Nat (LastNeeded points)
S6  (ne: h1 != h2)
S7  (m: List.Mem v values || List.Mem v (List.map Succ values)): List.Mem v (keyLines values)
S8  Iff (List.Mem (key, value) (Map.toList m)) (Map.get key m = Some value)
S9  Exists Nat ((n: Nat) => n * n = 49)
S10 Nat.LexLess a1 a2 b1 b2 -> !(a1 < b1) -> b1 < k -> a1 < k
```

- **Parsing:** nothing new. `!List.Mem x ys` is `!(List.Mem x ys)`, since
  `!` is looser than application (syntax.md).
- **Cost:** a printer change (`Not P` as `!P`) and a migration lane over
  std, aoc and examples. Small.
- **Leaves:** `List.Mem` still reads backwards from how people say it, and
  `Iff`/`Exists` stay prefix.

This is worth doing whatever else is chosen; it's part of the
recommendation (D1205).

### 5.2 (b) ASCII additions, Dafny- and Kotlin-style (recommended)

(a), plus `in`/`!in`, `<->` and `exists`:

```
S1  (areas: List Nat) -> largest areas in areas || (areas = Nil && largest areas = 0)
S2  (more: (e: (Nat, Nat)) -> e in xs -> e in ys)
S3  (ys: List Nat) -> x !in ys -> List.occurrences (z => q z && (z == x)) ys = 0
S4  OneCircuit n (firstConnections (Succ k) points) && !OneCircuit n (firstConnections k points)
S5  (two: 2 <= points.length): exists (k: Nat) => LastNeeded points k
S6  (ne: h1 != h2)
S7  (m: v in values || v in List.map Succ values): v in keyLines values
S8  (key, value) in Map.toList m <-> Map.get key m = Some value
S9  exists (n: Nat) => n * n = 49
S10 Nat.LexLess a1 a2 b1 b2 -> !(a1 < b1) -> b1 < k -> a1 < k
```

**What each one means.**

- `x in c` is a proposition: `List.Mem x c` on a list, and the
  corresponding proposition for `Set` and the keys of a `Map` (for a set,
  `Set.contains x c = True`, so that deciding it is the fast `Bool`
  lookup). Which types it works on comes from an interface, the way `<`
  comes from `Ord`; the exact interface is an implementation detail.
  `x !in c` is `Not (x in c)`, as `a != b` is `Not (a = b)`.
- **Where a `Bool` is expected it's decided**, by the rule that already
  turns `a <= b` into a `Bool` (syntax.md, "Anywhere a `Bool` is
  expected"). So `if x in seen then …`, `xs.filter (x => x !in seen)` and
  `test "…" := 3 in [1, 2, 3]` work, given a decision for list membership
  (from the element type's `DecEq`) and for sets (from `Set.contains`).
  One spelling for both the proposition and the check, as `<=` already
  has.
- `p <-> q` is `Iff p q`.
- `exists (x: T) => P` is `Exists T ((x: T) => P)`: the word `exists`, then
  exactly the lambda that `Exists` takes today. The type may be left out
  where it can be inferred (`exists k => LastNeeded points k`), as for any
  lambda. Several names (`exists (a b: Nat) => …`) nest.

**Precedence.** `in` and `!in` sit with `=`, `<` and the other comparisons
(non-associative), so `x in xs && y in ys` needs no brackets. Lean puts
`∈` and `∉` at level 50, the level of `=` and `≤`
(`notation:50 a:50 " ∈ " b:50 => Membership.mem b a`;
[Init/Notation.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Notation.lean)). `<->` goes between `->` and `||`,
non-associative, as in Rocq (`->` level 99, `<->` 95, `\/` 85, `/\` 80;
[Rocq library notations](https://rocq-prover.org/doc/V9.0.0/refman/language/coq-library.html)).
So `p && q <-> r` is `(p && q) <-> r` and `p -> q <-> r` is
`p -> (q <-> r)`. `exists … => body` takes everything to its right, as a
lambda does.

**Parsing conflicts, one by one.**

- **`in` and `rewrite`.** A bare `in` at bracket depth 0 ends a `rewrite`
  rule today, and must keep doing so. Inside a rewrite *rule* (a proof
  term), membership needs brackets: `rewrite memFoo (x in xs) in body`.
  Rewrite rules are proofs, which rarely take a proposition as an explicit
  argument, so this should be rare (speculative; no case in the repo
  today, since there is no `in` operator yet). After the rule's `in`, the
  body is an ordinary expression and `x in xs` works. The cost is that
  `in` would become a reserved word (`(in)` as a name goes), and the word
  has two jobs, which is a small strain on principle 7 ("one meaning per
  word", DESIGN.md §2), though that principle is about the words
  "checked", "total" and so on, not tokens.
- **`!in`.** A new two-character token, like `!=`. `!` followed by the word
  `in` can't mean anything today (`!in` would be `not` applied to a
  variable named `in`), so nothing changes meaning. Without it, `!x in xs`
  would be a trap: prefix `!` binds tighter than binary operators, so it
  means `(!x) in xs`. Kotlin has `!in` for the same reason
  ([Kotlin operators](https://kotlinlang.org/docs/operator-overloading.html):
  "`a !in b` → `!b.contains(a)`").
- **`in` for TypeScript readers.** In JavaScript, `"key" in obj` asks
  whether an object has a property (§4.11). Stitchwort has no such
  operation, so there's no clash in the language, only a possible first
  misreading; Python, Kotlin and Dafny readers see membership.
- **`<->`.** A new token. `<-` already exists (in `rewrite <- h`), so the
  lexer takes the longest match. `a<->b` (no spaces) means nothing today.
- **`exists`.** std has `Option.exists` and `Option.forall` (`Bool`
  functions, Scala's names; nothing in the repo calls them), while lists,
  maps, sets and vectors call the same thing `any` and `all`. Two ways out:
  make `exists` a word only at the start of an expression followed by a
  binder and `=>` (the parser already treats `in` and `at` this way), so
  `opt.exists p` keeps working; or rename them to `Option.any` and
  `Option.all`, matching the rest of std, and reserve `exists`.
  Recommended: rename, since it also tidies std (D1203); there are no users
  (memory: no backwards compatibility).
- **`->` stays function type and implication**, which is what it is in the
  core: no change.
- **`&&` on `Bool` versus on propositions**: unchanged. `in` gets the same
  two readings, by the same rule.
- **Operator sections (D1193).** If `(== 'S')` becomes a section, `(in seen)`
  is the section `x => x in seen`, handy for `filter`. It's free once both
  exist.
- **Rule E (value-first dot and pipe).** No conflict: `in` is an operator,
  not a dot call, and it keeps the predicate-first order of `List.Mem x xs`
  (D1199) while reading element-first. `xs.contains x` (receiver first,
  under rule E) and `x in xs` coexist, as `b.contains(a)` and `a in b` do in
  Kotlin.

**Printer.** Goals and messages print `List.Mem x xs` as `x in xs`,
`Not (List.Mem x xs)` as `x !in xs`, `Iff p q` as `p <-> q`, `Exists T f`
as `exists (x: T) => …`, and `Not p` as `!p`. The printer already does this
for `And`, `Or` and `Not (a = b)`, so this follows its pattern.

**Errors.** `x in 5` (no instance) says that `in` needs a list, set or map
on the right, naming the type it got. A `Bool`-context `x in xs` on a type
without `DecEq` is the usual `E-INSTANCE-NONE` at the `in`, as for `==`.

**Formatter, LSP, playground.** One space around `in`, `!in` and `<->`, as
for `&&`; `exists` like a lambda. The highlighters (VS Code grammar and the
playground's `paint()`) learn three tokens. Hover on `in` shows the
proposition it stands for. Nothing about input changes: it's all on the
keyboard.

**Docs and teaching.** syntax.md gains three table rows; the proofs chapter
(docs/guide/10-proofs.md) can introduce `x in xs` and `exists` where it
introduces lists and specifications, and it says what's written, so a
reader who knows Python, Kotlin or Dafny reads it without a lesson.

**Build cost** (estimate): one stage for `in`/`!in` (lexer, parser,
elaboration through an interface, decisions for lists and sets, printer,
formatter, highlighters, tests), a small stage for `<->` and `exists`
together, and a mechanical migration lane. No kernel change: each is sugar
for an existing term, so hashes are those of the long forms.

### 5.3 (c) Unicode canonical, ASCII as a fallback (Lean-style)

```
S1  (areas: List Nat) → largest areas ∈ areas ∨ (areas = Nil ∧ largest areas = 0)
S2  (more: ∀ e, e ∈ xs → e ∈ ys)
S3  ∀ ys, x ∉ ys → List.occurrences (z ↦ q z && (z == x)) ys = 0
S4  OneCircuit n (firstConnections (Succ k) points) ∧ ¬OneCircuit n (firstConnections k points)
S5  (two: 2 ≤ points.length): ∃ k, LastNeeded points k
S6  (ne: h1 ≠ h2)
S7  (m: v ∈ values ∨ v ∈ List.map Succ values): v ∈ keyLines values
S8  (key, value) ∈ Map.toList m ↔ Map.get key m = Some value
S9  ∃ n: Nat, n * n = 49
S10 Nat.LexLess a1 a2 b1 b2 → ¬(a1 < b1) → b1 < k → a1 < k
```

It's the shortest and the closest to a textbook. Against it:

- **Typing.** Every editor needs an input method: Lean's VS Code extension
  and Agda's Emacs mode turn `\in` into `∈` (§4.1, §4.2). Plain editors,
  `git commit` messages, the terminal REPL and the playground have none.
  The playground's `<textarea>` would need its own abbreviation handler.
- **Two spellings of everything.** With an ASCII fallback, the formatter
  must pick one, so code is rewritten under the author, and searches must
  try both (`grep '<='` misses `≤`).
- **Lookalikes.** `∶` versus `:`, `·` versus `.`, `∣` versus `|`; §4.12.
- **Fonts and accessibility**: §4.12.
- **It moves away from the mainstream surface Matt chose** (memory: "Scala/TS
  syntax style"), and from Scala, which removed its Unicode arrows (§4.11).
- **Cost:** the largest: lexer support for non-ASCII symbols, an input
  method in the playground and the VS Code extension, a formatter policy,
  and docs in two spellings.

### 5.4 (d) ASCII canonical, rendered as Unicode

Source as in (b); editors *display* `<=` as `≤`, `->` as `→`, `!=` as `≠`,
by font ligatures (one glyph drawn across the same two columns) or by
concealment (the editor hides the characters and shows another; Emacs's
`prettify-symbols-mode`, Vim's `conceal`; §4.12).

- **Ligatures keep the columns**, so they work in a `<textarea>` overlay
  and in any terminal with a ligature font. They're a font choice, made by
  each user in their own editor; nothing in the language is involved.
  Whether Recursive's `dlig` set includes `<=`, `!=` and `->` wasn't
  checked (its README says only that the code cut has "code ligatures").
- **Concealment changes widths**, which breaks the playground's
  textarea-over-highlight design (§2) and alignment in general, and it
  depends on each editor having such a feature (not checked for this note;
  §4.12). TLA+ notes that its Unicode conversion and ligatures don't mix,
  and that alignment-sensitive syntax makes conversion hard (§4.9);
  Stitchwort's layout is column-sensitive too.
- **What you see isn't what you type**: a newcomer reading `≤` on screen
  types `≤`, which must then either work (that's option (c)) or give a
  good error (D1208).
- **A word like `in` is unlikely to become `∈` by ligature** (speculative:
  fonts weren't surveyed for it), so the commonest gap isn't helped.

Recommendation: leave ligatures to users' fonts; don't build concealment.

### 5.5 (e) User-definable notation

Lean's `infix`/`notation`/`macro` and Agda's mixfix (§4.1, §4.2) let a
library add `∈` itself. Against it, for Stitchwort:

- **Every reader must know each library's notation** before they can parse
  its code; the mainstream languages Matt wants the surface to feel like
  don't do it (TypeScript has no operator definitions; §4.11).
- **Tools get harder**: the formatter, highlighter and parser need the
  declarations of every import before they can read a line, and the
  playground highlights without elaborating.
- **The need is small**: four symbols (`in`, `!in`, `<->`, `exists`) cover
  the gaps in §2. Interfaces already let a user's type have `+`, `<` and,
  under (b), `in`.

Not recommended. It can be revisited if a concrete need comes up.

## 6. Points that cut across the options

### 6.1 Quantifiers

"For all" is `(x: T) -> P`. Lean writes `∀ x : T, P` and accepts
`forall` (§4.1); Rocq `forall x : T, P` (§4.4); Dafny `forall x :: P`
(§4.7). A `forall` keyword would
duplicate 1,700 binders' worth of an existing form, and the dependent
function type *is* the meaning, which the proofs chapter already teaches
(`theorem plusZero: (n: Nat) -> n + 0 = n`). Not recommended.

A **bounded** form, `∀ x ∈ xs, P x` in Lean, is tempting given S2.
`(e in xs) -> e in ys` can't be it: today that's a function type whose
argument is a proof of `e in xs` for an `e` already in scope, and both
readings would be valid. Something like `(e: T) -> e in xs -> e in ys` is
already short under (b), and `List.All (e => e in ys) xs` exists. Not now
(D1206).

### 6.2 Sets

`∪`, `∩` and `⊆` have little use in proofs today: `Set.union` and friends
are functions, and subset statements are written out (S2) or as
`Set.isSubset a b = True`. Dafny reuses `+`, `*` and `<=` on sets (§4.7);
Stitchwort could give `Set` instances of `Add` and `Ord`, but `<=` on sets
is a partial order, which `Ord`'s laws don't allow. Named functions with
dot notation (`a.union b`) are clear. No operators (D1207).

### 6.3 Plain editors, the terminal and the playground

Matt's constraint is that tooling works in plain editors, the playground and
the terminal. ASCII meets it for free. Unicode needs an input method in
each, and the playground's textarea has none: adding one means a
key handler that rewrites `\in` + space as `∈`, kept in step with the VS
Code extension's table. It's doable, but it's tooling built only to type
what ASCII already types.

### 6.4 Unicode in source: an error that helps

Someone pasting `x ∈ xs` from Lean or a paper gets "unexpected character"
today. A table of the common symbols would let the error say what to write:
`∈` → `in`, `∉` → `!in`, `∀` → `(x: T) ->`, `∃` → `exists`, `∧` → `&&`,
`∨` → `||`, `¬` → `!`, `→` → `->`, `↔` → `<->`, `≤` → `<=`, `≥` → `>=`,
`≠` → `!=`, `λ` → `x => …`. Small, and it makes D1200 friendly (D1208).

## 7. Interactions with other work

- **Rule E (SW-450).** Nothing here uses dot notation or changes argument
  order. `in` reads element-first and builds `List.Mem x xs` (predicate-first,
  D1199). Migration of statements should run after rule E lands, to avoid
  two lanes rewriting the same lines.
- **Operator sections (D1193).** Compatible; `(in seen)` becomes a section.
- **Counterexample search.** `x in xs` is `List.Mem`, which it already
  handles where decidable; no change.
- **Hashes.** Each form is sugar for an existing term, so hashes don't
  change (not that this is a goal; memory: hash stability).

## 8. What isn't settled here

- The interface behind `in` (one with an element type and a container type,
  or separate instances per type): an implementation detail for the lane.
- Whether `Map` membership is `key in m` (keys), as in Python and Kotlin
  maps, or isn't offered. Recommended: keys, as both do (D1201).

## 9. Decisions

**D1200. ASCII only in source.** Names and operators stay ASCII; no Unicode
forms, canonical or alternative. *Recommended: yes.* (Rejects (c).)

**D1201. `x in c` and `x !in c` for membership.** A proposition (`List.Mem`
on lists; the corresponding proposition for sets and map keys), decided
where a `Bool` is expected; at the precedence of `=` and `<`; `in` becomes
reserved, and inside a `rewrite` rule membership needs brackets.
*Recommended: yes.*

**D1202. `p <-> q` for `Iff p q`**, between `->` and `||`, non-associative
(Rocq's placement). *Recommended: yes.*

**D1203. `exists (x: T) => P` for `Exists T (x => P)`**, with `exists` a
keyword followed by a lambda; `Option.exists`/`Option.forall` are renamed
`Option.any`/`Option.all` to match `List.any`/`List.all`. No `forall`
keyword: "for all" stays `(x: T) -> P`. *Recommended: yes.*

**D1204. The printer shows the operators**: `x in xs`, `x !in xs`,
`p <-> q`, `exists (x: T) => …`, and `!p` for `Not p`.
*Recommended: yes.*

**D1205. House style: operators over names in statements** (`&&`, `||`,
`!`, `!=`, and the new ones), with a migration lane over std, aoc and
examples after rule E lands. `And`, `Or`, `Not`, `Iff`, `Exists` and
`List.Mem` stay as the names of the definitions. *Recommended: yes.*

**D1206. No bounded quantifier syntax** (`∀ x ∈ xs`) for now; write
`(x: T) -> x in xs -> P x` or `List.All`. *Recommended: yes (not now).*

**D1207. No set operators** (`∪ ∩ ⊆`), and **no user-definable notation**.
*Recommended: yes.*

**D1208. Unicode logic symbols in source get an error naming the ASCII**
(the table in §6.4). No rendering (concealment) in the playground or the
editor extension; ligatures are left to users' fonts. *Recommended: yes.*
