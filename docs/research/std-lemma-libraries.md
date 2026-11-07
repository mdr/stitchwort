# How other proof assistants organise their lemma libraries, and what std should take (SW-2180)

Research note, 7 Nov 2026 (Opus, read only: no builds or runs). Matt, 7 Nov: he wants "a really
rich standard library with a lot of proven facts about the functions". This note asks how the
four big libraries keep theirs rich *and* findable, and what Stitchwort's std should copy.

It builds on two earlier pieces and doesn't repeat them:

- the SW-2159 survey (`docs/reviews/SW-2159-aoc-lemmas-to-std.md`), which found about 75
  generic lemmas the AoC days wrote for themselves, and about 30 more that restate something
  std already had, under another name;
- the search proposal's survey of search tools (`docs/proposals/search.md` §2–3: Hoogle,
  Rocq's `Search`, Isabelle's `find_theorems` and Sledgehammer, Loogle, `exact?`/`apply?`/`rw?`,
  Agda). Section 3 below only adds what that survey didn't cover: how naming and library
  layout make search work, and how libraries check themselves for duplicates.

## Summary

**What a user gets.** A lemma written once, under a name people can guess, found the first time
someone needs it, and not written again. Today that fails in two ways the SW-2159 survey
measured: about 30 AoC lemmas restate std, and about 75 generic ones never made it to std at all.

**What the other libraries do that std doesn't.** Four things, in order of payoff:

1. **A duplicate check that runs by itself.** Isabelle checks every new lemma you state against
   the library and says "can be solved directly with `Nat.le_antisym`" before you write a proof
   (`solve_direct`, run automatically). Mathlib found **353 duplicate theorems** in itself in
   October 2025 with a type-matching tool, despite its heavy human review. Human review doesn't
   catch duplicates; a machine does. Stitchwort already has the parts: `search --at` checks
   which existing lemmas close a goal with the kernel, and can leave a given theorem out.
2. **A checklist of the lemmas each operation should have.** Lean's core `List` library opens
   with one: for each operation, its length, its `i`-th element, membership in the result,
   injectivity, and how it combines with every other operation. Lean's standard library team
   goes further and tracks a table per container (each way to build a map, against each way to
   query one), with every cell a lemma or a gap. Std has no such list, so a gap is found only
   when a proof falls into it.
3. **A written naming guide.** Every library has one, and std's names already follow most of
   Lean's rules in camelCase (`lengthAppend`, `leOfEq`, `memFilterMapIntro`). But nothing says
   so, so the outliers grow: `Nat.lessTrans` next to `Nat.ltOfNotLe`, `List.sortLength` where
   the rest of std says `lengthMap`. A guide is cheap, and it makes grep-by-name work.
4. **One way to state each fact.** Mathlib fixes one "normal form" per idea (`s.Nonempty`, never
   `s ≠ ∅`), so there is one lemma to find, not two. Several of the 30 restatements were the
   same fact in another spelling: `(n == n) = True` against std's `Nat.equal n n = True`.

**Recommendation.** Build the duplicate check first (it finds the problem wherever it is), then
write the naming guide and the per-type checklists together with SW-2179's naming plan, then
fix search for the shapes the duplicate check shows it misses. Six tickets, about 6 hours of
lane time, at the end.

**What doesn't fit.** A default `simp` set (Stitchwort's evaluator does most of that work, and
Q5 of `simp.md` recommends rules listed per proof); a lemma for every linear arithmetic
fact (`omega` proves those, and SW-2159 already decided one-word proofs earn no std name);
Mathlib's scale of process (maintainers, reviewer teams, Zulip).

## 1. Why the 30 restatements happened

I dated ten of SW-2159's table A rows with `git log`: when the AoC file was added, and when
std's equivalent arrived.

| AoC lemma | AoC file added | Std lemma | Std lemma added |
| --- | --- | --- | --- |
| `natEqSelf` | 27 Oct | `Nat.equalRefl` | 16 Oct |
| `nearSelf` | 27 Oct | `Nat.absDiffSelf` | 20 Oct |
| `leBoth` | 28 Oct | `Nat.leAntisym` | 17 Oct |
| `boolOfIff` | 28 Oct | `Bool.eqOf` | 20 Oct |
| `maxAtLeast` | 28 Oct | `Nat.leMaxLeft` / `Right` | 18 Oct |
| `sizeWithin` | 28 Oct | `Set.sizeSubset` | 28 Oct |
| `containsInsertEither` | 28 Oct | `Set.containsInsertElim` | 28 Oct |
| `findMapAny` | 28 Oct | `List.memOfFindMap` | 5 Nov |
| `foldMinLe` | 31 Oct | `List.foldMinLeStart` | 28 Oct |
| `memSort` | 4 Nov | `List.memPerm` + `List.sortPerm` | 23 Oct |

`stitchwort search` arrived on 31 Oct (the proving guide's section on it,
`docs/proving-guide.md:481`). File dates are an upper bound on when each lemma was written, so
read the first column as "no later than". Three causes show:

- **No tool yet (7 of 10).** Most copies predate `search`. Since 31 Oct, the guide tells lanes to
  search before writing a lemma, and `search --at` finds the closing lemma for 27 of 29 AoC 2021
  goals (`docs/proving-guide.md:527-537`). This cause is mostly fixed already.
- **Std caught up later (3 of 10).** `Set.sizeSubset` and `Set.containsInsertElim` arrived the
  same day as the AoC copies, and `List.memOfFindMap` a week after. No search at writing time
  could have found them. Only a check that runs *after* std grows, over the projects' lemmas,
  catches these: a duplicate check (§4.3).
- **Same fact, different packaging (several, overlapping the above).** Even with search, some
  copies differ from std in form, not content:
  - `natEqSelf` (`aoc/src/Aoc/Year2025/Day07/Proofs/Part1.sw:33`) is `(n == n) = True`;
    `Nat.equalRefl` (`crates/elab/src/std/core/Equality.sw:56`) is `Nat.equal n n = True`. Same
    fact, different head constant.
  - `boolOfIff` (`aoc/src/Aoc/Year2024/Day06/Proofs/Part2.sw:132`) takes one `↔`; `Bool.eqOf`
    (`crates/elab/src/std/Bool/Bool.sw:63`) takes two implications.
  - `maxAtLeast` (`aoc/src/Aoc/Year2024/Day24/Proofs/Lemmas.sw:66`) is the `∧` of two std
    lemmas.
  - `memSort` is two std lemmas chained; std has no one-step `List.memSort`.

  Whether today's `search` sees through each of these I inferred from the search proposal's
  design (matching up to folded types, `matchHyps` over premises), not by running it:
  **medium confidence**. The first ticket measures it.

So the lesson for std is not "search harder". It is: check for duplicates mechanically and
repeatedly, state each fact one way, and fill in the obvious corollaries (`memSort`,
`lengthFilterMap`) before someone needs them.

## 2. The four libraries

### 2.1 Lean 4: core, Batteries and Mathlib

Lean now has three layers. Lean's own standard library (in the `lean4` repo, `src/Init` and
`src/Std`) holds `List`, `Nat`, `Int`, `HashMap` and their lemmas. Much of this was moved up
from Batteries (formerly Std4) in 2024. Batteries holds programming-oriented extras. Mathlib
holds mathematics.

**Naming.** Lean's standard library has a naming algorithm, written down
(`doc/std/naming.md` in `lean4`). Read the statement as a tree: the conclusion first, then each
hypothesis after `_of_`; a function's name, then its arguments; an infix operator's name between
its operands. Then shorten: drop the namespace, drop hypotheses that are obvious. So
`m.contains a = false → m[a]? = none` is `getElem?_eq_none_of_contains_eq_false`. Mathlib's
guide (leanprover-community.github.io/contribute/naming.html) uses the same scheme, plus a
dictionary: `le`, `lt`, `ne`, `mem`, `add`, `mul`, `zero`, `pos` (not `zero_lt`), `nonneg`.
Fixed words carry fixed meanings: `comm`, `assoc`, `refl` (explicit argument) and `rfl`
(implicit), `irrefl`, `symm`, `trans`, `antisymm`, `congr`, `inj` (`f a = f b ↔ a = b`),
`cancel`, `ext`, `mono`, `self`, `left`/`right` with rules for which is which, and `iff`
kept in the name even when it's unique without it, "so users don't try to `apply` it". Two rules
matter for us:

- "The more common you expect (or want) a theorem to be, the shorter you should try to make the
  name" (naming.md, with the `HashMap` example: users are steered to `∈`, so the `∈` lemma gets
  the short name, the `contains = false` one the long name).
- No primes to tell variants apart: "it is impossible to tell the difference without looking at
  the type signature". Use descriptive pairs instead.

**Layout.** One file per operation family. `src/Init/Data/List/` has `Basic.lean` (definitions),
`Lemmas.lean`, and separate files for `Count`, `Erase`, `Find`, `MinMax`, `Pairwise`, `Perm`,
`Sublist`, `TakeDrop`, `Zip`, `Sort`, and more. Lemmas live with their topic, not next to each
definition. Mathlib adds the rule that a lemma goes in the lowest file where it can be stated,
with a command, `#find_home`, that suggests the file (Mathlib's review guide,
mathlib.org/contribute/pr-review.html).

**Finding.** Covered in `search.md` §2 (`exact?`, `apply?`, `rw?`, Loogle, LeanSearch). Two
points beyond it: the name algorithm makes guessing work (type `List.length_` and complete), and
`simp` means most users never name a lemma at all. Mathlib's simp page
(leanprover-community.github.io/extras/simp.html) fixes "a simp normal form" per idea, so there
is one lemma to find, and a linter (simpNF) checks that every `@[simp]` lemma's left side is in
that form.

**Duplicates and review.** Mathlib's review guide asks reviewers whether the result exists
already (and suggests `exact?`), whether it's general enough, whether it's in the right file,
and whether the new definition comes with "a sensible API". That didn't prevent duplicates. In
October 2025 Jovan Gerbscheid wrote `Mathlib.Tactic.DuplicateDecls`, which compares theorem
statements after putting hypotheses in a canonical order and erasing binder kinds (implicit or
explicit) and universe levels, and skips declared aliases. Its first run reported 1,441
duplicate theorems across Lean, Batteries and Mathlib, and **353 in Mathlib alone**; a series
of PRs (Ruben Van de Velde, Kim Morrison and others) removed them, choosing by hand which name
to keep (Zulip thread "duplicate declarations", 24–31 Oct 2025). Renames go through
`@[deprecated]` aliases.

**Must-have API.** The header of `src/Init/Data/List/Lemmas.lean` is the clearest statement in
any library of what an operation `f` should come with:

- a lemma reducing a convenience function to basic ones;
- special cases of the arguments (`map_id`);
- the length of the result;
- the `i`-th element of the result;
- what `x ∈ L` or `x ∉ L` gives for `f L`, and what characterises `x ∈ f L`;
- injectivity, or congruence (`p L M → f L = f M`);
- what characterises the result (`f L = M ↔ …`), with special cases such as
  `L ++ M = [] ↔ L = [] ∧ M = []`, and negative ones (`cons_ne_nil`);
- how `f` interacts with every operation already described;
- `∀ i ∈ f L, P i`.

"Of course for any individual operation, not all of these will be relevant ... so some judgement
is required." The file also states simp-direction rules: conversions move inward, element-wise
operations move inside structural ones (`map f (L ++ M) → map f L ++ map f M`).

For maps and sets, Lean's standard library team keeps tables in a QA tool, Grove
(`doc/std/grove/` in `lean4`). For 18 associative containers (`HashMap`, `TreeMap`, `HashSet`,
their raw and extensional variants), it lists the creation operations, the query operations and
the modification operations, and a table "create then query" whose rows are creation operations,
whose columns are queries, and whose cells are the lemmas (`AssociativeContainers.lean`). An
assertion checks that every operation in the namespace appears in some table.

### 2.2 Agda's standard library

**Naming** (`doc/style-guide.md`, "Naming conventions"). Names are written in the notation
itself: `+-comm`, `*-assoc`, `length-map`, `map-++`, `m≤n+m`. A property is "prefixed by the
relevant operator/relation and separated from its name by a hyphen". Preconditions go first with
`⇒` (`asym⇒antisym`), and only when "important (mostly a judgment call)". Variables in the name
occur in alphabetical order. For a relation `P` and a function `f`, `f⁺` introduces (`… → P (f
…)`) and `f⁻` eliminates (`P (f …) → …`): `∈-map⁺`, `∈-map⁻`. A `-local` suffix marks the
version that needs the fact only on the elements present (`map-id-local`). Since the names are
the formulas, a name is close to unambiguous, at the cost of Unicode input.

**Layout.** Definitions in `Data.List.Base`, lemmas in `Data.List.Properties`, one section per
operation in definition order (the file has `-- map`, `-- zipWith`, `-- foldr`, `-- filter`,
`-- take`, … headers; 1,745 lines). Lemmas about a predicate go with the predicate:
`Data.List.Membership.Propositional.Properties`, `Data.List.Relation.Unary.All.Properties`.
Algebraic facts are also packaged as structures: `Data.Nat.Properties` exports
`+-*-isCommutativeSemiring` and `≤-isTotalOrder`, so a generic lemma about any commutative
semiring applies to `ℕ` at once.

**Finding.** Weak tooling (Emacs "search about", names and constants only; `search.md` card
S13). The library makes up for it with predictable names and the per-operation sections: to find
`length (map f xs)`, open `Properties`, go to `-- map`, read.

**Duplicates and review.** Review by maintainers on GitHub; the file layout makes a duplicate
visible because its twin would be in the same section. Every rename keeps the old name in a
"DEPRECATED NAMES" block at the end of the file, per version, with a `WARNING_ON_USAGE` pragma.

**Must-have API.** Implicit in the sections. For `filter` it is `length-filter`, `filter-all`,
`filter-notAll`, `filter-some`, `filter-none`, `filter-complete`, `filter-accept`,
`filter-reject`, `filter-idem`, `filter-++`, `filter-map`, `filter-≐` (congruence), `filter-∩`,
`filter-swap` (`src/Data/List/Properties.agda`). For `map`: `map-id`, `map-id-local`, `map-++`,
`map-cong`, `map-cong-local`, `length-map`, `map-∘`, `map-injective`.

### 2.3 Rocq (Coq) stdlib and its successors

The standard library moved out of the Rocq repository into its own (`rocq-prover/stdlib`), and
is now one library among several: MathComp (ssreflect) and stdpp (Iris) are the usual
alternatives.

**Naming.** The old stdlib's names were never fully systematic: `app_assoc`, `in_app_iff`,
`map_length`, and two generations of arithmetic names (`plus_comm` in `Arith`, `Nat.add_comm`
from `Numbers`). The cleanup is still going: Coq PR 14736 (merged 28 Nov 2021) deprecated
`Arith.Plus`, `Arith.Minus`, `Arith.Mult`, `Arith.Le`, `Arith.Lt`, `Arith.Min`, `Arith.Max` and
others as "(mostly) obsolete", pointing users to the `Nat.` lemmas; stdpp's maintainers found
some of the suggested replacements "isn't the same lemma" (stdpp MR 346). That is the cost of
two naming schemes living side by side for years.

MathComp went the other way, to very short names built from fixed suffixes (`ssrnat.v`'s
header): `addnC` (add, nat, commutative), `mulnA` (associative), `addnK` (cancel), `mulnDl`
(distributes over addition, on the left), `addSn` (successor), `leq_eqVlt` (`V` for "or"). Terse,
but once learnt, a name is a formula.

**Layout.** `theories/Lists/List.v` mixes definitions and lemmas, in `Section`s per topic.
Arithmetic is generic: `Numbers/` states each law once over abstract axioms (module functors)
and instantiates it for `nat`, `N` and `Z`, so `Nat.add_comm`, `N.add_comm` and `Z.add_comm` are
one proof. (From the directory layout and long familiarity; **I didn't re-read the functor files
for this note**.)

**Finding.** `Search` with patterns, `SearchPattern`, `SearchRewrite` (`search.md` card S3).
MathComp's names were designed to be searched by `Search _ (_ + _) "C"` (a pattern plus a name
fragment).

**Duplicates and review.** Maintainer review on GitHub (`CONTRIBUTING.md`); no automatic
duplicate check that I found. The `Arith`/`Numbers` story is the clearest example of what
happens without one.

**One point MathComp makes that matters here.** MathComp states order and equality facts with
*Boolean* operators (`m <= n` is a `bool`, `==` is decidable equality), and moves between the
`bool` and `Prop` forms with "reflection" lemmas (`eqP`, `leP`). Stitchwort is in the same world:
`a ≤ b` is a `Bool` that must be `True` (the `Nat.leAntisym` proof at
`crates/elab/src/std/Nat/Arith.sw:17` refutes `h2` with `Bool.falseNotTrue`). MathComp's lesson
is to pick one primary form for each fact and give the bridges once, not to state each lemma
twice.

### 2.4 Isabelle/HOL

**Naming.** By convention, not a written guide: snake case after the conclusion's head
(`length_append`, `map_append`, `set_append`, `distinct_append`), with single-letter suffixes
for the rule's use: `I` for introduction (`conjI`, `subsetI`), `E` for elimination (`conjE`),
`D` for destruction (`subsetD`), `_iff` for equivalences, `_conv` for rewriting one form into
another (`in_set_conv_nth`), `_cong` for congruence. In `src/HOL/List.thy` I counted 1,264
lemmas: 54 end in `_iff`, 44 in `I`, 43 in `_conv`, 24 in `D`, 13 in `_cong`.

**Layout.** One theory per type (`List.thy`, 9,109 lines), definitions first, then a
`subsubsection` per constant in definition order: `length`, `@` (append), `map`, `rev`, `set`,
`concat`, `filter`, `nth`, `take` and `drop`, `takeWhile`, `zip`, `fold`, `upt`, `distinct`,
`count_list`, `replicate`, `sorted`, and so on. HOL-Library is a second tier for material that
isn't core; the Archive of Formal Proofs (AFP) is the third, and its submission guidelines ask
authors to "identify parts of your submission as potentially suitable for inclusion in the
Isabelle distribution" (isa-afp.org/submission). That is our AoC-to-std path, made a step of
submission.

**Finding.** `find_theorems` with patterns and `intro`/`elim`/`dest`/`solves`/`simp:` filters,
and Sledgehammer (`search.md` cards S4–S6). The simp set is the main API: most list facts are
`[simp]`, so `simp` uses them without anyone naming them.

**Duplicates and review.** `solve_direct` (`src/Tools/solve_direct.ML`, Timothy Bourke and
Gerwin Klein): "Check whether a newly stated theorem can be solved directly by an existing
theorem. Duplicate lemmas can be detected in this way." It runs `find_theorems` with the
`solves` criterion on the goal just stated, and reports up to five lemmas ("the current goal can
be solved directly with …"). It runs automatically in Isabelle/jEdit (`auto_solve_direct`), so
the duplicate is pointed out before the proof is written. AFP entries are refereed, and checked
by a linter.

**Must-have API.** The per-constant subsections, plus the `set_X`, `length_X`, `X_append`,
`X_map`, `nth_X`, `distinct_X` families repeated across operations.

## 3. Side by side

| | Lean (core, Mathlib) | Agda stdlib | Rocq stdlib / MathComp | Isabelle/HOL | Stitchwort std today |
| --- | --- | --- | --- | --- | --- |
| Naming guide | written, with an algorithm and a dictionary | written | none for stdlib; MathComp's suffix tables | convention only | none written; practice mostly matches Lean's |
| Name shape | `length_append`, `le_of_eq` | `length-++`, `≤⇒≢` | `app_length`, `addnC` | `length_append`, `conjI` | `lengthAppend`, `leOfEq` |
| Intro / elim | namespaces, `mem_map` as `↔` | `⁺` / `⁻` | `_iff`, `/P` views | `I` / `E` / `D` | `Intro` / `Elim`, 18 and 20 names |
| Layout | file per operation family | `Base` + `Properties`, section per op | `List.v` sections; generic `Numbers` | theory per type, section per op | `Toolkit.sw` defs, `Lemmas.sw` lemmas, in the order they were needed |
| One form per fact | simp normal form, simpNF linter | by convention | bool-first, reflection lemmas | simp set | not stated |
| Duplicate check | `DuplicateDecls` (2025), by hand | review | review | `solve_direct`, automatic | none (SW-2159 by hand) |
| API checklist | `List/Lemmas.lean` header; Grove tables | implicit in sections | implicit | implicit in sections | none |
| Renames | `@[deprecated]` alias | deprecated block per version | deprecation phase | `legacy` / removal | no aliases (SW-2006) |

## 4. What std should adopt

Each part: the problem, the change, how we'd know it works.

### 4.1 A naming guide for lemmas

**The problem.** A lane that needs "the length of a sorted list" greps
`^theorem List\.length` (the proving guide's own advice, `docs/proving-guide.md:550`) and finds
nothing, because std calls it `List.sortLength` (`crates/elab/src/std/List/SortLemmas.sw:1304`),
while 92 other `List` lemmas put the query first (`List.lengthMap`,
`crates/elab/src/std/List/Lemmas.sw:180`). Only 2 put the operation first (`sortLength`,
`permLength`). The same lane looking for transitivity of `<` finds `Nat.lessTrans`
(`crates/elab/src/std/core/Division.sw:63`) and `Nat.lessIrrefl` (`Nat/Arith.sw:35`), but for
other `<` facts it needs `lt`: `Nat.ltOfNotLe` (`Nat/Arith.sw:93`), `Nat.modLt` beside
`Nat.modLess` (`Nat/Arith.sw:173,219`; the same fact, one with an `auto` premise). Across std,
55 names spell `<` as `less` and 53 as `lt`.

**The change.** Write down the rules std already mostly follows, as a section of the proving
guide (or its own page linked from it), and fix the outliers in SW-2179/SW-2006's rename sweep:

- **The algorithm:** Lean's (`doc/std/naming.md`): the conclusion first, read outside in (the
  head function, then its arguments), then `Of` and each hypothesis that matters, in order;
  camelCase; the namespace is the type the conclusion is about. Shorten by dropping what's
  obvious; the more common the lemma, the shorter the name.
- **The dictionary,** one word per symbol: `le` and `lt` (not `less`, `atMost`), `ne`, `eq`
  for `=` and `equal` only for the function `Nat.equal`, `mem` for `List.Mem` and `contains`
  for the `Bool` function, `pos` for `0 < n`, `zero`, `succ`, `nil`, `cons`, `append`, `snoc`.
  The `Bool`/`Prop` pairs that std already distinguishes (`leq` the function, `le` the
  relation) stay distinct.
- **The fixed words:** `Comm`, `Assoc`, `Refl`, `Irrefl`, `Symm`, `Trans`, `Antisymm`, `Cong`,
  `Injective` (`f a = f b → a = b`) and `Inj` (`↔`), `Cancel`, `Ext`, `Mono`, `Self`,
  `Left`/`Right` (Lean's rules for which is which), `Iff` always kept, `Intro`/`Elim` for "puts
  the function into a relation" and "takes it out" (Agda's `⁺`/`⁻`, Isabelle's `I`/`E`), and
  `Example` for worked examples (std has 129).
- **No primes, no numbered variants:** a variant gets a descriptive word (Lean's rule).

**What it should do.** A lane can guess a lemma's name from its statement often enough that
grep-by-name is a real search. Check: after the sweep, the outlier counts above are 0, and the
SW-2159 move lanes' new names need no renaming in review.

This is a lemma-name complement to SW-2179 (one name per *operation*), and should be written
after or alongside it, since lemma names are built from operation names.

### 4.2 One spelling per fact

**The problem.** `natEqSelf` and `Nat.equalRefl` are the same fact, `(n == n) = True` against
`Nat.equal n n = True` (§1). Whoever writes the next proof meets the goal in whichever spelling
their code used, and finds the lemma only if search sees through the difference.

**The change.** A rule in the naming guide: state lemmas in the spelling user code writes. That
means `==`, `≠`, `<`, `x ∈ xs`-style membership, and `xs.length` rather than the underlying
function (`Nat.equal`, `Nat.less`), the same rule Lean's naming doc applies with its `∈` versus
`contains` example. Where both forms are common, std states the fact in the user's form and
gives one bridge lemma (MathComp's reflection lemmas; std already has `Bool.eqOf`). The
duplicate check (§4.3) reports pairs that differ only in spelling.

**What it should do.** One lemma per fact. Check: the duplicate report on std (ticket T2) lists
no spelling pairs once they're merged.

Implementation calls (mine): this changes no kernel terms where the spellings are definitionally
equal, so it is a statement-style rule, like D2363's, not a language change.

### 4.3 A duplicate check

**The problem.** Ten days of AoC lanes produced about 30 copies of std lemmas (§1), and three of
the ten I dated were written before std had the lemma, so no search at the time could have found
them. Mathlib's experience is that review doesn't fix this either: 353 duplicates in a library
whose every line was reviewed.

**The change.** Two levels, both reusing what exists.

1. **Exact duplicates, cheap.** Compare every theorem's statement after normalising: hypotheses
   in a canonical order, binder kinds (implicit, explicit, `auto`) erased, binder names ignored
   (Mathlib's `DuplicateDecls` normalisation). Stitchwort content-hashes terms
   (`crates/core/src/hash.rs:702`), so the normalised statement's hash is a lookup key. It runs
   over std as a test, so std stays duplicate-free, and over a project against std as a command.
   It would find the `Nat.modLess`/`Nat.modLt` kind of pair (if the `auto` premise is erased)
   and table A rows that are word for word.
2. **Closed by one lemma, slower.** Isabelle's `solve_direct`: take each theorem's statement as
   a goal, and ask `search --at`'s closing step which existing lemmas prove it outright,
   leaving out the theorem itself and everything that uses it (`search_at.rs:1123`, `searchable`,
   already has `exclude`). This finds `leBoth` (closed by `Nat.leAntisym`) and, where the
   kernel accepts it, `natEqSelf` (closed by `Nat.equalRefl` if `==` at `Nat` reduces to
   `Nat.equal`). At about 2 s a goal with a warm cache (proving guide, `search --at`), the 3,018
   AoC theorems take about 100 minutes, so this is a weekly or on-demand report, run per
   namespace in a lane, not part of every check.

Neither level deletes anything. Like Mathlib's tool, it reports; a person picks which name to
keep (Jovan Gerbscheid's point in the Zulip thread).

**What it should do.** Check: level 2 run over the AoC namespaces finds at least the table A rows
of SW-2159 that D0 hasn't yet removed (or, run on the commit before D0, most of the 30). Level 1
run over std reports a short list, each a real duplicate or a deliberate variant to document.

### 4.4 An expected-lemma checklist for each std type

**The problem.** The SW-2159 survey found `List.lengthFilterMap`, `List.countFilterMap` and
`List.memSort` missing; each is an obvious entry in Lean's per-operation list (length of the
result, membership in the result, how it combines with other operations). A name-based count
over std (a lower bound, since some lemmas are named otherwise) shows the shape of the gaps:

| query \ operation | `++` | `map` | `filter` | `filterMap` | `reverse` | `take` | `drop` | `concat` | `flatMap` | `zip` | `range` | `replicate` | `sort` |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `length` | 1 | 3 | 3 | – | 2 | 2 | 3 | 1 | 2 | 9 | 2 | 1 | (1, as `sortLength`) |
| `mem` | 5 | 7 | 6 | 4 | 2 | 1 | 1 | 1 | 5 | 1 | 7 | – | – |
| `sum` | 1 | – | 2 | 1 | 1 | 1 | 1 | – | – | – | 12 | – | – |
| `count` | 1 | 1 | 1 | – | – | – | – | – | 1 | – | 2 | – | – |
| `get` | 3 | 3 | – | – | – | 2 | 1 | – | – | 6 | – | – | – |
| `distinct` | 7 | 8 | 1 | – | – | – | – | – | 1 | – | 2 | – | – |

(Counted by name prefix, `List.<query><Operation>`, over the 2,986 std theorems. A dash means no
lemma *named* that way; a few may exist under other names.)

For `Map` and `Set`, the same count for Grove's "create then query" table finds `Map.get` lemmas
for `empty`, `insert`, `remove`, `fromList`, `union`, `filter`, `map`, `alter`, `adjust`, but
`Map.contains` lemmas only for `insert` and `filter`, and no `Map.size` lemma for `empty`. For
`Set`, I found no lemma named `Set.containsEmpty` or `Set.containsSingleton` (these may hold by
`rfl` and need no lemma; **unchecked**).

**The change.** A short checklist per std type, written down (in each std namespace's module doc,
or one page), adapted from Lean's list and Grove's tables:

- **Every `List` operation `f`:** the length of `f xs`; `x ∈ f xs` as an `Iff` (or `Intro` and
  `Elim`); `get`/`getOr` of `f xs`; `f` of `[]`, `[x, ..xs]` and `xs ++ ys`; `f` after `map`
  and `map` after `f`; the congruence lemma (`FCong`, needed by `rewrite` and `decreasing`); and
  `sum`, `count`, `all`, `any` and `Distinct` of `f xs` where they make sense.
- **`Map` and `Set`:** a table of builders (`empty`, `singleton`, `insert`, `remove`, `fromList`,
  `union`, `filter`, `map`, `intersect`, `difference`) against queries (`get`, `contains`,
  `size`, `toList`, `isEmpty`), each cell a lemma or marked "by `rfl`" or "not meaningful";
  plus `ext` (exists: `Map.ext`, `Set.ext`), and `toList` sorted with distinct keys.
- **`Nat` and `Int`:** the ring and order laws that *rewrite* or are *passed as functions*
  (comm, assoc, distrib, cancel, `leRefl`, `leTrans`, `leAntisym`, `ltIrrefl`), the `div`/`mod`
  family (`divModEq`, `modLt`, `modMod`, `modAddMul`, …), `min`/`max`, `pow`, divisibility and
  `gcd`, digits and bits, and for `Int` the casts to and from `Nat` (`ofNat`, `toNat`,
  `natAbs`). Not every linear fact: those are `omega`'s (§5).

Then a script that prints the table for a type from the *statements* (the head constants on
each side of the conclusion), not the names, so it works even where names are irregular: Grove's
idea, as a report rather than a web tool.

**What it should do.** A gap is visible before a proof falls into it. Check: the report lists
`lengthFilterMap`, `countFilterMap` and `memSort` as gaps today, and as filled after SW-2159's L1
and L2 lanes.

### 4.5 Search improvements

**The problem.** §1's packaging cases: a goal that is an `∧` of two std lemmas
(`maxAtLeast`), a lemma whose premise is an `↔` where std takes two arrows (`boolOfIff`), and a
fact spelled with `==` where std spells it `Nat.equal`.

**The change, once measured.** I didn't run `search`, so I don't know which of these it already
handles. Ticket T1 runs the ~30 table A statements through `stitchwort search` and `search --at`
and records each miss with its reason. Likely fixes, each small, in the order the misses rank
them:

- split an `∧` goal and search each half (`exact Both (Nat.leMaxLeft m n) (Nat.leMaxRight m n)`);
- read an `↔` premise as its two implications in `matchHyps`, and an `↔` conclusion as either
  direction;
- fold `==` at a type with `DecEq` to the type's own equality function before matching, so both
  spellings meet.

**What it should do.** Check: T1's table, rerun after the fixes, shows the misses closed.

### 4.6 Layout: sections per operation

**The problem.** `List/Lemmas.sw` holds 437 theorems in 3,070 lines in roughly the order they
were needed (it starts `lengthAppend`, `lengthOntoEq`, `appendTakeDrop`, `scanLeftNil`, …). To
see what std knows about `filterMap`, you grep or run `stitchwort doc List.filterMap`, which lists
its theorems.

**The change.** Order each big lemma file by operation, with a heading comment per operation,
as Agda's `Properties` and Isabelle's `List.thy` do. Not split into more files: std's unit of
loading is a file (`docs/proposals/std-library.md` §4.2), and `stitchwort doc` already gives the
per-function view Lean gets from many files. Moving declarations changes no hashes
(`docs/core.md:426`).

**What it should do.** A reader can check an operation's coverage by reading one section, and a
duplicate in the same section is visible in review. It is the least important item here, and it
waits until SW-2159's L1 and L2 lanes, which edit `List/Lemmas.sw`, have merged.

### 4.7 The review rule

**The change.** Std lane briefs say: search for each new lemma's statement first (already in
the proving guide), name it by the guide, tick the checklist cells it fills, and run the duplicate
check (§4.3) on the namespace touched. AoC lane briefs keep D2831's rule (move generic lemmas to
std or `Aoc.Common`), with the AFP-style step that a lane's report lists its std candidates (the
proving guide already asks for this, `docs/proving-guide.md:563-567`).

## 5. What doesn't fit, and why

- **A default `simp` set.** Lean's and Isabelle's libraries are shaped around one: most list
  facts are tagged and used without being named. Stitchwort's evaluator already computes what
  Lean's basic simp lemmas do (`docs/proposals/simp.md`, "The short answer"), and `simp.md` Q5
  recommends rules listed per proof, not a default set, so a proof's meaning doesn't depend on
  what an import tags. Keep the *normal form* idea (§4.2); leave the attribute.
- **A lemma for every linear fact.** Mathlib's `Nat` has hundreds of order lemmas
  (`add_le_add`, `le_add_right`, …) because `simp` and `rw` need them by name. Std has `omega`,
  and SW-2159 decided one-word proofs get no std name. The checklist (§4.4) keeps only lemmas
  that rewrite, are passed as functions, or that `omega` can't prove (`div`, `mod`, `*` by a
  variable).
- **Generic algebra through structures** (Agda's `isCommutativeSemiring`, Rocq's `Numbers`
  functors). It would state `Nat` and `Int` laws once, but needs the interface work in
  `docs/proposals/interfaces.md`. Today `Nat` and `Int` share 25 lemma names (`addComm`,
  `mulAssoc`, …) by hand; the naming guide keeps them parallel until then.
- **Agda's Unicode names and MathComp's suffix codes.** Both make names into formulas, but
  Stitchwort names are identifiers people type, in camelCase, and the codes take learning.
  Lean's spelled-out words fit better.
- **Deprecated aliases.** Every library keeps old names for a while after a rename. SW-2006 says
  no aliases, and Stitchwort's renames are done across the whole tree in one lane, with no
  outside users yet, so the reason for aliases doesn't apply.
- **Mathlib's process** (maintainer and reviewer teams, `maintainer merge`). The orchestrator's
  review plus the machine checks above is our equivalent.

## 6. Calls I made

- The naming guide follows Lean's algorithm and words, in camelCase, because std's names already
  do (92 of 94 query-first `List` names) and Lean's is the only written algorithm of the four.
- `lt` over `less` in the dictionary (recommended in D3160): it matches Lean and Mathlib,
  is shorter, and the count is even (53 against 55), so neither costs more to sweep.
- Layout: sections, not more files (§4.6).
- The duplicate check reports and never deletes; level 2 is on demand, not per check, because of
  its cost.
- The search fixes wait for a measurement, not for my reading of the design.

## 7. Decisions for Matt

- **D3160: Adopt a written naming guide for std lemmas (Lean's conclusion-first algorithm in
  camelCase, a fixed word list with `lt`/`le` rather than `less`, and "state facts in the
  spelling user code writes"), and rename std's outliers to it in SW-2179/SW-2006's sweep?**
  [rec: yes, because std already mostly follows it, so the guide is mostly description, and it
  turns grep-by-name into a search that works.]
- **D3161: Add a duplicate check: an exact-duplicate test that keeps std free of duplicates
  (merge tier), plus an on-demand `solve_direct`-style report that a project's theorems are
  closed by an existing lemma, run by std and AoC lanes on the namespaces they touch?**
  [rec: yes, because Mathlib's 353 duplicates show review alone doesn't catch them, and it would
  have caught the 30 AoC copies mechanically, including the ones written before std had the
  lemma.]

## 8. Tickets to file

In order. T1 and T2 can run side by side; T3 waits for SW-2179; T4 after T2; T5 after T1; T6
after SW-2159's L1 and L2.

| # | Ticket | Model | Est. | Targeted tests | Notes |
| --- | --- | --- | --- | --- | --- |
| T1 | Measure search on the SW-2159 restatements: for each table A row (on the commit before D0 removes them), run `stitchwort search` with its statement and `search --at` with its proof replaced by `?`; record hit, miss and why, in a table on the ticket | DeepSeek | 45 min | none (no code change) | well bounded; gives 4.5's fix list |
| T2 | Exact-duplicate check (§4.3 level 1): normalised statement hash over std as a test, and over a project against std as a command; report, don't delete | Sonnet | 75 min | the new test; `task test:lane AREA=search` | D3161; near kernel terms, so Sonnet; triage of what it finds is a separate small ticket |
| T3 | Write the lemma naming guide (§4.1) and the per-type checklists (§4.4) as proving-guide sections; list std's outliers for the rename sweep | Sonnet | 45 min | `task test:one -- guide` only if it adds checked examples | D3160; after SW-2179, absorbs SW-2177's naming half if SW-2179 hasn't; renames go to SW-2006 (DeepSeek) |
| T4 | `solve_direct` report (§4.3 level 2): `stitchwort search --duplicates NAMESPACE`, each theorem's statement as a goal, existing lemmas that close it outright, the theorem and its users excluded; run once on AoC and file the results | Sonnet | 90 min | the command's own tests in `crates/driver/tests`; one AoC namespace by hand | reuses `search_at.rs`; Opus if it needs changes to how goals are opened |
| T5 | Search fixes from T1's misses (§4.5): `∧` goals split, `↔` premises as two arrows, `==` folded at `DecEq` types, in the order T1 ranks them | Opus | 60–90 min | `task test:lane AREA=search` (or the search tests by name) | Opus: matching and the unifier are core (D2506) |
| T6 | Order `List/Lemmas.sw` and `SortLemmas.sw` by operation with section headings; no statement changes | DeepSeek | 45 min | `task snap:hashes` (should show no change), `task test:one -- hash_stability` | after SW-2159 L1 and L2; low priority |

Plus a statement-based coverage report for §4.4's tables (Grove's idea), worth filing in the
backlog after T3 shows whether the written checklist is enough: Sonnet, 60 min.

## Sources

Read for this note (fetched 7 Nov 2026):

- Lean standard library naming conventions: `doc/std/naming.md`, and `doc/std/vision.md`, in
  https://github.com/leanprover/lean4/tree/master/doc/std (read in full).
- Lean core `List` lemmas, header comment: https://github.com/leanprover/lean4/blob/master/src/Init/Data/List/Lemmas.lean
  (header read; directory `src/Init/Data/List/` listed).
- Grove tables for associative containers: https://github.com/leanprover/lean4/blob/master/doc/std/grove/GroveStdlib/Std/CoreTypesAndOperations/Containers/AssociativeContainers.lean
  (read in full); Grove itself: https://github.com/TwoFX/grove (README only).
- Mathlib naming conventions: https://leanprover-community.github.io/contribute/naming.html
- Mathlib PR review guide: https://mathlib.org/contribute/pr-review.html
- Mathlib simp normal form: https://leanprover-community.github.io/extras/simp.html
- Mathlib `DuplicateDecls`: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/DuplicateDecls.html
  and the Zulip thread https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/duplicate.20declarations.html
  (first 100,000 characters read).
- Batteries `Batteries/Data/List/` (directory listed): https://github.com/leanprover-community/batteries
- Agda standard library style guide: https://github.com/agda/agda-stdlib/blob/master/doc/style-guide.md
  (naming sections read in full); `src/Data/List/Properties.agda` (section headings and the `map`
  and `filter` sections read); `src/Data/List/` and `src/Data/Nat/` listed.
- Rocq stdlib: https://github.com/rocq-prover/stdlib (README, CONTRIBUTING, `theories/` listed);
  Coq PR 14736: https://github.com/coq/coq/pull/14736 ; stdpp MR 346:
  https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/346 (from a search summary, not read).
- MathComp `ssrnat` naming suffixes: https://math-comp.github.io/htmldoc_2_2_0/mathcomp.ssreflect.ssrnat.html
  (header read).
- Isabelle `src/HOL/List.thy` and `src/Tools/solve_direct.ML`, from the GitHub mirror
  https://github.com/isabelle-prover/mirror-isabelle (List.thy's subsections and lemma names
  counted; solve_direct.ML's first 60 lines read).
- AFP submission guidelines: https://www.isa-afp.org/submission/

In this repository: `docs/reviews/SW-2159-aoc-lemmas-to-std.md`, `docs/proposals/search.md`
§2–3, `docs/proving-guide.md` §5, `docs/proposals/simp.md`, `docs/proposals/std-library.md`, and
the std sources under `crates/elab/src/std/` (theorem names counted with `grep`; the counts
here are by name and are lower bounds where noted).
