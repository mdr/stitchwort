# SW-2213: do the user docs cover what landed on 6 and 7 November?

Read-only audit, 7 November 2026, against `main` at `73a5cc0dc`. Nothing was
built or run. "The rule" below is CLAUDE.md's: a user-visible language
feature updates `docs/guide/` (examples checked) and `docs/syntax.md`, and
gets a tour page (`web/guide/`) if a newcomer would enjoy it.

## Summary

The two `decreasing` stages are well documented: SW-2029 and SW-2030 each
updated chapter 7, its checked example `recursion.sw` and `syntax.md` in the
same commit. The stage 1 sentence about an `if` "in a `match` that isn't the
definition's own case split" is gone from every user doc. The gaps are
around them. The tour's `decreasing` page still writes `if h:`. The
proving guide's one-line summary does too. And `docs/core.md`'s account
of `f.unfold` predates both stages. Record eta is the larger gap. It
has been in the kernel since SW-1642 (merged this morning), and the field-of-call lanes
(SW-1998, SW-2095, SW-2096, SW-2126) built on it. Yet no user doc
mentions it, and `docs/core.md`, the kernel's own spec, still says
"Record eta (D1981), if it's added" and has no `Proj` in its term table.
SW-1859 already covers the guide side; the kernel spec has no ticket. The
std additions (SW-2138, SW-2169) need only a line or two in chapter 6. One
correction to SW-2138: the guide does have a Map and Set section (chapter 6,
"Map and Set", two checked snippets) and the tour has a page (14). What
neither has is maps of sets, `popMin`, `getOr`, or anything on proving
things about a `Map` or `Set`. The language server's recovery messages
(SW-2117, SW-2118) are accurate and consistent, but the VS Code README never
says what they mean or what to do.

**Top five recommendations**

1. Bring `docs/core.md` up to date with the kernel: `Proj` in the term table,
   record eta's two rules in "Conversion", the stale "if it's added"
   sentence, and `f.unfold`'s new shape (`f.%plain`, `f.%unfoldStep`) (F1, F2).
2. Rewrite tour page 30 to show what stages 1 and 2 give a newcomer: a guard
   without a name, and a `match` whose equation the call finds (F3).
3. Run SW-1859 (record eta in the guide, `syntax.md`, a tour page) soon. It is the
   largest user-visible feature with no docs.
4. Chapter 6's Map and Set section: `popMin`/`min`, `getOr`, and maps of sets
   (`insertIn`, `containsIn`, `removeIn`). Chapter 7's new example already
   uses `set.popMin` before anything introduces it (F5).
5. Give the std rename lanes (std-naming.md §5) the user-doc page list in §4
   below, so each brief names its pages and runs `the_guide_` tests.

**Findings by severity:** 0 high, 3 medium, 7 low.

## Findings

| # | Sev | Conf | Where | What | Size |
|---|-----|------|-------|------|------|
| F1 | medium | high | `docs/core.md:240`, `:28-48` | The kernel spec says record eta is hypothetical ("if it's added") and its term table has no `Proj`, though both are in the kernel (`crates/core/src/term.rs:213`) | M |
| F2 | medium | high | `docs/core.md:195` (item 6) | `f.unfold` is described as `f x = f.%step x (y => f y)`; since SW-2029 it is `f.%plain` where an `if` or `match` was made plain, with the old equation kept as `f.%unfoldStep` | S |
| F3 | medium | high | `web/guide/30-decreasing.sw:9` | The tour still writes `if h: next < n`, the only form stage 1 made unnecessary; it shows neither feature | S |
| F4 | low | high | `docs/proving-guide.md:286-287` | "from `auto` (a guard `if h: next < n` in scope)": the name is no longer needed; a `match`'s equation counts too | S |
| F5 | low | high | `docs/guide/07-recursion.md:135-147` | `set.popMin` and `Set.sizePopMin` are used before the guide introduces `popMin` (chapter 6 doesn't list it) | S |
| F6 | low | high | `docs/guide/06-namespaces-and-library.md:261-287` | No maps of sets (`Map.insertIn`, `containsIn`, `removeIn`), no `popMin`/`min`, no `getOr`/`alter`; the tour page uses `getOr` but the guide doesn't | S |
| F7 | low | high | `docs/syntax.md` | `W-MATCH-NOT-FOUND` (SW-1485, SW-1721) is in the proving guide and the code (`matching.rs:1581`) but not in the reference; `W-MATCH-UNCONFIRMED` and `W-MATCH-DECISION-IF` are | S |
| F8 | low | high | `editors/vscode/README.md` | Nothing on the recovery pop-ups (SW-1820 to SW-2118): what "stopped checking X … edit one of its files" and "reload the window" mean, the restart budget, where the details are | S |
| F9 | low | medium | `docs/syntax.md:1091-1092` | `minutesLeft`'s guards still carry names (`fewerMinutes:`, `fewerHours:`); dropping them would show stage 1 with two measures, but SW-2145 F9 says that case is untested, so the test comes first (SW-2165) | S |
| F10 | low | high | `web/guide/` | Tour gaps a newcomer would enjoy: see §5 | M |

## 1. `decreasing`, stages 1 and 2 (SW-2029, SW-2030)

**Coverage.** Guide: yes. Chapter 7 says a plain `if` gives its condition
(`:121`), shows `gcd` without a name (`recursion.sw#gcd`), and adds the
`match` case with a checked example (`recursion.sw#match-fact`, `:137-147`).
`syntax.md`: yes, two bullets (`:1035-1064`) and a sentence in the `match`
section (`:1999`). Tour: no (F3). The page is the section a newcomer reads for
`decreasing`, and "you don't have to name the guard" and "the `match` gives
the call its fact" are the kind of thing the tour exists to show.

**Accuracy.** Checked against the commits, the examples and the code:

- The stage 1 sentence, an `if` "in a `match` that isn't the definition's
  own case split" showing the `if _:` form, was removed from `syntax.md` by
  `cc798e083` and appears nowhere else (`grep` over `docs/guide`,
  `docs/syntax.md`, `docs/proving-guide.md`, `docs/tutorial`, `web/guide`).
- Chapter 7's prose example "`match n - k with | Zero => k | Succ j => countUp
  n (k + 1)` is proved from `n - k = Succ j`" isn't a guide snippet, but it is
  `examples/accept/decreasing-match-fact.sw:12-17` word for word, so the
  examples suite checks it.
- `Set.sizePopMin`'s argument order (set, key, rest, found) matches its
  use in chapter 7 (`std/Set/Spec.sw:155`).
- The `E-DECREASING` note in chapter 7 is generated output
  (`<!-- output: check errors/decreasing.sw -->`), regenerated in `7d4c8bbbe`;
  the new unnamed-`match` wording ("(this `match`'s arm)", "name it, `match
  found: … with`") is in `decreasing.rs:2927,2940` and in
  `examples/reject/decreasing-match-unnamed.sw`'s snapshot, not in the guide.
  Not needed, but the guide's `total` example could show the error you get
  without `found:` instead of only saying it.
- Still imprecise, already filed: "false in the `else`" (`07-recursion.md:121`;
  it is `¬(c = True)` for a `Bool`) and the cases that keep `if _:`
  (conjunctions, a `Bool` `if` under a lambda) are SW-2145 F3/F8, in SW-2165.
  SW-2030 changed F3's list: an `if` inside a lifted `match` now keeps its tag,
  so SW-2165's `syntax.md` sentence should be written against stage 2's text,
  not the review's.
- Outside the guide: F2 (`core.md`), F4 (proving guide).

**Examples checked.** Every `<!-- snippet: file#region -->` in
`docs/guide/*.md` names a `-- begin region` that exists in its example file
(checked by script over all chapters; the `@declaration` form wasn't
checked). The chapter 7 snippets match `recursion.sw` text for text.

## 2. Record eta and fields of calls (SW-1913, SW-1998, SW-2095, SW-2096, SW-2126)

**Coverage.** None of these lanes changed a user doc, and none needed to on
its own: each restores behaviour proofs relied on before eta (a `match` or
`rfl` seeing inside `(f x).i`, the unifier treating a field of an unknown as
blocked). But they sit on record eta itself, which is user-visible and
undocumented: `p = { x = p.x, y = p.y }` by `rfl`, and a match on a record
computing on an unknown one. `docs/guide` and `syntax.md` say nothing
(`syntax.md:476` still presents `T.ext` as the way). `examples/accept/records.sw:57`
still says an unchanged update "isn't `rfl` until stage 2 (eta)". The tour has
no page. All of that is SW-1859 (from SW-1850 §5 item 1), backlog, and
`record-eta-remaining.md` stage 2′. Nothing to add except to run it.

**Accuracy.** F1 is the new finding. `docs/core.md` is the kernel's
specification: what the trusted checker accepts. It ends its proof-irrelevance
paragraph with "**Record eta** (D1981), if it's added, must be limited to
records with at least one field that isn't a proof". Its term table (`:28-48`)
has no `Proj`, and "Conversion" (`:239`) mentions eta for functions only. A
reader checking the kernel against its spec would conclude record eta
doesn't exist. `record-eta.md` §6 has the rules to copy in (an eta type,
`Proj`, rule 1 constructor against neutral, rule 2 `case` on a neutral eta
value), and the restriction the sentence states is the one the kernel
implements, so it becomes a statement of fact.

## 3. Std additions (SW-2138, SW-2169)

These are library functions and lemmas, each with an API doc in std (checked:
`Map.containsIn`, `insertIn`, `removeIn` at `std/Set/Set.sw:115-128`, the
lemmas in `Set/Spec.sw`). The rule asks for the guide only for functions
people will reach for. `Map.insertIn` and friends qualify: grouping into a
`Map k (Set v)` is a common AoC shape. The lemmas (`Set.minLeast`,
`findIndex` lemmas, SW-2169's sixteen `List` lemmas) don't need guide text:
`stitchwort doc` and `search` find them, and the guide doesn't list lemmas.

**Does the guide have a `Map`/`Set` section?** Yes, chapter 6 `:261-287`, with
checked snippets `library.sw#map` and `#set`, and the tour has
`14-map-set.sw`. SW-2138's "none" was wrong. What's missing (F6): maps of sets,
`popMin`/`min` (chapter 7 now relies on `popMin`, F5), `getOr` (the tour uses
it, the guide shows only `get`), `alter`, `Map.counts` (the tour's
`wordCounts` uses it, the guide's builds it by hand), and a word in chapter 10
on proving things about maps (`Map.getInsert` and the `containsIn` lemmas). I'd
add the first four to chapter 6 and leave proofs about maps for the std loop
kit's guide section (SW-2147) or a later chapter 10 section.

## 4. Pages the std renames will touch (std-naming.md §5)

Counted by `grep` over `docs/guide/*.md`, `docs/guide/examples/**`,
`docs/syntax.md`, `docs/proving-guide.md` and `web/guide/`. Each lane's brief
already lists these directories; this says which files actually have hits,
so the lane knows to run `the_guide_` tests and the web guide check.

| Lane | Old names | User-doc files with hits |
|------|-----------|--------------------------|
| N1 (SW-2188) | `getOrElse` | guide 03 (2), 06 (3), 10 (1); examples `data.sw`, `library.sw`, `proofs.sw`; `syntax.md` (3); tour `12-option-list`, `28-chained-comparisons`, `33-export` |
| N1 | `concatMap` | guide 06 (the "others worth knowing" list), 10 (1) |
| N2 (SW-2189) | `intersectAll`, `Set.intersect` | guide 06 `:334` and `library.sw:97`; tour `13-non-empty-list.sw:13` |
| N2 (if D3151) | `Set.min`/`Map.min` | none today; F5/F6's additions would add some, so land those after N2 or write `minimum` |
| N3 (SW-2190) | `List.inRange`, `inRangeIff` | guide 06 (3), 10 (4); `library.sw`, `proofs.sw`; `syntax.md` (3); tour `34-ranges.sw` |
| N4 (SW-2191, doing) | `allDistinct` | `syntax.md` (3); no guide hits (`List.distinct` isn't in the guide; `dedup` keeps its name) |
| N5 (SW-2192) | `memMap`, `memFilter` | `syntax.md` (1 each), `docs/proving-guide.md` (2) |
| S1 (SW-2193) | `Text.join`, `joinWith`, `Text.fold` | guide 05, 06; `interfaces.sw`, `library.sw`; `syntax.md` (`join` 1, `fold` 2); tour `06-defaults.sw` (`joinWith`) |
| O1 (SW-2194) | `rangeFrom`, `firstFrom` | `syntax.md` only (4 and 2) |
| L1/L2 (SW-2202, SW-2203) | `…Less` lemmas | `syntax.md` (`Nat.lessLe` 2, `Nat.lessTrans` 2), `docs/proving-guide.md` (`Nat.modLess` 3); `Nat.LexLess` and `Nat.decLessThan` are types/decisions and stay |

The proving guide is not in §5's list of directories. It is user-facing
(proof lanes and people read it first), so N5, L1 and L2 should include it.

## 5. What the tour lacks that a newcomer would enjoy

Already filed: holes and live goals (SW-1862), `@[tailrec]` (SW-1858),
record eta (SW-1859), and Float in the tour prose (SW-1860). Not filed:

- **The guard without a name, and a `match` that proves its own call smaller**
  (F3): the page exists, it just shows the old form.
- **`cases`**: `theorem … := cases` splitting `Bool`s and enumerations until
  each case computes. It is the most "it just works" tactic, and the tour has
  `omega`, `calc`, `rewrite` and `match induct` but not this.
- **Counterexamples**: a false theorem gets a counterexample when its proof
  fails (`syntax.md`, "Counterexamples to a theorem"). The tour already shows
  real compiler output with `data-failure-of` (`guide.html:94`), so a page with
  a plausible but false statement and its counterexample fits the format.
- **`"""` text with `${…}`**: no tour page has a multi-line text literal,
  though every AoC day starts with one.
- **Maps of sets**: a line on tour page 14 (`insertIn`), after N2.

`ring` and `stitchwort search` are also absent. They're less of a first-hour
delight, so I'd leave them out.

## 6. Language server recovery messages (SW-1820, SW-1948, SW-2086, SW-2088, SW-2089, SW-2091, SW-2117, SW-2118)

The messages are user-visible but not language features, so the rule
doesn't apply; the editor README is their natural home. I checked the five
pop-up texts (`crates/lsp/src/lib.rs:790, 877, 2576, 2615, 2657`). They are
consistent: every stop says "Reload the window", and a quarantined project
says "Edit one of its files to try again". The recovered case says "Details
are in the Stitchwort output; please report it". `editors/vscode/README.md`
names the output channel (`:82`) but not these messages or the budget. A short
"When the server hits an internal error" paragraph would close F8.

## 7. The rest of the log

- SW-2083, SW-1916 (lexer messages, invisible characters): `syntax.md` updated
  in the same commits (`0343c500d`, `b14db611b`, fixup `99a51d9cc`).
- SW-1719/SW-1721 (`W-MATCH-DECISION-IF`, unnamed `W-MATCH-NOT-FOUND`): in
  `syntax.md:2026`, chapter 10 and the proving guide; `W-MATCH-NOT-FOUND`
  missing from `syntax.md` (F7; chapter 10's part is SW-1861).
- SW-1630 (`W-REWRITE-UNCONFIRMED`, `W-MATCH-UNCONFIRMED`): in `syntax.md`
  and the proving guide.
- SW-1675/1676/1682/1684 (hover on `?`, numbered notes, Testing panel): in
  `editors/vscode/README.md` and chapter 1; chapter 9's stale line about tests
  in the editor is SW-1856.
- SW-1885, SW-2081 (pins), SW-1925/SW-1995/SW-2090 (rewind), SW-1997, SW-2106,
  SW-2128, SW-2129, SW-2139 and the design and review merges: nothing a user
  of the language sees.

## Checked and sound

- Chapter 7 and `syntax.md`'s `decreasing` text against SW-2029/SW-2030's
  commit messages, `examples/accept/decreasing-plain-if.sw`,
  `decreasing-match-fact.sw`, `examples/reject/decreasing-match-unnamed.sw`,
  and the `E-DECREASING` note's code.
- No remaining user-doc sentence says an `if` in a nested `match` keeps its
  proof in `f.unfold`, and none says a `match`'s equation needs a name to reach
  a recursive call.
- Every guide snippet region resolves; chapter 7's new snippet matches its
  example file.
- `E-MATCH-MOTIVE` advice (proving guide `:359`, `syntax.md:1304`) doesn't
  contradict stage 2's "no `E-MATCH-MOTIVE`" for `decreasing` definitions.
- The tour's other `if h:` uses (`28-chained-comparisons.sw`) need the name
  (it is passed to `at`), so they stay.

## The 1 November review

`docs/research/rust-codebase-review.md` has no findings about user docs, so
none are in this audit's scope. The earlier guide audit, SW-1850, filed
SW-1854 to SW-1864. All eleven are still in backlog, and none is made stale
by 6-7 November's work. SW-1859's scope (record eta) grew in importance,
since four more lanes now build on eta.

## Tickets to file

Grouped into lanes; none overlaps SW-1854 to SW-1864 or SW-2165.

**Lane A. [Sonnet] Kernel spec catches up (F1, F2), 45 min.** `docs/core.md`:
add `Proj(D, i, t)` to the term table. Write record eta's rules into
"Conversion", from `record-eta.md` §6.1-6.4 as built, including the
restriction to records with a field that isn't a proof. Replace the "if it's
added" sentence. Rewrite item 6 of "Recursion on a measure" for `f.%plain`,
`f.%plain.%same` and `f.%unfoldStep` (SW-2029, SW-2030). Read only plus one
doc; no tests. Opus reviews it (kernel terms, D2364), or the orchestrator
checks it statement by statement against the code.

**Lane B. [DeepSeek] `decreasing` stage 1-2 in the tour and proving guide
(F3, F4), 30 min.** `web/guide/30-decreasing.sw`: `if next < n` without a
name, plus a second definition whose `match` gives its call the fact (as
`countUp` in `examples/accept/decreasing-match-fact.sw`), with a test and a
theorem by `f.unfold`. Update the page's paragraph in `guide.html:170`. Proving
guide `:286-287`. Run `task test:one -- the_guide_examples_check`. Not beside
SW-2165 (both touch the `decreasing` docs).

**Lane C. [Sonnet] Map and Set in chapter 6 (F5, F6), 40 min, after N2
(SW-2189).** In `library.sw#map`/`#set`: `getOr`, `Map.counts`, `alter`,
`popMin` and `minimum` (or `min`, per D3151), and a maps-of-sets test
(`insertIn`, `containsIn`, `removeIn`); a sentence each. Link chapter 7's
`popMin` to it. One line on tour page 14. `task test:one -- the_guide_` and
the web guide check.

**Lane D. [DeepSeek] Small reference gaps (F7, F8), 30 min.** `syntax.md`:
`W-MATCH-NOT-FOUND` beside `W-MATCH-UNCONFIRMED` in the `match` section (text
from the proving guide `:378-389`). `editors/vscode/README.md`: a paragraph on
the recovery pop-ups, quoting `lsp/src/lib.rs`'s messages. Docs only; no tests.

**Lane E. [Sonnet] Three tour pages: `cases`, counterexamples, multi-line
text (§5), 75 min.** Each a short page checked by
`the_guide_examples_check`; the counterexample page uses a
`data-failure-of` block with the real output. Ask the playground's owner
whether counterexample search runs in the web build first; if not, drop
that page.

**Add to existing tickets:** SW-2165, write the `syntax.md` sentence against
stage 2's text (§1). SW-2188/2192/2202/2203 briefs: include
`docs/proving-guide.md` and the files in §4.

## Calls I made

- Counted `docs/core.md` and the proving guide as user docs for this audit:
  `core.md` because it is the kernel's specification readers check against,
  the proving guide because proof writers read it first.
- Didn't count the language server's messages under the rule (not a language
  feature); filed them against the editor README instead.
- Recommended no guide text for SW-2169's and SW-2138's lemmas: the guide
  doesn't list lemmas, and `stitchwort doc` finds them.
- Left `ring` and `search` out of the tour suggestions.
- Didn't move SW-2213 on the board: the review brief says not to edit
  `board/tickets.json`.

## Questions for Matt

- **D3210:** CLAUDE.md's docs rule covers the guide, `syntax.md` and the tour.
  Should it also say that a kernel change (a new term form, a new conversion
  rule) updates `docs/core.md` in the same lane? Record eta (SW-1642)
  and the four lanes built on it all merged today, and the spec still says
  it doesn't exist. [rec: yes]
