# Proposal: documentation of Stitchwort code

**Status:** draft 1, 1 November 2026. Ticket SW-1013. Starts from the research note
[research/documentation.md](../research/documentation.md) (written by Codex; its claims were
treated as unverified and re-checked here) and an Opus review of that note. Matt's decisions
D2134–D2139 and D2141 (1 November) are stated as decided. New questions are D2142–D2151 in
[§9](#9-decisions-for-matt). An independent review follows in
[Review 1 and how it was addressed](#review-1-and-how-it-was-addressed).

Labels:

- **[checked: file:line]**: read in this repo at `f464c595` (main, 1 November);
- **[run]**: run with `target/release/stitchwort` built from main on 1 November;
- **[measured]**: counted by a script in [documentation/](documentation/) (named at each use),
  run from the repo root. The scripts read source text with regular expressions, so their counts
  are close, not exact;
- **[cited]**: read on the linked page on 1 November;
- **[memory]**: from memory, not confirmed;
- **[inferred]**: my reasoning, not tested.

## The short answer

- **The problem is real but modest, and mostly about finding.** An agent learns what a std
  function does by running `stitchwort search`, which prints a type and `file:line`, then reading
  the source around that line. The comment it needs is *above* the line it is given. Std already
  has a comment above 54% of its declarations (74% of definitions) [measured]. What is missing is
  a way to see it, and the examples and theorems that go with it, in one step.
- **Stage 1 shows what exists** (D2136): a one-line summary in `stitchwort search` results, a
  `doc` and `summary` on `check --index` symbols, a new `stitchwort doc NAME`, and docs in hover
  (language server and playground). Docs are read from the source text when they are shown; the
  elaborator, the kernel, hashes and the check cache don't change.
- **Until the sorting pass, stage 1 reads plain `--` blocks too** (D2142), so it is useful at
  once; the `--|` marker (D2134) then separates user docs from maintainer notes.
- **Examples are found by name** (D2135): `test "List.unzip"` and `theorem Text.padLeftExample`
  are examples of `List.unzip` and `Text.padLeft`. Today that attaches 181 of std's 594 tests and
  96 of its 115 `…Example` theorems; only 129 of 1,108 std definitions have one [measured].
  AoC and roguelike tests are named in prose and attach almost nowhere.
- **Theorems about X** (D2141) come from the existing search, ranked: theorems named after X
  first, rewrite rules with X on the left first within them, at most 8 shown with the total and
  the command for the rest.
- **Then** (stage 2) the `--|` sorting pass and a coverage report (D2138); (stage 3) checked
  links ``[`Name`]`` with a warning `W-DOC-LINK`; (later) examples in comments and a website.
- **Cost:** stage 1 about two Sonnet lanes; stage 2 is mostly review of about 5,000 comment
  blocks; stage 3 one lane [inferred, §7].

## 1. The problem, with evidence

### 1.1 How an agent finds what a function does today

Take `List.filterMap`. An agent that knows the name runs a name search [run]:

```
$ stitchwort search '"filterMap"'
 1. Std.List.filterMapSome  theorem
    [a: Type] → [b: Type] → (xs: List a) → (f: a → b) → List.filterMap xs (x => Some (f x)) = List.map xs f
    std/List/Lemmas.sw:803  (import Std (List))
 …
9 results; showing 5 (--limit N for more)
```

The function itself is 9th of 9: a name-only search lists the seven `filterMap…` theorems before
the two definitions (`--limit 20` shows the order) [run]. With `--definitions` it is second,
after `Std.Map.filterMap`, as:

```
 2. Std.List.filterMap  definition
    [a: Type] → [e: Effect.Effects] → [div: Effect.Divergence] → [b: Type] → List a → (a → {e} Option b) → {e} List b
    std/List/Toolkit.sw:204  (import Std (List))
```

The type is the elaborated one, with the implicit effect row and divergence parameters, and
without the parameter name `f` that the source has. To read what it does, the agent reads
`crates/elab/src/std/List/Toolkit.sw` (in this repo) or `stitchwort std-source
List/Toolkit.sw` (anywhere), and must start *before* line 204, because the comment is on lines
202–203 [checked: List/Toolkit.sw:202-204]:

```
-- Keeps the `Some` results, in order. `f` may perform abilities, which run in
-- list order (`f x` is the first argument, so it runs before the rest).
def List.filterMap: List a → (f: a → {e} Option b) → {e} List b
```

Its examples (none attached by name; §5.4) and its 22 theorems (`stitchwort search
'List.filterMap' --theorems`) are separate searches [run]. So answering "what does it do, how is
it used, what is proved about it" is three or four commands and some slicing.

### 1.2 Coverage of existing comments

A `--` block directly above a declaration (attributes in between allowed) is the convention
formatter.md records: "By convention, a doc comment is a run of `--` lines directly above a
declaration with no blank line between" [checked: docs/proposals/formatter.md:64-65]. Counted by
[doccov.py](documentation/doccov.py), leaving out `%` helpers and `…Example` theorems [measured]:

| | definitions | types | theorems | instances | all |
|---|---|---|---|---|---|
| std (90 files) | 823 / 1,108 (74%) | 58 / 69 | 1,030 / 2,366 (44%) | 24 / 80 | 1,945 / 3,635 (54%) |
| aoc/src (408 files) | 1,305 / 1,904 (69%) | 116 / 145 | 1,448 / 2,010 (72%) | 1 / 1 | 2,870 / 4,060 (71%) |
| games/rogue/src (29 files) | 97 / 146 (66%) | 14 / 22 | 74 / 176 (42%) | – | 185 / 345 (54%) |

(The review of the research note counted 891/1,189 std definitions; it seems to have included
`%` helpers or counted differently. The order of magnitude agrees.)

Not every block is for users. 47 of std's 1,945 blocks name a ticket, a D number, a proposal
file or a timing [measured: doccov.py]; across all of std, 141 comment lines name a ticket, a D
number or a `.md` file (`grep -rhE '^\s*--.*(SW-[0-9]+|\bD[0-9]{3,4}\b|proposals/|\.md\b)'
crates/elab/src/std | wc -l`) [run]. Markers undercount: `List.filterStep`'s block is about why
the function exists ("A function of its own so the recursive call is written once…"), with no
marker [checked: List/Toolkit.sw:40-43]. Separating these is what the `--|` sorting pass is for.

First sentences are short enough to be summaries: over std's 915 commented non-theorem
declarations, the median is 64 characters, 90% are at most 139, and 44 exceed 160 (longest 355)
[measured: [summ.py](documentation/summ.py)].

### 1.3 Lane notes: functions missed or misused

The evidence is a handful of cases, not a measured rate. Each is quoted with what it shows.

- **Rewrote lemmas std had.** "I first wrote `compareSelf` and `lessNotGreater` too, then found
  std's `Ord.compareSelf` and `Ordering.lessNotGreater` by grepping the std sources; with no
  search by type, a lemma is easy to miss" [checked: aoc/NOTES-2024.md:7928-7931]. This predates
  `stitchwort search`, which now addresses it.
- **Found by grep.** "finding `tailOf`, not `tail`, took a grep" [checked:
  aoc/NOTES-2024.md:373].
- **A request for three functions that already existed.** SW-1006 (1 November) asked for
  `Text.padLeft`, `Option.toList` and `List.allSome`; a lane found all three in std, and Matt
  closed it (D2131) [checked: board/tickets.json, SW-1006]. To be exact about what this shows:
  the original day 24 note was right when written ("No `Text.padLeft`", aoc/NOTES-2024.md:7906);
  the three were added on 28 October (`f7264e47`, SW-831); SW-1006 came from a stale item in
  SW-816. So it shows that "does std have X?" is not quick to answer, for the orchestrator as
  well as lanes. It is not a case of a lane failing to find a function while coding.
- **A cost the comment states, found by measuring.** Day 15 moved boxes with `boxes.difference
  group |> .union moved`; part 2 took 19.8 s, and 0.97 s with the arguments the other way, because
  `union` and `difference` are fast only when one set is small [checked:
  aoc/NOTES-2024.md:4656-4667]. `Set.union`'s comment has said so since 24 October ("O(n log m)
  when one set, of n keys, is much smaller … see `Map.union`") [checked: Set/Set.sw:40-42;
  `git log -S'much smaller'` gives `96b79502`, 24 October]; the note was written on 28 October
  (`155a64e1`). Whether the lane read that comment isn't recorded; nothing it ran would have shown
  it [inferred].
- **Where evidence is thin.** Most "No `X`" items in aoc/NOTES-2021.md were true when written:
  `Option.mapCong`, `List.filterFilter` and `List.flatMapCong` were each added to std after the
  note that asked for them [checked: `git log -S` on each, 31 October–1 November]. I found no
  note where an agent misread what a std function computes. The case for this work is cheaper
  lookup and fewer duplicate requests, not a record of wrong programs.

## 2. What exists, and what this proposal does with it

| What | Where | Here |
|---|---|---|
| The `--` comment; no block or doc comments | docs/syntax.md:11; lexer skips to end of line [checked: crates/syntax/src/lexer.rs:321-326] | **Reused.** `--|` is already a comment; no lexer change (D2134). No `.sw` file in the repo contains `--|` today [run: `grep -rln --include='*.sw' -- '--\|' .`] |
| The convention: `--` lines directly above a declaration | formatter.md:64-65 | **Extended**: stage 1 reads it; stage 2 replaces it by `--|` for user docs |
| The formatter's comment trivia | `lex_with_trivia`, `Comment`, `Trivia` (leading comments, blank lines) [checked: lexer.rs:204-252]; `decl_ranges`, the column-0 split, attributes belonging to the declaration after them [checked: crates/syntax/src/parser.rs:387-392]; used by the formatter [checked: crates/fmt/src/lib.rs:92-94] and the language server [checked: crates/cli/src/lsp.rs:633-655] | **Reused** as the attachment machinery (§4) |
| `check --index` (JSON version 3) | symbols with name, kind, file, range, container, type; kinds include `ctor`, `field`, `op`, `test`; library symbols only if referenced [checked: docs/proposals/code-navigation.md:94-101; crates/driver/src/nav.rs:59-75] | **Extended**: `doc`, `summary` on symbols |
| `stitchwort search` (JSON version 1) | results with name, kind, type, file, line, import; no docs [checked: crates/driver/src/search.rs:418-451, 901-948]; `…Example` and `%` hidden unless `--all` [checked: search.rs:827-837] | **Extended**: `summary`. D2063's "no natural language" stands: summaries are shown, never matched (§5.2) |
| `stitchwort std-source PATH` | prints an embedded std file [run: `stitchwort --help`; checked: crates/cli/src/main.rs:503] | **Kept**; `doc` reads the same embedded text |
| Hover | language server: type, then `kind name`, then omitted defaults [checked: lsp.rs:897-914]; playground tooltip: name, kind, type from the index [checked: web/index.html:2751-2770] | **Extended** with the doc (§5.5) |
| The guide and its harness | quoted snippets and outputs are checked [checked: crates/cli/tests/guide.rs:1-25]; the library tour [checked: docs/guide/06-namespaces-and-library.md:166-274] | **Kept** as the narrative; not replaced by generated docs. The tour can quote `stitchwort doc` output through the harness's `<!-- output: … -->` |
| Std tests and `…Example` theorems | 594 `test`s, 115 `…Example` theorems, all checked [measured: [examples.py](documentation/examples.py)] | **Reused** as examples, by name (D2135) |
| `private` | does not exist: "There is no `private`: anything can be named from anywhere" [checked: docs/guide/06-namespaces-and-library.md:162] | Nothing to design; the research note's "private implementation scope" (its line 168) does not apply. `%` helpers stay hidden as search hides them |
| Proving guide, "search first" | docs/proving-guide.md:343-371 [checked] | **Extended**: add `stitchwort doc` there once built |

## 3. Decided (1 November 2026)

- **D2134**: user-facing docs are `--|` comments; maintainer notes stay `--`. One sorting pass
  converts the existing comments.
- **D2135**: examples attach by name, with no new syntax: a `test` named after a definition and an
  `X.yExample` theorem are shown with `X.y`. Code inside doc comments is deferred, and taken up
  only if linking proves insufficient.
- **D2136**: the first release is for agents, through the CLI: summaries in `search` (text and
  JSON), `doc` on `check --index` symbols, `stitchwort doc NAME`, and hover in the language server
  and playground. A website comes later.
- **D2137**: `doc` and summaries work for any namespace (AoC, the roguelike), not only std.
- **D2138**: a coverage report first; enforcing docs on std namespaces later, after the sorting
  pass.
- **D2139**: this proposal gives evidence, a cost per stage, and D numbers for open questions,
  and is reviewed independently.
- **D2141**: `stitchwort doc NAME` lists theorems about the definition, found with the search
  machinery. Docs link a theorem (``[`Name`]``, checked) rather than restate a property in prose.

## 4. Attachment rules

**The doc block of a declaration** is found from the first token of the declaration:

1. For a top-level declaration, the first token of its `decl_ranges` group, so attributes
   (`@[noReceiver]`) belong to it and the doc goes above them. For a member (a constructor `|`
   line, a record or interface field, an ability operation), the first token of the line its name
   is on.
2. Take that token's leading comments (`Trivia::leading`). The **comment run** is the last group
   of them with no blank line inside it and none between it and the token
   (`blank_lines_before == 0` on the token and on each comment after the first).
3. The **doc** is the `--|` lines of the run, in order, each with `--|` and one following space
   removed. A `--|` line with nothing after it is a paragraph break. `--` lines in the run are
   maintainer notes: skipped, not shown. So a maintainer note may sit next to a doc, above or
   below it.
4. Until the sorting pass (D2142): if the run has no `--|` line, the whole run of `--` lines is
   the doc, marked as such (`"docMarker": "--"` in JSON). After the pass this fallback is removed.
5. A trailing comment (on the declaration's own line) is never a doc.

**Equations and arms** (`| Nil, f => Nil`) get no docs: only the declaration does.

**File and namespace docs.** A `--|` block at the top of a file followed by a blank line (or
directly above a `namespace` line) is the file's doc. `stitchwort doc` on a namespace prints the
docs of its files, in file order, then its declarations with their summaries (§5.3). There is no
"one primary overview per namespace" rule: several files may each have one, as Go concatenates
package comments of a multi-file package [cited: go.dev/doc/comment]. Std has no `namespace`
lines; its namespaces come from the names (`def List.map` is in `Std.List`), so a std file's doc
belongs to the namespaces of the declarations in it [inferred; checked that
List/Toolkit.sw:1-4 is such a header].

**Text.** Docs are plain text with Markdown-ish conventions already used in std comments:
backticks for code, blank `--|` lines for paragraphs, `-` lists. Nothing is rendered in stage 1:
the CLI prints the text; the language server sends it as Markdown (it already sends Markdown
[checked: lsp.rs:907-910]).

**Summary.** The first sentence of the first paragraph: up to the first `.` that is outside
backticks and followed by a space or the end, skipping `e.g.` and `i.e.`. If that is over 160
characters, cut at the last space before 160 and add `…`. Measured on std: 44 of 915 would be cut
[measured: summ.py]. A summary is never generated from the type.

**Why not attach during elaboration.** Docs are read from the source text when they are shown,
by re-lexing the declaration's file with trivia. The checker lexes without trivia because trivia
"takes more memory than the tokens" [checked: lexer.rs:253-256]; showing docs for ten search
results, one `doc` call or one hover re-lexes a few files. Nothing in the elaborator, the kernel,
the core hashes or the check cache changes, so a doc edit invalidates nothing it doesn't today
(today a comment edit re-elaborates its namespace: check-cache.md:177-178). The cost is that a doc
shown from a project file is read from the file on disk, which may have changed since the check
that found the name; the line is then wrong. The index and the language server have the text
they checked, so only `search` and `doc` can see this, and they reload the project through the
check cache, which re-checks a changed file first [inferred from check-cache.md: the key
includes the source text]. This is D2143.

## 5. Stage 1: design

### 5.1 Data

One function in `stitchwort-syntax`, used by every consumer:

```rust
pub struct Doc {
    pub text: String,          // the doc, markers removed, lines joined with '\n'
    pub summary: String,       // §4's first sentence
    pub marker: DocMarker,     // Bar (`--|`) or Plain (`--`, D2142's fallback)
    pub span: Span,            // the doc lines, for diagnostics and links (stage 3)
}
pub fn docs(file: FileId, text: &str) -> HashMap<u32 /* byte offset of the name */, Doc>
```

It lexes with trivia, splits with `decl_ranges`, and keys each doc by the byte offset of the
declaration's name, which every consumer already has (an index symbol's `range`, a search
result's line plus the name, a `LiveRef`'s target). Docs are owned by the source declaration,
not a core hash: two definitions with the same hash keep their own docs [checked: core hashes
omit a definition's own name and source locations, crates/core/src/hash.rs:29-31].

### 5.2 `stitchwort search`: a summary per result

Text: one more line, the summary, after the location; nothing for an undocumented result.

```
 2. Std.List.filterMap  definition
    [a: Type] → [e: Effect.Effects] → [div: Effect.Divergence] → [b: Type] → List a → (a → {e} Option b) → {e} List b
    std/List/Toolkit.sw:204  (import Std (List))
    Keeps the `Some` results, in order.
```

JSON: a `summary` field, a string or `null`. A new field doesn't change the version (search.md
§4.1's rule). Ranking and matching don't change: D2063 ruled out natural-language search, and a
summary is never matched against the query.

One search change belongs here, D2150: with only `"text"` name parts, a result whose name *is*
the text after its namespace (`List.filterMap` for `"filterMap"`) ranks first. Today it ranks
last (§1.1).

### 5.3 `stitchwort doc NAME`

```
stitchwort doc NAME [--project DIR | FILE] [--json] [--theorems N]
```

- **NAME** is resolved as search resolves names: the full name (`Std.List.filterMap`), the name
  without `Std.` (`List.filterMap`), or a project name as `import N (..)` sees it. Several matches
  print a list of them and exit 2; none prints the closest names (a `"text"` search on the last
  component) and exits 1. A namespace name (`List`, `Aoc.Year2024.Day06`) prints the namespace's
  file docs, then each definition, type, interface and ability in it (not theorems) with its
  summary, one per line, grouped by file.
- **What it prints**, for a definition:
  1. name, kind, the **header as written** (the declaration's source up to `:=` or its first
     equation; it keeps parameter names that the elaborated type drops), location and import line;
  2. the doc, or `(no doc)`;
  3. examples (§5.4), each with its source text, not run;
  4. theorems (§5.5), at most 8 by default (`--theorems N`, `0` for none).
- Exit 0 when the name is found, documented or not.

Worked example (the output is designed, not run; the theorem order is computed by hand from the
search runs in §5.5):

```
$ stitchwort doc List.filterMap
Std.List.filterMap  definition
  def List.filterMap: List a → (f: a → {e} Option b) → {e} List b
  std/List/Toolkit.sw:204  (import Std (List))

  Keeps the `Some` results, in order. `f` may perform abilities, which run in
  list order (`f x` is the first argument, so it runs before the rest).

Examples: none (a `test "List.filterMap"` or `theorem List.filterMapExample` would be one)

Theorems: 22 mention it; 8 shown
  List.filterMapSome       List.filterMap xs (x => Some (f x)) = List.map xs f
  List.filterMapMap        List.filterMap (List.map xs g) f = List.filterMap xs (x => f (g x))
  List.filterMapAppend     List.filterMap (List.append xs ys) f = List.append (List.filterMap xs f) (List.filterMap ys f)
  List.filterMapAll        ((x: a) → x ∈ xs → f x = Some x) → List.filterMap xs f = xs
  List.filterMapCong       ((x: a) → f1 x = f2 x) → List.filterMap xs f1 = List.filterMap xs f2
  List.filterMapCongMem    ((x: a) → x ∈ xs → f1 x = f2 x) → List.filterMap xs f1 = List.filterMap xs f2
  List.filterMapSomeMem    ((x: a) → x ∈ xs → f x = Some (g x)) → List.filterMap xs f = List.map xs g
  List.findMapIsHeadFilterMap  …
  all 22: stitchwort search 'List.filterMap' --theorems
```

Theorem statements are printed without their leading type and value parameters (`[a: Type] →
(xs: List a) → …`), which the search prints in full; the JSON keeps the full type.

A second example, where examples exist [run: `stitchwort search '"padLeft"' --all`]:

```
$ stitchwort doc Text.padLeft
Std.Text.padLeft  definition
  def Text.padLeft (text: Text) (n: Nat) (char: Char): Text
  std/Text/Text.sw:21  (import Std (Text))

  `Text.padLeft text n char` is enough copies of `char` followed by `text` to make it
  n characters long (it is `text` itself when that is already n long or longer).

Examples:
  theorem Text.padLeftExample: Text.padLeft "7" 2 '0' = "07" := rfl     std/Text/Text.sw:24

Theorems: 1 mentions it
  Text.padLeftLongEnough   Text.padLeft "123" 2 '0' = "123"
```

JSON (version 1):

```json
{"version": 1,
 "name": "Std.List.filterMap", "kind": "definition",
 "header": "def List.filterMap: List a → (f: a → {e} Option b) → {e} List b",
 "type": "[a: Type] → [e: Effect.Effects] → [div: Effect.Divergence] → [b: Type] → List a → (a → {e} Option b) → {e} List b",
 "file": "std/List/Toolkit.sw", "line": 204, "import": "import Std (List)",
 "doc": "Keeps the `Some` results, in order. `f` may perform abilities, which run in\nlist order (`f x` is the first argument, so it runs before the rest).",
 "summary": "Keeps the `Some` results, in order.",
 "docMarker": "--",
 "examples": [],
 "theorems": {"total": 22, "shown": [
   {"name": "Std.List.filterMapSome", "type": "…", "file": "std/List/Lemmas.sw", "line": 803,
    "group": "rewrite"}]},
 "warnings": []}
```

- `doc`, `summary` and `docMarker` are `null` when there is no doc.
- An example is `{"kind": "test" | "theorem", "name", "file", "line", "source"}`.
- `group` is `rewrite` or `other` (§5.5).
- `docMarker` disappears with D2142's fallback after the sorting pass.

### 5.4 Examples, by name (D2135)

An **example of X** is:

1. a `test` whose description, as written, is X's name as the test's file would write it
   (`test "List.unzip"`, or `test "orElse"` in the file declaring `Option.orElse`), or starts with
   a *qualified* name of X followed by a space, `,` or `:` (`test "Result.map, an error"`,
   `test "Nat.divisors of zero"`);
2. a theorem named `X.yExample` or `X.yExample2`, `X.yExample3`, … for X = `X.y`, if `X.y` is a
   declaration (a definition or a theorem).

Single-word prefixes don't count: "need Some" would attach to `Fail.need`, but "example part 1"
would attach to every AoC day's `example` value [measured: examples.py, "first word" counts].
Tests are found in the parsed source of X's namespace's files (tests are `test` symbols in the
index already [checked: code-navigation.md:94-97]); `…Example` theorems by name.

What this attaches today [measured: examples.py]:

| | tests | attached (exact / qualified prefix) | `…Example` theorems | attached |
|---|---|---|---|---|
| std | 594 | 181 (123 / 58), to 133 declarations | 115 | 96 (42 to a definition, 54 to a theorem) |
| aoc/src | 1,246 | 7 exact, all one-word (`square`, `example`, `at`) | 5 | 0 |
| games/rogue/src | 100 | 0 | 0 | 0 |

So for std, 129 of 1,108 definitions have an example; AoC and the roguelike name their tests in
prose ("a wall above blocks the way"), and `doc` will show no examples there unless tests are
renamed (not proposed). The coverage report (§6.2) counts definitions with an example.

**Not counted:** theorems that are examples in all but name, such as `Text.padLeftLongEnough:
Text.padLeft "123" 2 '0' = "123" := rfl` [checked: Text/Text.sw:26]. They appear among the
theorems. D2145 asks whether a closed theorem (no parameters) proved by `rfl` should count.

Examples are shown, never run, by `doc` or hover. Tests run under `stitchwort test` as now;
`…Example` theorems are checked by `check`. Both are already checked by the test tiers, so a
shown example has passed at the last merge [checked: workflow.md, the tiers].

### 5.5 Theorems about X (D2141)

**Which.** The theorems whose statement mentions X: the search part that is a bare name
(`stitchwort search 'List.filterMap' --theorems`), with `…Example` theorems left out (they are
examples) and `%` helpers hidden as search hides them.

**Ranked**, in groups, then by search's existing keys (premises, size, name):

1. *rewrite*: named after X (the name contains X's last component, ignoring case:
   `filterMapAppend`, `memFilterMapElim`) and an equation or `Iff` whose left side is headed by X
   (search's `--rewrite` with the pattern `X _ … _`, place `left`);
2. *other*, named after X;
3. *other*, the rest (`Char.toTextDigits` mentions `List.filterMap` but is about digits).

Std's convention, "Most functions come with theorems about them, named after what they say" (docs/guide/06-namespaces-and-library.md:172), is what makes
group 1 and 2 meaningful [checked]. For `List.filterMap` the search gives 22 theorems [run]; 7
are rewrites named after it, 8 are other theorems named after it, 7 are the rest (the transpose
and digit lemmas) [run: the `--rewrite` and plain searches, sorted by hand].

**Capped** at 8, with the total and the command that lists all. A congruence lemma (`…Cong`,
`…CongMem`) is kept: proofs need it.

**Scope.** For a std name: std only (`--project` adds the project). For a project name: the
name's namespace and the namespaces that import it, directly or not, found from the project's
import lines without checking (D2146). Search today loads the whole project through the check
cache; in a fresh worktree (cold cache) a search inside `aoc/` was still checking after 120 s
[run, stopped], while a std-only search took about 1 s [run: `time stitchwort search
'List.filterMap' --theorems`]. Lanes start in fresh worktrees, so the narrower scope matters.

### 5.6 `check --index`: `doc` and `summary`

Each symbol gets `doc` and `summary` (strings), absent when it has none. Version stays 3: a new
optional field changes no meaning [inferred; code-navigation.md moved to 3 when goals were
added]. The index writer re-lexes each indexed file once with trivia. Library symbols are only the
referenced ones (code-navigation.md:100-101), so the cost is bounded by what the program uses.
The summary is included so the playground doesn't reimplement §4's rule in JavaScript.

### 5.7 Hover

- **Language server**: after the type and `kind name`, the doc as Markdown, then the defaults as
  now. The target's text is the workspace's (open or on disk) or the embedded std text. No
  examples or theorems (they belong to `doc`) [the research note says the same, its line 200].
- **Playground**: the tooltip adds the summary line from the index (D2147).

## 6. Stage 2: the sorting pass and the coverage report

### 6.1 The sorting pass (D2134)

For each comment run that is a doc today (§4 rule 4):

1. a script marks every line `--|`, except lines that match the maintainer markers (a ticket, a D
   number, a `docs/` or `.md` path, a timing) and the sentences joined to them, which stay `--`
   and move below the `--|` lines;
2. a model reviews each file's diff and splits the rest by hand: rationale ("A function of its
   own so…"), check-time notes and proof strategy stay `--`; what a caller needs (what it
   computes, order, effects, edge cases, cost) becomes `--|`;
3. a reviewer reads it, namespace by namespace, std first.

Scale [measured: doccov.py]: std 1,945 blocks (3,149 lines), aoc 2,870 blocks (4,309 lines),
roguelike 185 blocks (277 lines). Comments only, so no hash or behaviour changes; it changes std's
text, so every std cache is rebuilt once [inferred: the cache key includes source text]. The
formatter keeps comments as written [checked: formatter.md:9, 47], so `--|` survives `fmt`.

Then D2142's fallback is removed: a `--` block above a declaration is no longer a doc.

### 6.2 The coverage report (D2138)

```
stitchwort doc --coverage [NAMESPACE…] [--json]
```

Per namespace: definitions, types, interfaces and abilities with a doc / total; with an example /
total; theorems with a doc / total (reported separately, never mixed in); and the undocumented
names. A doc that only repeats the name or is under 4 words counts as missing (D2148). It reports;
it never fails. Enforcing it on chosen std namespaces is a later decision, after the pass
(D2138).

## 7. Stage 3: checked links

**Syntax.** ``[`Name`]`` in a `--|` line: a name in backticks inside square brackets, as rustdoc
accepts [cited: rustdoc "Linking to items by name": "Backticks around the link will be stripped,
so ``[`Option`]`` will correctly link to `Option`"]. Plain backticks stay plain code. Bare
`[Name]` (Go's form) is not a link, because `[x]` is a list literal in Stitchwort prose (D2149).

**Resolution.** The name is resolved as the doc's file resolves names: its imports and its
namespace, after the file's namespace is checked, so a link may point forward or to the
declaration itself. Links add no dependency between declarations or namespaces.

**Diagnostics.** `check` reports an unresolved or ambiguous link as the warning `W-DOC-LINK` at
the link's span, with the closest names; the language server shows it live. Warnings have this
form already (`W-UNREACHABLE`, `W-NO-EFFECT`, …) [checked: grep of `"W-` in crates/]. For std, a
test fails if any std doc has a `W-DOC-LINK`, so std stays clean while projects only warn.
`check` must then find `--|` comments, which it doesn't lex today: the lexer records `--|` lines
(not other comments) even without trivia, which is a few strings per declaration [inferred].

**Display.** `doc` and hover print a link as its name; `doc --json` adds `"links": [{"text",
"target", "file", "line"}]`. With D2141, a doc that states a property writes "see
[`List.filterMapAppend`]" instead of restating it.

## 8. Costs, dependencies, and later stages

Estimates are mine [inferred], in Sonnet lanes of about a day, from the size of similar
features (search's stage 1, the index's `signature` field).

| Stage | Work | Cost | Depends on |
|---|---|---|---|
| 1a | `syntax::docs` (§5.1) with unit tests on attachment (attributes, members, blank lines, mixed `--`/`--|` runs, trailing comments); `summary` in search text and JSON; `doc`/`summary` in the index; LSP and playground hover; syntax.md and code-navigation.md | 1 lane | nothing new |
| 1b | `stitchwort doc`: name resolution, header as written, examples by name, theorems through the search API with the groups and cap, namespace listing, JSON; the project import-graph scope (D2146); search's exact-name rank (D2150); proving-guide and guide updates; CLI tests | 1 lane | 1a |
| 2a | the sorting script, then review of std (1,945 blocks) | 1 lane for the script and std's first namespaces; then about a lane per 500 blocks reviewed [inferred] | 1a (to see the result through `doc`) |
| 2b | `doc --coverage` | under a lane | 1a |
| 2c | the sorting pass on aoc and the roguelike (3,055 blocks) | as 2a, can wait | 2a |
| 3 | `--|` kept by the lexer, link resolution after each namespace, `W-DOC-LINK`, the std test, `links` in JSON; then rewriting prose that restates theorems into links (editorial, ongoing) | 1 lane, plus editing | 2a for std (links in `--` text aren't checked) |
| later | examples inside comments (D2135 defers them); a static website from the same `Doc` data (D2136) | medium each; the site needs a Markdown renderer (none in Cargo.lock today [run: no `pulldown`, `comrak` or `markdown` in it]) and upkeep | 1–3 |

## 9. Decisions for Matt

**D2142. Should stage 1 read plain `--` runs as docs until the sorting pass, marked
`docMarker: "--"`?** [Recommended: **yes**.]
Assumptions, in full:
1. Stage 1 is built before the sorting pass (the agreed build order).
2. Without the fallback, stage 1 shows no doc anywhere until stage 2, since no `.sw` file has
   `--|` today [run].
3. Some of what it shows will be maintainer notes; 47 of 1,945 std blocks carry a marker, and
   more are rationale without one [measured; §1.2]. That noise is visible and temporary.
4. The fallback is removed when the pass is done, so `--` keeps its D2134 meaning in the end.

**D2143. Should docs be read from the source text when shown (§4), rather than carried through
elaboration and the check cache?** [Recommended: **yes**.]
Assumptions, in full:
1. Every consumer already has the declaration's file and name position (index symbols, search
   results, `LiveRef`s) [checked: §2].
2. Re-lexing a file with trivia is cheap at the scale of one `doc` call, ten search results, a
   hover, or the files an index covers [inferred; not timed].
3. A project file edited after the check that found a name could show a stale doc in `search` or
   `doc`; both reload through the check cache, which re-checks a changed file first, so this
   should not happen in practice [inferred].
4. Stage 3 still needs `check` to see `--|` lines for link warnings; that is a lexer change of its
   own, not this one.

**D2144. Should a test attach to X when its description is X's name, or starts with a qualified
name of X followed by a space, `,` or `:` (§5.4)?** [Recommended: **yes**.]
Assumptions, in full:
1. The rule attaches 181 of 594 std tests to 133 declarations [measured].
2. Allowing one-word prefixes adds wrong attachments ("example part 1" in AoC) [measured].
3. AoC and roguelike tests stay unattached; renaming them is not proposed.

**D2145. Should a closed theorem (no parameters) proved by `rfl` that mentions X count as an
example of X?** [Recommended: **no, not in stage 1**; revisit after the coverage report.]
Assumptions, in full:
1. D2135 names the two ways examples attach; this would add a third.
2. Such theorems (e.g. `Text.padLeftLongEnough`) already appear in X's theorem list.
3. A closed theorem can mention several functions, so it would attach to each of them.

**D2146. For a project name, should `doc` look for theorems only in the name's namespace and the
namespaces that import it, not the whole project?** [Recommended: **yes**.]
Assumptions, in full:
1. A theorem about X can only be in a namespace that sees X: X's own or one that imports it,
   directly or through others (namespaces can't depend on each other in a cycle: docs/guide/06-namespaces-and-library.md:160).
2. The import graph comes from the import lines without checking.
3. Lanes run in fresh worktrees with cold caches, where a search inside `aoc/` took over 120 s [run].
4. For a std name, std only, unless `--project` is given.

**D2147. Hover: the full doc in the language server, the summary only in the playground's
tooltip?** [Recommended: **yes**.]
Assumptions, in full:
1. Editors show Markdown hovers with scrolling; the playground's tooltip is a small `div`
   [checked: web/index.html:2520, 2751-2770].
2. Neither shows examples or theorems; those are `doc`'s.

**D2148. In the coverage report, should a doc of fewer than 4 words, or one that only repeats the
name, count as missing?** [Recommended: **yes**.]
Assumptions, in full:
1. The report measures (D2138); it doesn't enforce.
2. Std has short real docs ("Joins a list of lists.", List/Toolkit.sw:208, 5 words), so the
   threshold must stay low.

**D2149. Should only ``[`Name`]`` be a link, not bare `[Name]`?** [Recommended: **yes**.]
Assumptions, in full:
1. `[x]`, `[1, 2]` are list literals and appear in comments (`[1, 2, 3, 4].findMap` in std
   tests; prose quotes code).
2. rustdoc accepts the backticked form [cited]; Go uses bare `[Name]` [cited: go.dev/doc/comment],
   but Go has no list literal of that shape.

**D2150. In `stitchwort search` with only `"text"` parts, should a result whose last name
component equals the text rank first?** [Recommended: **yes**, in stage 1b.]
Assumptions, in full:
1. Today `'"filterMap"'` ranks `List.filterMap` 9th of 9, after its theorems [run].
2. It changes ranking only for text-only queries; pattern ranking (D2062–D2064) is untouched.
3. Search's JSON version doesn't change (ranking isn't a field's meaning).

**D2151. Who does the sorting pass?** [Recommended: **a script proposes, Sonnet lanes split each
namespace, Opus reviews; std first, aoc and the roguelike after**.]
Assumptions, in full:
1. The split is judgement (rationale versus behaviour), so DeepSeek is not used for it.
2. About 5,000 blocks in all [measured]; std's 1,945 matter most to other code.
3. The pass changes comments only; `fmt` and the test tiers confirm nothing else moved.

## 10. Other systems

Short, and only what bears on a decision here.

| System | Marker and attachment | Examples | Links | What we take |
|---|---|---|---|---|
| Go | ordinary `//` comments "immediately before top-level … declarations with no intervening newlines"; package comments of several files "are concatenated" [cited: go.dev/doc/comment] | `ExampleF`, `ExampleT_M`, with a lower-case suffix for more; compiled, run only with an `Output:` comment [cited: pkg.go.dev/testing] | `[Name]`, `[pkg.Name]` [cited]; the Go version they arrived in isn't on that page (1.19 [memory]) | the closest model: attachment by position, examples by name (D2135), file docs concatenated (§4) |
| Rust | `///` and `//!` [memory] | doctests in comments [memory] | ``[`Name`]`` resolved "in the scope of the module where the item is defined" [cited: rustdoc linking page] | link form and scope (§7); doctests deferred (D2135) |
| Lean 4 / Mathlib | `/-- -/` docstrings, part of the syntax [memory]; hover shows them [memory]; doc-gen4 builds the site [memory] | separate `example`/`#guard` [memory] | in doc-gen4 [memory] | the missing-doc linters `docBlame` ("checking definition doc strings") and `docBlameThm` (theorems) are separate [cited: Batteries Lint docs]: theorems counted apart, as §6.2 does |
| Haskell | Haddock `-- |` [memory] | `doctest`: "a tool that checks examples and properties in Haddock comments", `>>>` lines [cited: hackage doctest], a separate tool | identifier markup [memory] | a separate example checker drifts from the docs [memory]; another reason for examples by name |
| Idris 2 | `|||` lines, "always before the declaration"; "the first paragraph … is taken to be an overview"; `:doc f` at the REPL [cited: Idris 2 manual] | the manual shows a fence; whether it's checked isn't stated [cited] | – | a summary from the start of the doc; a REPL/CLI command (`doc`) |
| Agda | literate files; HTML of highlighted source [memory] | the checked source itself [memory] | – | nothing for stage 1; the guide already does narrative |

## 11. What was not verified

- The stage 1 output in §5.3 is designed, not run; the theorem order there was computed by hand
  from two search runs.
- Costs (§8) are estimates.
- The cost of re-lexing for an index over a large project was not timed.
- The [memory] cells of §10.
