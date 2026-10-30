# Proposal: `stitchwort search`, lemma search by type

**Status:** draft 1, 30 October 2026. Ticket SW-915, from
[agentic-proving.md](../research/agentic-proving.md) T4 and §7.4, approved as a design note with a
measuring prototype by D2044. The prototype is on the branch, hidden and marked experimental:
`stitchwort dev search` ([§4](#4-the-prototype-and-what-it-measured)). Two decisions are in
[§7](#7-decisions-for-matt).

Labels, as in the other notes:

- **[checked: file:line]**: read in the Stitchwort source or docs, at `ea855ed6` (main when this
  was written) plus the prototype commit;
- **[run]**: run with the release CLI built from this branch on 30 October 2026, under
  `dev/memguard --cap-gb 2` and `timeout 300`. Times are wall-clock milliseconds printed by the
  prototype. **The machine was shared with other lanes** (load average 31–38 during the load-time
  runs), so times vary by up to about 4× between runs; each figure gives the run it came from;
- **[cited: Cn]**: from a card in [agentic-proving.md](../research/agentic-proving.md) §4. No new
  web reading was done for this note;
- **[inferred]**: my reasoning from checked or cited facts;
- **[unverified]**: believed, not confirmed.

## The short answer

- **Lemma search by type is cheap enough to do by brute force.** Loading every std file takes
  4.1 s cold and 0.21 s through the check cache. Matching one pattern by unification against all
  2,328 std theorems takes 20–70 ms. With a filter on the constants the pattern names, it takes
  0.1–0.5 ms [run, §4.2].
- **An index is needed for precision, not speed.** Without the constants filter, unification
  unfolds definitions and matches far too much: `Nat.min ?a ?b ≤ ?a` matches 219 theorems,
  including `Float.Theory.magnitudeBound` at rank 2. With the filter it matches 4, and the right
  lemma is first [run, §4.3]. The filter is Loogle's rule: a theorem must mention every constant
  the pattern names [cited: C7]. It is an in-memory set per theorem, built in about 20 ms. **No
  on-disk index is needed** while the check cache is warm (D2046).
- **The known lemmas were found.** Every lemma the friction notes say was missed or rewritten,
  and a lemma for each of the ticket's example shapes, ranks **first** for a pattern of its shape
  with the filter on (§4.3), except `List.memMap`, third behind two lemmas of the same shape. The
  other gaps are in the prototype and have known fixes: `_ ++ _` needs a
  typed hole, and a named hole under a binder isn't compared.
- **Design:** `stitchwort search 'PATTERN'`, with:
  - `_` holes, `?x` named holes, and `⊢` for the conclusion only;
  - `"name"` substrings, and bare lowercase names as named holes;
  - folded unification that solves from call arguments, under a per-theorem budget, after the
    constants filter;
  - all of std plus the project; ranking by place, then specificity, then name;
  - human output, and `--json` with name, type, file:line and the `import` line.
- **Stage 2:** try the candidates at a `?` and report the ones that close it, as `exact?` does. It
  needs structured goals (agentic-proving.md T3) first (§3.9).

## 1. The problem, with our evidence

**The lanes found lemmas only with grep, and twice rewrote lemmas std already had.**

- Day 7 of AoC 2024: "finding `tailOf`, not `tail`, took a grep"
  [checked: aoc/NOTES-2024.md:373].
- Day 24: "I first wrote `compareSelf` and `lessNotGreater` too, then found std's
  `Ord.compareSelf` and `Ordering.lessNotGreater` by grepping the std sources; with no search by
  type, a lemma is easy to miss" [checked: aoc/NOTES-2024.md:7906–7909]. agentic-proving.md §5
  cites this as 7876–7880; the notes have grown since, and the quote is now at 7906.
- Missing std lemmas and functions are the largest friction category: about 40 recorded items
  (agentic-proving.md §5, row A). Some were truly missing; for the rest, the notes don't say
  whether a search would have found them.

**Agents elsewhere lean on search.**

- mini-Lean-agent's most useful single step was `exact?` returning a lemma [cited: C1].
- VeruSAGE: removing vstd and the cheat checker together cost 26%, 24% and 9% of solved tasks.
  o4-mini "hallucinat[ed] about which lemma functions actually exist" [cited: C20].
- Ax-Prover's agents called `lean loogle` 5.88 times per run on average [cited: C8].

**A grep session against a search session.** These are three needs from the notes and the
ticket, each tried both ways on std [run]:

| Need | grep over `crates/elab/src/std` | prototype |
|---|---|---|
| "the length of `xs ++ ys`" | `grep -rn "^theorem.*length (.* ++ "` finds **nothing**: std writes `List.append` in statements. Knowing to grep `List.length (List.append` finds `lengthAppend` and `lengthSnoc` | `'List.length ((_: List _) ++ _) = _'`: `List.lengthAppend`, then `List.lengthSnoc` |
| "`compare x x` is `Equal`" | `grep -rnE "compare (\w+) \1"` is an error in this shell's grep (ugrep: "invalid escape"). `grep "compare x x"` works only if the variable is named `x` | `'Ord.compare ?x ?x = _'`: `Ord.compareSelf` first, of 38 |
| "`count` is monotone in the predicate" | `grep -rn "^theorem.*List.count .* ≤ List.count"` finds **nothing**: `countLeMem`'s conclusion is on the line after `theorem` (SortLemmas.sw:1346–1347) | `'List.count ?xs _ ≤ List.count ?xs _'`: `List.countLeMem`, the only match |

Grep needs the name, or the exact spelling and line layout of the statement. Search needs only
the shape.

## 2. What others do

Lean's tools are the model. No other language's search was read for this note.

- **Loogle** [cited: C7]:
  - It searches Mathlib "by constant, lemma name, subexpression, type, or conclusion", e.g.
    `(List.replicate (_ + _) _ = _)`.
  - Holes are `_`, and named holes `?a` must match the same term:
    `(?a -> ?b) -> List ?a -> List ?b`.
  - `|- tsum _ = _` restricts the match to the conclusion.
  - A query's comma-separated parts must all hold: constants, `"name"` substrings and patterns.
  - It has a CLI with `--json`, and an on-disk index that "quietly rebuilds … whenever the
    underlying .oleans change". Auto-generated declarations are hidden.
  - The card doesn't record Loogle's ranking or its exact matching algorithm. This note doesn't
    rely on them.
- **`exact?`** [cited: C1, C3]: at a goal, it tries library lemmas whose conclusion fits and
  offers a "Try this" edit. lean-lsp-mcp exposes it as `lean_code_actions`. mini-Lean-agent ran
  it in a scratch file and used the lemma Lean suggested.
- **lean-lsp-mcp** [cited: C3] wraps Loogle, LeanSearch, Lean Finder and premise search. It also
  has a local search (ripgrep plus the server's symbol index) "to confirm declarations actually
  exist and prevent hallucinating APIs".
- **VeruSAGE** [cited: C20] gave a generic coding agent the vstd *source* to search. Removing it
  (together with the cheat checker) cost up to 26% of tasks.

What to take:
- Loogle's query language, nearly whole. It is small and agents already know it from Lean.
- The constants rule (§3.3).
- JSON output.
- The `exact?` step as stage 2.

What not to take yet: an on-disk index that rebuilds itself (D2046), and natural-language search
(LeanSearch and the like), which needs a model.

## 3. The design

### 3.1 Pattern syntax

`stitchwort search 'PART, PART, …'`. Every part must hold.

| Part | Meaning |
|---|---|
| `"text"` | the theorem's full name contains `text` (`"tail"`) |
| `List.length` (a bare name) | the type mentions this definition (Loogle's constant search) |
| a pattern with `_` | some subterm of the type, a hypothesis, or the conclusion is an instance of it |
| `⊢ pattern` (or `\|- pattern`) | the conclusion is an instance of it |
| `?x` | a named hole: every `?x` matches the same term, and different names match different terms (§3.3) |
| a bare lowercase name not in scope (`a`, `xs`) | a named hole, as `?a`. So `Nat.min a b ≤ a` can be pasted from a goal. A misspelt *qualified* name is still an error |

The pattern is elaborated as an expression, in a scope that imports every std namespace and the
project's namespaces, so `List.length` and `Nat.min` resolve without imports [run: the prototype
does this with one `import Std (…)` line, search_dev.rs:139].

**Overloaded operators need a fallback.** `List.length (_ ++ _) = _` fails today:
"`++` joins two texts or two lists … this is a `?1`" [run]. The operator picks `Text.append` or
`List.append` from the operand's type, and reports an error when that is unknown
[checked: crates/elab/src/check.rs:3680–3697]. In a pattern, an overloaded operator with an
unknown operand type should try each resolution (List, then Text), run the search for each, and
merge the results. The prototype needs `(_: List _) ++ _` instead.

### 3.2 What is searched, and how each theorem is opened

- **Candidates**: every final, named definition with `theorem` set
  [checked: crates/core/src/globals.rs:26–52; crates/driver/src/audit.rs:125–134 does the same
  walk]. Names with `%` (helpers) are skipped. With `--defs`, definitions are searched as well
  (for "a function `List a → List a`").
- **Types** are the stored elaborated `Def::ty` (a term), and are evaluated with gluing on, so
  calls stay folded (docs/proposals/folded-calls.md).
- **Opening**: each Π binder, implicit and explicit, becomes a fresh unknown. That includes type
  parameters, `[auto …]` arguments (instance dictionaries and decision proofs) and explicit
  variables. The *targets* are, in order:
  1. **whole**: for a pattern that is a function type, the type after its leading implicit
     binders;
  2. **conclusion**: the type with every binder opened;
  3. with no `⊢`, each **explicit hypothesis**;
  4. with no `⊢`, each **call inside** the conclusion or a hypothesis (not under a further
     binder) whose head is the pattern's head.
- **Implicit and `auto` arguments**: in the pattern, an implicit or auto argument that
  elaboration doesn't solve is left an unknown, not an error. The theorem's instance argument
  then solves it: `Nat.min _ _ ≤ _` leaves `≤`'s dictionary open, and it unifies with whatever
  the theorem has. The pattern is never sent to `auto`. A pattern can't usefully pin an instance,
  and searching for "the `Ord` instance of `Nat`" is not a lemma search.
- **A conclusion that is a bare theorem variable** (`(p: Prop) (h: p): p`) matches everything,
  so it is skipped [run: search.rs:256].

### 3.3 Matching: unification on folded types, after a constants filter

**The filter.** A theorem is unified with only if its type mentions every definition the
elaborated pattern mentions. That is Loogle's rule [cited: C7]. Both sides are read back folded
(`quote_folded`), so a field such as `Ord.compare`, which elaborates to the helper
`Ord.%compare`, is named the same way on both. The stored term alone doesn't always name it;
that cost the prototype `Ord.compareSelf` until both sides were read back the same way [run].
The filter is what makes results precise (§4.3).

**The unification.** The pattern's value is unified with each target by
`unify_solving_arguments`:
- Two calls of the same definition are equal if their arguments are, and the solutions that
  come from the arguments are kept [checked: crates/elab/src/unify.rs:194–206, 1112–1135].
- Without it, `same_arguments_solving_nothing` falls back to comparing the calls' unfoldings,
  which loses the folded shape the pattern was written in.
- Every attempt runs inside a fresh resource budget of 200,000 steps
  [checked: search.rs:25 `ATTEMPT`]. Running out counts as no match: 3 of the 2,328 std
  theorems run out for every unfiltered pattern [run].
- Each attempt is undone: its solutions go back off the trail, and its unknowns are dropped. The
  prototype calls `undo_since` (made `pub(crate)`) and truncates the unknowns.

**How far to unfold: as far as the unifier does under the budget, but only for theorems that
pass the filter.** Unfolding is what lets `Ord.compare ?x ?x` (a field of an instance) match.
Unfolding a theorem that doesn't share the pattern's constants is how the false matches arise:
- `≤` on `Nat` computes to a `Bool` equation, so `Nat.min ?a ?b ≤ ?a` against
  `Finite.check`'s conclusion `p x = True` solves `p` higher-order and "matches";
- `Effect.bindIn`'s `{row} b` unfolds to a function type and "matches" `List ?a → List ?a`.

All of these are filtered out [run, §4.3]. Unfolding is deliberately not made shallower inside
the filter. A theorem that passes the filter and needs unfolding to match is usually a genuine
instance.

**The lossy rule isn't a source of false matches.** The rule is the one the unifier notes in
`LOSSY`: "equal arguments are enough for equal calls, not needed for them, so for a definition
that isn't injective such a solution is one of several"
[checked: crates/elab/src/unify.rs:99–106]. For search that direction is sound. If the
arguments unify, the two calls are equal, so the theorem really does state an instance of the
pattern. What the rule can lose is a match whose arguments differ but whose calls compute to
the same thing. That is a missed result, not a wrong one, and the filter would usually have
dropped it anyway [inferred]. A wrong match can come only from unfolding, which the filter
bounds, or from identifying the theorem's own variables, which the next rule bounds.

**Named holes.** All occurrences of `?x` are unified with each other after the match. Different
named holes must stay different: if `?a` and `?b` end up as the same unknown, the match is
rejected. So `Nat.min ?a ?b ≤ ?a` finds `minLeLeft` and not `minLeRight` with `m` and `n` made
one. Without this rule the prototype returned both [run]. A named hole inside a binder of the
pattern (`List ?a → List ?a`, where the second `?a` is under the arrow's binder) is an unknown
applied to that variable. The prototype doesn't compare those yet, and returns nothing for that
query [run]. The real version should compare such holes after instantiating the binder.

**Specificity**, used for ranking [run: search.rs, `Hit`]:
- *absorbed*: what the theorem's own variables had to become. Each variable solved to a term
  counts that term's size, and each variable made the same as another counts 1. A general
  `x = x` lemma absorbs a whole side; `Graph.notGreaterOfThen` absorbs `Less` for
  `⊢ Not (Less = Greater)`.
- *instantiated*: how many of the pattern's holes had to become more than one of the theorem's
  variables. `lengthAppend` fills one hole (the right side) and `lengthSnoc` fills two
  (`[x]` and the right side).

### 3.4 Scope

- **All of std**, loaded eagerly. `load_all_libraries` exists, as the test-only "eager `Std`"
  mode [checked: crates/elab/src/library.rs:998–1006], and `audit Std` already uses it outside
  tests (SW-912). Lazy loading stays the default for checking; only `search` loads everything.
  It goes through the check cache, whose units include library files
  [checked: crates/driver/src/check_cache.rs:6]. That gives 0.21 s warm against 4.1 s cold [run].
- **The project**: its namespaces, loaded as `audit` loads them with no targets
  (`Target::Everything`), through the project's cache [checked: crates/cli/src/main.rs, `audit`].
  With a file argument instead: that file, as `check FILE` does.
- **Hidden by default**: `%` helpers, generated declarations, and theorems named `…Example`
  (111 of std's 2,282 `theorem` lines [run: grep]). They are closed `rfl` checks, not lemmas.
  `--all` shows them.
- **Not searched**: unfinished declarations (`?` in their closure). They can't be used: a use is
  itself unfinished [checked: agentic-proving.md §6, docs/syntax.md:1229–1230].

### 3.5 Ranking

In order, each a tie-breaker for the one before:
1. **place**: whole, then conclusion, then hypothesis, then inside. A lemma *about* the shape
   beats one that merely *uses* it;
2. **absorbed**, ascending;
3. **instantiated**, ascending;
4. **project before std**. The project's own lemmas are the ones a lane is likeliest to want, or
   to have duplicated. The ticket suggested std first; I put the project first for that reason,
   and it changes nothing for std-only searches;
5. **shorter full name**, then the name.

Name hits (`"text"`) rank an exact final-component match first.

### 3.6 Output

Human (default), one result per two lines, at most 10 (`--limit N`):

```
 1. Std.List.lengthAppend : [a: Type] → (xs: List a) → (ys: List a) → List.length (List.append xs ys) = List.length xs + List.length ys
    std/List/Lemmas.sw:5  import Std (List)
2 matches
```

`--json`, in the shape of `audit --json` (a `version`, the results, a summary;
[checked: crates/cli/src/main.rs, `print_audit`]):

```json
{"version": 1, "query": "...", "results": [
  {"name": "Std.List.lengthAppend", "short": "List.lengthAppend",
   "type": "[a: Type] → (xs: List a) → …", "file": "std/List/Lemmas.sw", "line": 5,
   "import": "import Std (List)", "place": "conclusion",
   "absorbed": 0, "instantiated": 1}],
 "total": 2, "shown": 2}
```

- `file` is what `stitchwort std-source` takes, so an agent can read the proof. The prototype
  prints `<prelude>:N` for the core: the real version maps it back to `core/<File>.sw`.
- `import` is the line to add. It is null for a project namespace already imported, or for
  prelude names that need none.
- The type is printed with the hover printer. That prints `List.append xs ys`, not
  `xs ++ ys` [run]. Printing operators back is the printer's job and isn't needed here.

### 3.7 CLI shape

```
stitchwort search 'PATTERN' [--project DIR | FILE] [--json] [--limit N] [--defs] [--all]
```

- Exit 0 with results, 1 with none, and 2 for a pattern that doesn't elaborate (printed as a
  diagnostic against the pattern text, as the prototype does).
- It sits beside `check`, `audit` and `axioms`, a CLI with JSON output, as D2041 decided.

### 3.8 The language server (optional)

- A custom request `stitchwort/search {pattern}` returning the JSON results, for an editor
  command palette.
- Workspace symbols already search by name [checked: crates/cli/src/lsp.rs:83–100].
- Stage 2's results fit a code action at a `?`, as `lean_code_actions` exposes `exact?`
  [cited: C3]. The server has no code actions today, so this is optional and after stage 2.

### 3.9 Stage 2: what closes this `?`

`stitchwort search --at FILE:LINE:COL` (or, later, `check --suggest`):
1. Take the goal at the `?`: hypotheses and target, from the structured goal (T3, being built in
   `goals.rs` and `nav.rs`).
2. Candidates: theorems that pass the filter for the target's constants, and whose
   **conclusion** unifies with the target, with the theorem's binders opened as unknowns and the
   goal's locals rigid. This is §3.3 with the pattern's holes replaced by the goal's own terms.
3. For each candidate, in rank order, fill its remaining explicit hypotheses:
   - from a hypothesis in scope of the right type (unification);
   - else from `auto`'s decision procedures;
   - else leave it as a `?`.
4. Elaborate the term `lemma _ … h …` against the goal in a transaction (`undo.rs`), and
   kernel-check it.
5. Report "closes it" (no `?` left) first, then "closes it with N new goals", and give the text
   to paste.
6. Stop after a budget, by default the first 50 candidates.

It can't make a proof wrong: anything it suggests is checked as written, like any other proof.
It belongs with proof-automation.md T5's "try automation at each `?`" pass, and can share its
flag [inferred].

## 4. The prototype, and what it measured

### 4.1 What it is

Kept on the branch, hidden, and marked experimental (not dropped to a patch):

- `crates/elab/src/search.rs` (new):
  - `search_pattern` elaborates a pattern and keeps its holes as unknowns;
  - `type_constants` computes the constants filter;
  - `search_one` opens and matches one theorem, undoes the attempt and scores it;
  - `rank` sorts the hits.
- `crates/cli/src/search_dev.rs` (new): `stitchwort dev search PATTERN [--limit N] [--no-filter]
  [--defs] [--json] [--repeat N] [--cache-dir DIR]`. It prints timings and counts on standard
  error.
- Three one-line edits:
  - `mod search` in crates/elab/src/lib.rs;
  - `undo_since` made `pub(crate)` in unify.rs;
  - the `Dev::Search` variant and its dispatch in crates/cli/src/main.rs.
  None of the files other lanes are changing is touched.

It searches std only, not a project. It handles `_`, `?x`, `⊢` and `"name"`. It has no operator
fallback and no hiding of examples. It compares named holes only at the top level.

To run the queries: `docs/proposals/search/queries.sh [CACHE_DIR] [--no-filter]`.

### 4.2 Cost

| Step | Time | Run |
|---|---|---|
| Load every std file, cold (no cache) | **4.08, 4.08, 4.14 s**; process 4.42–4.44 s; peak memory 0.15 GB | 3 runs, load average 38 |
| Load every std file through the check cache (warm) | **0.21 s** (209–210 ms); process 0.58 s | 3 runs, same load; cache 38 MB |
| Enumerate the candidates | 2,328 theorems (3,572 with definitions) in 0.2–0.3 ms | every run |
| Constants filter, built for every candidate (evaluate and read back folded) | 19 ms quiet; 22–118 ms under load | run 2; run 3 |
| The same from the stored term only (syntactic) | 2–5 ms, but misses `Ord.%compare` | run 1 |
| Elaborate a pattern | 0.0–0.1 ms | every run |
| **Match one pattern against all 2,328 theorems, unfiltered** | **20–72 ms** median of 5, 2,288–10,134 unifications | run 3 `--no-filter` |
| **Match with the constants filter** | **0.1–0.5 ms** median of 5, 1–196 unifications | run 2 |
| `_ = _` (nothing to filter on: 2,083 matches) | 38 ms quiet, 156 ms under load | runs 2, 3 |

The cold load is std's elaboration, the same work as `audit Std`, which took 5.0 s. That cache
is invalidated by a compiler rebuild or a std edit, which is when a lane in this repository would
pay it.

### 4.3 The queries, and where the known lemma ranks

All with the filter on, from run 2 [run]. "Known" means a lemma named in the friction notes, or
one I looked up by grep for the ticket's examples.

| Query | Matches | Known lemma: rank | Unfiltered: matches, known lemma's rank |
|---|---|---|---|
| `List.length ((_: List _) ++ _) = _` | 2 | `List.lengthAppend`: **1** (`lengthSnoc` 2) | 168, **1** (then `padRightLength`, `lengthSnoc`, `Text.lengthAppend`) |
| `List.length (_ ++ _) = _` | error: `++` needs its operand's type (§3.1) | n/a | n/a |
| `List.length ((_: List _) ++ _)` (anywhere) | 17 | `lengthAppend`: **1** | 122, 1 |
| `_ ∈ List.map _ _` | 17 | `List.memMap`: **3** (after `memMapOfSub` and `memMapFilterMap`: same place and specificity, shorter-name tie-break) | 103, not recorded |
| `⊢ _ ∈ List.map _ _` | 5 | `memMap`: **3** | 18, not recorded |
| `Nat.min ?a ?b ≤ ?a` | 4 | `Nat.minLeLeft`: **1**; `minLeRight` correctly excluded | 219, **1**, then `Float.Theory.magnitudeBound`, `Finite.check`, … |
| `Nat.min _ _ ≤ _` | 5 | `minLeLeft` **1**, `minLeRight` **2** | 235, 1 |
| `Ord.compare ?x ?x = _` (day 24's `compareSelf`) | 38 | `Ord.compareSelf`: **1** | 105, 1 |
| `⊢ Not (Less = Greater)` (day 24's `lessNotGreater`) | 6 | `Ordering.lessNotGreater`: **1** | 6, 1 |
| `List.count ?xs _ ≤ List.count ?xs _` | 1 | `List.countLeMem`: **1** | 161, 1 |
| `List.zip ?xs (List.tailOf ?xs)` (day 7) | 1 | `List.zipWithNextZip`: **1** | 6, 1 |
| `"tailOf"`, with definitions (day 7) | 1 | `List.tailOf`: **1** | n/a |
| `List _ → List _`, with definitions | 239 | `List.tailOf`: **7** (after `init`, `sort`, `dedup`, `pairs`, `tails`, `attach`) | n/a |
| `List ?a → List ?a`, with definitions | 0 | missed: the named hole under the arrow (§3.3) | n/a |

**What the table says** [inferred]:
- The filter is what makes results usable. Unfiltered, the known lemma still ranks first in
  every row where its unfiltered rank was recorded, but in most rows among 100–235 matches, most of them false
  matches through unfolding.
- `memMap` ranks 3rd behind two lemmas that conclude the same shape. Telling them apart needs
  the hypotheses: `memMap` needs one, `memMapOfSub` two. Ranking by fewer explicit hypotheses
  is a cheap next tie-breaker to try.
- A type pattern for a *function* (`List _ → List _`) finds dozens of candidates. Name parts are
  what make function search useful; `"tail", List _ → List _` would give a short list.

### 4.4 Is an index needed?

- **For speed: no.** Even unfiltered, matching is 20–72 ms against 4,100 ms of cold load or
  210 ms of warm load. A project adds its own theorems, a few hundred in aoc
  (agentic-proving.md §7.4), so about 10–20% more matching [unverified: not measured on a
  project].
- **For precision: yes, a constants set per theorem.** It is built in memory when the search
  starts, about 20 ms for std. Loogle's head-symbol and constant indexes do the same job
  [cited: C7]. The prototype's subterm targets (§3.2 item 4) already use the head symbol as a
  filter.
- **On disk: not now** (D2046). It would only save the cold 4 s, which the check cache already
  saves whenever it is warm. Each entry would need a key that changes when std or the compiler
  changes: the content hash of each declaration (`def_hash`,
  [checked: crates/core/src/hash.rs:90]) or the check cache's own unit key.

## 5. Risks

- **False matches through unfolding** (§4.3), if the filter is weakened. A pattern that names no
  constant (`_ = _`) can't be filtered: it matches 2,083 of 2,328 theorems, which is correct and
  useless. Warn when a pattern names no constant.
- **Missed matches.**
  - The lossy rule misses a match whose calls are equal but whose arguments differ (§3.3).
  - The budget gives up on 3 std theorems [run].
  - An instance whose field names elaborate differently in a pattern than in a stored type was
    missed until both sides were read back folded. More such cases may exist: compare the two
    readings in a test (§6).
- **Pattern elaboration differs from checking.** Unsolved implicits and dictionaries are kept as
  holes, and the pattern is never sent to `auto` (§3.2). The pattern path must not touch
  checking state: the prototype clears unknowns before and after
  ([checked: crates/elab/src/lib.rs `clear_metas`]), and stage 1 should run it in its own
  session.
- **The cold load after a compiler rebuild** (4 s, more under load) may make agents give up on
  search after an std edit. Print "loading the library (first search after a rebuild)" on
  standard error when the cache misses.
- **Ranking is heuristic.** It was tuned on these 14 queries, which is overfitting by
  construction. Keep the ranking fields in the JSON, so callers can see why, and collect real
  queries from lanes before tuning further.
- **Unfinished project theorems** are hidden, so a lane can't find the lemma it is still
  proving. That is intended.

## 6. Stage plan and tests

| Stage | What | Tests |
|---|---|---|
| **S1** | `stitchwort search` over std plus project, from this prototype: the §3.1 syntax including `"name"`, bare-name holes and the operator fallback; the filter; named holes under binders; hiding of examples; the ranking; human and `--json` output; `<prelude>` mapped back to `core/` files | (a) a golden test of the §4.3 queries: the known lemma at rank 1, or within the top 3 for `memMap`; (b) for every std theorem T, the pattern made from T's own conclusion, with its variables as holes, finds T (self-retrieval over 2,328 theorems: catches filter and reading-back mismatches such as `Ord.%compare`); (c) named-hole distinctness (`minLeRight` excluded); (d) a pattern that doesn't elaborate is exit 2 with a diagnostic; (e) JSON schema snapshot; (f) the search leaves a session it shares unchanged (unknowns and trail lengths before and after) |
| **S2** | `search --at FILE:LINE:COL`: the §3.9 "what closes this `?`", after T3's structured goals land | for a set of std theorems, replace the proof by `?` and check that the theorem's own proof lemma, or one that closes it, is offered first; every suggestion re-checks when pasted |
| **S3** | optional: the LSP request and the code action at `?`; JSON in the agent guide (T7); an on-disk index only if D2046's revisit condition is met | LSP round-trip test |

Tier: S1's golden and self-retrieval tests are lane-tier. Self-retrieval over all of std costs
about 2,328 × 0.2 ms ≈ 0.5 s matching, plus the warm load [inferred from §4.2].

## 7. Decisions for Matt

**D2045. Should `search` match only theorems that mention every definition the pattern names
(Loogle's rule), and unify only with those?** Recommended: **yes**.

The assumptions, in full:
1. Agents and people write a pattern with the definitions they care about named (`List.length`,
   `Nat.min`) and the rest as holes. A theorem that never mentions a named definition is not what
   they asked for, even if it unifies after unfolding. Loogle makes the same assumption
   [cited: C7].
2. The definitions are compared after evaluating and reading back folded, on both the pattern
   and the theorem. On the 14 queries of §4.3 this found every known lemma. Fields of instances
   (`Ord.compare` as `Ord.%compare`) and other elaboration differences can still make a theorem
   look as if it lacks a definition it has, and S1's self-retrieval test (§6) is what checks
   that.
3. Unification under a 200,000-step budget is the matching relation inside the filter. It is
   allowed to unfold definitions, solve from call arguments (the lossy rule, sound for search,
   §3.3) and open every binder of the theorem, implicit and `auto` ones included.
4. Without the filter, matches through unfolding outnumber real ones (168–235 against 1–5 in
   §4.3). The measured cost of the filter is about 20 ms per search to build.
5. A pattern that names no definition (`_ = _`, `(_: Nat) ≤ _`) is searched unfiltered, with a
   warning.

**D2046. Should `search` load all of std through the check cache for every run, and build its
filter in memory, with no on-disk search index for now?** Recommended: **yes**. Revisit if lanes
report that cold searches (after a compiler rebuild or an std edit) are frequent, or if a
project's theorems push matching past about 100 ms.

The assumptions, in full:
1. Load times on this machine under load: 4.1 s cold, 0.21 s warm through the check cache;
   matching 0.1–0.5 ms filtered and up to 72 ms unfiltered (§4.2). A quiet machine would be
   faster, not slower.
2. The check cache already stores each library file's checked declarations
   (check_cache.rs:6), and is invalidated exactly when an index would be: a compiler rebuild or a
   change to the file. So an on-disk index would save only the cold case, which the cache's own
   next run also fixes.
3. Loading everything is only for `search` (and `audit Std`). Checking keeps lazy loading
   (docs/proposals/std-library.md §4.0).
4. A project's theorems, a few hundred in aoc, add matching time in proportion to their number
   (unmeasured), and nothing to std's load.
5. The memory peak of 0.15 GB with all of std loaded [run] is acceptable for a CLI command
   under the 2 GB lane cap.

## 8. What was not verified

- **Projects.** The prototype searches std only. Neither project load time nor project theorem
  counts were measured for search.
- **Stage 2** was not prototyped. Its cost (elaborating up to 50 candidate terms per `?`) is
  unmeasured.
- **Loogle's ranking and its exact matching rule** (instantiation of the lemma only, or two-way
  unification) are not in card C7, and this note doesn't depend on them. §3.3's rule (two-way
  unification, with named-hole distinctness and the filter) is this note's own.
- **Quiet-machine timings.** Every time here was taken with other lanes running. The cold-load
  figure (4.1 s) agrees with `audit Std --no-search` (5.0 s total) on the same machine.
- **Whether the ranking generalises** beyond the 14 queries it was looked at with (§5).
- **The overloaded-operator fallback** (§3.1) and **comparing named holes under binders**
  (§3.3) are designed, not built.
