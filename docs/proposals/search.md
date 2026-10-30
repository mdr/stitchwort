# Proposal: `stitchwort search`, lemma search by type

**Status:** draft 3, 30 October 2026. Ticket SW-915, from
[agentic-proving.md](../research/agentic-proving.md) T4 and §7.4. Draft 1 (D2044) compared only
Lean's tools; draft 2 (D2052) compared the wider field and measured the design with the prototype
`stitchwort dev search`; an external reviewer read it
([search/review-1.md](search/review-1.md), from the brief
[search/review-brief.md](search/review-brief.md)) and approved it with changes. Matt accepted
D2054–D2056 and decided D2062 and D2063 (30 October). Draft 3 folds in those decisions and the
review, measures what changes, and gives the staged plan. Stage 1 is not started: Matt reads this
draft first. New decisions are in [§10](#10-decisions-for-matt).

Labels:

- **[read: Sn]**: from source card Sn in [§2](#2-what-others-do-the-cards). §2 is draft 2's
  reading record, unchanged: draft 3 read no new outside source;
- **[review: §n]**: from the external review, [search/review-1.md](search/review-1.md), read in
  full for this draft. The review cites Lean's online documentation for `exact?`,
  `solve_by_elim` (default depth 6) and the "star" fallback; those pages were **not read** here,
  so they support nothing beyond what S8 already says;
- **[cited: Cn]**: from a card in [agentic-proving.md](../research/agentic-proving.md) §4;
- **[checked: file:line]**: read in the Stitchwort source, at `547b54f8` plus this branch;
- **[run]**: run with the release CLI built from this branch on 30 October 2026, under
  `dev/memguard --cap-gb 2`. The machine was shared with other lanes (load average 11–20 during
  the runs), so every time is approximate and varies between runs; counts (queries, matches,
  unifications) do not;
- **[inferred]**: my reasoning from the above; **[unverified]**: believed, not confirmed.

## The short answer

- **Three match relations, as D2062 decided, and they help.** Each match is labelled
  `instance` (the theorem instantiates to the pattern: only the theorem's variables took
  structure), `generalisation` (the pattern's holes took the theorem's structure, the theorem's
  variables stayed variables) or `commonInstance` (both did; ranked last, labelled weak). Ranked
  relation first, then place, then draft 2's keys, the wanted theorem comes first (strict, ties
  broken by name as a client sees them) for 87.8% of std's conclusions, 80.5% of equation left
  sides and 38.3% of lemma uses in std's proofs, against 87.1%, 79.5% and 36.5% for draft 2's
  ranking on the same matches [run, §6].
- **One refinement: a written `_` may take any structure.** If a `_` taking structure counted
  against the relation, `Ord.compare ?x ?x = _` would rank `Ord.compareSelf` third, behind
  lemmas whose conclusion is a bare `x = y`, because `_ := Equal` would make it a generalisation.
  Only named holes, and every hole of a pattern made from a goal, decide the relation; then all
  five of draft 1's hand queries rank their lemma where draft 2 did, and `Nat.leTrans` is first
  (was second) for the transitivity pattern [run, §6.3]. This is D2064.
- **The higher-order misses were a skip rule, not unification.** Draft 2 skipped any target whose
  head is one of the theorem's own variables (`p x`). Trying them (the unifier already has
  higher-order pattern solving and a first-order approximation) finds all 13 conclusions and all
  17 left sides draft 2 missed, for 0.5% more unifications [run, §6.1]. No new matching
  algorithm is needed for these; full higher-order unification is not proposed.
- **Two-way unification is not always most general.** For 146 conclusions the theorem matched
  its own statement only as a generalisation until a one-way retry (the pattern's holes frozen)
  found the instance match. So the relation needs that retry, not just a reading of two-way
  unification's solution [run, §5.1].
- **A new benchmark, from proofs.** Each of the 5,350 (proof, lemma) pairs in std's proofs
  (8,089 uses) gives a query: the statement the lemma proved there, with the proof's variables as
  holes. It is far harder than self-retrieval, and it shows that **the constants filter loses
  most of these lemmas**: without a second pass, 2,760 of 5,173 queries lose the lemma to it,
  because the goal names constants the lemma doesn't (§6.2). The relaxed second pass (D2063)
  brings the lemma back in 2,195 queries: found 25% → 68%, strict top-1 19% → 38%. Without any
  filter, 79% are found and 39.3% come first, at about 1.5 times the time.
- **Stage 2 must treat a goal's variables as rigid, and its filter must differ.** Searching a
  goal is the proof-use benchmark's situation. The filter's rule ("the theorem names everything
  the pattern names") is wrong for it: a lemma that instantiates to a goal names fewer constants
  than the goal. Stage 2 searches unfiltered, or with the conclusion's head only (D2066).
- **Data types in the filter (D2054)**: measured now. Lossless on self-retrieval, and it halves
  the conclusions benchmark's time (624,431 → 225,782 unifications); on proof uses it loses 96 more
  lemmas to the filter [run, §6].
- **`--rewrite` with `Iff`**: 32 std theorems conclude with an `Iff`; each one's left side
  finds it [run]. Conditional equations were already candidates;
  their premises are counted in `premises`.
- **SW-919 (the evaluation panic) is still hit**: 4 pairs on the filtered conclusions benchmark,
  12 unfiltered; 80 on the proof-use benchmark with its relaxed pass. Stage 1 ships only after
  SW-919 is fixed (§8).
- **The plan**: stage 1 is the real `stitchwort search` command (JSON version 1, std and the
  project, tests, docs in syntax.md) in four steps; stage 2 is first-class, returns candidates
  that leave goals, in four classes (§8).

## 1. The problem, with our evidence

Unchanged from draft 2, in brief:

- Lanes found lemmas only with grep, and twice rewrote lemmas std already had:
  "finding `tailOf`, not `tail`, took a grep" [checked: aoc/NOTES-2024.md:373]; "I first wrote
  `compareSelf` and `lessNotGreater` too, then found std's `Ord.compareSelf` and
  `Ordering.lessNotGreater` by grepping the std sources; with no search by type, a lemma is easy to
  miss" [checked: aoc/NOTES-2024.md:7906–7909] (draft 2's check; not re-read for draft 3).
- Missing std lemmas are the largest friction category, about 40 items (agentic-proving.md §5,
  row A).
- Agents elsewhere lean on search: mini-Lean-agent's most useful single step was `exact?`
  [cited: C1]; Ax-Prover's agents called Loogle 5.88 times a run [cited: C8]; removing vstd and
  the cheat checker together cost VeruSAGE up to 26% of tasks [cited: C20].
- Grep needs the name or the exact spelling and line layout.
- Argument order: `List.map _ (List.map _ _)`, the Lean and Haskell order, is a type error in
  Stitchwort, whose `List.map` takes the list first [run, draft 2].

## 2. What others do: the cards

Draft 2's reading record, unchanged (draft 3 read no new outside source; see the labels above).

**Reading record.** Systems compared: 7 (Hoogle, Idris 2, Rocq, Isabelle with Sledgehammer's
filters, Lean 4 with Mathlib, natural-language and premise-selection search, Agda). Sources read
in full: 17; in part: 10; not read: 6 (listed below). WebSearch calls: 3. Everything else was
fetched from known URLs (GitHub raw files, arXiv, authors' pages) into the lane's scratch folder.
No paywalled paper is needed: every public copy was found.

The cards follow agentic-proving.md's register: claim, what to take, full text, sections read.

**S1. Hoogle (Haskell).** Source `src/Output/Types.hs` and `src/Action/Search.hs`, README
([GitHub](https://github.com/ndmitchell/hoogle), master); N. Mitchell, *Hoogle Searching
Overview* (blog, June 2020); *Hoogle: Finding Functions from Types* (slides, TFP, 16 May 2011).

*Claim:*
- Type search is two passes. Each distinct signature (about 150K in Stackage) has an 18-byte
  fingerprint: arity, number of names, and its three rarest names. A scan picks the 100 best
  fingerprints; a union-find unification then ranks those (Types.hs `searchTypes`,
  `matchFingerprintEx`, `matches`).
- Costs are hand-set numbers: a rare name the query has and the answer lacks costs up to 5,000, a
  common one 400; an answer with one argument fewer than the query 1,000, one more 300; each
  extra class constraint on a
  type variable 3; unification work counts 500 per step.
- Argument order: only a two-argument query is also tried with its arguments swapped
  (`permuted`); a query is also tried with `Maybe` around its result (`partial`).
- History (slides): five designs — alpha-equality, unification, edit distance, structural edit
  distance, fingerprints. "Unification … Works OK, but not great, in practice … Not what humans
  want": `a` matches everything. Edit costs were first made up by hand, which "did not scale at
  all"; then a list of example searches with ordered results, added "when someone complains",
  became constraints for a solver. "1/6 of searches are type based."
- Blog: version 5 is "O(n) but small-constant" over a memory-mapped file rebuilt nightly, because
  version 4's elaborate index "required a lot of babysitting" and had "corner cases which have
  terrible complexity".

*Take:* the regression list of real queries with their wanted order, as the way to tune
tie-breaks; the linear scan with a cheap prefilter (what draft 1 does); rarity as a prefilter
signal, not necessarily a ranking one (§6.1).

*Full text:* read in full (Types.hs, the blog post, the slides); Search.hs and the README in
part (the search dispatch and the search syntax).

**S2. Idris 2 `:search`.** Source `src/Idris/REPL.idr` (`TypeSearch`), `src/Idris/REPL/Common.idr`
(`equivTypes`), `src/Idris/REPL/FuzzySearch.idr`, the `:s`/`:fs` help in `src/Idris/Parser.idr`
([GitHub](https://github.com/idris-lang/Idris2), main).

*Claim:*
- `:search` elaborates the query, binds its free names as Π parameters (`piBindNames`), keeps
  the definitions whose arity is the same, and unifies the whole types; a match is one that
  leaves no constraints and no holes. No ranking: the context's order. No reordering, no
  subterm search, no index.
- `:fs A B -> C` ("fuzzy search") keeps definitions with every name of `A` in some argument and
  every name of `C` in the result: a constants filter split by position.
- Proof search at a hole is a separate command (`:ps`, `TTImp/Interactive/ExprSearch.idr`).

*Take:* that a dependently typed language's built-in search is close to exact whole-type
unification, and that this is too strict alone; `:fs`'s argument/result split is a cheap filter
we already have in place (`Hypothesis` versus `Conclusion`).

*Full text:* read in full (the three search paths named); ExprSearch.idr's header only.

**S3. Rocq `Search`, `SearchPattern`, `SearchRewrite`.** Reference manual
`doc/sphinx/proof-engine/vernacular-commands.rst` (the Search section), source
`vernac/search.ml`, `vernac/comSearch.ml` ([GitHub](https://github.com/rocq-prover/rocq), master).

*Claim:*
- `Search` items: a pattern (`_` and `?id`, repeated `?id`s must match the same), a string (a
  name substring with fuzzy matching up to edit distance 2 for strings over 4 characters, or a
  notation), `hyp:`, `concl:`, `headhyp:`, `headconcl:`, `head:`, `is:` (Lemma, Instance,
  Definition, …), `-` for negation, `[ … | … ]` for disjunction; `inside`/`outside` modules.
  `SearchHead` is not in the current manual; `headconcl:` does its job.
- `SearchPattern` matches the conclusion after the `∀`s and premises. `SearchRewrite` matches
  `eq _ pat _` or `eq _ _ pat`: either side, `=` only (search.ml `rewrite_pat1/2`).
- Matching is `Constr_matching` against each declaration's type, with no index:
  `generic_search` walks the whole environment. comSearch.ml: name-only output "is still too slow
  due to the non-indexed nature of the underlying search mechanism".
- Ranking (`prioritize_search`): fewer distinct constants and smaller types first, priority
  `−(3 × distinct symbols + size)`, then the name.

*Take:* `SearchRewrite` (both sides, equations only); `is:` and `inside`/`outside` as later
filters; negation.

*Full text:* read in full (the manual section and both files). `pretyping/constr_matching.ml` was
downloaded and **not read**, so how far Rocq's matching unfolds is [unverified].

**S4. Isabelle `find_theorems`.** Source `src/Pure/Tools/find_theorems.ML`
([mirror](https://github.com/isabelle-prover/mirror-isabelle), master).

*Claim:*
- Criteria: `name:`, `intro`, `elim`, `dest`, `solves` (these need a goal), `simp:` (a term the
  theorem rewrites as a simp rule), a pattern, each negatable with `-`.
- A pattern matches a subterm by `Pattern.matches`: higher-order pattern matching, one way (the
  pattern is instantiated, not the theorem). It is tried only if the theorem's constants include
  the pattern's: "Including all constants and frees is only sound because matching uses
  higher-order patterns".
- `solves` applies the theorem to the goal (`resolve_tac`/`eresolve_tac` and assumption): a
  stage-2 search inside the search command.
- Ranking (`sorted_filter`): smaller theorem, then fewer premises, then smaller substitution,
  then term order. Duplicates are removed preferring the nicer name.

*Take:* the constants prefilter (independent confirmation of D2045); premise count and size as
tie-breaks; `solves` as the model for stage 2; `simp:` as the model for rewrite mode.

*Full text:* read in full.

**S5. Sledgehammer's MePo (heuristic relevance).** J. Meng, L. C. Paulson, *Lightweight Relevance
Filtering for Machine-Generated Resolution Problems*, J. Applied Logic 7(1), 2009 (preprint,
[author's copy](https://www.cl.cam.ac.uk/~lp15/papers/Automation/filtering-jal.pdf)); source
`src/HOL/Tools/Sledgehammer/sledgehammer_mepo.ML`.

*Claim:* a fact's relevance is relevant symbols over all symbols, rarer relevant symbols weighing
`1 + 2/log(n+1)`; accepted facts make their symbols relevant; the pass mark rises each round
toward 1. On 285 problems, filtering beat the raw problems for every prover; 8% of filtered
problems lost an essential clause. "We do not feel that our methods can be significantly
improved … A machine learning approach may be able to derive information from successful proofs."

*Take:* rarity weights (measured in §6.1, not adopted for ranking). MePo selects premises for a
prover, a recall task; ours is a precision task for a reader.

*Full text:* read in full (preprint); source read in part (fudge factors, weights, the
iteration).

**S6. Sledgehammer's MaSh (learned relevance).** J. C. Blanchette, D. Greenaway, C. Kaliszyk,
D. Kühlwein, J. Urban, *A Learning-Based Fact Selector for Isabelle/HOL*, JAR 57(3), 2016
(preprint, [author's copy](https://wwwbroy.in.tum.de/~blanchet/mash2.pdf)); source
`sledgehammer_mash.ML`.

*Claim:* features are symbols, subterm patterns to depth 2, types and the theory; sparse naive
Bayes and k-nearest-neighbours, IDF-weighted, learn which facts proofs of similar goals used. It
keeps a persistent state, learns incrementally, needs no setup ("zero click") and answers in "a
few hundred milliseconds". With MePo alone 48.5% of 4,896 lemmas were reproved; adding MaSh and
MeSh, 66.1%. On Judgment Day, MeSh solved 919 goals to MePo's 801.

*Take:* if Stitchwort ever wants relevance beyond patterns, this is the shape: learned from
std's own proofs (each `Def` records what it uses), small, local, no model at query time (§5.5).

*Full text:* read in full (preprint); source read in part (the two learners).

**S7. Loogle.** Source `Loogle/Find.lean` ([GitHub](https://github.com/nomeata/loogle)), with
[cited: C7].

*Claim:*
- Index: a relation from each constant to the declarations that mention it, intersected over the
  query's constants; a suffix trie for name fragments. Cached on disk keyed by Lake's `depHash`.
- Elaboration ignores type-class failures and applies no default instances, "so that generic
  patterns like `|- 0 ≤ ?a * ?a` are not specialized to `Nat`".
- Matching: `isDefEq` at reducible transparency. The theorem's parameters are opened as local
  constants (`forallTelescope`), the pattern's as unknowns: one-way. A function-type pattern
  matches "up to parameter reordering": its conclusion against the theorem's, then each of its
  parameters against a different one of the theorem's, which may have more (`matchHyps`).
- Ranking: module order (a topological order, "so basic lemmas come earlier"), then the type's
  size, then the name.

*Take:* `matchHyps` (§5.2); not specialising generic patterns (§5.4).

*Full text:* read in full.

**S8. `exact?` and `apply?`.** Lean 4 source `src/Lean/Meta/Tactic/LibrarySearch.lean`, and
`src/Lean/Meta/LazyDiscrTree.lean`'s match ordering ([GitHub](https://github.com/leanprover/lean4),
master).

*Claim:* a lazily built discrimination tree over every conclusion (`↔` also split into its two
directions); keys `*` and `Eq * * *` are dropped "because they match too much" and tried only in
a second pass. Candidates come longest-key-match first, interleaved with those for the goal's
symmetric form; each is `apply`'d and its new goals given to `solve_by_elim` (depth 6; optionally
`grind` or `try?`). It stops at the first complete solution, or when 10% of the heartbeat budget
remains.

*Take:* stage 2's loop (§5.7): conclusion match, then fill the rest from hypotheses, under a
budget, first complete solution first.

*Full text:* LibrarySearch.lean read in full; LazyDiscrTree.lean in part (keys, `MatchResult`,
`getMatch`).

**S9. `rw?`.** Lean 4 source `src/Lean/Meta/Tactic/Rewrites.lean`.

*Claim:* a discrimination tree keyed on both sides of every `=` and `↔` conclusion; every
subterm of the goal is looked up, larger subterms first; weight is the key length, doubled for
left-to-right. Each candidate is tried with `rewrite`, side conditions by `solve_by_elim`;
results that `rfl` then closes come first; at most 20.

*Take:* stage 2's rewrite form (the reverse direction of §5.3: the goal's subterms against
lemma sides).

*Full text:* read in full.

**S10. Mathlib `#find`.** Source `Mathlib/Tactic/Find.lean`.

*Claim:* an index by the head symbol of each conclusion; `isDefEq` (reducible) plus the same
`matchHyps`; at most 20 results. Loogle grew from it.

*Full text:* read in part (`findType` and `#find`; not the `find` tactic's body).

**S11. LeanSearch.** G. Gao, H. Ju, J. Jiang, Z. Qin, B. Dong, *A Semantic Search Engine for
Mathlib4*, arXiv 2403.13310v2.

*Claim:* every Mathlib theorem is translated to informal text by GPT-3.5 with its definitions
and docstrings; formal plus informal text is embedded with E5-mistral-7b and stored in Chroma
(HNSW); each query is first expanded by GPT-4 (or DeepSeek). On 50 queries in 18 groups, nDCG@20
is 0.733 against 0.024 for BM25 and 0.365† for Moogle. For queries written as Lean terms, the
formal-only corpus did best without augmentation (0.774 against 0.612): such retrieval "relies
heavily on lexical rather than semantic information". Limitation: the 7B model "may pose
challenges when deploying … on … laptops". Moogle's "technical details have not been released".

*Take:* not the system. The evidence that formal queries are served by formal matching.

*Full text:* read in full.

**S12. LeanPremise and LeanHammer.** T. Zhu, J. Clune, J. Avigad, A. Q. Jiang, S. Welleck,
*Premise Selection for a Lean Hammer*, ICLR 2026, arXiv 2506.07477v2.

*Claim:* encoders of 23M–82M parameters, trained contrastively on 469,965 states from 206,005
Mathlib proofs (6.5 A6000-days for the largest), embed states and premises; a server runs FAISS
over cached embeddings, "about 1 second amortized on a CPU server". Recall@32 is 72.7% against
MePo's 42.1%; LeanHammer proves 33.3% of held-out theorems against 27.5% with MePo, and the union
with MePo proves more than either: "symbolic and neural methods have complementary strengths".

*Take:* the cost of the learned route (training data from proofs, a served model); its
complementarity with symbol methods. Premise selection feeds a hammer, a recall task, not a
reader.

*Full text:* read in full.

**S13. Agda.** User manual: `tools/search-about.lagda.rst`, `tools/auto.rst`,
`tools/emacs-mode.rst` (the command list) ([GitHub](https://github.com/agda/agda), master).

*Claim:* `Search About` (`C-c C-z`) lists definitions in scope whose type mentions every given
identifier and whose name contains every given string: a constants and name filter, no pattern.
`Auto` (`C-c C-a`) searches for a term at a hole, with hints, a one-second default timeout, and
`-l` to list up to ten solutions; "any solution coming from Auto is checked by Agda".

*Take:* nothing new; it confirms the constants filter as the minimum, and that hole-filling
search lives with the hole.

*Full text:* read in full (search-about and auto); emacs-mode.rst in part.

**Not read** (support nothing here): *Lean Finder* (arXiv 2510.15940; downloaded, not read for
lack of time); *LeanDojo/ReProver* (arXiv 2306.15626; downloaded, not read); Moogle (no paper);
Rocq's `constr_matching.ml` (downloaded, not read); Isabelle's isar-ref manual (not fetched; the
source was read instead); Mitchell's *Hoogle Overview* in The Monad.Reader 12 (not fetched; the
2011 slides and 2020 post cover the same ground and later).

## 3. The comparison

| System | Pattern language | Matching (up to what) | Argument order, currying | Classes, instances | Rewrite search | Ranking | Index | Output for tools |
|---|---|---|---|---|---|---|---|---|
| Hoogle | Haskell type, `a` variables; names | fingerprint prefilter, then union-find unification of type variables [S1] | 2-arg queries also swapped; arity ± costed; `Maybe` result tried | extra constraints on variables cost 3 each | no | summed hand-set costs: rarity, arity, size, unification work [S1] | memory-mapped file, daily; linear scan | JSON API (README) |
| Idris 2 `:search` | a type; free names become Π | whole-type `unify`, same arity, no leftover constraints [S2] | none | through unification | no | none | none | REPL text |
| Rocq `Search` | `_`, `?x`, strings, notations, `hyp:` `concl:` `head…:` `is:`, `-`, disjunction | `Constr_matching` [S3; unverified how far it unfolds] | `SearchPattern` strips ∀ and premises | `is:Instance` filter | `SearchRewrite`: `eq _ p _` or `eq _ _ p` | −(3·distinct constants + size) | none (walks the environment) | names + types; name-only flag |
| Isabelle `find_theorems` | patterns, `name:`, `intro` `elim` `dest` `solves` `simp:`, `-` | higher-order pattern matching, one way, after a constants-subset filter [S4] | via `intro`/`elim`/`dest` against the goal | through types | `simp:` | size, premises, substitution size [S4] | none | text (and Isabelle/jEdit) |
| Sledgehammer MePo / MaSh | none (the goal) | symbol overlap / naive Bayes, kNN on features [S5, S6] | n/a | type classes as features | n/a | relevance score | MaSh: persistent learned state | facts to provers |
| Loogle | constants, `"name"`, terms, `⊢ term` | `isDefEq` (reducible), one way, after a constants index [S7] | `matchHyps`: any order, theorem may have more | no default instances, failures ignored | via `⊢ _ = _` patterns | module order, size, name | on disk, keyed by `depHash` | `--json` |
| `exact?` / `apply?` | the goal | discrimination tree on conclusions, then `apply` + `solve_by_elim` [S8] | `apply` fills any order | instance search during `apply` | no | key match length, then first that closes | lazy tree, per process | "Try this" edit |
| `rw?` | the goal | tree on lemma sides vs every goal subterm [S9] | n/a | as above | yes, both directions | key length, forward ×2; `rfl` first | lazy tree | "Try this" edit |
| Mathlib `#find` | a term or type | `isDefEq` + `matchHyps` [S10] | `matchHyps` | as Loogle | no | none (first 20) | head symbol | messages |
| LeanSearch / LeanPremise | natural language / goal state | embedding cosine (7B / 23–82M model) [S11, S12] | n/a | n/a | n/a | similarity | vector store, served | web API / tactic |
| Agda | identifiers and strings | constants and name filter [S13] | n/a | n/a | no | none | none | Emacs buffer |
| **Stitchwort, draft 3** | `_`, `?x`, `⊢`, `"name"`, bare lowercase names; `--rewrite` | two-way unification on folded types, per-theorem budget, labelled `instance` / `generalisation` / `commonInstance` with a one-way retry; filtered by definitions and data types, relaxed pass if empty | `matchHyps` (greedy) | dual search, deduplicated with `via` | `--rewrite`: either side of a stated `=` or `Iff` | relation, place, specificity, premises, size, name | in memory, from the check cache | JSON version 1 (§4.1) |

## 4. The design, draft 3

Draft 2's design stands except where §5 changes it. In one place:

- **Command:** `stitchwort search 'PART, PART, …' [--project DIR | FILE] [--rewrite] [--json]
  [--limit N] [--defs] [--all]`; exit 0 with results, 1 with none, 2 for a pattern that doesn't
  elaborate. The syntax stays this small (review point 15): no `hyp:`/`is:`/negation selectors.
- **Parts:** `"text"` (name substring), a bare qualified name (the type mentions it), a pattern
  with `_` and `?x`, `⊢ pattern` (conclusion only), bare lowercase names as named holes (so a goal
  can be pasted). Overloaded operators with an unknown operand type are tried at each resolution
  and the results merged (draft 1 §3.1).
- **Scope:** all of std, loaded through the check cache, plus the project; `%` helpers, generated
  declarations and `…Example` theorems hidden unless `--all`; unfinished declarations not
  searched. No on-disk index (D2056).
- **First pass, filtered:** a theorem is compared only if its type, read back folded, names every
  definition and data type the pattern names (D2054). The filter is a retrieval index, not part
  of what a match means (review point 4).
- **Second pass, relaxed:** if the first pass finds nothing, the search runs again without the
  filter, and the JSON says `"searchTier": "relaxed"` (D2063). A pattern that names nothing is
  searched unfiltered from the start (`"unfiltered"`), with a warning; one that elaborates to a
  bare hole is refused.
- **Matching:** two-way unification on folded types, a 200,000-step budget per theorem. Targets:
  the whole type (function patterns), the conclusion, each premise, each call inside
  (`subterm`), and the parameters in any order with the theorem allowed more (`reordered`,
  Loogle's `matchHyps`, greedy). Targets headed by one of the theorem's variables (`p x`) are
  tried (§5.2); a target that *is* one of its variables is not.
- **Relation** (D2062, §5.1): each match is `instance`, `generalisation` or `commonInstance`; a
  match found crossed is retried one way. A theorem's best target wins: the best relation, then
  the best place.
- **Rewrite** (`--rewrite`): the two sides of a conclusion stated as `=` or as `Iff`, places
  `left`/`right`, and `equation: "eq" | "iff"` (D2065). Conditional equations are candidates;
  their premises are left open and counted in `premises`.
- **Instances:** a pattern naming an interface field at a concrete type is searched twice
  (resolved, and with the dictionary a hole); a theorem found both ways appears once, with
  `"via": ["resolved", "generic"]` (D2063, review point 7).
- **Ranking:** relation, place, `absorbed`, `instantiated`, `premises`, size, name (§5.1). Every
  key is in the JSON.
- **Output:** §4.1.

### 4.1 The JSON contract, version 1

```json
{"version": 1,
 "query": {"pattern": "Ord.compare ?x ?x = _", "elaborated": "Ord.compare ?x ?x = ?1",
           "names": [], "rewrite": false},
 "searchTier": "filtered",
 "results": [
   {"name": "Std.Ord.compareSelf", "type": "[a: Type] → [auto ord: Ord a] → (x: a) → Ord.compare x x = Equal",
    "file": "std/Ord/Ord.sw", "line": 48, "import": "import Std (Ord)",
    "relation": "instance", "place": "conclusion", "via": ["generic"],
    "absorbed": 0, "instantiated": 1, "premises": 0, "size": 19}],
 "total": 38,
 "budget": {"candidates": 2328, "compared": 45, "outOfBudget": 0,
            "truncated": true, "exhausted": true},
 "warnings": []}
```

- `version` changes when a field changes meaning or goes; new fields don't change it.
- `relation`: `instance`, `generalisation`, `commonInstance`. `place`: `whole`, `reordered`,
  `conclusion`, `left`, `right`, `premise`, `subterm` (D2063 renames: `inside` → `subterm`; the
  `hyps` key → `premises`, and the place `hypothesis` → `premise` with it, so one word means
  one thing).
- `equation` only with `--rewrite`.
- `budget`: how many theorems there were, how many passed the filter and were compared, how many
  comparisons ran out of their step budget (a theorem that did is a possible missed match),
  whether results were cut at `--limit` (`truncated`), and whether every candidate was compared
  (`exhausted`; false only if a whole-search time limit stops it, which stage 1 doesn't have).
  This answers review point 9: "no result" and "gave up" differ.
- The prototype already prints `relation`, `place` (`subterm`, `premise`), `premises`, `size`,
  `equation`, `searchTier` and `budget` without `exhausted` [run]; `query`, `via` and
  `warnings` are not built.

## 5. What changed, and why

### 5.1 Match relations (D2062)

**The definitions, as built in the prototype.** After a successful unification, each unknown is
read: the theorem's own variables (`opened`) and the pattern's holes (`free`).
- `absorbed`: the total size of what the theorem's variables became, plus one for each two made
  the same (draft 2's).
- `instantiated`: how many holes became more than a variable (draft 2's), plus, in a pattern made
  from a theorem or a goal, one for each two holes made the same.
- The relation is `instance` if no *deciding* hole was instantiated, `generalisation` if not that
  but `absorbed` is 0, and `commonInstance` otherwise. Deciding holes: named holes (`?x`) in a
  written pattern; every hole in a pattern made from a theorem or goal. A written `_` may take any
  structure, which is what the review's tier A allows ("query holes can of course bind"
  [review: §1]) and what `_` asks for.
- A solution under the pattern's binders (`x y => a`, from a hole under an arrow) is read under
  them, so a hole that only binds a theorem variable counts as a variable. Draft 2 counted it as
  structure.

**The one-way retry.** Two-way unification's solution need not be most general: its first-order
approximation "finds *a* solution, not necessarily the most general one"
[checked: crates/elab/src/unify.rs:1210–1213]. So a match read as `generalisation` or
`commonInstance` is unified again with the deciding holes frozen (the unifier treats a frozen
unknown as rigid [checked: unify.rs:990–1010]), and if that fails and it was `commonInstance`,
with the theorem's variables frozen. On the conclusions benchmark this upgraded 146 matches; 91
of them were a theorem against its own statement [run]. It costs 12% more unifications there
(557,200 → 621,300), because a match that is not `instance` is unified up to three times, and
every target of a theorem is tried until an `instance` one is found.

**What the ranking does** (relation first, as decided, against draft 2's order on the same
matches; strict top-1 = first after ties are broken by name):

| Benchmark | draft 2's ranking | relation first (D2062) | common-instance last only |
|---|---|---|---|
| conclusions (2,301) | 87.1% | **87.8%** | 87.1% |
| left sides (1,537) | 79.5% | **80.5%** | 79.6% |
| proof uses (5,173) | 36.5% | **38.3%** | 37.5% |

The gain is small on self-retrieval, where the theorem is an `instance` of its own statement and
the others mostly aren't, and larger on proof uses, where the lemma used is an `instance` of the
goal in 3,450 of the 3,495 found (99%) [run]. Mean rank among those found improves most: on
proof uses 12.0 → 7.4 (ties against the theorem).

Before the refinement above (every `_` deciding), relation-first put `Ord.compareSelf` third for
`Ord.compare ?x ?x = _`, behind `Ord.isLessEqAntisymm` and `Map.Spec.notEqualOfCompare`, which
end in a bare `x = y` and so are `instance` matches that absorb the whole pattern [run]. With it,
all five hand queries rank as in draft 2 (§6.3). The benchmarks don't change, since their
patterns have no written `_`.

### 5.2 Higher-order matching

The review recommended theorem-side higher-order pattern matching, not full higher-order
unification [review: §1]. What the prototype found:
- Draft 2's misses (13 conclusions, 17 left sides) were caused by a rule in the prototype, not by
  unification: a target whose head is one of the theorem's variables was skipped, applied or not
  [checked: draft 2's search.rs, "matches anything: no match"]. The rule is right for a bare
  variable (`(p: Prop) (h: p): p`) and wrong for `p x`.
- The unifier already solves `?p x = t` when `x` is a variable (a Miller pattern), and otherwise
  tries matching last arguments (`?m … x = f … y` as `?m … = f …`, `x = y`)
  [checked: unify.rs:1213–1234, 1286–1340].
- With such targets tried, all 13 + 17 are found; the cost is 3,131 more unifications on the
  conclusions benchmark (0.5%), and the hits per query don't change (median 1, p90 23) [run].
- On proof uses, `Eq.cong` (`f x = f y`) is still missed 244 times: the goal is computed
  (`Succ a = Succ b`, `0 = 1`), and `Succ` is a constructor, so neither a pattern solution nor
  the first-order approximation recovers `f` [run]. That is higher-order unification proper;
  it is not proposed. Stage 2's "applicable leaving goals" class would offer `Eq.cong` by its
  conclusion head only.

**Decision:** keep the unifier's existing pattern solving and approximation; try `p x` targets;
no new matching algorithm (D2067).

### 5.3 Evaluating the ranking (D2063)

Every ranking table now reports, over **all** queries (a query whose theorem isn't found counts
as a miss, not left out): strict top-1, top-1 with ties in the theorem's favour, MRR (strict),
recall@5 and recall@10 (strict). Draft 2's headline 88.2% counted ties in the theorem's favour
and only queries where it was found; the same figure for draft 3 is 89.6% (§6.1). The difference
between strict and ties is 1.3–1.8 points on every benchmark: some remaining ranking work is
tie-breaking, but most of the gap to 100% is not.

**Proof-use retrieval** (review point 2, D2063) is built (§6.2). It rebuilds the goal a lemma was
used at from the kernel's proof terms, not the source: for each use `L a1 … an` in a std proof
(or a helper of it), L's type applied to the arguments, with each of the proof's variables in
scope a hole. Differences from a real goal [inferred]:
- the proof's variables are holes, where a goal's are rigid; a variable that is a function
  (`cmp x y`) becomes an unknown applied to unknowns, which matching can't solve as a pattern.
  Some of the 545 "other" misses are this (`?1 ?6 ?8 = Equal`) [run];
- the statement is the lemma's own, instantiated and computed, so it is as close to the lemma as
  a goal can be; a real goal may be stated differently up to computation;
- 318 uses apply a negation to get `Void` (`Nat.zeroNotSucc h`): the goal is `Void`, and the
  lemma's conclusion as stated is `Not (…)`. Search by conclusion can't find these.

The reviewer's stronger stage-2 measure ("of the first K suggestions, how many kernel-check and
close the goal") needs stage 2; it is S2's test (§8).

### 5.4 The filter and the relaxed pass (D2063, D2066)

- **Self-retrieval:** the filter still loses nothing, with or without data types [run, §6.1].
- **Proof uses:** it loses most lemmas. The goal names what the proof was about; the lemma names
  less (`Nat.leTrans` doesn't name `List.length`). Draft 2's filter alone: 2,760 of 3,876 misses
  were filtered out [run].
- **The relaxed pass** runs in 2,726 of 5,173 proof-use queries (filtered result empty) and
  finds the lemma in 2,195 of them. 571 lemmas are still lost: the filtered search found
  something, so no second pass ran.
- **Filter "either"** (the theorem's conclusion names something, and the pattern names all it
  does, as an alternative to the rule): worse, 2,992 found against 3,495, because it makes the
  first pass non-empty more often and so suppresses the second [run].
- **No filter:** 4,066 found, strict top-1 39.3%, recall@10 58.3%, at 169–180 s against 115 s
  for the whole benchmark [run]. On self-retrieval no filter is worse (85.5% against 87.8%).

So for a written pattern (stage 1), the filter plus the relaxed pass is right: patterns name what
they want. For a goal (stage 2), the filter's direction is wrong: an `instance` match's theorem
names a subset of the goal's constants, not a superset. D2066 proposes that stage 2 search
unfiltered, which costs about 25–45 ms a goal on std (median, p90 of the proof-use run) [run].

### 5.5 Rewrite: `Iff` and conditional equations (D2063)

- `--rewrite` takes both sides of a conclusion `l = r` or `Iff l r` (std's `↔` is the record
  `Iff` [checked: crates/elab/src/std/Logic/Logic.sw:6]). 32 theorems conclude with an `Iff`; all
  32 left sides find their theorem [run]. Each result says `equation: "eq"` or `"iff"`.
- **The name clash:** D2062 calls the match relation `relation`; D2063 calls eq/iff
  `relation: iff`. One field can't carry both, so draft 3 uses `equation` for eq/iff (D2065).
- Conditional equations (`x ≠ 0 → f x = g x`) were candidates already: the prototype opens every
  parameter, premises included, and matches the conclusion. Their premises are left open
  (stage 1 doesn't try to prove them) and counted in `premises`; stage 2 tries to discharge them
  (review point 11).
- A side that computes away (`n + 0`) is still refused, not matched (draft 2 §5.3).

### 5.6 Instances: deduplication with provenance (D2063)

The double search stays (draft 2 §5.4). A theorem found by both searches is listed once, at its
better rank, with `via` listing both. The review's longer-term idea, indexing a projection under
both `Ord.compare` and `Nat.compare` [review: §4], is noted, not planned: it changes what the
filter sees, and the double search measured fine. Not built in the prototype; unmeasured.

### 5.7 Stage 2, first-class

The review: stage 2 "may become the main interface", should return candidates that leave goals,
in classes, with a small closing search, not a general automation tactic [review: §8]. Draft 3's
stage 2 (§8, S2):
- **Input:** a goal from SW-914's index (`--at FILE:LINE:COL`), its hypotheses opened as rigid
  variables (frozen unknowns), not holes (§5.3's finding), and its target as the pattern.
- **Candidates:** unfiltered (D2066), `instance` matches only, ranked as §5.1; `rw?`'s direction
  for rewrites (draft 2 §5.7).
- **Closing:** each candidate's remaining parameters from hypotheses (by unification), `rfl`,
  `auto` instances, `omega` on linear arithmetic goals, then the same closing step on what is
  left, to depth 3. Everything suggested is elaborated and kernel-checked.
- **Classes** (review point 12): `exact` (closes alone), `withHypotheses` (closes with local
  hypotheses), `afterObligations` (closes after small generated obligations: `rfl`, `auto`,
  `omega`), `leavesGoals` (applies, leaving goals, each listed). All four are returned, in that
  order.
- **Budget:** candidates (50), unification steps per candidate, closing steps; the JSON says
  which ran out, as in stage 1.
- **Not:** a general proof search; no lemma chains beyond depth 3.

### 5.8 Smaller points

- **Budget reporting** (review point 9): the 200,000-step budget per theorem was reached by
  1,062 of 621,300 comparisons on the conclusions benchmark (353 of 2,301 queries had at least
  one), and by 12,707 of 8.3 million on proof uses [run]. So it isn't too generous to be
  reached; how close normal queries come below it is not measured (no per-comparison step count
  is kept). Stage 1 reports `outOfBudget`.
- **Greedy any-order assignment** stays (D2063); backtracking later. Not measured here.
- **No currying or tupling, no natural language, no on-disk index** (D2063).
- **Panics** (review point 10): counted in every run (§6.4). Stage 1 ships after SW-919.

## 6. The measurements

All with the prototype on this branch [run]. To reproduce:
`docs/proposals/search/queries-draft3.sh [CACHE_DIR] [self|left|uses|hand]`. "Draft 2" below
means draft 2's matching (no relations, `p x` targets skipped, no relaxed pass) and ranking
(`proposed`), rerun with this branch's code. Two counting changes in this branch move draft 2's
own figures slightly: `instantiated` counts only holes left unsolved by elaboration (a constant
offset before, so no ranking changed), and reads solutions under the pattern's binders (§5.1).
Draft 2's published 88.2% (ties, found queries only) is 89.9% by the same measure in the rerun,
89.4% over all queries.

### 6.1 Self-retrieval

Strict top-1 / top-1 with ties / MRR (strict) / recall@5 / recall@10, over all queries:

| | conclusions (2,301) | left sides |
|---|---|---|
| draft 2 | 87.6 / 89.4 / 0.915 / 96.2 / 97.7; 13 missed | 80.6 / 81.8 / 0.878 / 97.6 / 98.4; 17 missed (1,537) |
| draft 3 matching, draft 2 ranking | 87.1 / 88.9 / 0.914 / 96.4 / 98.1 | 79.5 / 81.1 / 0.870 / 96.9 / 98.8 |
| **draft 3** (relations, `p x`, relation-first) | **87.8 / 89.6 / 0.918 / 96.5 / 98.2; none missed** | **80.5 / 82.1 / 0.878 / 97.1 / 98.9; none missed** (1,537) |
| draft 3 with `Iff` sides | | 80.8 / 82.4 / 0.880 / 97.2 / 98.9; none missed (1,569) |
| draft 3, data types in the filter | 87.9 / 89.7 / 0.919 / 96.6 / 98.3 | 80.8 / 82.4 / 0.880 / 97.2 / 98.9 (with `Iff`) |
| draft 3, no filter | 85.5 / 87.8 / 0.904 / 96.2 / 98.0 | 77.1 / 79.2 / 0.856 / 96.6 / 98.6 |
| Isabelle's ranking, draft 3 matching | 71.7 / 72.7 / 0.788 / 87.0 / 90.5 | 62.7 / 63.6 / 0.742 / 88.7 / 94.4 |

Draft 2's "draft 2" row for left sides ranks with "proposed"; strict 80.6%, against 80.5% for
draft 3: within noise of each other, while draft 3 finds the 17 missed ones.

Cost (whole benchmark; times approximate, shared machine):

| | unifications | out of budget | time |
|---|---|---|---|
| conclusions, draft 2 | 557,200 | 1,062 | 11.8 s |
| conclusions, draft 3 | 624,431 | 1,062 | 10.5 s |
| conclusions, draft 3 + data types | 225,782 | 569 | 5.9 s |
| conclusions, draft 3, no filter | 5,394,214 | 7,685 | 70 s |
| left sides, draft 2 / draft 3 / + `Iff` | 216,285 / 279,516 / 294,190 | 256 / 273 / 276 | 4.0 / 5.0 / 5.1 s |

Per query (draft 3, conclusions): median 0.1 ms, p90 22 ms, p99 69 ms, max 150 ms.

### 6.2 Proof-use retrieval

8,089 uses of std theorems in std's proofs; the first use of each lemma in each proof gives
5,350 queries, of which 5,173 make a pattern (177 skipped: the lemma isn't applied to all its
parameters, or its conclusion is a variable). Each is searched over all 2,328 std theorems but
the proof's own.

| | found | strict top-1 | ties | MRR | R@5 | R@10 | time |
|---|---|---|---|---|---|---|---|
| draft 2, no relaxed pass | 1,297 (25.1%) | 19.2% | 19.9% | 0.203 | 21.6% | 22.3% | 32 s |
| draft 2 + relaxed pass | 3,486 (67.4%) | 36.6% | 37.9% | 0.417 | 47.3% | 51.5% | 112 s |
| **draft 3** (+ relaxed pass) | **3,495 (67.6%)** | **38.3%** | **39.6%** | **0.434** | **48.3%** | **52.8%** | 115 s |
| draft 3 + data types | 3,399 (65.7%) | 38.3% | 39.6% | 0.432 | 48.2% | 52.4% | 106 s |
| draft 3, filter "either" | 2,992 (57.8%) | 36.0% | 37.1% | 0.400 | 44.6% | 48.0% | 78 s |
| draft 3, no filter | 4,066 (78.6%) | 39.3% | 40.8% | 0.460 | 52.4% | 58.3% | 169–180 s |
| Isabelle's ranking, draft 3 | 3,495 | 23.9% | 24.6% | 0.306 | 38.7% | 45.2% | |

Why the lemma is missed (draft 3, no filter, 1,107 misses): the goal is `Void` (a negation
applied) 318; `Eq.cong` on a computed goal 244; other 545, among them proof variables that are
functions (`?1 ?6 ?8 = Equal`), `Bool.inspect` (its conclusion is `motive b`, and
the goal shows the motive applied and computed, `?0 ≤ ?1 / ?2`), and arithmetic the goal shows computed (`?2 + (?1 * ?2) ≤ ?0 / ?2 * ?2`) [run].
With the filter, 571 more are lost to it (draft 3).

Per query (draft 3): median 24 ms, p90 38 ms, p99 84 ms, max 878 ms. Hits per query: median 16,
p90 63, p99 540.

### 6.3 Hand queries (draft 3 settings)

| Query | draft 2 | draft 3 |
|---|---|---|
| `List.length ((_: List _) ++ _) = _` → `lengthAppend` | 1 | 1 |
| `_ ∈ List.map _ _` → `memMap` | 3 | 3 |
| `Nat.min _ _ ≤ _` → `minLeLeft` | 1 | 1 |
| `Ord.compare ?x ?x = _` → `compareSelf` | 1 | 1 (3 if every `_` decided the relation) |
| `⊢ Not (Less = Greater)` → `lessNotGreater` | 1 | 1 |
| `mode:subset, (_: Nat) ≤ _ → _ ≤ _ → _ ≤ _` → `leTrans` | 2 of 38 | **1** of 38 |
| `mode:subset, List _ → Nat → List _` (`--defs`) | `drop`, `take` first | `drop`, `dropRight`, `removeAt`, `take` first |
| `mode:subset, (?a: Nat) ≤ ?b → ?b ≤ ?c → ?a ≤ ?c` | not run | `leTrans` not found: named holes under binders (below) |
| `List ?a → Nat → List ?a` (`--defs`) | 221; `Effect.bindIn` first | 222, the same; with data types 16, zip lemmas first, still no `drop` |
| `mode:rewrite, iff:on, _ ∈ List.append _ _` | | filtered pass empty; relaxed: 27, the first four `List.contains`/`distinct` lemmas, not about append |
| `DecEq.decide _ _` | 0 | filtered empty; relaxed: 15, the first four all ending in `p x` |

Two gaps these show:
- **Named holes under binders** (draft 1's gap, still open): a named hole used at two binder
  depths elaborates to two unknowns of different arity, which can't be made one. S1 fixes this by
  elaborating each named hole once, outside the pattern's binders (§8, S1a).
- **The relaxed pass is noisy**: unfiltered, a theorem ending in `p x` matches nearly any
  pattern, absorbing all of it. It ranks low among `instance` matches only by `absorbed`. S1
  ranks a match whose theorem variables absorbed the whole pattern after every other match of
  its relation (a `*` key, as `exact?` treats it [read: S8]).

### 6.4 Internal errors (SW-919)

Counted per comparison; each is caught and the comparison counted as no match. The benchmark
doesn't keep the panic message; the 4 filtered conclusion pairs are those SW-919 records
(`applying a constructor`, `Std.Parse.runFrom…`), the others are not confirmed to be the same.

| | filtered | no filter |
|---|---|---|
| conclusions | 4 | 12 |
| left sides | 2 | 12 |
| proof uses | 80 (relaxed passes included) | 91 |

On the way, this branch caused and fixed one of its own (`applying a data type`: a named hole's
occurrences made one before the target had solved them, at different arities); the fix is to
unify them after the target, as draft 2 did.

## 7. The review's points, and how each was handled

| # | Review point [review: §n] | Handled | How, or why not |
|---|---|---|---|
| 1 | Stratify the match relation: instance, generalisation, common instance last and weak (§1) | adopted (D2062) | §5.1; with a written `_` free to bind (D2064) and a one-way retry |
| 2 | Theorem-side higher-order pattern matching for `p x`, not full HO unification (§1) | adopted, investigated | §5.2: the existing unifier suffices once `p x` targets are tried; all 30 misses found (D2067) |
| 3 | Strict top-1, top-1 with ties, MRR, recall@5/10 (§2) | adopted (D2063) | every table in §6 |
| 4 | Proof-use retrieval benchmark (§2) | adopted (D2063) | §6.2; 5,173 queries |
| 5 | "Of the first K suggestions, how many close the goal" (§2) | deferred to S2 | needs stage 2; it is S2's test |
| 6 | Log real agent queries with the lemma then used (§2) | adopted (draft 2's S1 query log) | S1d; fields as the review lists |
| 7 | Filter is an index, not semantics; relaxed second pass; JSON says which (§3) | adopted (D2063) | §5.4, `searchTier` |
| 8 | Don't make the filter definitionally complete (§3) | adopted | no unfolding in the filter |
| 9 | Report budget truncation and exhaustion (§8, minor) | adopted (D2063) | `budget` in the JSON; §5.8 measures how often the 200,000 steps run out |
| 10 | The panics block heavy reliance on search (minor) | adopted | S1 ships after SW-919 |
| 11 | `--rewrite` with `Iff` labelled, conditional equations with premises open; no computed equations (§6) | adopted (D2063) | §5.5; field `equation` (D2065) |
| 12 | Stage 2 first-class, small closing search, four classes, budget-driven (§8) | adopted (D2063) | §5.7, S2 |
| 13 | Keep `search`, `apply?`, `exact?` separate in the API (larger suggestion) | adopted in substance | stage 1's matching returns relations; stage 2's classes are `apply?`/`exact?`'s answers; one command each (`search`, `search --at`) |
| 14 | Relation before place in the ranking (ranking section) | adopted (D2062) | §5.1 |
| 15 | `hypotheses` → `premises`; `inside` → `subterm` (ranking, minor) | adopted (D2063) | §4.1; also `hypothesis` place → `premise` |
| 16 | Keep the syntax small (minor) | adopted (D2063) | §4 |
| 17 | Dedupe the instance double search, keep provenance (§4) | adopted (D2063) | `via`, §5.6 |
| 18 | Index projections under both names (§4, long term) | deferred | the double search works; revisit if logged queries show misses |
| 19 | Replace greedy any-order assignment with min-cost matching (§5) | deferred (D2063) | not measured; S3 |
| 20 | No currying/tupling isomorphisms (§5) | adopted (D2063) | |
| 21 | No natural-language search (§7) | adopted (D2063) | revisit conditions as draft 2 §5.5 |
| 22 | Allow only controlled reduction of reducible wrappers in rewrite (§6) | deferred | stage 1 uses sides as stated; no case in std was found that needs it |

## 8. The staged implementation plan

**Gate:** stage 1 merges only after SW-919 (the unifier can solve an unknown with an ill-typed
value, and evaluating it panics) is fixed by the lane that owns the unifier. Search must not
panic; its benchmark is the test.

### Stage 1: `stitchwort search`

| Step | What | Tests |
|---|---|---|
| **S1a** core | Move the matching out of the prototype into `crates/elab/src/search.rs` proper: relations with the one-way retry, `p x` targets, the filter with data types, the relaxed pass, places and names as §4.1, `--rewrite` with `Iff`, the ranking of §5.1 (with whole-pattern absorption last within a relation), named holes elaborated once outside binders, refusal of a pattern that is a bare hole | unit tests in elab for each relation, the retry, `p x`, named holes under binders (`(?a: Nat) ≤ ?b → ?b ≤ ?c → ?a ≤ ?c` finds `leTrans` first) |
| **S1b** command | `stitchwort search` in the CLI: parts, `--project`/file scope (std plus the project's declarations, loaded through the check cache), hiding, `--limit`, `--defs`, `--all`, exit codes, the human output, the JSON contract version 1 (§4.1), the instance double search with `via` | CLI tests on a small project (a project lemma found, std's found, hidden helpers hidden); a JSON snapshot; exit codes |
| **S1c** benchmarks as tests | self-retrieval over std as a test: every conclusion and left side (`Iff` included) found, none lost to the filter, no panic; strict top-1 at least 86% / 78% (today 87.9% / 80.8%, less a margin); the proof-use benchmark's recall@10 at least 50% with the relaxed pass (today 52.8%); draft 1's hand queries and `leTrans` first | the full benchmarks take 6 s and 5 s (conclusions with data types, left sides) and about 2 minutes (proof uses): merge tier gets a 300-theorem sample of each (about 1 s), daily the two self-retrieval sets in full, full tier the proof-use set |
| **S1d** docs and log | `docs/syntax.md` section "Lemma search, `stitchwort search`" after "Auditing theorems" (syntax, scope, relations, places, JSON, exit codes, examples); `docs/proving-guide.md` points proof lanes to it; the opt-in query log (`--log FILE` or `STITCHWORT_SEARCH_LOG`): query, results shown, and the lemma the next `check` used | doc examples run as tests (the syntax.md examples harness, if the section's examples are marked as checked; else a CLI test per example) |

The prototype (`dev search` and its directives) stays for measuring until S1c's tests replace its
benchmarks, then goes.

### Stage 2: `stitchwort search --at FILE:LINE:COL`

| Step | What | Tests |
|---|---|---|
| **S2a** | read the goal from `check --index`; hypotheses as frozen unknowns; search unfiltered (D2066), `instance` matches | a goal per class in a test project |
| **S2b** | closing: hypotheses, `rfl`, `auto`, `omega`, depth 3; kernel-check; the four classes (§5.7); budgets in the JSON | std theorems with their proof replaced by `?` (a sample): the share where the first 5 suggestions include one that closes the goal (review point 5), and every suggestion re-checks when pasted |
| **S2c** | `rw?`'s direction: the goal's subterms against equation and `Iff` sides | a rewrite goal per kind |
| **S2d** | LSP code action at `?` (S3 in draft 2, moved here: agents use the CLI, editors the LSP) | LSP round trip |

### Stage 3 (later, if logged queries ask for it)

Min-cost any-order assignment instead of greedy (review point 19); indexing projections under
both names (point 18); tie-break tuning from the query log.

## 9. Risks

- **The relaxed pass is noisy** (§6.3): it is labelled, and whole-pattern absorption ranks last.
- **Proof-use numbers are a proxy**: the queries are the lemma's own statement, instantiated, so
  they flatter search; but the proof's variables are holes, not rigid, which hurts it (§5.3).
  Stage 2's closing test is the real measure.
- **The one-way retry triples a non-`instance` match's cost**: 12% more unifications on the
  conclusions benchmark; with data types in the filter the whole benchmark still takes half
  draft 2's time [run].
- **Two-way unification is not most general** (146 cases): the retry covers the relation, but a
  match two-way unification misses entirely isn't retried. Not measured how often that happens.
- **Projects are unmeasured** (draft 1 §8, still).
- **SW-919** gates stage 1.

## 10. Decisions for Matt

**D2064. Should a written `_` be free to take any structure without lowering the match's
relation, with only named holes (`?x`), and every hole of a pattern made from a goal, deciding
whether a match is an `instance`?** Recommended: **yes**.

The assumptions, in full:
1. D2062's relations are kept as decided: `instance` (only the theorem's variables took
   structure), `generalisation` (the pattern's holes took structure, the theorem's variables
   stayed variables), `commonInstance` (both); ranked relation, place, `absorbed`,
   `instantiated`, `premises`, size, name.
2. A user who writes `_` asks for "whatever is there"; a named hole or a pasted goal's variable
   names something specific. The review's tier A says query holes "can of course bind" [review:
   §1].
3. Without this rule, relation-first ranking puts `Ord.compareSelf` third for
   `Ord.compare ?x ?x = _`, behind lemmas ending in a bare `x = y`; with it, all five of draft
   1's hand queries rank as in draft 2 and `leTrans` is first for the transitivity pattern
   [run, §6.3].
4. The benchmarks (§6.1, §6.2) don't change, since their patterns have no written `_`; the rule
   is supported by five hand queries, not by a benchmark.
5. `instantiated` still counts a `_` that took structure, so within a relation the closer fit
   (`lengthAppend` before `lengthSnoc`) still ranks first.

**D2065. Should the eq/iff label of a rewrite result be the field `equation` (`"eq"` or
`"iff"`), leaving `relation` for the match relation?** Recommended: **yes**.

The assumptions, in full:
1. D2062 names the match relation `relation`; D2063 writes "Iff (`relation: iff`)" for the
   rewrite label. One field can't carry both.
2. `equation` appears only with `--rewrite`; `relation` is on every result.
3. Nothing else in the JSON contract is called `equation`.

**D2066. Should stage 2 (`search --at`) search a goal without the constants filter, `instance`
matches only, with the goal's hypotheses as rigid variables, while stage 1 keeps the filter and
its relaxed second pass?** Recommended: **yes**.

The assumptions, in full:
1. The proof-use benchmark stands in for stage 2's goals: each use of a lemma in a std proof,
   its statement there as the query, the proof's variables as holes (§5.3 lists how this differs
   from a real goal).
2. On it, the filter loses the lemma in 2,760 of 5,173 queries; the relaxed pass recovers 2,195
   of them; without a filter the lemma is found in 4,066 (78.6%) against 3,495 (67.6%), strict
   top-1 39.3% against 38.3%, recall@10 58.3% against 52.8% [run, §6.2].
3. The cost is about 1.5 times: median 25–28 ms and p90 about 45 ms per goal over std, on a
   shared machine [run]. A project adds its own theorems; unmeasured.
4. The reason is structural: a lemma that instantiates to a goal names a subset of the goal's
   constants, so "the theorem names everything the pattern names" is the wrong direction for a
   goal [inferred]. Filter "either" (also let through a theorem whose conclusion's constants are
   all in the goal) was measured and is worse (2,992 found) [run].
5. Written patterns keep the filter: on self-retrieval, no filter is 2.3 points worse at top-1
   and 7 to 12 times slower [run, §6.1].
6. Rigid hypotheses are designed, not measured; the benchmark used holes.

**D2067. Should S1 try targets headed by one of the theorem's variables (`p x`, `f x = f y`)
with the unifier's existing higher-order pattern solving and first-order approximation, and not
add a higher-order matching algorithm?** Recommended: **yes**.

The assumptions, in full:
1. Draft 2's 30 self-retrieval misses were all such targets, skipped by the prototype; tried, all
   30 are found, for 0.5% more unifications and no change in hits per query [run, §5.2].
2. A target that *is* a bare theorem variable (`(p: Prop) (h: p): p`) is still skipped: it
   matches anything.
3. What still fails (`Eq.cong` against a computed `Succ a = Succ b`, 244 proof uses) needs
   higher-order unification proper, which the review advises against [review: §1]; stage 2's
   `leavesGoals` class covers `Eq.cong`-like lemmas by applying them.
4. In the relaxed pass such theorems match almost anything; they rank after every other match of
   their relation (S1a).
5. The unifier is being rewritten by the postponement lane; this decision relies only on it
   keeping pattern solving and the first-order approximation, which `elaborate` needs anyway.

## 11. Changes from draft 2

- **Relations** (D2062): `relation` on every match, ranked first; the one-way retry; a written
  `_` doesn't decide the relation (D2064) (§5.1).
- **Higher-order misses**: a prototype rule, now removed; all 30 found (§5.2, D2067).
- **Evaluation**: strict top-1, ties, MRR, recall@5/10 over all queries; the proof-use benchmark
  (§5.3, §6.2).
- **Filter**: relaxed second pass (`searchTier`); data types measured (lossless on
  self-retrieval, half the time); stage 2 unfiltered (D2066) (§5.4).
- **Rewrite**: `Iff` sides, `equation` field (D2065); conditional equations' premises open (§5.5).
- **Instances**: dedupe with `via` (§5.6).
- **Stage 2**: first-class, four classes, rigid hypotheses, budgets (§5.7).
- **JSON contract version 1**, renames `subterm`, `premises`, `premise` (§4.1).
- **The review's points and their handling** (§7); **the staged plan** (§8), gated on SW-919.
- **Prototype**: directives `tiers:`, `ho:`, `iff:`, `data:`, `filter:`, `relax:`, `every:`,
  `self:uses`, ranking `tiered`; `docs/proposals/search/queries-draft3.sh`.

## 12. What was not verified

- **Projects**: std only, still.
- **Instance dedupe, `via`, `query` and `warnings` in the JSON, refusal of bare-hole patterns,
  named holes under binders, the whole-absorption rank rule**: designed, not built.
- **Stage 2** in every part, including rigid hypotheses and the closing search.
- **How close normal queries come to the step budget** (only whether they reach it).
- **How often two-way unification misses a match a one-way one would find** (the retry runs only
  after a two-way success).
- **The panic messages** beyond the 4 SW-919 pairs.
- **The order among equally specific results**: still from five hand queries and the benchmarks;
  no query log exists.
- **The Lean documentation the review cites**: not read.
- **Quiet-machine timings.**
