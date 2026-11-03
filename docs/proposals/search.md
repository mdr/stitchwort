# Proposal: `stitchwort search`, lemma search by type

**Status:** draft 3, 30 October 2026. Ticket SW-915, from
[agentic-proving.md](../research/agentic-proving.md) T4 and §7.4. Draft 1 (D2044) compared only
Lean's tools; draft 2 (D2052) compared the wider field and measured the design with the prototype
`stitchwort dev search`; an external reviewer read it
([search/review-1.md](search/review-1.md), from the brief
[search/review-brief.md](search/review-brief.md)) and approved it with changes. Matt accepted
D2054–D2056 and decided D2062 and D2063 (30 October). Draft 3 folds in those decisions and the
review, measures what changes, and gives the staged plan. Stage 1 is built, after Matt read this draft (D2088):
[As built (stage 1)](#as-built-stage-1). New decisions are in [§10](#10-decisions-for-matt).

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

## As built (stage 1)

Stage 1 (S1a–S1d) is `stitchwort search`, documented in
[syntax.md](../syntax.md#lemma-search-stitchwort-search) (SW-915; D2088 accepted D2064–D2067,
D2089 decided the kinds). The matching is `crates/elab/src/search.rs`, the command
`crates/driver/src/search.rs` and `crates/cli/src/main.rs`. The prototype `stitchwort dev search`
and its directives are gone; its benchmarks are tests (below), and
`search/queries-draft3.sh` runs only with a build of 20fd3dc2 or earlier.

**As planned**: the three relations ranked first, with the one-way retry; a written `_` free to
take structure (D2064); `p x` targets tried with the unifier as it is (D2067); the filter with data
types, and the relaxed second pass (`searchTier`); named holes made once, outside the pattern's
binders; a pattern that is a bare hole refused (`E-SEARCH-PATTERN`); places as §4.1, `equation`
(D2065); `--rewrite` with `Iff` and conditional equations; the instance double search with `via`;
std and the project loaded through the check cache; helpers and `…Example` theorems hidden unless
`--all`; exit codes 0, 1, 2.

**Changed from the plan:**

- **Kinds (D2089)**: theorems, definitions and constructors are all searched by default, and each
  result has `kind`. `--theorems`, `--definitions` and `--constructors` narrow it (any of them
  together), in place of draft 3's `--defs`. An interface's law (a field whose type is a
  proposition, `Ord.flip`) is a `theorem`.
- **Types before unification (SW-924)**: a target whose type differs from the pattern's isn't
  unified (20fd3dc2).
- **Whole-pattern absorption** ranks last within its relation when the target's head is one of the
  candidate's variables (`p x`), as planned, and also when one of the candidate's variables took a
  term as large as the whole pattern. Definitions made the second rule necessary: a conclusion
  `{row} a` unifies with any pattern by taking `a` to be it, and in the relaxed pass such
  definitions came first.
- **`p x` targets in practice** match patterns headed by a variable or a hole (`(?q: Nat → Prop)
  3`, a theorem's own statement); the unifier can't solve `?p ?k` against an `=` or a `≤` (no
  pattern, and the first-order approximation needs an application), so they rarely match a written
  pattern. As D2067 expected; no new algorithm.
- **Scope**: a project's namespaces are in a pattern's scope as `import N (..)` brings them, and
  the import line names the namespace; with a `FILE`, a pattern sees names as the file does. A
  project or file that doesn't check is reported, and what checked is searched.
- **JSON version 1** has, beyond §4.1: `kind`; `query.text` (draft 3's `query.pattern`), with
  `mentions`, `holes` and `kinds`; `budget.internalErrors`; and on an error, `{"version": 1,
  "error": {"code", "message"}}`. `via` is left out for a pattern searched once.
- **A unifier fix**: matching last arguments (`first_order`) could solve the head unknown itself
  (`?m a b = f c ?m` pairs `b` with `?m`) with a constructor, and then apply it: a panic in core,
  found by the proof-use benchmark. It now fails, taking the solution back (unit test in
  `unify.rs`). Only comparisons that panicked before change, so no hash moves.
- **The proof-use benchmark's holes have types**: each proof variable given as an argument (to the
  lemma, or a call in its arguments) gets its parameter's type, so SW-919's guard can refuse
  ill-typed pairings. Without types, two comparisons panicked (`Eq.trans`'s use in
  `List.sumByGet` against `List.sumByAttach`).

**Built after stage 1** (SW-927): overloaded operators with operands nothing types (`_ ++ _`, `_ + _`) are tried at each reading (lists and texts; `Nat` and `Int`) and the results merged, as §4 promised: the pattern as written first, then with the first hole of each such operator's group ascribed each type, every combination up to 16; a reading what surrounds it rules out doesn't elaborate (`List.length (_ ++ _)` is lists only), and readings that elaborate the same are searched once. If one reading finds something without the relaxed pass, the readings that needed it are dropped. The query log (S1d): `--log FILE` or `STITCHWORT_SEARCH_LOG`, one JSON line per search (syntax.md). The lemma a later `check` used isn't recorded yet; the format has an `event` field for it.

**Not built**: everything of stage 2 (now built: below).

## As built (stage 2)

Stage 2 is `stitchwort search --at FILE:LINE[:COL]` (or `--at FILE --goal N`), documented in
[syntax.md](../syntax.md#what-closes-this--stitchwort-search---at) (SW-915, D2094). The elaborator's
half is `crates/elab/src/closing.rs`, the driver's `crates/driver/src/search_at.rs`.

**As planned (§5.7, D2066, review §8)**: the goal read from the file's goals (the same data as
`check --index`, SW-914); hypotheses opened as frozen unknowns, so matches are `instance` only;
unfiltered; candidates in stage 1's rank order, at most 50, each comparison under its step budget;
premises filled from hypotheses (by unification), then `rfl`, `omega` and `byDecision`; every
proof elaborated and kernel-checked before it is called closing; the four classes; rewrites in
`rw?`'s direction; JSON version 1 with a budget saying `truncated` and `exhausted`; the code
action.

**Changed from the plan:**

- **Checking is by text.** Each plan is printed as the proof an agent would paste, and that text is
  elaborated inside `(((h: A) => …) : (h: A) → … → T)` (`Elaborator::check_proof`: no `?`, kernel;
  with `?`, the goals left, printed as a file's). So what is checked is what is shown, and the
  goals an `applicable` result leaves are the elaborator's own. A solved argument that can't be
  printed is `_`; if the printed form fails, the proof is tried again with every solved argument
  `_`.
- **Two sessions.** The search needs the whole library loaded; a proof checked there can use an
  instance or decision procedure from a library file the goal's file doesn't load (found:
  `byDecision` closed `m + n = n + m` with every file loaded, and fails in the file). So the
  proofs are checked in a second session with only the file loaded.
- **Depth.** One application, its premises filled by hypotheses (as a whole, by unification,
  backtracking over the choices, at most three plans and 200 choices a candidate) or by one
  closer each. Draft 3's "depth 3" (a hypothesis applied to further premises, or a closer leaving
  goals for another round) isn't built: no measured goal needed it yet.
- **`auto`**: an `[auto]` parameter is filled by elaboration as always; for an explicit premise,
  the closer is `byDecision` (Lean's `decide`).
- **Noise rules, from the first runs**: a lemma whose conclusion names nothing (`r = l`,
  `Nat.succInjective`'s `m = n`) is suggested only if it closes the goal (30 of 31 `applicable`
  results on `List.length (xs ++ ys) = …` were such); an `applicable` result whose goal has an
  unknown in it (`?3 m n`) is dropped; so is an `afterObligations` one whose obligation is the
  goal itself (`omega` alone closes it: `tactics` says so once).
- **Rewrites that then close**: `rewrite L … in rfl` (or `omega`) is a closing suggestion too.
- **Project files** weren't supported (stage 2b, below, adds them): the file was checked on its own, as `check FILE` does.
  The goal's statement must be writable on its own (SW-914's `lemma` rules); otherwise
  `E-SEARCH-AT`.

**Measured** (31 October 2026, `crates/driver/tests/search_at_bench.rs`, full tier): std theorems
whose whole proof is one lemma applied to their own variables (46 goals once the reflective
tactics' lemmas, `Ring.prove…` and `Omega.prove…`, are left out): a kernel-checked closer (or a
tactic alone) for 80.9%; the lemma the proof used is among the closers for 67.4%, first for 54.3%,
in the first five for 63.0%. Most misses are concrete `…Example` goals (`3 ∈ List.append [1, 2]
[3]`), where the goal as elaborated has computed past the lemma's conclusion. Every 10th std
statement as a goal (222 goals, the theorem itself left out): something else closes 23.4%. About
0.5 s a goal on std (std loaded through the check cache; 200 to 400 checks).
AoC goals were not measured then: they are a project's, which `--at` didn't read yet (now it does: stage 2b below).

**Tests**: `crates/driver/tests/search_at.rs` (lane `search`): a goal per class, a rewrite, an
introduced variable, a false goal; every closing suggestion is pasted in place of its `?` and the
file checked again. `search_at_bench.rs` (daily a quarter, full all). `crates/cli/tests/search.rs`
`what_closes_a_goal` (the command, exit codes, the JSON snapshot). `crates/cli/tests/lsp.rs`
`a_code_action_at_a_goal_offers_what_closes_it`.

**Tests and tiers** (lane area `search`, docs/testing.md): `crates/driver/tests/search_match.rs`
(relations, `_`, `p x`, named holes under binders, refusals, rewrite: a small file);
`crates/driver/tests/search_bench.rs` (self-retrieval: every theorem found, no internal error,
strict top-1 at least 86% of conclusions and 78% of left sides over all std in the daily tier, two
points less on the merge and lane tiers' sample of every 8th; the hand queries in every tier; the
proof-use benchmark, recall@10 at least 50%, in the full tier only); `crates/cli/tests/search.rs`
(the command end to end, and a snapshot of the JSON).

**Measured** (31 October 2026, on a loaded machine, so times are rough):

| Benchmark | queries | not found | strict top-1 | MRR | R@5 | R@10 | internal errors | time |
|---|---|---|---|---|---|---|---|---|
| conclusions (all std) | 2,324 | 0 | 87.7% | 0.917 | 96.4% | 98.3% | 0 | 7 s |
| left sides, `Iff` included | 1,587 | 0 | 81.2% | 0.883 | 97.6% | 99.4% | 0 | 4 s |
| proof uses | 5,197 | 1,830 | 38.2% | 0.428 | 47.6% | 51.0% | 0 | 126 s |

The query counts are higher than §6's (2,301 conclusions) because interface laws now count as
theorems. Draft 3's script, with a build of 20fd3dc2 (SW-924's fix alone): the self and left
sections had no internal error in any of their 10 runs; the proof-use section had 1 in three of its
six runs and 3 unfiltered, the cases fixed above.

## As built (stage 2b)

Stage 2b (SW-915, D2100) is `search --at` in a project's files, and the code action there, as
[syntax.md](../syntax.md#what-closes-this--stitchwort-search---at) documents. The driver's half is
`Session::search_at_project` (`crates/driver/src/search_at.rs`) with `load_for_goal` and
`recheck_for_goal` (`crates/driver/src/project.rs`).

- **One session.** It loads the whole library first (as the language server does), then every
  namespace of the project but those that use the goal's (they can't be imported by it), through
  the check cache, the goal's namespace last, with a mark just before it. It stays in that
  namespace's scope, with the file's own imports (`Elaborator::use_file_scope`), so the goal is
  read, and the proofs written (aliases, `import P (S)`, full names for what the file doesn't
  import) and checked, as the file sees them. The goal's declaration and what uses it are
  unfinished, so not searched.
- **Checked in the file.** Every closing suggestion shown, and every tactic, is pasted in place of
  the `?` and the namespace checked again from the mark; one with an error there, or that leaves
  the goal open, is dropped with a warning. On the benchmark below none was dropped. Each such
  check costs a check of the namespace, so they have a `--time` of their own.
- **Not built**: suggestions don't promote unshown ones when a shown one is dropped; a namespace's
  own theorems aren't used to fill premises (only hypotheses are).

Found on the way and fixed: planning rewrites printed each call of the target unbudgeted, which for
AoC 2024 day 22's `mostBananas possibleSequences 2000 buyers` computed a list of 130,000 sequences
(minutes, 5 GB): now under a comparison's budget. The search now stops at `--time` too. The tactics
are written as the file writes them (`Std.byDecision` without the import: pasting `byDecision`
failed). SW-942: `cases` is a closer (alone, for obligations, and after a rewrite, but a rewrite
whose closer closes the goal alone isn't suggested); a pattern that computes to a hole says so; the
out-of-steps warning names the declarations (always std's three `Float.Theory` lemmas about
`magUnits 9218868437227405311`, whose statements run out of depth against any `Nat` sum or `≤`).

**Measured** (31 October 2026, `crates/driver/tests/search_at_aoc.rs`, full tier; one run, three
workers, on a machine with a load average near 30). Every AoC theorem whose proof is one lemma
applied to plain arguments (28), or a closer alone (25), had its proof replaced by `?` in memory
and was asked about:

| | goals | a closer found | the original among the closers | first | in the first 5 |
|---|---|---|---|---|---|
| one-lemma proofs | 28 | 42.9% | 39.3% | 35.7% | 39.3% |
| closer alone (`rfl`, `omega`, …) | 25 | 92.0% | 92.0% | | |
| all | 53 | 66.0% | | | |

Times: a median of 16 s a goal in the benchmark (load and three at once), 290 s at most (a
namespace of heavy `rfl` proofs, checked again for each suggestion, before the in-file checks had
their own time limit). With the command alone and a warm cache: 1.9 s (2025 day 7), 2.1 s (2021
day 2), 24 s (2024 day 22, whose proofs namespace takes 11 s to check). The cost beyond the
library's 0.2 s is checking the goal's namespace, once and again for each suggestion.

The misses, with why:

- **Goals that can't be written on their own** (4: 2024 day 18 `containsCons`, day 22
  `digitChangesPossible`, 2025 day 3 `leftmostLargest`, day 5 `stackSorted`): `E-SEARCH-AT`, as
  for SW-914's `lemma`.
- **The lemma fits only once the goal's definition is unfolded** (most of the rest): 2021 day 2
  `aimedDepthCons` (`List.sumCons _ _` proves `aimedDepth aim (Cons command rest) = …` because
  `aimedDepth` is a `List.sum`), 2024 day 16 `scoreCons` and `scoreAppend` (`List.sumBy…` for
  `score`), day 11 `part2Correct` and days 20 and 21's `part1Correct`/`part2Correct` (the
  `solvePartN` of the goal is the lemma's left side only after unfolding). Search matches
  conclusions without unfolding the goal first; stage 2's std benchmark misses the same way.
- **A premise only a theorem fills** (2024 day 21 `shortestWithoutRobots`): `shortestIfOptimal 0
  ? code` is listed as applicable, leaving `optimalWithoutRobots`, which is a theorem in the
  namespace, not a hypothesis.
- **Out of time** (2024 day 21 `numericWalksYours`, day 22 `pruneMix`): heavy namespaces.
- **A lemma whose conclusion names nothing** (2024 day 17 `finishedInjective := Eq.cong …`):
  never suggested by design; `cases` closes it alone, so a closer was found.
- Not diagnosed: 2024 day 11 `blinkPerm` (`List.permFlatMap`, 41 matched, nothing closing).

One found at 2: 2024 day 15 `coversSelf := Inl rfl` came after day 23's `firstOfTwo`, which proves
the same statement: a lemma of an unrelated namespace, written in full with its import.

**Tests**: `search_at_aoc.rs` (daily: `Aoc.Common` and the 2021 days, 6 goals, through a view of
the project's files; full: all), `crates/cli/tests/search.rs` `what_closes_a_goal_in_a_project` (a
three-namespace project: alias, full name and import, nothing that uses the goal, run from another
folder; JSON snapshot), `crates/cli/tests/lsp.rs`
`a_code_action_at_a_goal_in_a_project_offers_what_closes_it` (the editor's unsaved text), and
`search_at.rs` `cases_closes_a_goal_alone`.

## As built (stage 3)

Stage 3 (SW-989, D2116) makes `search --at` work on the goals the AoC 2021 lanes met (days 9 to
18, 1 November 2026), measured on a benchmark of those goals first.

**The benchmark** (`crates/driver/tests/search_at_aoc.rs` `search_at_on_real_2021_goals`, daily and
full tiers): 29 proof positions the lanes asked `search --at` about or wrote by hand
(aoc/NOTES-2021.md, SW-960 to SW-980), each with its proof replaced by `?` in memory, in the
project (`Aoc.Common`, the 2021 days, 2024 day 24), with what closed it. A goal is a hit when what
its proof used is among the closing suggestions or offered as a step (applicable, or a rewrite);
for the 6 that were refused and have no single known closer, when it is read at all. The lane
tier has the refusal kinds as a small file (`search_at.rs`
`goals_that_dont_print_back_are_searched`: every closer pasted and checked again).

| | refused | closed by what the proof used | offered it as a step | hit rate | a goal (median, max) |
|---|---|---|---|---|---|
| main (before) | 9 | 8 of 23 | 4 | 14/29 (48%) | 1.8 s, 39 s |
| after | 0 | 10 of 23 | 7 | 23/29 (79%) | 1.5 s, 31 s |

The maximum is AoC 2021 day 16, whose proofs namespace takes about 14 s to check, once and again
for each suggestion confirmed in the file. One run each, on a machine with a load average near 22.

**The query log** (stage 1's `--log`, `STITCHWORT_SEARCH_LOG`) was never switched on: no log
file existed. What the lanes searched was read from their transcripts instead (11 AoC lanes, 1
November): 44 `search --at` runs (9 refused, 9 closed the goal, the rest offered nothing that
closed it) and about 50 pattern or `--rewrite` searches (26 with results).

**The goal as the elaborator had it.** `--at` used to read its goal by printing the statement,
`(h: A) → … → T`, and elaborating that text; a goal whose printed form isn't valid source was
refused. Two ways out were weighed: make every printed goal valid source, or search the goal's
terms. The second was built, because some goals can't be printed as source at all: a `x✝`
variable has no name a proof can use (renaming it in the statement would make suggestions that
don't paste), a lifted `f.%match1` has no source form unless the printer folds it back, and a
hypothesis a case split refined to mention a later pattern variable has to be moved. And each
gap the printer has, now or later, would be a refusal. So the elaborator keeps each goal it
prints as terms (`goals.rs`, `GoalSnapshot`: the context's own variables, hidden ones included,
in an order where each type mentions only those before, a `let` of data with its value, and the
target, read back folded, no unknown left in them), keyed by the `?`'s span, the latest 256;
`Elaborator::open_goal_at` opens one for search and `Elaborator::check_proof_at` checks a proof
text in its context (the variables bound, those a proof can't name hidden), closing the term over
the context for the kernel. The printed text is the fallback when no snapshot was kept (the
std benchmark's made-up goals). The printer's own bugs remain display bugs (SW-969 item 5,
SW-971 item 3, SW-980 item 1, SW-967 item 5): goals still show `split.%match1`, and
`List.Any (y => y = y)` for `y ∈ xs` with a `y` in scope.

**Better candidates**, each measured on the benchmark:

- **Specific lemmas first** (19 → 20 with the next two): the candidates tried, 50 at most, are
  ordered by how many definitions their conclusion names, then as `search` ranks them. A `≤` on
  `Nat` is `Nat.leq a b = True`, which every `b = True` lemma fits; those had filled the 50 and
  pushed `List.countLeMem` (day 11) to 75th.
- **`Eq.sym`**: an equation goal is searched the other way round too; a lemma found so is
  suggested as `Eq.sym (L …)` (day 14's `List.sumByFlatMap`).
- **Hypotheses**: one that is the goal closes it; each equation or `Iff` is tried as a rewrite
  both ways (day 16's `rewrite <- h in ?`, a step; the lemma after it, `List.takeAppend`, needs
  a second round, not built).
- **No-op results**: an applicable result that leaves the goal itself is dropped
  (`Bool.canonicalTrue … ?`, SW-963).
- **Witnesses** (21 → 23): the "folded goal" misses (days 15 and 17, SW-965 item 3) weren't about
  folding: matching unfolds `flatMap` and `count` (calls are compared by their arguments, then
  unfolded), and `List.distinctFlatMap` and `List.memFlatMapIntro` matched. Their plans failed
  because an explicit argument only premises mention (`key`, `x`) was written `_`, which
  elaboration can't work out. Such an argument is now a `?` for the writer, when the lemma's
  conclusion names a definition inside its relation, and the suggestion lists the goals it
  leaves, after the others.
- A long solved argument (the goal's term computed) is written `_` where that checks the same.

**Not built** (what the benchmark still misses, and the rest of SW-989's list):

- **The induction hypothesis** (4 goals: days 10, 12, 16, 17). In an equation-style theorem the
  recursive call is the declaration being proved, which isn't finished, so it isn't a candidate,
  and a proof checked at the goal can't name it. Offering it means binding the declaration in the
  goal's context as a hypothesis and checking termination only in the file (project files already
  are), with `checked: elaborated` in a file on its own; and offering `omega [IH]` as a closer.
- **A second round**: a rewrite by a hypothesis followed by a lemma (`rewrite <- h in
  List.takeAppend xs ys`).
- Day 9's `List.length (Map.keys r) = Map.size r` (`Map.sizeToList` under `Eq.trans`).
- Not measured, not built: conjuncts of a conclusion that is a defined conjunction
  (`Graph.distancesShortest`), class laws as lemmas (`Ord`'s `equal`), the generated `T.ext`,
  `byDecision` obligations on undecidable goals, a premise pattern `P → _` matching a later
  premise, `--in NAMESPACE`.
- Found: one closer check can cost a lot. `cases` as the obligation of
  `Std.Float.Theory.magUnitsLeReflect line 3 ?` (a goal `line < 4`) took 1.5 s and 1.2 GB; each
  check runs under the declaration's resource limits, and a smaller step budget doesn't stop
  `cases` (tried: no change). Fixed in SW-1082: the cost was the size limit (10M nodes of a value,
  `Nat.leq (magUnits a) (magUnits c)` grown until it tripped it), so a tried proof is checked
  under 200,000 nodes (`Elaborator::proof_limits`; not through `options.limits`, which key the
  check cache). Goal 2 of the `what_closes_a_goal` file: 1.55 GB to 0.31 GB, same answers; the
  lane tests no longer leave that lemma out.

## As built (SW-993, stage 3 follow-ups)

SW-993 (1 November 2026) built four of stage 3's "Not built" items, `--in`, and made the query log
safe to switch on. Each was measured on the AoC 2021 benchmark, run once per item on a shared
machine.

**The benchmark first.** It panicked on main: six of its goals no longer matched their files
(SW-983 replaced AoC proofs by new std lemmas, SW-984 moved day 15's into `Aoc.Common`). Each was
put back as the lane met it: the theorem written again with `?` (day 10's `toNatAtMostOne` and
`countAtMostLength`, day 16's `takeAppendLength`), or the `?` where the std lemma now stands, that
lemma left out (`exclude`: day 9's `Map.lengthKeys`), or the same proof's new text (days 11 and
15). Main's search scored 23 of 29 on it, as SW-989 reported.

| | closed by what the proof used | offered as a step | hit rate |
|---|---|---|---|
| main (benchmark repaired) | 10 of 23 | 7 | 23/29 (79%) |
| + the induction hypothesis | 13 | 7 | 26/29 (90%) |
| + a hypothesis's rewrite, then a lemma | 14 | 7 | 27/29 (93%) |
| + one-premise arrows, conjuncts, `--in` | 14 | 7 | 27/29 (93%) |

Self-retrieval over std is unchanged after every item (conclusions 87.6% strict top-1, MRR
0.917; left sides 80.8%, 0.880; no internal error). The benchmark's bar is now 80% (it was 70%).

- **The induction hypothesis** (days 12, 16's `lengthEvaluateAll`, 17 closed). The goal keeps,
  beside its terms, what the declaration's parameters stand for there
  (`GoalSnapshot::owner_args`: the context's first variables, `Cons x rest` for a list a case
  split took apart). A goal variable inside a constructor of one, of its type, is structurally
  smaller (`n` of `Succ n`, `rest`), and only such calls are offered: each choice of smaller
  variables (four at most) is planned with the other arguments as at the goal, premises from
  hypotheses (`visitsMember cave rest later`), and, for an equation, with a side matched against a
  call of the target, which solves the rest (`dyAfter n (step probe)`: matching `Nat.iterate n
  step ?p` against `Nat.iterate (Succ n) step probe` unfolds the latter). Each call is checked with
  the declaration bound at the goal as a hypothesis of its type (`check_proof_at`'s `recursive`):
  alone, as `omega [call]`, and as a rewrite. The target and the instantiated conclusion often
  compute to forms the unifier doesn't equate (`x + 2 * Succ n` and `2 + (x + (n + n))`), so the
  arguments are checked against their parameters' types instead when that fails. Termination is
  checked only with the proof pasted: in a project every closing suggestion is (stage 2b), so
  there it is; in a file on its own nothing checks it, and the suggestion says `checked:
  elaborated`. When nothing using it closes, the calls are listed (`inductionHypotheses`), and the
  benchmark counts them as steps. A computed argument is printed as computed (`dyAfter n ({ x =
  probe.x + probe.dx, … })` for `step probe`); it checks, but reads worse than the original.
- **A rewrite by a hypothesis, then a lemma** (day 16's `takeAppendLength` closed): when a
  hypothesis's rewrite leaves a goal no closer closes, that goal, opened from its statement in the
  checking session, is searched for lemmas that close it with nothing left open, each checked at
  the first goal after the rewrite (`rewrite <- h in List.takeAppend xs ys`). Only after a
  hypothesis's rewrite, not a lemma's (lengthBitsOf's `lengthSnoc` then the induction hypothesis,
  and pairsStep's two rewrites, remain steps).
- **Class laws and `T.ext`**: both were already candidates (a law is a theorem; `Point.ext`
  matches `(?a: Point) = ?b` and closes `a = b` from `hx` and `hy` at a goal). The miss was the
  pattern's shape: a function-type pattern with one premise (`Ord.compare ?x ?y = Equal → ?x =
  ?y`) is matched whole from the candidate's first explicit parameter (`x`), and the reordered
  match, which skips the candidate's extra parameters, required two of the pattern's. It takes one
  now; `(?a: Nat) < ?b → ?a ≤ ?b` finds `Nat.lessLe` first too (both are hand queries). Not built:
  `Eq.cong` around a lemma (`Some a = Some b` from `Point.ext`, day 18's `shiftAppend`).
- **Conjuncts** (`Item::Part`): a theorem whose conclusion is a conjunction, written or the body
  of the definition it calls (`Graph.Shortest`), is a candidate per conjunct too, nested to three
  deep, but only where written as a conjunction: a conjunct that is itself a call isn't unfolded.
  Unfolding every conjunct was tried first: AoC 2021 day 11's `Part2Answer` gave `AllFlashIn`'s
  `1 ≤ answer`, which fit day 12's `1 ≤ visits …`, and checking its theorem's `rfl` premise took
  145 s. A conjunct ranks after declarations that match as well. Results say `conjunct` (`left`,
  `right.left`); proofs take it with `And.left (…)`. No benchmark goal uses one.
- **`--in NAMESPACE`**, repeatable, for `search` and `--at`.

**The query log.** It is opt-in (`--log FILE` or `STITCHWORT_SEARCH_LOG`), and nothing set it, so
nothing was logged. Version 1 wrote `cwd`, the absolute folder (naming the user's home), and file
paths as given; version 2 writes no folder, and paths relative to the folder the command ran in
(or a file's name alone outside it). It appends to a local file; nothing is sent. The event for
"the lemma the next `check` used" is still not built. Proposed, not done (lane setup unchanged):
lanes that prove theorems set `STITCHWORT_SEARCH_LOG` to a file per lane in an ignored folder of
the main checkout that outlives worktrees (`search-logs/<ticket>.jsonl`, the folder in
`.gitignore`), and a merge leaves the file there; reading the logs is a separate step that never
leaves the machine.

**Not built, or still missing**: day 9's `Map.sizeToList` under `Eq.trans` (skipped);
`byDecision` on undecidable goals and premise patterns in any position (skipped); day 16's
`groupsValue` (closed by `cases`, but not by what the proof used); a lemma's rewrite followed by
the induction hypothesis (lengthBitsOf, pairsStep, countAtMostLength stay steps).

**Found**: one closing check can take minutes and gigabytes, and nothing stops a check once
started (the deadline is read between checks). AoC 2021 day 16 `Sound.sw`'s `totalThen` took
45 s to 345 s in the five runs of the daily sample, almost all of it one check of `List.consInjective
_ (Cons …)` (289 s in a run with timings): a std lemma's plan, a path this work didn't change, so
probably as before it (stage 2b reported 290 s at most for such a namespace) [inferred]; one run of the sample (after the conjuncts, before they stopped
unfolding) was stopped by the 16 GB memory guard, the goal not identified. A step and memory limit
per check, smaller than the declaration's, would bound both.

**A check's time limit (SW-1017, 1 November 2026).** Each closing check of `search --at` may take
half of `--time` (and no more than is left), and is stopped from inside: `Budget::set_deadline`
(`crates/core/src/budget.rs`) is read every `POLL` evaluation steps, like the cancellation flag, and
ends the operation with `ResourceError::Deadline`. Unlike running out of steps it is not "no": an
attempt inside the check passes it on, as out-of-stack does, so a slow machine never turns a
comparison into a different elaboration. A check stopped this way is counted (`budget.gaveUp`,
omitted when zero) and named in a warning; it is never reported as a failed check. Nothing changes
when no check reaches the limit. Measured on AoC 2021 day 16 `Sound.sw:83` (`totalThen`, `--time 600s`):
the closing phase took 926 s, nearly all one `List.consInjective _ (Cons …)` check, and with the limit
it ends at the time given (`--time 40s`: 40 s, the two `consInjective` checks given up at 20 s). Still
unbounded: the in-file confirmation of each closing suggestion (it checks the namespace again, 70 s
here for three), and a memory bound (no per-check term-size cap exists; `Limits::size` is 10 million
nodes and only bounds quoting).
