# Proposal: `stitchwort search`, lemma search by type

**Status:** draft 2, 30 October 2026. Ticket SW-915, from
[agentic-proving.md](../research/agentic-proving.md) T4 and §7.4. Draft 1 (D2044) compared only
Lean's tools; draft 2 (D2052) compares the wider field, settles the design questions draft 1 left
open, and measures them with the prototype `stitchwort dev search` (hidden, experimental). Three
decisions are in [§9](#9-decisions-for-matt). An external reviewer's brief is
[search/review-brief.md](search/review-brief.md).

Labels:

- **[read: Sn]**: from source card Sn in [§2](#2-what-others-do-the-cards), read as the card says;
- **[cited: Cn]**: from a card in [agentic-proving.md](../research/agentic-proving.md) §4;
- **[checked: file:line]**: read in the Stitchwort source, at `a4546812` plus this branch;
- **[run]**: run with the release CLI built from this branch on 30 October 2026, under
  `dev/memguard --cap-gb 2`. The machine was shared with other lanes (load average 7–10 for the
  draft 2 runs); times vary between runs;
- **[inferred]**: my reasoning from the above; **[unverified]**: believed, not confirmed.

## The short answer

- **The field agrees on the core, and draft 1 had it.** Every type-pattern search read here
  (Loogle, Isabelle's `find_theorems`, Rocq's `Search`, Hoogle) filters by the constants a pattern
  names, then matches structurally; none needs a model. Isabelle's `find_theorems` uses the same
  constants-subset prefilter as Loogle [read: S4, S7].
- **Ranking: specificity first, then size.** Over a benchmark of 2,301 std conclusions and 1,537
  equation left sides, each searched for with its own statement, ranking by how specifically a
  theorem fits (draft 1's `absorbed` and `instantiated`) puts it first 80–88% of the time; ranking by
  size, as Isabelle, Rocq and Loogle do, 63–73% [run, §6.1]. Size and hypothesis count stay as
  tie-breaks. Rarity weighting (MePo, MaSh, Hoogle) adds nothing measurable after specificity and
  costs 8–9 points before it.
- **Argument order: match hypotheses in any order, and let the theorem have more (Loogle's
  `matchHyps`).** Without it, `(_: Nat) ≤ _ → _ ≤ _ → _ ≤ _` misses `Nat.leTrans`, because std
  states variables as explicit parameters; with it, `leTrans` is second of 38 [run, §6.2].
- **A rewrite mode, as Rocq's `SearchRewrite`.** `mode:rewrite, List.length (List.append _ _)`
  finds `lengthAppend` then `lengthSnoc`, and nothing else [run, §6.3]. It must use equations as
  stated: forcing `≤` to its computed equation lost 257 of 1,767 lemmas. Our 8 recorded `rewrite`
  failures, read again, are about how `rewrite` works, not about finding a lemma (§5.3).
- **Instances: search twice.** A pattern that names an interface field at a concrete type
  (`Ord.compare (?x: Nat) ?x`) elaborates to the instance's function (`Nat.compare`) and loses the
  generic lemma (`Ord.compareSelf`); the generic pattern loses the `Nat` one [run, §6.4]. Search
  both and merge.
- **No natural-language search, now or in the stage plan.** The tools that do it need a hosted 7B
  embedding model and an LLM per query (LeanSearch) or a trained encoder served from a GPU or CPU
  server (LeanPremise) [read: S11, S12]. Our users are agents, which write patterns; for
  pattern-like queries even LeanSearch's model did best on the formal text alone [read: S11].
- **D2045 and D2046 stand, changed:** the filter gains data types (`List`, `Nat`), whose absence
  leaves `List _ → Nat → List _` unfiltered (247 matches, 35 ms) [run]; no on-disk index.
- **Stage 2** builds on SW-914's goals: the goal's `target` becomes a conclusion pattern with the
  hypotheses' names as named holes, and the candidates are tried at the `?` (§5.7). The candidate
  lists are short: median 1, 90th percentile 23 theorems per conclusion [run, §6.1].
- **Found on the way:** an internal error in evaluation (`applying a constructor`,
  crates/core/src/value.rs:815) on 4–12 pairs of std theorems during matching (§6.1), and 13
  conclusions that unification can't match even with themselves, all higher-order (§6.1).

## 1. The problem, with our evidence

Unchanged from draft 1, in brief:

- Lanes found lemmas only with grep, and twice rewrote lemmas std already had:
  "finding `tailOf`, not `tail`, took a grep" [checked: aoc/NOTES-2024.md:373]; "I first wrote
  `compareSelf` and `lessNotGreater` too, then found std's `Ord.compareSelf` and
  `Ordering.lessNotGreater` by grepping the std sources; with no search by type, a lemma is easy to
  miss" [checked: aoc/NOTES-2024.md:7906–7909].
- Missing std lemmas are the largest friction category, about 40 items (agentic-proving.md §5,
  row A).
- Agents elsewhere lean on search: mini-Lean-agent's most useful single step was `exact?`
  [cited: C1]; Ax-Prover's agents called Loogle 5.88 times a run [cited: C8]; removing vstd and
  the cheat checker together cost VeruSAGE up to 26% of tasks [cited: C20].
- Grep needs the name or the exact spelling and line layout (draft 1 §1's three examples:
  `++` is written `List.append` in std statements; a conclusion on the line after `theorem`).

**New evidence for argument order** [run]: `List.map _ (List.map _ _)`, the Lean and Haskell
order, is a type error in Stitchwort, whose `List.map` takes the list first
(`[E-TYPE-MISMATCH] … expected ?0 → {?1} ?3, but this has type List ?8`). So is
`List.Sorted (List.sort _)`, whose relation comes first. An agent's habits from other libraries
show up as argument-order mistakes in patterns, at the term level as well as in function types.

## 2. What others do: the cards

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
| **Stitchwort, draft 2** | `_`, `?x`, `⊢`, `"name"`, bare lowercase names; `--rewrite` | two-way unification on folded types, per-theorem budget, after a constants filter (definitions and data types) | `matchHyps` for arrow patterns (§5.2) | dual search: instance resolved and generic (§5.4) | `--rewrite`: either side of a stated `=` (§5.3) | place, specificity, hypotheses, size, name; fields in JSON (§5.1) | in memory, built per run from the check cache (§5.6) | `--json` with name, type, file:line, `import` line, ranking fields |

## 4. The revised design

Draft 1's design stands except where §5 changes it. In one place:

- **Command:** `stitchwort search 'PART, PART, …' [--project DIR | FILE] [--rewrite] [--json]
  [--limit N] [--defs] [--all]`; exit 0 with results, 1 with none, 2 for a pattern that doesn't
  elaborate.
- **Parts:** `"text"` (name substring), a bare qualified name (the type mentions it), a pattern
  with `_` and `?x`, `⊢ pattern` (conclusion only), bare lowercase names as named holes (so a goal
  can be pasted). Overloaded operators with an unknown operand type are tried at each resolution
  and the results merged (draft 1 §3.1).
- **Scope:** all of std, loaded eagerly through the check cache, plus the project; `%` helpers,
  generated declarations and `…Example` theorems hidden unless `--all`; unfinished declarations
  not searched.
- **Filter:** a theorem is compared only if its type, read back folded, mentions every
  definition **and data type** the pattern mentions (§5.6). A pattern that names neither is
  searched unfiltered, with a warning.
- **Matching:** draft 1's two-way unification on folded types with a 200,000-step budget per
  theorem, named holes distinct; targets in order: whole type, reordered parameters (§5.2),
  conclusion, hypotheses, calls inside. With `--rewrite`, only the two sides of a conclusion
  stated as `=` (§5.3).
- **Instances:** a pattern that names an interface field (`Ord.compare`) at a concrete type is
  searched twice, as elaborated and with the dictionary a hole, and the results merged (§5.4).
- **Ranking:** place; `absorbed`; `instantiated`; hypotheses; size; name (§5.1). Every key is in
  the JSON.
- **Output:** as draft 1 §3.6, plus `hyps` and `size` in the JSON; places `whole`,
  `reordered`, `conclusion`, `left`, `right`, `hypothesis`, `inside`.

## 5. The seven questions, settled

### 5.1 Ranking near-matches

**What others do.** Size first: Isabelle (size, premises, substitution size), Rocq (3 × distinct
constants + size), Loogle (module order, size) [read: S3, S4, S7]. Hoogle sums hand-set costs,
tuned by a constraint solver against a list of complaints [read: S1]. MePo and MaSh weight rare
symbols [read: S5, S6]. `exact?` orders by how much of the discrimination-tree key matched,
which is a specificity measure [read: S8].

**What we measured** (§6.1). A benchmark that doesn't depend on hand-picked queries: every std
theorem's own conclusion (2,301 queries) and every equation's own left side (1,537), with the
theorem's variables as holes. The theorem itself must be found; where it ranks measures the
ranking. Rank 1 (counting ties in its favour):

| Ranking | conclusions | left sides |
|---|---|---|
| draft 1: place, absorbed, instantiated, name length | 88.0% | 81.9% |
| **proposed: place, absorbed, instantiated, hypotheses, size** | **88.2%** | **80.5%** |
| proposed with rarity after specificity | 88.0% | 81.7% |
| rarity first, then specificity | 79.2% | 72.2% |
| Isabelle: size, premises, substitution size | 73.1% | 64.3% |
| Rocq: 3 × constants + size | 73.4% | 65.5% |
| Loogle: load order, size | 70.6% | 63.4% |

**The decision: specificity first, then hypotheses, then size, then name.**
- Specificity (`absorbed`: how much of the pattern the theorem's own variables swallowed;
  `instantiated`: how many holes had to become more than a variable) is the substitution-size
  idea of Isabelle and the "more general is fine, less general isn't" lesson of Hoogle's slides,
  made the primary key. It is what separates `x = x`-style lemmas from the one asked for.
- Hypotheses and size are tie-breaks among equally specific matches, as Isabelle orders them.
  The benchmark cannot judge tie-breaks (its target is exactly specific by construction), and
  the hand queries split: size puts `memMap` first and `lengthAppend` second; draft 1 the reverse
  (§6.1). So the order among ties is tuned the way Hoogle tunes it: from a list of real queries
  and the lemma the agent then used, kept as a regression test (S1 below).
- Rarity is dropped: it moves nothing after specificity, and costs 8–9 points before it.
- `place` stays first: a lemma about the shape beats one that merely uses it.

### 5.2 Argument order and currying

**What others do.** Loogle and Mathlib's `#find` match a function pattern's parameters in any
order, and let the theorem have more (`matchHyps`) [read: S7, S10]. Hoogle swaps two-argument
queries only and costs arity differences [read: S1]. Idris and draft 1 need the same order and
arity [read: S2]. Rittri's and Runciman's isomorphism search (currying, tuples) is in Hoogle's
history and was dropped as "less useful for modern code" [read: S1, slides].

**What we measured** (§6.2) [run, with `--defs`]:
- `List _ → Nat → List _` finds `List.drop`, `List.take`, `List.chunksOf`, `List.removeAt`,
  `List.dropRight` first in every mode. Asked the other way round, `Nat → List _ → List _` finds
  nine `Nat`-first functions; with reordering `drop` and `take` follow at 10 and 11. Reordering
  adds 8 matches (252 → 260); letting the theorem have more parameters adds 26 (→ 278).
- `(_: Nat) ≤ _ → _ ≤ _ → _ ≤ _` (transitivity) **misses `Nat.leTrans`** in draft 1's mode and
  with same-count reordering: `leTrans` is stated `(a b c: Nat) → a ≤ b → b ≤ c → a ≤ c`, five
  explicit parameters against the pattern's two. With `matchHyps` it is second of 38, after
  `Nat.leMin`; the 11 draft-1 matches were all incidental hypotheses.
- Currying is not a separate problem in a dependently typed language whose functions are all
  curried; std has no tuple-taking variants to equate [inferred].

**The decision: `matchHyps` for arrow patterns** (the `subset` mode): conclusion against
conclusion, then each pattern parameter against a different theorem parameter, greedily; exact
order ranks first (`whole` before `reordered`). It is needed for implication patterns, which are
how an agent asks for a transitivity or monotonicity lemma. Pattern binders are opened as rigid
variables, not unknowns: a hole under an arrow is an unknown applied to them, which unification
solves only then (the prototype found nothing until this was fixed, commit `2d342995`).

Term-level order (`List.map _ (List.map _ _)`) is a different problem: the pattern doesn't
elaborate. S1's elaborator could try permuting the explicit arguments of an ill-typed application
in a pattern, as the overloaded-operator fallback does for `++`. Not designed here; the error
message already shows the expected type.

### 5.3 A rewrite-search mode

**What others do.** Rocq's `SearchRewrite` (either side of `eq`), Isabelle's `simp:`, and `rw?`
(lemma sides against every subterm of the goal, both directions, `rfl` first) [read: S3, S4, S9].

**What we measured** (§6.3) [run]:
- `mode:rewrite, List.length (List.append _ _)`: `lengthAppend` (left, exact), `lengthSnoc`;
  2 matches. `mode:rewrite, List.reverse (List.reverse _)`: `reverseReverse`, then its example.
  `mode:rewrite, List.map (List.map _ _) _`: `mapMap` first of 14. `mode:rewrite, Ord.compare ?x ?x`:
  `compareSelf` first.
- Taking "the conclusion is an equation" after evaluation, as draft 1's matching would, lost 257
  of 1,767 left sides: `≤` on `Nat` computes to a `Bool` equation, so `Nat.leRefl`'s conclusion
  "is" an equation whose sides no pattern names. Using equations as stated: 17 of 1,537 lost, all
  higher-order (§6.1).
- `mode:rewrite, (_: Nat) + 0` returned 1,564 matches: `+ 0` computes away, the pattern names no
  definition, and every equation over `Nat` matches. A pattern that elaborates to a bare hole
  must be refused, not searched [inferred].

**Our corpus.** agentic-proving §5 row E counts 8 `rewrite` failures. Read again
[checked: aoc/NOTES-2024.md:308–331, 667–692, 876–907, 2550–2556]: they are `rewrite` missing a
term the goal has already unfolded (items 3, 8 and 6 of their days), a hole that can't solve an
instance argument, `rewrite` with `_` rewriting one instance only, and a missing congruence
lemma (`List.allCong`). Only the last is a finding problem, and rewrite search would have shown
that `List.anyCong` exists and `List.allCong` doesn't. So rewrite search is worth having for the
`rw?`-style question "what can I rewrite this with", not as a fix for row E [inferred].

**The decision:** `--rewrite` in S1, Rocq's semantics (either side of a stated `=`, places
`left`/`right`); the reverse direction (`rw?`: the goal's subterms against lemma sides) in
stage 2, where there is a goal (§5.7).

### 5.4 Instances and generic functions

**What others do.** Loogle elaborates with type-class failures ignored and no default instances,
so a generic pattern stays generic [read: S7]. Hoogle charges for constraints the query lacks
[read: S1]. Rocq filters `is:Instance` [read: S3].

**What we measured** (§6.4) [run]:
- `Ord.compare ?x ?x = _` (type unknown): `Ord.compareSelf` first of 38, all generic `Ord`
  lemmas; `Nat.compareSelf` is not among them.
- `Ord.compare (?x: Nat) ?x = _`: the instance is resolved and the field projection computes:
  the pattern's constants are `[Std.Nat.compare]`, `Nat.compareSelf` is first of 10, and the
  generic `Ord.compareSelf` is filtered out.
- `List.sort _ = _` finds `sortEqOfPerm` first; the `[auto ord: Ord a]` argument is an unknown
  that unifies with each lemma's. `DecEq.decide _ _` and `Show.toText _` find nothing: std's
  lemmas are stated with `==` and with concrete `toText` functions.

**The decision:** in a pattern, an `auto` argument that elaboration does solve, at a concrete
type, makes a second search with that dictionary left a hole (draft 1 already leaves unsolved
ones as holes); the results are merged, the concrete ones first by the ranking (they are more
specific). The pattern is never sent to `auto` itself.

### 5.5 Natural-language search

**What others do.** LeanSearch: an LLM translates the library once, a 7B embedding model serves
queries, an LLM rewrites each query [read: S11]. LeanPremise: a 23–82M encoder served by FAISS,
trained on 206,005 proofs [read: S12]. MaSh: a learned selector with no neural model, from
proofs, local, "a few hundred milliseconds" [read: S6]. Lean Finder and Moogle: not read.

**The decision: no, and not in the stage plan.** The reasons:
1. Agents, our main users, write patterns: the friction notes' searches were all for a shape
   (§1), and the agent already holds the natural-language understanding a query rewriter would
   add.
2. LeanSearch's own data: for queries written as formal terms, the formal-only corpus without
   augmentation did best (0.774 against 0.612) [read: S11].
3. Cost: a model at query time is a server or a multi-gigabyte local download, which the
   check-and-search CLI otherwise doesn't need; LeanSearch names laptops as a limitation.
4. 40% of std theorems have a comment line just before them (912 of 2,282) [run: grep], so a
   lexical fallback over names and comments is cheap if it is ever wanted.

Revisit if logged queries (§7, S1's query log) show agents searching for things they can't
shape, or if people, not agents, become the main users of search. The cheap next step then is
MaSh's: learn from std's proofs which lemmas similar statements used, with no model to serve.

### 5.6 D2045 and D2046, revisited

**D2045 (the constants filter): keep it, and widen it.**
- It loses nothing: on the 2,301-conclusion and 1,537-left-side benchmarks, every theorem not
  found with the filter is also not found without it (13 and 17, all higher-order) [run, §6.1].
  That is draft 1 assumption 2's self-retrieval test, run on all of std.
- It is what keeps other rankings usable: without it, Isabelle's ranking finds the theorem first
  in 9.7% of conclusions instead of 73.1%, because unfolding brings in small, false matches
  [run].
- It costs 9.5 s for the 2,301 conclusion queries filtered, 75 s unfiltered [run].
- **Widen it to data types.** The filter collects `DefId`s only; `List`, `Nat` and `Option` are
  data types, so `List _ → Nat → List _` names "no constant", is searched unfiltered (0 skipped,
  247 matches, 35 ms), and false matches through unfolding head the list for
  `List ?a → Nat → List ?a` (`Effect.bindIn`, `doneIn`, `lowerIn`) [run]. Hoogle's
  fingerprint is mostly type constructors [read: S1].
- Isabelle's filter is the same rule, with a soundness note: it is sound because matching uses
  higher-order patterns [read: S4]. Ours is sound in the same sense, a missed result rather than
  a wrong one (draft 1 §3.3).

**D2046 (no on-disk index): keep it.** Nothing in draft 2 needs one: the filter index is built in
20 ms, the benchmark's 2,301 searches take 4 ms each [run]. Hoogle's history argues against an
elaborate index ("required a lot of babysitting") [read: S1]; Loogle's on-disk cache exists
because Mathlib is 100 times std [inferred].

### 5.7 Stage 2: what closes this `?`

**What it builds on.** SW-914 merged: `check --index` writes, per open goal, `hypotheses`
(name, type), `target`, and a paste-ready `lemma` [run, §6.5]:

```json
"goal":{"hypotheses":[{"name":"xs","type":"List Nat"},{"name":"ys","type":"List Nat"}],
 "target":"List.length (List.append xs ys) = List.length xs + List.length ys",
 "lemma":"theorem lengthTwiceGoal1 (xs: List Nat) (ys: List Nat): List.length (List.append xs ys) = List.length xs + List.length ys := ?"}
```

**How stage 2 uses it.** `stitchwort search --at FILE:LINE:COL` (or `check --suggest`):
1. Read the goal of the `?` from the same index.
2. **Conclusion candidates:** the `target` as a `⊢` pattern, the hypotheses' names as named
   holes, run with this note's matching, filter and ranking. Run now by hand,
   `⊢ List.length (List.append ?xs ?ys) = List.length ?xs + List.length ?ys` finds
   `lengthAppend` alone [run]. Over std, such queries return a median of 1 candidate, 23 at the
   90th percentile, 544 at the 99th [run, §6.1]. Isabelle's `solves` and `exact?` do this step
   with a goal [read: S4, S8].
3. **Fill the rest:** for each candidate, in rank order, its remaining explicit parameters from
   a hypothesis of the right type (unification), else a decision procedure (`auto`), else leave
   `?`; elaborate `lemma args…` against the goal in a transaction and kernel-check it.
4. **Rewrite candidates** (`rw?`'s direction): for each subterm of the target, the lemmas whose
   stated left (or right) side matches it, under the same filter; report the rewritten goal,
   those that then close by `rfl` first [read: S9].
5. Report complete closures first, then "closes with N new goals", each with the text to paste;
   stop after a budget (50 candidates by default), as `exact?` stops at 10% of its heartbeats.

It can't make a proof wrong: every suggestion is elaborated and kernel-checked as written.

## 6. The measurements

All with the prototype on this branch [run]. To reproduce:
`docs/proposals/search/queries-draft2.sh [CACHE_DIR] [self|order|rewrite|instances|ranking]`.
The directives (`mode:`, `rank:`, `self:`) are parts of the query string, so `main.rs` is
unchanged.

### 6.1 Self-retrieval over std

For each std theorem T, the pattern is T's conclusion (or, for an equation stated with `=`, its
left side) with T's variables as holes; the search runs over all 2,328 std theorems; the
benchmark records whether T is found and where it ranks. "Opt" counts ties in T's favour, "pess"
against it.

| | conclusions | left sides (`mode:rewrite`) |
|---|---|---|
| queries | 2,301 (27 skipped: the conclusion is a variable) | 1,537 (791 skipped: not stated as `=`) |
| T not found, with the filter | 13 | 17 |
| T not found, without the filter | the same 13 | the same 17 |
| matches per query (median / p90 / p99 / max) | 1 / 23 / 544 / 1,877 | 2 / 16 / 133 / 1,373 |
| time for all queries, filtered / unfiltered | 9.1–9.5 s / 75 s | 3.9–6.9 s / 54 s |
| unifications that ran out of budget, filtered | 948 of 557,200 | 256 of 216,285 |
| internal errors (panics), filtered / unfiltered | 4 / 12 | 2 / 10 |

Rankings, filtered (rank 1 opt, top 3 opt, MRR opt, mean pess):

| Ranking | conclusions | left sides |
|---|---|---|
| draft1 | 88.0%, 95.5%, 0.921, 1.58 | 81.9%, 95.7%, 0.890, 1.80 |
| draft1+hyps | 87.1%, 95.1%, 0.915, 1.58 | 80.3%, 95.0%, 0.880, 1.49 |
| **proposed** | 88.2%, 95.1%, 0.921, 1.61 | 80.5%, 95.4%, 0.883, 1.49 |
| proposed+rare | 88.0%, 95.4%, 0.920, 1.55 | 81.7%, 95.6%, 0.889, 1.74 |
| rare-first | 79.2%, 87.7%, 0.841, 6.16 | 72.2%, 88.7%, 0.814, 2.45 |
| isabelle | 73.1%, 84.8%, 0.798, 10.01 | 64.3%, 84.7%, 0.757, 2.91 |
| rocq | 73.4%, 84.9%, 0.802, 9.03 | 65.5%, 85.0%, 0.766, 2.89 |
| loogle | 70.6%, 83.4%, 0.781, 9.89 | 63.4%, 84.3%, 0.751, 2.78 |

Unfiltered, rank 1 opt for conclusions: draft1 86.0%, proposed+rare 87.7%, isabelle 9.7%, rocq
8.4%, loogle 6.2%.

**What it says** [inferred]:
- The filter never cost a result on std, and size-based rankings depend on it.
- Specificity-first rankings are within 2 points of each other; the tie-break among them isn't
  decided by this benchmark (its target is exactly specific by construction), so it comes from
  real queries (S1's query log).
- **The misses are higher-order.** Of the 13 conclusions, 6 were looked at: `List.memOfAll`
  (`… → p x`), `Eq.cong` (`f x = f y`), `Bool.inspect` (`motive b`), `Map.induction` (`p m`),
  `List.sumRangeZero` (`f x = 0`), `List.findKey` (`key y = kk`) [checked]: a theorem variable
  applied in head position, which two-way unification of unknowns can't solve. Isabelle's
  higher-order pattern matching handles these [read: S4]; one-way matching with the theorem's
  variables rigid would too [unverified].
- **A bug:** `internal error: applying a constructor` (crates/core/src/value.rs:815) on pairs such
  as `Std.Parse.runFromMark` against `Std.Parse.runFromNatThere` and, unfiltered,
  `Std.List.sumByRangeSucc` against `Std.List.occurrencesOr`. The benchmark catches and counts
  them; a real `search` must not panic. To be filed as a bug with these pairs.

Draft 1's hand queries, the known lemma's rank:

| Query | draft1 | proposed | isabelle | rocq | loogle |
|---|---|---|---|---|---|
| `List.length ((_: List _) ++ _) = _` → `lengthAppend` | 1 | 1 | 2 | 2 | 1 |
| `_ ∈ List.map _ _` → `memMap` | 3 | 3 | 1 | 1 | 2 |
| `Nat.min _ _ ≤ _` → `minLeLeft` | 1 | 1 | 1 | 1 | 2 |
| `Ord.compare ?x ?x = _` → `compareSelf` | 1 | 1 | 1 | 1 | 2 |
| `⊢ Not (Less = Greater)` → `lessNotGreater` | 1 | 1 | 1 | 1 | 1 |

### 6.2 Argument order (`--defs`)

| Query | plain | `permute` | `subset` (`matchHyps`) |
|---|---|---|---|
| `List _ → Nat → List _` | 247; `drop`, `take` 1–2 | 255; same top | 266; same top |
| `Nat → List _ → List _` | 252; nine `Nat`-first functions | 260; `drop` 10, `take` 11 | 278 |
| `(_: Nat) ≤ _ → _ ≤ _ → _ ≤ _` | 11; no `leTrans` | 11; no `leTrans` | 38; `leMin` 1, `leTrans` 2 |
| `List ?a → Nat → List ?a` | 221; `Effect.bindIn`, `doneIn`, `lowerIn` first | 221 | n/a |

The last row is draft 1's named-hole-under-a-binder gap together with the missing data-type
filter: the pattern names no definition, so it is unfiltered and unfolding wins.

### 6.3 Rewrite search (`mode:rewrite`)

| Query | Result |
|---|---|
| `List.length (List.append _ _)` | `lengthAppend` (left 0 0), `lengthSnoc`; 2 matches, 19 of 2,328 compared |
| `List.reverse (List.reverse _)` | `reverseReverse`, `reverseReverseExample`; 2 |
| `List.map (List.map _ _) _` | `mapMap` first of 14 |
| `Ord.compare ?x ?x` | `compareSelf` first of 6 |
| `(_: Nat) + 0` | 1,564: the pattern computes to a hole (§5.3) |
| `List.map _ (List.map _ _)` | type error: Stitchwort's `map` takes the list first (§1) |

### 6.4 Instances

| Query | Constants | Result |
|---|---|---|
| `Ord.compare ?x ?x = _` | `Ord.%compare` | `Ord.compareSelf` first of 38; no `Nat` lemma |
| `Ord.compare (?x: Nat) ?x = _` | `Nat.compare` | `Nat.compareSelf` first of 10; no generic lemma |
| `Nat.compare ?x ?x = _` | `Nat.compare` | the same 10 |
| `List.sort _ = _` | `List.sort` | `sortEqOfPerm`, `sortOfSorted`, `sortOfSortedNat` |
| `List.Sorted _ (List.sort _)` | | `sortSorted`, `sortSortedNat` (conclusion), 4 in all |
| `DecEq.decide _ _`, `Show.toText _` | | 0 |

### 6.5 Cost

As draft 1 §4.2 (load 4.1–4.5 s cold, 0.21–0.28 s through the check cache; filter index 19–25 ms;
a filtered match 0.1–0.5 ms), plus: a reordered match adds about 20% unifications
(16,638 → 19,960 for `List _ → Nat → List _`) [run].

## 7. Stage plan

| Stage | What | Tests |
|---|---|---|
| **S1** | `stitchwort search`: draft 1's S1 (syntax, filter, named holes under binders, hiding, JSON, `core/` paths) **plus** data types in the filter; `matchHyps` for arrow patterns; `--rewrite`; the instance dual search; the §5.1 ranking; refusing a pattern that elaborates to a hole; an opt-in query log (pattern, results, and the lemma the next `check` used) for tuning | the self-retrieval benchmark as a test: every std conclusion and left side found except a listed set of higher-order ones, none lost to the filter, no panic; rank-1 rate at least 85% / 78% (today's 88.2% / 80.5% less a margin); draft 1's hand queries; `leTrans` in the top 3 for the transitivity pattern; JSON snapshot |
| **S1a** | fix the `applying a constructor` panic (core) | the two pairs of §6.1 |
| **S2** | `search --at FILE:LINE:COL` from SW-914's goals (§5.7), conclusion and rewrite candidates, checked suggestions | for std theorems with the proof replaced by `?`: the theorem's own proof lemma, or one that closes it, offered; every suggestion re-checks when pasted |
| **S3** | LSP request and a code action at `?`; agent guide (T7); higher-order matching for the 13 + 17 misses, if logged queries show them | LSP round trip |

Tier: the self-retrieval test costs about 10 s for conclusions and 4–7 s for left sides with a
warm cache [run]; it belongs in the merge tier, with a 200-theorem sample in the lane tier.

## 8. Risks

- **Two-way unification admits crossed matches**: the theorem's variable takes pattern
  structure while a pattern hole takes theorem structure (`Nat.leMin` for
  `Nat.min ?a ?b ≤ ?a`, `[conclusion 23 2]`) [run]. The ranking puts them last; one-way matching
  (Isabelle, Loogle, Rocq) wouldn't produce them, but would lose matches where the agent pasted
  concrete terms. Keep two-way, rank by specificity, show the fields.
- **Higher-order misses** (13 conclusions, 17 left sides).
- **The panic** (§6.1), until S1a.
- **Ranking tie-breaks are unvalidated** beyond 5 hand queries; the query log is the remedy.
- **Patterns that compute away** (`(_: Nat) + 0`) or name nothing: refuse or warn.
- **Reordering widens results** by 3–10% on function patterns (§6.2); exact order ranks first.
- **Projects** are still unmeasured (draft 1 §8).

## 9. Decisions for Matt

**D2054 (replaces D2045). Should `search` filter by every definition *and data type* the pattern
names, match by unification inside the filter, and rank by specificity first?** Recommended:
**yes**.

The assumptions, in full:
1. A theorem that never mentions a definition or data type the pattern names is not what the
   agent asked for, even if it unifies after unfolding. Loogle and Isabelle make the same
   assumption for constants [read: S4, S7]; Hoogle's fingerprints rely on type constructors
   [read: S1].
2. The filter loses no result on std: every theorem not found with it is also not found without
   it, on 2,301 conclusions and 1,537 left sides [run, §6.1]. Adding data types to it is
   unmeasured; the self-retrieval test in S1 is what checks it.
3. Matching is draft 1's two-way unification of folded types, under a 200,000-step budget, with
   distinct named holes; a pattern that names an interface field at a concrete type is also
   searched with the dictionary a hole (§5.4).
4. Ranking is place, then `absorbed`, then `instantiated`, then hypotheses, then size, then
   name. It puts the theorem first for 88.2% of its own conclusions and 80.5% of its own left
   sides, against 63–73% for size-first rankings [run, §6.1]. The order among equally specific
   results is not validated by that benchmark and will be tuned from logged queries.
5. 13 conclusions and 17 left sides, all with a theorem variable in head position, aren't found
   by this matching; that is accepted for S1.

**D2055. Should S1 include `--rewrite` (either side of a stated equation) and `matchHyps`
(a function pattern's parameters matched in any order, the theorem allowed more), and leave
natural-language search out of the stage plan?** Recommended: **yes**.

The assumptions, in full:
1. Agents write type patterns; the friction notes' missed lemmas were all findable by shape
   (§1), and the agent supplies whatever natural-language understanding a query needs.
2. `matchHyps` is needed because std states variables as explicit parameters: without it the
   transitivity pattern misses `Nat.leTrans`; with it `leTrans` is second [run, §6.2]. It adds
   3–10% more results on function patterns, ranked after exact-order matches.
3. Rewrite search uses equations as stated (`Term::Eq` conclusions); taking computed equations
   lost 257 of 1,767 [run, §5.3]. It doesn't fix the 8 recorded `rewrite` failures, which are
   about `rewrite` itself; it answers "what rewrites this term".
4. Natural-language search needs a served model: a 7B embedding model plus an LLM per query
   (LeanSearch), or a trained encoder on a server (LeanPremise) [read: S11, S12]. For queries
   written as formal terms, LeanSearch's model did best on the formal text alone [read: S11].
   Revisit if the query log shows agents searching for what they can't shape, or if people
   become the main users; then try MaSh's model-free learning from std's proofs first [read: S6].

**D2056 (replaces D2046). Should `search` keep loading std through the check cache with an
in-memory filter and no on-disk index, and should stage 2 (`search --at`) be built on SW-914's
structured goals as §5.7 describes?** Recommended: **yes**.

The assumptions, in full:
1. Loading costs 0.21–0.28 s warm and 4.1–4.5 s cold; the filter index 19–25 ms; a filtered search
   about 4 ms on average over the 2,301-query benchmark, with patterns made and ranked [run].
   Those times were taken on a shared machine and would be lower on a quiet one.
2. The check cache is invalidated exactly when an index would be (a compiler rebuild, a std
   edit), so an on-disk index would only save the cold case.
3. Stage 2 takes the goal's `target` and `hypotheses` from `check --index`, searches the target
   as a conclusion pattern with the hypotheses' names as named holes, fills each candidate's
   remaining parameters from hypotheses or `auto`, and kernel-checks every suggestion; it adds
   `rw?`'s direction for rewrites. Candidate lists are short (median 1, 90th percentile 23
   theorems) [run, §6.1].
4. A suggestion that is pasted is checked like any proof, so stage 2 can't make a proof wrong.

## 10. Changes from draft 1

- §2: the comparison widened from Lean's tools (3 cards, no new reading) to 13 source cards over
  7 systems, read for this draft; §3 is new.
- **Ranking** (draft 1 §3.5): hypotheses and size replace name length as tie-breaks; the choice
  is measured on 3,838 self-retrieval queries, not 14 (§5.1, §6.1).
- **Argument order** (new): `matchHyps` for arrow patterns (§5.2). Draft 1 matched function
  types only in order and with the same arity, and missed `Nat.leTrans`.
- **Rewrite mode** (new): `--rewrite`, equations as stated (§5.3).
- **Instances** (draft 1 §3.2): the dual search for interface fields at concrete types (§5.4).
- **The filter** (draft 1 §3.3, D2045): widened to data types; shown lossless on all of std;
  D2054 replaces D2045.
- **Natural language** (draft 1 §2, "not yet"): out of the stage plan, with reasons and revisit
  conditions (§5.5).
- **Index** (D2046): unchanged in substance; D2056 replaces it and adds stage 2.
- **Stage 2** (draft 1 §3.9): built on SW-914's goals, with a rewrite direction (§5.7).
- **Found:** a panic in evaluation during matching; 30 higher-order statements unification
  can't match with themselves (§6.1).
- **Prototype:** directives `mode:`, `rank:`, `self:`; reordered matching opens pattern binders
  as variables; `docs/proposals/search/queries-draft2.sh`.

## 11. What was not verified

- **Projects:** still std only (draft 1 §8).
- **Data types in the filter**, the **instance dual search** and **refusing patterns that compute
  to a hole** are designed, not built.
- **One-way matching** was not prototyped; that it would catch the higher-order misses is
  [unverified].
- **Rocq's matching** in detail (`constr_matching.ml` not read).
- **Lean Finder, LeanDojo, Moogle**: not read; nothing here rests on them.
- **Tie-break order among equally specific results**: 5 hand queries split; no real query log
  exists yet.
- **Quiet-machine timings.**
