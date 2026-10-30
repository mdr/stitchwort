# External review 1 of the search design (draft 2)

Received 30 October 2026 on the reviewer brief (review-brief.md), pasted verbatim. "Lemma Search Review" and links are the reviewer's citations of the brief page.

This is a strong proposal. I think the overall direction is right, and the prototype data is unusually useful for a design note at this stage. My main recommendation would be: **ship the Stage 1 search substantially as proposed, but make the matching relation more explicitly stratified rather than treating symmetric unification as one undifferentiated notion of “match.”** The Stage 2 `exact?`-like tool is likely to become even more valuable than the raw search command for agents.

The proposal is solving a real problem rather than inventing a feature in search of a use case: agents are repeatedly grepping, missing existing lemmas, and even reproving them, while exact spelling, notation and argument-order differences defeat textual search. Lemma Search Review Given that Stitchwort has roughly 2,330 library theorems already, this is exactly the point where type-directed retrieval starts paying for itself. Lemma Search Review

## Overall assessment

I would approve this design with a few changes.

The pieces I especially like are:

- **The constants filter.** The measurements make a compelling case for it. It gives a very large speedup, appears not to introduce additional misses in the benchmark, and materially improves ranking quality. Lemma Search Review
- **Specificity-based ranking rather than textual/name heuristics.** Your proposed ranking gets 88.2% top-1 on conclusion self-retrieval and substantially beats the Isabelle/Rocq/Loogle-like baselines you tested. Lemma Search Review
- **Searching theorem parameters in any order, with extra theorem parameters allowed.** `Nat.leTrans` is an excellent motivating example: ordinary whole-type matching misses exactly the sort of lemma a user intuitively expects to find. Lemma Search Review
- **Keeping rewrite search syntactic at first.** Your finding that treating computed propositions as equations destroys precision is quite persuasive: 257/1767 lost versus 17/1537 when respecting equations as stated. Lemma Search Review
- **Returning machine-readable provenance and ranking fields.** For an agent-first language, `name`, full type, file/line, import, and explicit ranking factors are exactly the right outputs. Lemma Search Review

The biggest conceptual issue is that the current matching algorithm conflates several useful relations:

1. “this theorem has essentially this shape,”
2. “this theorem can instantiate to this query,”
3. “the query can instantiate to this theorem,” and
4. “these two expressions merely have a common instance.”

Those are not equally useful search results.

---

# 1. Matching relation

I would **not make unrestricted two-way unification the primary semantic definition of a search hit**.

Your worry about crossed matches is well founded. With both theorem variables and query holes as metavariables, unification answers something approximately like:

> “Do these two expressions have a common instance?”

That relation is symmetric and mathematically neat, but library search is not really a symmetric problem.

Normally the user's query represents information they know, while a theorem represents something they might instantiate. So the most meaningful relation is closer to:

> **Can this theorem be instantiated so that it matches my query?**

That is fundamentally directional.

The design currently opens theorem binders as unknowns and also allows pattern holes to instantiate, then ranks matches by how much each side absorbed. Lemma Search Review That is clever, and `absorbed` is a useful signal, but I would expose the distinction structurally rather than recover it only through ranking.

### I would use three tiers

**Tier A — theorem-instance match**

The query's non-hole structure is rigid. Instantiate theorem variables only.

This should get the best rank.

For:

```text
?x + 0 = ?x
```

query holes can of course bind, but structure such as `+`, `0`, and `=` cannot disappear into theorem metavariables.

This corresponds most closely to “the theorem can be used for something of this shape.”

**Tier B — pattern/generalisation match**

Allow query holes to absorb theorem structure too, but don't allow both sides to cross-generalise arbitrarily.

This supports deliberately vague searches like:

```text
List _ -> _
```

**Tier C — common-instance/unification match**

Your present symmetric unification.

Keep it because it can find genuinely useful things that stricter matching misses, but label it as a fuzzy/weak match and put it after directional matches.

This gives you a nice conceptual interpretation of your existing `absorbed` metric rather than throwing it away.

### Higher-order cases

For misses such as `p x` and `f x = f y`, I would indeed investigate **higher-order pattern matching on the theorem side**, rather than broad higher-order unification.

Those misses are exactly the classic situation where first-order-ish metavariable treatment is too weak. Lemma Search Review

But I would constrain this to Miller-pattern-like cases if Stitchwort's core syntax permits it. Full higher-order unification is not what you want here: it is semi-decidable, generates unintuitive solutions, and would make latency/ranking much harder to reason about.

So my preference is:

> rigid query + theorem-side higher-order pattern instantiation  
> → ordinary directional matching  
> → finally symmetric unification as a fallback

rather than “symmetric unification, but smarter.”

That is also broadly consistent with the systems you surveyed: Isabelle's matching facilities are explicitly one-way/higher-order matching, while Lean's goal-directed tools actually try application rather than merely asking whether expressions unify. Lemma Search Review

---

# 2. Evaluating the ranking

Your self-retrieval benchmark is useful, but I agree with your own caveat: **it is a benchmark of structural faithfulness, not really a benchmark of usefulness.** You already note that it necessarily favours specificity and cannot resolve equally-specific alternatives. Lemma Search Review

I would keep it. It is excellent as a regression test.

But I would add two considerably more important benchmarks.

### A. Proof-use retrieval

Your idea of using “the lemma actually used at each proof step” is the right next benchmark.

Given a proof containing:

```text
foo x y
```

reconstruct the goal state immediately before that application, remove `foo`, then ask search to retrieve it.

Measure at least:

- Recall@1
- Recall@5
- Recall@10
- MRR
- proportion where the actual lemma isn't returned at all.

This is much more informative than self-retrieval.

One caveat: the lemma actually used is **not necessarily uniquely best**. If three lemmas solve the goal, ranking one equivalent lemma above the historical one should not count as a hard failure.

That suggests the stronger Stage-2 benchmark:

> of the first K suggestions, how many kernel-check and close the goal?

That is arguably the metric agents actually care about.

### B. Real agent queries

The logged-agent-query dataset you propose is probably eventually the gold standard.

I would record:

```text
query
goal/context if available
results shown
candidate selected
whether candidate was used unchanged
final proof
time / number of subsequent search attempts
```

That lets you measure something much more meaningful than “did the known lemma rank first?”:

> **Did search reduce proof-search effort?**

Given Stitchwort's agent-first usage model, you have an unusually good opportunity to collect this data automatically.

### One change to the current benchmark

Don't count ties “in T's favour” in the headline top-1 figure. Lemma Search Review

It is fine as a secondary diagnostic, but it makes the 88.2% figure optimistic. For an actual client consuming ordered results, ties are resolved somehow. Report:

- strict top-1,
- top-1 allowing ties,
- MRR,
- Recall@5/10.

The difference could reveal exactly whether your remaining ranking work lies mostly in tie-breaking.

---

# 3. Constants filter under computation

I think this is **absolutely the right default prefilter**.

The data is compelling: filtered runs are roughly an order of magnitude faster while finding exactly the same misses in this benchmark. Lemma Search Review

But I would phrase its contract as:

> a high-precision retrieval index, not part of the definition of semantic matching.

That gives you freedom to weaken/fallback later.

The main false-negative cases I would expect are the ones you identify, plus a few others:

- reducible aliases;
- typeclass/interface projections;
- coercions;
- notation after elaboration;
- definitions whose relevant constant only appears after reduction;
- wrappers whose result type is definitionally equal to something mentioning the queried type;
- overloaded operations which elaborate differently depending on inferred type;
- propositions encoded through reducible definitions.

Because your read-back is deliberately folded, this tension is unavoidable. Lemma Search Review

I would therefore use a **two-pass strategy**:

```text
1. constants-filtered search
2. if too few/no useful matches, relaxed search
```

That is essentially the same good engineering trade-off Lean makes with its “star” fallback for declarations with overly general indexing keys: specific indexed candidates first, broader candidates only when necessary. Current Lean's `exact?`/`apply?` explicitly retain such a fallback. [Lean Language](https://lean-lang.org/doc/reference/latest/releases/v4.27.0/?utm_source=chatgpt.com)

You could even return:

```json
"searchTier": "indexed"
```

or

```json
"searchTier": "fallback"
```

so agents know the distinction.

I would *not* try to make the filter definitionally complete. You will end up duplicating the elaborator/reducer and spending the performance win.

---

# 4. Instances

The double search is a pragmatic and defensible solution.

The example in the proposal demonstrates exactly why it is needed: generic `Ord.compareSelf` and concrete `Nat.compareSelf` become different search surfaces depending on whether the dictionary projection is reduced. Lemma Search Review

I would not initially search “modulo arbitrary instance resolution.” That sounds principled but would make search depend deeply on local instance availability and resolution behaviour.

A better long-term conceptual model might be to preserve an **interface-projection view** alongside the elaborated concrete term.

For example, internally recognize:

```text
Ord.compare [NatOrd]
```

as having both keys

```text
Ord.compare
Nat.compare
```

This is essentially a search/index normalization, not definitional equality.

Then a generic and concrete query naturally converge in the index.

But I wouldn't block the feature on this. Your double-search approach is small, understandable, and the measured example supports it.

One thing I would add: **deduplicate by declaration while retaining the best provenance**. If a theorem is reached through both generic and resolved searches, JSON should probably explain why it matched rather than silently behaving as if there were only one path.

---

# 5. Parameters in any order

This is worth keeping.

Your `Nat.leTrans` example is decisive: same-count reordering still misses it, while “the theorem may have more parameters” finds it and ranks it second. Lemma Search Review

I would, however, replace greedy assignment eventually.

### Do you need full backtracking?

Probably not general exponential search.

The parameter lists involved in library lemmas are normally tiny. So a bounded bipartite matching algorithm is very cheap.

You can construct an edge:

```text
query parameter i -> theorem parameter j
```

when the two can unify under a speculative trail, then search for a minimum-cost matching.

The cost can incorporate:

- exact structural match,
- amount absorbed,
- instantiation count,
- positional displacement.

For a theorem with, say, 3–8 arguments, this is trivial compared with elaboration/unification cost.

Dependency complicates this because parameter types may mention earlier binders, so it is not literally an independent bipartite graph. But even a small DFS with pruning and reversible unification state should be manageable.

Given that your elaborator already has a trail specifically allowing speculative unification to be undone, the infrastructure is unusually well suited to it. Lemma Search Review

### Currying and tupling

I would **not support currying/tupling isomorphisms yet**.

Hoogle needed this because Haskell API search is heavily about finding arbitrary functions whose interfaces are “morally” equivalent. Stitchwort proof search has a much stronger notion of applicability.

Searching:

```text
A -> B -> C
```

for:

```text
(A, B) -> C
```

will increase recall but also significantly widen the semantic meaning of search.

Your any-order rule already handles the practical “I remembered argument order incorrectly” problem. Stop there until logs show currying/tupling is genuinely missed by agents.

---

# 6. Rewrite search

I like your conservative design:

> only equations explicitly stated with `=`; search left and right sides.

The empirical result strongly supports this. Lemma Search Review

I would add **`Iff` fairly soon**, but I would probably expose it as proposition rewriting rather than silently treating it identically to equality.

For example:

```text
--rewrite
```

could include both equality and iff, with JSON saying:

```json
"relation": "eq"
```

or:

```json
"relation": "iff"
```

That fits how users think about rewriting propositions.

### Conditional equations

Yes, include them.

A theorem like conceptually:

```text
x != 0 -> f x = g x
```

is an excellent rewrite candidate.

But Stage 1 should return it as a candidate with one unsatisfied premise, rather than trying to prove the side condition.

Stage 2 can attempt to discharge it.

That fits your architecture very naturally:

```text
retrieval -> candidate application -> premise solving
```

rather than making retrieval itself proof search.

### Computed equality

Your instinct is right: don't normalize arbitrary propositions until they become equality.

The `≤` example shows why. Once computation changes the outer shape, “rewrite search” ceases to correspond to what the author declared.

I'd permit only very controlled reduction necessary to expose wrappers/aliases marked reducible, not general evaluation.

---

# 7. Natural-language search

I agree with leaving it out.

For Stitchwort specifically, this is an unusually easy call because your primary users are LLM agents. They are already extremely good at converting:

> “lemma saying map preserves length”

into something like:

```text
List.length (List.map ?xs ?f) = List.length ?xs
```

The structured search engine should exploit the information already latent in the type system rather than convert types to embeddings and back.

Your stated reasons—agents can generate patterns and a semantic model would require serving infrastructure—are sound. Lemma Search Review

I would revisit natural-language search only if your logs show this failure pattern:

1. agent fails to formulate an effective pattern,
2. repeatedly searches semantically related but structurally wrong types,
3. eventually greps/searches names/comments instead.

Until then, a learned retriever adds infrastructure, nondeterminism and difficult evaluation for little demonstrated benefit.

There **is** evidence from theorem-proving systems that learned premise selection can be powerful, especially when proof libraries become very large; your own survey mentions Sledgehammer/MePo/MaSh and neural systems. Lemma Search Review But that problem gets much more compelling at tens or hundreds of thousands of declarations than at ~2,300.

---

# 8. Stage 2: “what closes this `?`?”

I think this should be treated as a **first-class feature, not merely an optional second phase**.

For agents it may become the main interface.

Raw search asks:

> “What looks like this type?”

Stage 2 asks the thing the agent actually wants:

> “What can I put here?”

That distinction matters enormously.

Your proposed pipeline is already good: obtain the structured goal, search candidates, fill remaining parameters from hypotheses/instances, kernel-check, and return actual closers. Lemma Search Review

Lean's current `exact?` follows essentially this architecture: try a library declaration against the goal, then use `solveByElim` to discharge the subsidiary goals. [Lean Language](https://lean-lang.org/doc/api/Lean/Meta/Tactic/LibrarySearch.html?utm_source=chatgpt.com) `solve_by_elim` itself performs recursive application with bounded depth and backtracking. [Lean Language](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference?utm_source=chatgpt.com)

### What I would take from Lean

Use a deliberately **small recursive closure search** after applying the candidate.

Something like:

```text
candidate theorem
    ↓
instantiate against target
    ↓
remaining subgoals
    ↓
assumption / rfl / auto instance / tiny elimination search
```

Depth 3–6 is probably plenty initially.

Lean currently defaults `solve_by_elim` to depth 6. [Lean Language](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference?utm_source=chatgpt.com) You don't need to copy that number, but the shape is sensible.

Most importantly, distinguish:

```text
exact closure
closure with local hypotheses
closure after N small generated obligations
applicable but leaves obligations
```

I would return all four classes.

For an agent, this:

```text
Std.foo x y
-- leaves:
--   1. x <= y
```

can be much more useful than no result.

### What I would avoid

I would *not* immediately make Stage 2 into a broad automation tactic.

Don't bolt Sledgehammer/grind-style automation onto it yet.

Its value is explainability:

> here is the library lemma you were missing.

That directly addresses the measured friction from your agents.

If Stage 2 begins proving substantial facts through six unrelated lemmas, it stops being lemma discovery and becomes a theorem prover. That's a different feature.

### Candidate budget

50 is a perfectly reasonable initial bound, but I'd make it **budget-driven rather than semantically fixed**.

For example:

```text
maxCandidates = 50
maxUnificationSteps = ...
maxClosureSteps = ...
```

and JSON should say whether search was exhausted or truncated.

That is especially useful for agents: “no result” and “gave up after 50 candidates” are materially different information.

---

# A larger architectural suggestion

I think the proposal is very close to discovering that Stitchwort really has **three related search operations**.

### `search`

“What declarations resemble this type/pattern?”

High recall, ranked, allows fuzzy/common-instance matching.

### `apply?`

“What declarations can apply to this goal?”

Directional. May leave subgoals.

### `exact?`

“What declarations can close this goal after trivial/local discharge?”

Strongest guarantee.

They can absolutely share the same retrieval machinery.

But I would keep these concepts separate in the underlying API even if you initially expose only:

```text
stitchwort search
```

and:

```text
stitchwort check
```

The distinction will simplify matching semantics and ranking tremendously.

A result can then have an explicit relation like:

```json
{
  "relation": "exact",
  "place": "conclusion"
}
```

or:

```json
{
  "relation": "applicable",
  "remainingGoals": 2
}
```

or:

```json
{
  "relation": "commonInstance",
  "absorbed": 4
}
```

That is much more informative than trying to make one scalar ranking encode all of those meanings.

---

# One thing I would change in the ranking now

The current lexicographic order is:

> place → absorbed → instantiated → hypotheses → size → name. Lemma Search Review

I broadly like it.

But if you adopt directional match classes, I would put **match relation before place**:

```text
relation
place
absorbed
instantiated
unsatisfied hypotheses
size
name
```

Because a true theorem-instance match against an internal call is usually more meaningful than a symmetric/common-instance match against the whole conclusion.

I'd also call `hypotheses` something like `premises` or `remainingParameters` in JSON if that is what is actually being counted. “Hypotheses” is overloaded because you also use that word for theorem parameters/goal context.

---

# Minor concerns

A few smaller points jumped out.

The **200,000-step per-theorem unification budget** seems extremely generous relative to the measured execution times. Lemma Search Review I would report in diagnostics whether any normal query comes remotely close to it. An accidental pathological declaration multiplied by thousands of candidates could otherwise become surprising.

Likewise, the four evaluation internal errors found by the benchmark are worth treating as blockers for relying heavily on speculative search, even though they do not invalidate the design. Search exercises elaboration paths far more adversarially than ordinary source programs will. Lemma Search Review

I also think **“calls inside” should rank very low**, just as proposed. It is potentially extremely useful for discovery, but semantically it's closer to subterm search than theorem search. I might even expose it as a distinct `place: "subterm"` category rather than `inside`.

Finally, I would keep the **human syntax deliberately small**. The proposed mixture of strings, identifiers, `_`, named holes, `⊢`, and pasted goals is already near the maximum I'd want. Lemma Search Review The temptation will be to accrete Rocq/Isabelle-style selectors. For agents, structured JSON and a few orthogonal CLI switches are probably preferable.

---

## My answers to the eight questions, condensed

1. **Matching:** make theorem→query directional matching primary; keep symmetric unification as a lower-ranked fallback. Add restricted higher-order pattern matching for theorem metavariables rather than full HO unification.

2. **Ranking benchmark:** retain self-retrieval as a regression test, but add reconstructed proof-step retrieval and real agent-query logs. Report MRR/Recall@K and strict top-1, not only ties-in-your-favour.

3. **Constants filter:** keep it. Don't attempt definitional completeness. Fall back to an unfiltered/relaxed pass when the indexed search yields nothing useful.

4. **Instances:** the double search is a good V1. Longer term, consider indexing both generic projection and resolved implementation forms instead of searching modulo arbitrary instance resolution.

5. **Argument order:** keep “any order, theorem may have more.” Replace greedy assignment with bounded backtracking/min-cost matching eventually. Ignore currying/tupling until evidence says otherwise.

6. **Rewrite:** include explicit `=` and probably `Iff`; include conditional equalities as candidates with premises. Don't turn arbitrary computed propositions into rewrite rules.

7. **Natural language:** leave it out. At ~2.3k theorems with LLM agents already generating queries, structural search gives you much more determinism per unit complexity.

8. **Stage 2:** prioritize it. Apply candidate + cheap local/backtracking discharge + kernel check. Also report useful candidates that leave a small number of goals rather than restricting output to complete closure.

## Bottom line

I think **the proposal is substantially ready to implement**. The strongest aspect is that nearly every major design choice has either a concrete agent failure motivating it or prototype measurements supporting it, rather than being copied wholesale from another prover. The problem statement itself is unusually well grounded: existing agents demonstrably miss and re-prove library lemmas, while the proposed structured search is already fast enough through the warm cache to sit naturally in their interactive loop. Lemma Search Review Lemma Search Review

The one change I'd make before cementing the semantics is **to stop calling symmetric unification simply “matching.”** Make “the theorem instantiates to my query,” “the theorem is applicable to my goal,” and “these two types have a common instance” distinct relations. You already have most of the machinery and ranking signals necessary to do that. It will make the behaviour easier to explain, easier to benchmark, and much easier to evolve when Stage 2 arrives.