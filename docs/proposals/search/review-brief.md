# Reviewer brief: lemma search by type for Stitchwort

**For:** an expert in proof assistants or code search, outside the project, with no access to its
repository. Everything you need is on this page.
**What we ask:** your view on the design below, and answers to the questions in
[§7](#7-questions-for-the-reviewer). Anything else you notice is welcome.
**Status:** design note draft 2 (30 October 2026), with a working prototype. Every Stitchwort
example below was run, and its real output is shown.

## 1. Stitchwort in brief

**What it is.** Stitchwort is a dependently typed functional programming language written in
Rust. Programs and proofs are the same kind of thing: a theorem is a definition whose type is a
proposition, and its proof is a term. Side effects are *abilities* (algebraic effects): a
function's type says which effects it may perform, e.g. `{Fail | e} a`, and handlers give them
meaning. An elaborator turns source into a core calculus, and a **small kernel re-checks
everything the elaborator produces**, so elaborator bugs can't make a false theorem pass. The
language is used to write and prove things about real programs: solutions to Advent of Code
puzzles (correctness theorems about each day's solution) and a roguelike game.

**Who uses it.** AI agents first: most code and proofs are written by coding agents working in
parallel "lanes", which drive the command-line tool (`stitchwort check`, JSON output) and read
its messages. People use it too, through an editor's language server.

**Enough syntax to read the examples.** This file checks [run]:

```
import Std (List, Nat, Ord)

-- A function; the type parameter `a` is implicit, `x => …` is a lambda.
def countAbove [a: Type] (xs: List a) (key: a → Nat) (limit: Nat): Nat :=
  List.length (List.filter xs (x => Nat.leq (Succ limit) (key x)))

-- A theorem is a definition whose type is a proposition; the proof is a term.
theorem lengthOfBoth (xs: List Nat) (ys: List Nat): List.length (xs ++ ys) = List.length xs + List.length ys :=
  List.lengthAppend xs ys

-- An instance argument: `Ord.compareSelf` takes `[auto ord: Ord a]`, found here for `Nat`.
theorem compareSame (n: Nat): Ord.compare n n = Equal := Ord.compareSelf n

-- A computation the checker runs: closed terms are checked by evaluation.
theorem countExample: countAbove [3, 9, 12] (x => x) 8 = 2 := rfl
```

```
$ stitchwort check Brief.sw
checked Brief.sw
```

- `(x: T)` is an explicit parameter; `[a: Type]` an **implicit** one, filled in by unification;
  `[auto ord: Ord a]` an **instance argument**, found by a search (`auto`) for a dictionary.
- Library functions usually take the data first: `List.map xs f`, `List.filter xs p`. (This
  matters for search: §2.)
- `++` is overloaded (lists or texts) and elaborates to `List.append`; `≤` on `Nat` is a
  definition that computes to a `Bool` equation.
- `?` is a hole. Checking a file with a hole reports the goal [run]:

```
theorem lengthTwice (xs: List Nat) (ys: List Nat): List.length (xs ++ ys) = List.length xs + List.length ys := ?
```

```
$ stitchwort check Goal.sw
[GOAL] Goal: in `lengthTwice`
   ╭─[ Goal.sw:3:112 ]
   │
 3 │ theorem lengthTwice (xs: List Nat) (ys: List Nat): List.length (xs ++ ys) = List.length xs + List.length ys := ?
   │                                                                                                                ┬  
   │                                                                                                                ╰── xs: List Nat
   │                                                                                                                    ys: List Nat
   │                                                                                                                    ⊢ List.length (List.append xs ys) = List.length xs + List.length ys
───╯
1 goal open: the declarations with them, and what uses them, aren't finished, so they aren't checked
```

(Goal.sw is `import Std (List)` followed by the line above.)

and `check --index` gives agents the same goal as data [run]:

```json
"goal":{"hypotheses":[{"name":"xs","type":"List Nat"},{"name":"ys","type":"List Nat"}],
 "target":"List.length (List.append xs ys) = List.length xs + List.length ys",
 "lemma":"theorem lengthTwiceGoal1 (xs: List Nat) (ys: List Nat): List.length (List.append xs ys) = List.length xs + List.length ys := ?"}
```

**The standard library** has about 2,330 theorems (2,328 named, non-helper theorems loaded; 2,282
`theorem` lines in its source, 111 of them closed `…Example` checks), over lists, maps, sets,
naturals and integers, orderings, parsing and effects.

**Unification and implicit arguments, briefly.**
- Elaboration creates *unknowns* (metavariables) for implicit arguments, `_` holes and instance
  arguments, and solves them by unification. Solutions are recorded on a trail and can be undone,
  so the elaborator can try something and take it back.
- Values are *glued*: a call such as `List.length xs` is kept as the call while comparing, and
  unfolded to its definition only when a comparison needs to look inside. Unfolding runs under a
  resource budget.
- Two calls of the same definition are taken as equal if their arguments unify (a "lossy" rule:
  sufficient, not necessary, for a non-injective definition); otherwise unification may unfold.
- Instance arguments are dictionaries (records): `Ord.compare` is a field of the `Ord`
  dictionary, and at a known type the field computes to that type's function (`Nat.compare`).

## 2. The problem, with evidence

- Agents found lemmas only with `grep`, and twice re-proved lemmas the library already had. From
  the lanes' notes: "finding `tailOf`, not `tail`, took a grep"; "I first wrote `compareSelf` and
  `lessNotGreater` too, then found std's `Ord.compareSelf` and `Ordering.lessNotGreater` by
  grepping the std sources; with no search by type, a lemma is easy to miss."
- "Missing std lemma or function" is the largest category of recorded friction (about 40 items
  in the lanes' notes on the puzzles and the game); for many, the notes don't say whether the
  lemma existed.
- Grep needs the name, or the statement's exact spelling and line layout: std writes
  `List.append` where users write `++`; a conclusion may be on the line after `theorem`.
- Argument order trips agents from other libraries: the pattern `List.map _ (List.map _ _)`
  (Lean's and Haskell's order) is a type error here [run]:
  `expected ?0 → {?1} ?3, but this has type List ?8`.
- Elsewhere: an agent study found that Lean's `exact?` returning a lemma was the agent's most
  useful single step; another gave a coding agent the source of its verification library to
  search, and removing it (with a cheat checker) cost up to 26% of solved tasks.

## 3. What exists elsewhere

We read the primary sources (code, manuals, papers) for each system.

| System | Pattern language | Matching | Argument order | Instances | Rewrite search | Ranking | Index |
|---|---|---|---|---|---|---|---|
| Hoogle | Haskell types | fingerprint prefilter (arity, size, 3 rarest names), then unification of type variables | 2-argument queries also swapped; arity differences costed | extra constraints cost | no | summed hand-tuned costs, tuned against a list of complaint queries | memory-mapped file, linear scan |
| Idris 2 `:search` | a type | whole-type unification, same arity, nothing left over | none | via unification | no | none | none |
| Rocq `Search` | `_`, `?x`, strings, `hyp:`/`concl:`/`headconcl:`, `is:`, negation | `Constr_matching` per declaration | `SearchPattern` strips ∀ and premises | `is:Instance` | `SearchRewrite`: either side of `eq` | −(3·distinct constants + size) | none |
| Isabelle `find_theorems` | patterns, `name:`, `intro`/`elim`/`dest`/`solves`/`simp:` | higher-order pattern matching, one way, after a constants-subset filter | via `intro`/`elim` against a goal | via types | `simp:` | size, premises, substitution size | none |
| Sledgehammer MePo / MaSh | the goal | symbol overlap / naive Bayes and kNN learned from proofs | n/a | features | n/a | relevance | MaSh: learned state |
| Loogle (Lean) | constants, `"name"`, terms, `⊢ term` | `isDefEq` at reducible transparency, one way, after a constants index | parameters in any order, theorem may have more (`matchHyps`) | no default instances | via `⊢ _ = _` | module order, size | on disk |
| Lean `exact?`/`apply?`, `rw?` | the goal | discrimination tree, then `apply` + `solve_by_elim`; `rw?`: lemma sides vs goal subterms | `apply` | instance search | `rw?` | key length; first that closes | lazy tree |
| LeanSearch, LeanPremise | natural language; goal state | embeddings (7B model plus an LLM per query; or a 23–82M encoder on a server) | n/a | n/a | n/a | similarity | vector store |
| Agda | identifiers, strings | constants and name filter (`Search About`) | n/a | n/a | no | none | none |

## 4. The design

`stitchwort search 'PART, PART, …' [--rewrite] [--json] [--limit N] [--defs] [--project DIR]`

- **Parts.** `"text"` (name substring); a qualified name (the type must mention it); a pattern
  with `_` holes and `?x` named holes (all `?x` match the same term; different names, different
  terms); `⊢ pattern` (conclusion only); bare lowercase names as named holes, so a goal can be
  pasted.
- **Scope.** All of std, loaded through the compiler's check cache, plus the project.
- **Filter.** A theorem is compared only if its type (read back folded) mentions every
  definition and data type the pattern mentions (Loogle's and Isabelle's rule).
- **Matching.** Each theorem's binders are opened as fresh unknowns; the pattern is unified with
  each target under a per-theorem budget of 200,000 steps, and the attempt is undone. Targets, in
  order: the whole type (for a function-type pattern), the parameters in any order with the
  theorem allowed more (`matchHyps`), the conclusion, each hypothesis, each call inside. With
  `--rewrite`, only the two sides of a conclusion stated as `=`.
- **Instances.** A pattern naming an interface field at a concrete type is searched twice, with
  the instance resolved and with the dictionary left a hole, and the results merged.
- **Ranking**, lexicographic, every key in the JSON: *place* (whole, reordered, conclusion,
  left/right side, hypothesis, inside); *absorbed* (the total size of what the theorem's own
  variables had to become: smaller is more specific); *instantiated* (how many pattern holes had
  to become more than a variable); hypotheses; size; name.
- **Output.** Human-readable, or JSON with name, type, file and line, the `import` line to add,
  and the ranking fields. From the prototype [run] (its cache option omitted, line breaks added):

```
$ stitchwort dev search 'List.length ((_: List _) ++ _) = _' --json
{"experimental":true,"results":[{"absorbed":0,"file":"std/List/Lemmas.sw","import":"import Std (List)",
 "instantiated":1,"line":5,"name":"Std.List.lengthAppend","place":"conclusion",
 "type":"[a: Type] → (xs: List a) → (ys: List a) → List.length (List.append xs ys) = List.length xs + List.length ys"},
 {"absorbed":0,"file":"std/List/Lemmas.sw","import":"import Std (List)","instantiated":2,"line":824,
 "name":"Std.List.lengthSnoc","place":"conclusion",
 "type":"[a: Type] → (xs: List a) → (x: a) → List.length (List.append xs [x]) = Succ (List.length xs)"}],"total":2,"version":0}
```

  The overloaded `++` needs its operand's type in a pattern today [run]:
  `List.length (_ ++ _) = _` → `` `++` joins two texts or two lists … this is a `?1` ``. The
  design tries each resolution and merges.
- **Not included:** natural-language search (no served model; agents write patterns); an
  on-disk index (loading is 0.2 s warm).
- **Stage 2, "what closes this `?`":** take the goal from `check --index`, search its target as
  a conclusion pattern with the hypotheses as named holes, fill each candidate's remaining
  parameters from hypotheses or `auto`, kernel-check, and report what closes the goal; plus
  `rw?`'s direction, lemma sides against the goal's subterms. By hand today [run]:
  `⊢ List.length (List.append ?xs ?ys) = List.length ?xs + List.length ?ys` →
  `Std.List.lengthAppend … [conclusion 0 0]`, 1 match.

## 5. The measurements

All on a shared machine with the prototype; std has 2,328 theorems.

**Cost.** Loading all of std: 4.1–4.5 s cold, 0.21–0.28 s through the check cache; building the
filter: about 20 ms; one filtered match against every theorem: 0.1–0.5 ms; unfiltered: 20–70 ms.

**Self-retrieval benchmark.** For every std theorem T: its conclusion (2,301 queries; 27 skipped
because the conclusion is a variable), or the left side of a conclusion stated as `=` (1,537
queries), with T's variables as holes, searched over all of std. T must be found; its rank
measures the ranking.

| | conclusions | left sides |
|---|---|---|
| T not found, with the constants filter / without | 13 / the same 13 | 17 / the same 17 |
| matches per query, median / 90th / 99th percentile | 1 / 23 / 544 | 2 / 16 / 133 |
| time for all queries, filtered / unfiltered | 9.1 s / 75 s | 3.9 s / 54 s |

Every miss we inspected (6 of 13) has a theorem variable in head position (`p x`, `f x = f y`,
`motive b`). The run also hit an internal error in evaluation on 4 pairs of theorems (12
unfiltered), which we will fix.

**Rankings**, share of queries where T ranks first (ties in its favour):

| Ranking | conclusions | left sides |
|---|---|---|
| place, absorbed, instantiated, hypotheses, size (proposed) | 88.2% | 80.5% |
| place, absorbed, instantiated, name length (draft 1) | 88.0% | 81.9% |
| the proposed, with symbol rarity (IDF) after specificity | 88.0% | 81.7% |
| rarity first, then specificity | 79.2% | 72.2% |
| size, premises, substitution size (Isabelle) | 73.1% | 64.3% |
| 3 × distinct constants + size (Rocq) | 73.4% | 65.5% |
| load order, size (Loogle) | 70.6% | 63.4% |

Without the filter, Isabelle's ranking puts T first for 9.7% of conclusions.

**Argument order** (functions included):

| Query | in order | any order, same count | any order, theorem may have more |
|---|---|---|---|
| `List _ → Nat → List _` | 247 matches; `drop`, `take` first | 255 | 266 |
| `Nat → List _ → List _` | 252; nine `Nat`-first functions | 260; `drop` 10th, `take` 11th | 278 |
| `(_: Nat) ≤ _ → _ ≤ _ → _ ≤ _` | 11; no `Nat.leTrans` | 11; none | 38; `Nat.leTrans` 2nd |

`Nat.leTrans` is stated `(a b c: Nat) → a ≤ b → b ≤ c → a ≤ c`: its variables are explicit, so
only the third mode finds it.

**Rewrite search:** `--rewrite` on `List.length (List.append _ _)` → `lengthAppend`, then
`lengthSnoc`; 2 matches. Treating a conclusion as an equation *after* evaluation (`≤` computes
to one) lost 257 of 1,767 lemmas; using equations as stated, 17 of 1,537.

**Instances:** `Ord.compare ?x ?x = _` → `Ord.compareSelf` first of 38, no `Nat` lemma.
`Ord.compare (?x: Nat) ?x = _` elaborates to `Nat.compare` → `Nat.compareSelf` first of 10, no
generic lemma. Hence the double search.

## 6. What we are fairly sure of, and what we are not

- Sure: the constants filter costs nothing on std and is what makes results precise; specificity
  beats size as the first ranking key on this benchmark; implication patterns need `matchHyps`.
- Not sure: the order among equally specific results (5 hand queries disagree with each other);
  whether two-way unification is the right matching relation (§7 Q1); projects (only std was
  measured).

## 7. Questions for the reviewer

1. **Matching relation.** We unify both ways: the theorem's variables and the pattern's holes are
   all unknowns. That lets a pasted goal with concrete terms find a general lemma, but admits
   "crossed" matches (the theorem's variable swallows pattern structure while a pattern hole
   swallows theorem structure), which we rank last. Isabelle, Rocq and Loogle match one way.
   Would you match one way, and add the other direction (instance-of, as `exact?` does) as a
   separate mode? Would higher-order pattern matching on the theorem side be the right fix for
   misses like `p x` and `f x = f y`?
2. **Evaluating the ranking.** Our benchmark uses each theorem's own statement as the query. It
   can't judge tie-breaks among equally specific results, and favours specificity by
   construction. What would you use instead or as well? We are considering the lemma actually
   used at each step of std's proofs as ground truth (as MaSh learns), and a log of agents'
   queries with the lemma they then used.
3. **The constants filter under computation.** We require a theorem to mention every definition
   (and data type) the pattern names, both read back with calls folded. Where would you expect
   this to be wrong in a dependently typed language with computation in types: instance
   projections, notations, coercions, definitions that are reducible aliases?
4. **Instances.** We search twice when a pattern names an interface field at a concrete type
   (resolved, and generic). Is there a principled alternative, such as searching modulo instance
   resolution, or normalising patterns and theorems to a canonical projection form?
5. **Parameters in any order.** We assign pattern parameters to theorem parameters greedily, left
   to right, as Loogle does. Greedy can miss an assignment a backtracking or bipartite matching
   would find. Is that worth fixing in practice? And should currying or tupling isomorphisms
   (Rittri, Runciman) matter in a language where everything is curried?
6. **Rewrite search.** We search both sides of conclusions stated with `=` only. Would you include
   `↔` (std has `Iff` lemmas), conditional equations' side conditions, or sides that compute
   (a pattern like `n + 0` computes to `n` and then matches everything)?
7. **Natural-language search.** We leave it out because our users are agents that write
   patterns, and because it needs a served model. Are we missing evidence that LLM agents gain
   from semantic or learned retrieval over a pattern search they can drive themselves?
8. **Stage 2.** We plan an `exact?`-like "what closes this `?`" built on structured goals, with a
   budget of 50 candidates and kernel-checked suggestions. What would you take from Lean's
   `LibrarySearch`/`solve_by_elim`, Isabelle's `solves`, or Agda's Auto, and what would you
   avoid?

## Glossary

- **place:** where a pattern matched: the whole type, reordered parameters, the conclusion, a
  side of an equation, a hypothesis, or a call inside.
- **absorbed:** the total size of the terms the theorem's own variables had to become in the
  match; 0 means the theorem is at least as specific as the pattern.
- **instantiated:** how many of the pattern's holes had to become more than one of the theorem's
  variables.
- **folded / glued:** calls kept as calls while comparing, unfolded only when needed.
- **std:** the standard library.
