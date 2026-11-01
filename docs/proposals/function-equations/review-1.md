# Review 1 of function-equations.md (draft 1)

Independent review by a Claude Opus subagent, 1 November 2026, given the note and the repository
(not the author's conclusions). It reviewed commit `c4e0f228`. Saved as written; how each point
was addressed is in the note's "Review 1 and how it was addressed".

---

**Verdict: approve with changes.** The core design is sound and the evidence holds up. I reran every prototype and they behave as the note says: p1, p2b, p4, p6b and p7 check, p2 fails three ways, and the day 12 project checks. The `J` proof through a named `match` is real, and so is the case for `f.induct` on day 12. But the note leaves out several shapes that the generator will meet on its first run over std: indexed families, or-patterns, and helpers inside `decreasing` definitions. Its hypothesis form for `Bool` guards is not the form the hand-written lemmas chose, so it understates the migration cost. And its evidence for D2180 is wrong, though the fix makes D2180 easier, not harder. None of this needs a rework. Note that the working copy has uncommitted edits on top of `c4e0f228` that already fix part of finding 2 and add `Int`/`Fin` and effect-polymorphism text. This review is of `c4e0f228`.

## Findings

**1. Major: overlap hypotheses are ill-typed on indexed families.**
- §3.2 and D2175 state the hypothesis as `x = C vars → Void`. When an earlier arm's pattern fixes an index, the two sides of that equation have different types.
- Evidence: `review/r1.sw` defines `def short: Vec Nat n → Nat | VNil => 0 | VCons x VNil => 1 | v => 2`. The hypothesis `(notArm1: v = VNil → Void)` gives `E-TYPE-MISMATCH: expected Vec Nat n, but this has type Vec Nat 0`.
- Lean handles this with `mkEqHEq`, which is the note's own [L1] quote. std has no `HEq` (`git grep HEq crates/elab/src/std` finds nothing).
- §3.2's "not generated" list only covers impossible branches.
- Fix: choose one of three forms and add it as a decision:
  - an index equation plus a transport;
  - a generated `Bool` predicate such as `isVNil v = False`;
  - skip the arm and count it as `Unsupported`.

**2. Major: the `Bool`-guard hypothesis forms don't match what agents wrote, and §6.1 / D2184 understate the change.**
- The `else` of `if fresh: b = False` gives `fresh: Not (b = False)`. Both hand-written versions chose `taken: b = True` instead: `fillSkip` (`Fill.sw:100`) and `Graph.searchSkip` (`Search.sw:276`).
- The prototype needed a helper `trueOfNotFalse` for this (`Induct.sw:12`, used at `:116`). So "no `Bool`-to-`Prop` conversion" (§6.1) is overclaimed.
- `fillOther` (`Fill.sw:114-116`) needs no `fresh`. The generated `.eq.cons.ifTrue.ifFalse` needs both `fresh` and `grows`, so it is less general.
- The working copy now says this for day 12. D2184's "replace `Graph.searchSkip`" still treats it as a rename of a public std lemma.
- Fix: normalise a negated `Bool` equation against a constant to its complement (`Not (b = False)` becomes `b = True`); the proof converts with one step. Make this a decision. For D2184, decide between deprecating the std names and keeping them as one-line corollaries.

**3. Minor: the evidence for §3.5 / D2180 is wrong, and the rule should be wider.**
- D2180 assumes `if h:` branches that use `h` are rare ("none in the evidence"). std has at least five outside instances:
  - `Char.fromNat` (`Char.sw:20`)
  - `Fin.ofNatCheck` (`Fin.sw:81`)
  - two in `Int/Safe.sw` (`:20`, `:24`)
  - `Mod.sw:36`
- All of them are `Bool` equations once unfolded. `review/r2.sw` proves the `ifTrue` equation for `if h: i < n then Some (Fin.ofNatLt n i h) else None` with `Decidable.elimEq` and `J … (Bool.uniqueEq (Nat.leq (Succ i) n) True h2 h)`, and it checks.
- Doing the same step with `rewrite` instead gave `E-UNIVERSE`, so the generator should build the `J`.
- Fix: the condition is "`p` computes to an equation in a type with `DecEq`, `<`/`≤` on `Nat`/`Int` included". Correct the assumption text to say such branches are common and are covered by this rule.

**4. Major: constructs the note misses.**
- **Or-patterns.** `Tree::Leaf.alternatives` (`lib.rs:797-812`): an arm `| A | B => e` has no single left side. Lean splits these.
- **Local `def`s and lifted `match`es inside a `decreasing` definition** that call the owner. Those helpers take `%rec` (`decreasing.rs:19-21`), so `reach.left.eq1` would state `%rec`, which source can't use. The note needs a rule: state them with `%rec := (y => f y)`, or don't generate them.
- **Implicit and auto parameters** (`[a] [n]`, `[auto ord: Ord s]` as in `Graph.searchFrom`): the statement template in §3.1 lists only header parameters and pattern variables.
- **Names for `_` pattern variables** (`explode.eq1` comes from `Regular _`).
- **Merging character literals** is defined only when the earlier arms constrain that one column. Say what happens with `| 'k', Nil | c, xs`.
- **`opaque` definitions with a number pattern above `MAX_NUMBER_SPLIT` = 64** get no `f.unfold` (`opaque.rs:298-300`), so proof route 3 in §4 fails for them. §4 also says the limit is "about 100"; it is 64.
- **Records:** record patterns are not discussed.

**5. Minor: "names from source alone" conflicts with skipping decided after elaboration.** The `Unsupported` helpers with copies, the §3.5 limit and the 10× size bound are all decided after elaboration. The working copy adds that the hypothesis also depends on how the `if` was elaborated. So the index can list a name that is never made. Say what naming a skipped equation gives: an error with the reason that `doc` shows. The library already marks update lemmas `candidate: true` (`library.rs:684`), which is the precedent.

**6. Minor: naming has an asymmetry the note doesn't discuss.**
- `Graph.searchFrom` (arms) gets `.eq1` / `.eq2.ifFalse`. `Garden.fill` (`:= match stack with`, compiled into the same tree) gets `.eq.cons.ifFalse`.
- Rewriting one form into the other renames every equation. That cuts against D2176's argument that names are stable.
- Decide whether a whole-body `match` on a parameter counts as arms.
- Also say that a local `def eq` or `def induct` becomes reserved. Nothing uses those names today: my `grep` over std, aoc, games and examples found none.

**7. Minor: the cost argument rests on tiny bodies.**
- `gen_cost.py` times 5-arm definitions whose right sides are a few symbols long. The 0.08 ms per equation is real for those.
- "At most one more check of every body" is inferred, not measured. Substituting `let`s can make a statement much bigger than its body, as §10 admits.
- The 10% gate handles all this, so it isn't blocking. Add one data point at the size of `Garden.fill` or `searchFrom` before 1a merges.

**8. Minor: the evidence framing is slightly stretched.**
- "Agents have reshaped five programs" sits next to agentic-proving's category K (5). But K's five are mostly roguelike items (`agentic-proving.md:840`), not the rows of §1.1.
- The roguelike row was already fixed in the kernel by SW-533.
- This design removes three or four reshapes (days 12, 16, 18, 23). Say that number.

**9. Minor: some prototype claims don't reproduce from the files.**
- `p6.sw` contains only the definition, not the three failing attempts. I reproduced them in `review/r3.sw`, which gives `E-REWRITE-MOTIVE`, `E-MATCH-MOTIVE`, `E-MATCH-MOTIVE`. So `cases` fails with `E-MATCH-MOTIVE` here, not `E-CASES` as on p2.
- `p3.sw` fails with `E-CASES` from `kindEq3 n cases`, but the note says `E-OMEGA` with the model `n = 10`.
- Commit the prototypes, or quote the failing lines and outputs.

**10. Nit: citation drift.**
- `docs/syntax.md:58`, cited for doc's `rewrite` group, is blank; the text is at `:61`.
- "Made as kernel terms" is at `derive_induct.rs:40-41`, not `:37-39`.
- `docs/syntax.md:394` does not say that written update-lemma names are refused.
- Update lemmas are generated as source, not as kernel terms (`update_lemmas.rs:23`), so they are only a partial model.
- `explodeUnfold`'s hypothesis (`Explode.sw:21`, `depth < 4 ∨ …`) is weaker than `notArm2`, so the generated `explode.eq3` is less general. All six uses are at the `Regular a, Pair x y` or `Pair x y, _` shapes, where `cases` works, so nothing breaks. Say it.
- The default hypothesis name `found` reads badly on `= None`; p7 itself used `none`.

## Checked and correct

- Citations: `matching.rs:10-19` (generalisation, the `rfl` passed for a named scrutinee) and `:124-131` (the note text); `decreasing.rs:9-30`; `opaque.rs:20-25`; `lib.rs:802-813`; `library.rs:664-686`; `hash.rs:1-6`; `core.md:143,232-234,349-362`; `syntax.md:198,289,795,871,986-990,1100-1104,1748`; `Fill.sw:98-118,121-187` (21 and 67 lines; uses at `:145,164,179`); `Day18.sw:57-70`; `Search.sw:243-290`; Day 23 `Search.sw:24-33`; `Bool.sw:57`; `NOTES-2024.md:3517-3535, 5017-5034, 7573-7592`; `NOTES-2021.md:4546-4560` (0.98 → 1.1 s), item ranked 2nd at `:4644`; `equation-lemmas.md:765-767`; `proof-automation.md:898-899`; `explodeUnfold` used 6 times.
- Prototypes: p1, p2b, p4, p6b and p7 check, and p2 gives the three stated errors. The day 12 project checks (`check --no-cache Aoc.Year2024.Day12.Proofs`, 4.8 s user; the note says 3.8 s). `fillCorrectByInduct` is 51 lines.
- Soundness: every equation is kernel-checked and nothing new is trusted. The `J` motive over the scrutinee and its equation is the right construction. Proving `f.induct` through the same `decreasing` pipeline with the same decrease proofs is plausible: the prototype `fillInduct` does it by hand.
- Literature: I fetched Lean's FunInd module docs and the quoted phrases are there ("for each branch…", "tail-call positions", "equalities connecting the discriminant", fixed parameters, an unfolding variant). The rows for Isabelle (sequential, `simps`/`induct`), Rocq (`f_equation`, `f_ind`, `funelim`), Agda (`--exact-split`, `CATCHALL`) and F*/Dafny (fuel) match my understanding. I did not fetch those sources, so treat them as unverified.

## Decisions

D2173–D2184 are the right questions, and each one states its recommendation and assumptions. Add:
- (a) the overlap form for indexed families (finding 1);
- (b) normalising `Bool` guards (finding 2);
- (c) whether a whole-body `match` on a parameter counts as arms (finding 6);
- (d) in D2184, deprecate or delete std's `Graph.search*` names.

Correct D2180's assumption (finding 3).

My scratch files are in the session scratchpad under `review/`: `r1.sw` (indexed family), `r2.sw` (`if h:` with `Bool.uniqueEq`) and `r3.sw` (the three failures on a `decreasing` definition).
