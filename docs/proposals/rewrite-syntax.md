# How `rewrite` is written

**Status:** design note, nothing built. Ticket SW-3647, for D3666 (Matt,
16 Nov 2026, leaning towards a `using` style, "but maybe it does deserve
some more thought and consideration of options"). Judged by the end
state only (D2303): migration cost doesn't count.

**The short answer.** Keep the rule straight after `rewrite` and the
hypothesis after `at`, as today, and drop the brackets from `rewrite
repeatedly` so that it is the same form with one extra word:

```
rewrite h then byComputing
rewrite <- e at h
rewrite repeatedly steps, words
rewrite repeatedly words at h then t
```

The `using` style reads more like English for the one call in nine that
rewrites a hypothesis, but costs six characters on all the others, and
reverses what the word after `rewrite` means compared with today and with
every other prover looked at here (§1). It is the runner-up (§3, option B);
if Matt prefers it, it should be adopted whole, never mixed with today's
form (option C).

## 1. How others write it

Every system looked at puts the **rule** straight after the rewrite
keyword. The hypothesis, where there is one, comes after a connective.

| System | Rewrite once | A hypothesis | Repeatedly / simplifier | Sources |
|---|---|---|---|---|
| Lean 4 | `rw [e₁, ← e₂]` | `rw [e] at h`, `at h ⊢`, `at *` | `simp only [e₁, e₂] at h`; `simp` (the `@[simp]` set); `simp?` prints the `simp only [..]` that would do; `simp_all` | L1 |
| Rocq | `rewrite e₁, <- e₂` | `rewrite e in H` | `autorewrite with db₁ db₂ in H` (named bases built by `Hint Rewrite`); `rewrite ?e`, `rewrite !e` repeat one rule | R1, R2 |
| Isabelle | `subst eq` | `subst (asm) eq` | `simp only: e₁ e₂`, `simp add: e`, `(simp (no_asm_use))`; `unfolding defs`; `using facts` feeds facts to the next method | I1, I2 |
| Idris 2 | `rewrite prf in expr` (term level, as Stitchwort's is) | none: rewrite before binding | none | D1 |
| Agda | `f ps rewrite eq = v`, in a clause | the clause's arguments are generalised too | none | A1 |

Points that bear on the choice:

- **Rule first is universal.** "rewrite `h`" means "rewrite *with* `h`" in
  Lean, Rocq, Idris and Agda, and Isabelle's `subst eq` the same. Nobody
  puts the target first.
- **Isabelle's `using` is not "rewrite with".** It adds facts for the next
  proof method to use, whatever that method does with them (I2): `using h
  by simp` lets `simp` read `h` as an assumption. It is the nearest thing
  to Matt's spelling, and means something looser.
- **Named sets** are named after a keyword in both systems that have them:
  Rocq's `autorewrite with db`, Lean's `simp only [..]` (lists; the set is
  the attribute). Rocq's `autorewrite` doesn't support `at` at all (R2).
- **Several targets** are one call in Lean (`at h ⊢`, `at *`); Stitchwort
  has one (`at h`), and nests for more.

## 2. Counts in this repo

All `rewrite`s in std (`crates/elab/src/std`), `aoc`, `tools/toyfmt`,
`games/rogue` and `sf`, read by a small tokeniser at `9c1085a49`
**[measured]**; it agrees with a plain word count (5,086, which includes
comments) to about 1%.

| | goal | `at h` | together |
|---|---|---|---|
| calls | 4,482 (89%) | 541 (11%) | 5,023 |
| one rule | 3,117 (70%) | 448 (83%) | 3,565 (71%) |
| two rules | 899 | 87 | 986 |
| three or more | 466 | 6 | 472 |
| rules with `<-` | 944 of 6,585 (14%) | 89 of 643 (14%) | |
| with `then` | 4,225 (94%) | 350 (65%) | |
| `then byComputing` | 1,374 | 13 | |
| one rule that is a bare lower-case name (a hypothesis or local fact, mostly) | 1,054 (24%) | 180 (33%) | |

- **Chains.** `then rewrite …` straight after a `rewrite` is rare: 89
  chains of two, 6 of three, 1 of four. Several rules go in one `rewrite`
  with commas.
- **More than one target**, written today as `rewrite p at h then rewrite
  p …`: about 12 places.
- **Length.** The median `rewrite …` up to its `then` is 32 characters; the
  mean 38.
- **`rewrite repeatedly`** is a day old: 26 uses, all in examples and the
  guide. The projects have none yet; the toy formatter's `Words.sw`
  conversion (simp-revisited.md §6) is where its weight will be.

So the common case is a goal rewrite with one rule and a `then`:
`rewrite h then t`. Whatever is added to that is paid about 4,500 times.

## 3. The options

Each is shown on the same six real proofs:

1. a short goal rewrite: `crates/elab/src/std/Fin/Fin.sw:128`;
2. a hypothesis, right to left: `crates/elab/src/std/Nat/Arith.sw:609`;
3. a hypothesis rebound for the body: `aoc/src/Aoc/Year2024/Day18/Proofs/Part2.sw:60`;
4. a long chain: `crates/elab/src/std/Parse/RunsTokens.sw:81` (and five
   rules at once, `tools/toyfmt/src/Toy/Fmt/SpellProofs.sw:1425`);
5. `rewrite repeatedly` with a named set: `stepWords`'s arms, as
   simp-revisited.md §6 writes them with stage 2's `rules words`;
6. `<-` on the goal: `crates/elab/src/std/Result/Result.sw:92`.

### A. Today: rules first, `at`, brackets for `repeatedly`

Reads: "rewrite with *these*, at *that*, then …".

```
| FZero => rewrite h then byComputing
| Zero => Void.impossible (Bool.falseNotTrue (rewrite <- e at h))
let got: bytes.get index = Some byte := rewrite ended at answer then answer
rewrite first then rewrite <- List.lengthAppend before read then rewrite rest then byComputing
rewrite ifSplit, conditionSplit, thenSplit, trueSplit, elseSplit then …
| Line, steps, _ => cases then rewrite repeatedly [steps, words]
| [] => rewrite <- Result.okInjective done then Trivial
```

Shortest on the common case. The odd one out is `repeatedly`'s brackets:
plain `rewrite` lists rules with bare commas, `rewrite repeatedly` in
brackets, and with named sets they wrap one name, `[words]`. The brackets
are there only so that `repeatedly` stays an ordinary name elsewhere.

### B. `using` (Matt's lean): target first, `using` before the rules

Reads: "rewrite *that* using *these*", which is how English uses the
verb: the thing rewritten is its object.

```
| FZero => rewrite using h then byComputing
| Zero => Void.impossible (Bool.falseNotTrue (rewrite h using <- e))
let got: bytes.get index = Some byte := rewrite answer using ended then answer
rewrite using first, <- List.lengthAppend before read, rest then byComputing
rewrite using ifSplit, conditionSplit, thenSplit, trueSplit, elseSplit then …
| Line, steps, _ => cases then rewrite repeatedly using steps, words
| [] => rewrite using <- Result.okInjective done then Trivial
```

The grammar is `rewrite [targets] [repeatedly] using rules [then t]`.
`using` becomes a reserved word (no `.sw` file in the five projects uses it
as a name), and `repeatedly` must be one too, since `rewrite h repeatedly
using words` would otherwise read `h repeatedly` as a call. Several targets
come for free, `rewrite h, k using e`. A bare `rewrite h` is an error that
says "`rewrite using h`, or `rewrite h using …`".

Against it: six more characters on 5,023 calls, about a fifth of the median
call; the case it reads better for is the 11% with a target; and readers
coming from Lean, Rocq, Idris or Agda read `rewrite h` the other way.

### C. Mixed: rules first, `using` only with a target

Reads like A for the goal and like B for a hypothesis.

```
| FZero => rewrite h then byComputing
| Zero => Void.impossible (Bool.falseNotTrue (rewrite h using <- e))
let got: bytes.get index = Some byte := rewrite answer using ended then answer
| Line, steps, _ => cases then rewrite repeatedly steps, words
```

The word after `rewrite` is a rule or a target according to a word that
comes later: `rewrite steps then words` and `rewrite steps using words`
look alike and mean opposite things. The parser can cope (read a list, then
look for `using`); a reader can't at a glance, and an editor completing
after `rewrite ` doesn't know whether to offer lemmas or hypotheses. Not
recommended.

### D. Brackets everywhere (Lean's shape)

Reads: "rewrite with [this list], at that".

```
| FZero => rewrite [h] then byComputing
| Zero => Void.impossible (Bool.falseNotTrue (rewrite [<- e] at h))
let got: bytes.get index = Some byte := rewrite [ended] at answer then answer
rewrite [first, <- List.lengthAppend before read, rest] then byComputing
| Line, steps, _ => cases then rewrite repeatedly [steps, words]
| [] => rewrite [<- Result.okInjective done] then Trivial
```

Uniform with `repeatedly`, and the brackets end the rules, so `at` and `in`
need no special treatment inside a rule (today's parser has modes for
both), and `at h, k` could list targets plainly. Costs two characters per
call and bracket noise on the 71% with one rule.

### E. Today without the brackets (recommended)

Reads like A; `repeatedly` is an adverb on the same form.

```
| FZero => rewrite h then byComputing
| Zero => Void.impossible (Bool.falseNotTrue (rewrite <- e at h))
let got: bytes.get index = Some byte := rewrite ended at answer then answer
rewrite first, <- List.lengthAppend before read, rest then byComputing
rewrite ifSplit, conditionSplit, thenSplit, trueSplit, elseSplit then …
| Line, steps, _ => cases then rewrite repeatedly steps, words
| [] => rewrite <- Result.okInjective done then Trivial
rewrite repeatedly words at h then t          -- stage 2's `at`
```

`repeatedly` becomes reserved straight after `rewrite` (no project uses it
as a name), so `rewrite repeatedly` takes exactly what `rewrite` takes:
rules with commas and `<-`, `at`, `then`. One grammar, one adverb.

## 4. How each handles the rest

| | A today | B `using` | C mixed | D brackets | E no brackets |
|---|---|---|---|---|---|
| Characters on the common case (`rewrite h then t`) | 0 | +6 | 0 | +2 | 0 |
| The word after `rewrite` | rule | target, or `using` | either, decided later | `[` | rule |
| Same as Lean, Rocq, Idris, Agda | yes | no | goal only | yes (Lean) | yes |
| Several targets | `at` one; nest for more (about 12 places) | `rewrite h, k using e` | as B | `at h, k` | as A; `at h, k` could be added later |
| `then` | after rules or target | after rules | after rules | after `]` or target | as A |
| `in` (ends a rule, D3648) | needed | needed | needed | not needed inside `[..]` | needed |
| `calc` step `:= rewrite p` | as is | `:= rewrite using p` | as is | `:= rewrite [p]` | as is |
| Named sets | `[words]` | `using words` | `words` | `[words]` | `words` |
| Messages quoting it ("rule 2 of 2 of `rewrite … at h`", the suggestions in `search --at`) | as is | reworded | reworded, two shapes | reworded | as is |
| Editor completion after `rewrite ` | rules | targets and rules | can't tell | rules | rules |
| Expand (stage 2: `rewrite repeatedly` → the plain `rewrite`s it made) | brackets come off | drop `repeatedly` | drop `repeatedly`, maybe add `using` | drop `repeatedly` | drop `repeatedly` |
| Aloud | "rewrite with h" (the "with" unsaid) | "rewrite h using e" | mixed | "rewrite with list h" | as A |

Not taken further:

- **`rewrite e in h`**, Rocq's spelling. `in` is membership and ends a
  rule (D3648); giving it a third meaning brings back the confusion D3648
  removed.
- **`rewrite with e`**, a connective on the goal form only. Longer than A
  for nothing: there is nothing else `rewrite e` could mean.

## 5. Recommendation and end state

**E.** The common case stays `rewrite h then t`, as short as it can be and
as every other prover writes it; a hypothesis keeps `at`, which Lean users
already know; and `rewrite repeatedly` becomes the same form plus one word,
so named sets read `rewrite repeatedly words` rather than `[words]`.

End state:

| Form | Meaning |
|---|---|
| `rewrite r1, <- r2` | rewrite the goal, then close it by computing |
| `rewrite r1, r2 then t` | `t` proves what's left |
| `rewrite r1, r2 at h then t` | `h` rewritten and rebound for `t` |
| `rewrite r1 at f x y` | the term with its type rewritten |
| `rewrite repeatedly r1, words` | until no rule fits, then close |
| `rewrite repeatedly words at h then t` | the same on `h` |

The change from today: `repeatedly` reserved after `rewrite`; no brackets;
`at` with `repeatedly` (already stage 2). Small: the parser's
`repeated_rules` goes, `rewrite_body` reads the rules once for both.

If Matt prefers B for how it reads, B whole is a sound end state too: one
grammar, several targets for free; the cost is the six characters and the
habit of other provers. C is the one to avoid.

## 6. Decision for Matt

**D3666: which spelling?** [rec: E, today's form with `rewrite repeatedly`'s
brackets dropped; reopens the brackets part of D3647]

## Findings for the board

- **1,374 goal rewrites end `then byComputing`**, which `rewrite p` alone
  means (docs/syntax.md, `rewrite` table): about 23,000 characters. A
  warning with a fix, or the formatter, could drop them.
- **89 `then rewrite` chains** could be one `rewrite` with commas (the
  table says they're the same): a fix of the same kind.

## Sources

Fetched 16 Nov 2026.

- L1: Lean reference, Tactic reference (Rewriting; Simplification):
  https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/
- R1: Rocq reference, Reasoning with equalities (`rewrite`, `in ident`):
  https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html
- R2: Rocq reference, Programmable proof search (`autorewrite ->? *? with
  ident+ occurrences? using ltac_expr?`; "the `at` clause is currently not
  supported"): https://rocq-prover.org/doc/v9.3/refman/proofs/automatic-tactics/auto.html
- I1: Isabelle Isar reference, Generic (`simp` modifiers `add: del: flip:
  only: split: cong:`, `(no_asm_use)`; `subst (asm)`):
  https://isabelle.in.tum.de/library/Doc/Isar_Ref/Generic.html
- I2: Isabelle Isar reference, Proof (`using` "augments the facts to be used
  by a subsequent refinement step"; `unfolding`):
  https://isabelle.in.tum.de/library/Doc/Isar_Ref/Proof.html
- D1: Idris 2, Pattern matching proofs (`rewrite prf in expr`):
  https://idris2.readthedocs.io/en/latest/proofs/patterns.html
- A1: Agda, With-abstraction (`f ps rewrite eq = v`):
  https://agda.readthedocs.io/en/latest/language/with-abstraction.html
- Counts: `count.py` in the lane's scratchpad, run over the five projects at
  `9c1085a49`.
