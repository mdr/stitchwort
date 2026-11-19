# Review of the walk step design (SW-4238)

Fable, 19 Nov 2026, for Matt's request of the same day ("some Fable level
investigation into this type of tactic"). It reviews
[`docs/proposals/proof-walk-step.md`](../proposals/proof-walk-step.md)
(Opus, SW-4231) against prior art and against the code, read at `main`
`735541c03`. The probes are in [`SW-4238-probes/`](SW-4238-probes/) (as
`.sw.txt`, so no test or hook picks them up), checked one file at a time
with the main checkout's release binary (built 19 Nov, 14:49). A paper
lane: nothing in `tools/fmt` was checked, which matters for §1.

How claims are marked: **[measured]** run or counted by me today;
**[read]** in the file or page named; **[recalled]** from memory, not
re-read today; **[estimated]** my judgement.

## In plain words (two minutes)

**The design is sound and worth building, in a smaller form and after a
30-minute baseline lane.** A proof step that follows a function's body
and uses each called function's lemma is what every comparable system
has, and the proposal's rules (use a callee's lemma, never guess between
two, stop with an error that points) match what those systems learned.
Nothing in it touches the kernel.

**But the proposal's "before" picture is partly out of date.** It says
two things can't be done today, and builds its two parts on them. On
single-file copies of the comma list, both can be done today
[measured]:

- **The spelled-out pieces (`[p := …] [j := …]`) are not needed.** The
  comma list's proof checks with all eight deleted, in the one-run
  family, through the look-ahead bridge, and in the two-run family.
- **A `match` written inside a function can be walked.** The comma list
  as *one* function, with its `match` and both `if`s inline, is proved by
  hand in 28 lines with nothing spelled. The failure the proposal reports
  appears only when `j` is spelled out by hand.

I could not check this on the formatter's real files (a paper lane), and
the real files spell the pieces on 729 steps, so something there may
differ. **That is the first thing to find out**, by a small lane that
deletes the spellings and keeps what checks.

**What that changes.**

1. The walk's value is no longer "removes the spellings and lets the
   parser be un-cut": those look cheap or free. It is **writing the chain
   itself**: the comma list's 28 hand-written proof lines become 2 (the
   proposal's sketch, not yet checkable). That is still the gap SW-4222
   measured against Lean (118 lines to 45).
2. The two parts (a) and (b) merge into one lane. The walk writes the
   chain a person writes now, and the elaborator that already checks that
   chain does the hard part.
3. Success is measured against the cleaned-up text, not today's.

**Seven changes to the design** (§3): unfold a called function only when
asked; use local hypotheses for a parameter's calls without listing them;
one registered lemma per function and family; the cache gap is in std's
lazy loading, not where the proposal put it; say what happens when code
follows an `if`; a command-line "expand", since agents write these
proofs; the two-run family in the pilot, since it is the bigger one.

**The decision** (§6): build it as amended, about 5 agent hours in six
lanes, the first of them the baseline, with a stated point at which to
stop. I recommend yes.

## Contents

1. [What the probes show](#1-what-the-probes-show)
2. [Prior art](#2-prior-art)
3. [The design, point by point](#3-the-design-point-by-point)
4. [The pilot](#4-the-pilot)
5. [End state and lanes](#5-end-state-and-lanes)
6. [One decision for Matt](#6-one-decision-for-matt)
7. [Findings for tickets](#7-findings-for-tickets)
8. [Sources](#8-sources)

## 1. What the probes show

Five files, each a cut-down copy of real code with std only (`Nat` for
`Item`, `Parse.Invariant.any` for `GoodItems`) [all measured]:

| Probe | What it is | Result |
|---|---|---|
| `inline-match` | a function with `match fuel, seen` and an `if` inline after an effectful call; the proof is `Parse.givesThen lemma (seen _ => match fuel, seen with …)` with `Parse.givesDone` in each arm | checks |
| `inline-match-spelled-j` | the same proof with `[p := …]` and `[j := seen => match …]` written out | fails: "`_holds` is `Parse.givesThen`'s implicit `holds`, not worked out" |
| `comma-list-one-function` | `Parser.sw:1825-1848`'s four functions as one loop, with the theorem of `ParseWalk.sw:963`, proved by hand | checks; 28 proof lines, no spellings |
| `comma-list-cut-bridge` | the four functions as cut, with a `Modes` record, a `peek` method and the `Reads0` bridge `givesAfter0`; `givesCommaListFrom`'s proof with its eight spelling lines deleted | checks; 28 proof lines against the real one's 37 |
| `comma-list-two-run` | the `Parse.Follows` walk over the cut functions with `followsThenEq`, nothing spelled | checks |

What this says about the proposal's §1:

- **Its three reasons why inference fails did not reproduce.** "The goal
  is computed past the call", "the first step is in another family" and
  "the goal's parser is one unfolding away" are all present in
  `comma-list-cut-bridge`, and SW-3561's inference handles each. Its
  trigger is the shape `?j (?p ())`, not a list of lemma names [read:
  `parse-proof-library.md` §4, "As built"], so the bridge is covered.
- **Its probe's failure is the spelling's, not the `match`'s.** The
  message it quotes is the one `inline-match-spelled-j` gives, and that
  file differs from the passing one only in spelling `j`. A `match`
  written again in the proof is not the definition's `match`.
- **The quote about why the parser is cut is about something else.**
  "A `match` written inside a rule is a function the proofs can't name"
  (`tools/fmt/NOTES.md:1213`) is in the notes on `Rules.sw`, the
  printer's pure rules, where `rewrite` needs a name [read]. I used it
  for the parser in SW-4222 §3.2 and the proposal followed me. That was
  my error.

What it does **not** say:

- That the real files' spellings can go. They are on 729 steps (1,519
  lines) [measured: a script over `Syntax/*.sw`]: 192 of `givesAfter0`'s
  254 uses, 135 of `Parse.givesThen`'s 589, 124 of `followsThenEq`'s
  257, 45 of `Parse.followsMap`'s 122, 34 of `readsAfter0`'s 51, 32 of
  `Parse.followsThen`'s 448. So most plain `then` steps are already
  written without them, and the look-ahead bridges nearly always with.
  The proofs were written on 18 and 19 November, after the inference was
  built (16 and 17 November) [read: `git log`], so either the real
  bridges have a shape my copy lacks, or lanes copied the first proofs'
  style. The real two-run comma list, `followsCommaListFrom`
  (`FollowsBase.sw:451`), has no spellings at all [read], and its
  one-run twin in `ParseWalk.sw` has eight. Some spellings are certainly of another
  kind: `followsListItem` (`FollowsBase.sw:667`) spells a `p` that is a
  whole `a || b` expression with its own lemma, and `Parse.followsMap`'s
  are its two functions.
- That `ReadsAt`, `Kept` or `Carries` walks behave the same. Only
  `Gives` and `Follows` were probed.

So the proposal's two motivating numbers (1,583 spellings; 536
single-call functions) describe the text as written, not what the
language requires. The walk has to be judged on what is left after they
are cleaned up.

## 2. Prior art

### 2.1 Lean 4: `mvcgen`, then `vcgen`

All from Lean 4.35.0's installed source and its release notes [read],
plus what I ran for SW-4222 [measured then].

**Registering.** `@[spec]` on a theorem `foo_spec : ⦃P⦄ foo a b c ⦃Q⦄`
makes it "a specification for calls to `foo`"; on a definition it means
"unfold this" (`Std/Tactic/Do/Syntax.lean:76-84`). Lemmas are filed in a
discrimination tree keyed on the program. The brackets take lemmas,
definitions to unfold, and erasures (`[-foo]`).

**Choosing.** Candidates are sorted by priority and the first that
unifies is taken (`Lean/Elab/Tactic/Do/Spec.lean:23-55`): among equal
priorities the choice is silent. Getting the order right took several
fixes in 4.34: "makes `vcgen` prefer a spec named in a `vcgen [...]`
argument over one collected from an ambient local hypothesis"; "a
bracketed definition's unfoldings now rank below both a named spec and a
`*` hypothesis for the same program, so at a recursive call `vcgen`
applies that spec and stops rather than unfolding `f` again"
(release notes v4.34.0, lines 546-558). The result is three bands above
every `@[spec]`: named in the brackets, local hypotheses, unfoldings
(`Attr.lean:355-361`).

**At a bind,** the callee's spec is applied and the walk goes on in the
continuation. **At `if`, `match`, `cond`** it first tries to compute the
match, then splits ("last resort: split match", `VCGen.lean:171-200`),
with the branch condition as a hypothesis. **Code after a split:** by
default "we aggressively split `if` and `match` statements and inline
join points unconditionally. For some programs this causes exponential
blowup of VCs"; `+jp` chooses "a more conservative (but slightly lossy)
encoding" (`Syntax.lean:36-43`). **Loops** take an `invariants` clause;
4.34 added `for … invariant` in the program text. **Failure** (`throw`)
has its own postcondition per exception layer (`Std/Do/PostCond.lean`);
in SW-4222 a plain `throw` left `mvcgen` with unsolved instance goals
[measured then].

**No lemma for a call.** `mvcgen` simplified and, failing that, left the
goal. `vcgen` makes it an error by default: "report a hard error when no
`@[spec]` theorem matches the current program head … `mvcgen` exhibits
[the other behaviour] implicitly" (`Syntax.lean:49-55`). A plain
definition is never unfolded unless tagged or in the brackets.

**What is left.** Goals in which the program no longer occurs, tried by a
small closer, with machine-made names (`rename_i`) and `with` to run one
tactic on all of them.

**Why it is being replaced** (release notes v4.35.0, lines 44-60):

1. *Generality.* `vcgen` works on "any program type rather than only …
   monads", and assertions "can live in any complete lattice".
2. *Speed.* "On the AddSubCancel benchmark, where the program is a
   stateful loop body repeated 2200 times, `vcgen` needs 0.32 s where
   `mvcgen` needs 66 s, and the kernel checks the resulting proof in
   0.53 s instead of 246 s." `vcgen`'s time "grows linearly with the program size".
3. It "is still marked experimental". Invariant suggestions were not
   carried over. In SW-4222 it failed outright on my file ("Unknown
   constant `Std.WP.Triple.intro`") [measured then].

What I take from Lean: named beats local beats registered, written down
from the start; a missing lemma is an error, not a silent unfold;
unfolding is asked for; the cost of code after a split must be stated;
proof size must be linear in the program.

### 2.2 The others

| System | Registering | Choosing | Unfolding a callee | What it teaches | Source |
|---|---|---|---|---|---|
| seL4's `wp` (Isabelle, `lib/Monads`) | `wp` attribute on rules; `wp_comb`, `wp_split` sets; `wpc` for case splits; `wpsimp` wraps `(wpfix\|wp\|wpc\|clarsimp)+` | "always preferring to apply the theorem most recently added to a set" | never; `simp: f_def` by hand | the rule sets "are not necessarily ideal. Updating these rulesets would create difficult maintenance problems, and thus they are largely left as first defined". Also: "prove a collection of rules about a given program function, one for each conjunct"; and `wp (trace)` lists the rules used | [read] `l4v/lib/Monads/wp/WP_README.thy` |
| CFML (Rocq) | `RegisterSpec` hint, one database | "`xspec` looks … both in the database and in the context" (hypotheses); the context search "relies on heuristic, thus sometimes one needs to explicitly refer to the hypothesis" | never; a missing spec is an error | hypotheses as specs for local functions | [read] `cfml/lib/coq/WPTactics.v:184-215` |
| Iris (Rocq) | none | the user names the lemma at each call: `wp_apply lem` | `wp_pures` "will not reduce lambdas/recs that are hidden behind a definition"; `wp_rec`, `wp_lam` by hand | the largest body of such proofs works with **no registry**; explicit lists are a real option | [read by the proposal]; the rest [recalled], the docs site returned 429 again |
| Dafny | the contract is on the method | one per method | methods: never. Functions: "the default fuel setting for recursive functions is 1,2 … [more] may also increase verification time, so use it with care" | fuel-limited unfolding is a known source of unstable proofs | [read] Dafny reference, `Attributes.md` §11.2.8; the call rule [recalled] |
| Why3 | the contract is on the function | one | never | "the original form of WP calculi can possibly generate formulas that are of exponential size"; a per-expression switch avoids it | [read] Why3 manual, `doc/vcgen.rst` |
| F\* | the function's computation type | one | never (effectful code) | everything goes to a solver | [recalled]; the tutorial page was fetched and only skimmed |
| EasyCrypt (two runs) | none | `call` with a named two-run lemma; one-sided and two-sided rules; `seq` to line the two programs up | by hand (`inline`) | two-run walking is done in lockstep, with manual alignment where shapes differ | [recalled] |

**Where they agree.** A call is reasoned about by its lemma. An
effectful callee is unfolded only on request, in every system. A missing
lemma is reported at the call. Program conditions are split with the
condition kept.

**Where they differ, and what happened.** Global registries with an
ordering rule (Lean's priorities, seL4's last-added-wins) are the part
their own authors report trouble with. Systems with one contract per
function (Dafny, Why3, F\*, CFML's database) or none (Iris) don't have
that trouble.

**Where Stitchwort's case is easier.** `Parse.Gives inv p holds` has no
precondition to compute: the walk runs forwards and each step's fact is
the callee's `holds`. There is no schematic precondition (the "principle
caveat" of seL4's `wp`), no state assertion language, and no frames. The
design is right to be much smaller than `mvcgen`.

**Where it is new.** Nobody has a walk for two runs. SW-4222 found Lean
and Rocq "about even" with Stitchwort there. It is also Stitchwort's
larger family (§3.10).

## 3. The design, point by point

| # | Point | Verdict |
|---|---|---|
| 3.1 | What the walk is: parts (a) and (b) | **Change**: one mechanism; the walk writes the hand chain |
| 3.2 | Registration | **Keep** attributes; **change** to one lemma per function and family |
| 3.3 | Choosing a lemma | **Keep** "two that fit is an error"; **add** local hypotheses for parameters |
| 3.4 | How far it unfolds | **Change**: only when asked |
| 3.5 | Inner `if` and `match` | **Keep**; **add** the rule for code after a split |
| 3.6 | Recursion and fuel | **Keep**; state the limits |
| 3.7 | Effects | **Keep** stage 1's limits |
| 3.8 | Failure messages and expanding | **Keep**; **add** a command-line form and expanding a failed walk |
| 3.9 | Check time and brittleness | **Keep** the bar; **add** a refactoring test |
| 3.10 | Two-run families | **Change**: in the pilot, not beside it |
| 3.11 | The cache gap | **Change**: it is elsewhere |
| 3.12 | Or-patterns (D3694), functional induction (SW-4229) | no conflict; one shared piece |
| 3.13 | Syntax | **Keep**; one naming point |

### 3.1 What the walk is

The proposal has two parts: (a) read `p` and `j` off the body, and (b)
split inner `match`es by stating each arm's type "itself, folded", so
that the kernel accepts it by conversion. §1 shows the elaborator already
does both for a hand-written chain: it finds `p` and `j`, and a proof
`match` on the program's scrutinees refines the goal in each arm.

**Change.** Define the walk by its expansion: *`walk [..] then t` means
the chain a person would write* (`then`-lemma, proof `match`, `done`,
`weaken`), and the walk's job is to produce that chain from the body:
which step comes next, which lemma, which premises, which closer. Then:

- parts (a) and (b) are one lane, and "stepping into a definition's
  `match`" needs no new treatment of definitions;
- **Expand walk is exact by construction**, and the bar "every expansion
  checks again" (§4) is cheap to meet;
- check time is the hand proof's plus the planning.

The build lane chooses whether it emits surface syntax and elaborates
it, or builds the same applications directly. One caution from
`inline-match-spelled-j`: an expansion must not print a `[j := …]` that
contains a `match`, because that text does not check. It should print no
spellings where inference works, which on the probes is everywhere.

### 3.2 Registration

Three options: a naming convention, explicit lists only (Iris), or
attributes (Lean, seL4, CFML).

- **A convention: no,** for the proposal's reason (names aren't uniform,
  and a miss is silent).
- **Explicit lists only** would work, and is the most in keeping with
  "Stitchwort's proofs say what they use". But the bracket lists get
  long (the two-run walk in the proposal's §4.2 names four lemmas for one
  step), and the lists are what a lane gets wrong.
- **Attributes: keep,** with three constraints that the prior art's
  troubles point to:

1. **One `@[walk]` lemma per function and family, checked where it is
   declared.** A second one for the same head whose thunk overlaps the
   first is an error at the attribute, naming the first. No priorities,
   no ordering. Today 62 of 1,167 function-and-family pairs have more
   than one lemma, and 27 of those are in `ReadsAt` (half its heads:
   `readsAtBumpFirst`, `readsAtBumpRead`, …) [measured]. The general one
   is tagged; the special ones go in the brackets. Two lemmas tagged in
   unrelated modules and met in a third are still an error at the walk,
   as proposed.
2. **Keep the family attributes** (`walk.then`, `walk.done`,
   `walk.weaken`) and their shape check. They are few and in std.
3. **`@[walk]` thunks are first-order**: the head applied to distinct
   variables or closed terms. A lemma about `k (bump())` is a `then`
   rule (a bridge), not a call lemma.

### 3.3 Choosing a lemma

**Keep** the three tiers and the rule that two fitting lemmas in a tier
is an error. That is stricter than Lean and seL4, and their notes say
why it should be.

**Add: a local hypothesis is used for a call whose head is a
parameter.** `endsGives` and `nextGives` are in the theorem's statement
and speak about `ends` and `next`, which nothing global can be registered
for. CFML and Lean both look in the context. The comma list's walk then
needs only `walk [reads0Peek modes]`, or `walk []` once that is tagged.
If two hypotheses fit the same call, it is the usual error.

**Fix the order between unfolding and lemmas** (Lean's 4.34 regression):
a lemma named in the brackets beats `unfold f` for the same call, and
`unfold f` beats a registered lemma. The theorem's own recursive call is
never unfolded.

**Premises.** The proposal fills a lemma's other premises "from the
facts the walk has introduced, the hypotheses in scope and the bracket
terms". Keep, with one rule: a premise is filled only when its type is
fully known after matching the call, or exactly one candidate fits.
Otherwise it is a leftover goal. No search over combinations.

### 3.4 How far it unfolds

The proposal unfolds any called function that is not recursive and has
no `@[walk]` lemma in the goal's family.

**Change: unfold only the goal's own head, and what the brackets name
(`unfold f`).** A call with neither a lemma nor an `unfold` stops with
`E-WALK`, whose note gives both fixes.

Why:

- **It is the trap I met in Rocq** (SW-4222 §4): the walk went into
  `expect` instead of using its lemma, and passed silently into a harder
  goal. Under the proposed rule the same happens whenever a lemma exists
  but is not visible: not imported (walk lemmas live in `ParseWalk.sw`,
  the functions in `Parser.sw`), not yet tagged, or proved in another
  family (`givesBump` exists, a `Carries` walk meets `bump()`). The walk
  then goes into `bump`, into `Parse.next`, and stops inside std with a
  message about a place the user never wrote.
- **Every system in §2 asks first.** Lean made a missing spec a hard
  error in the rewrite.
- **It removes a dependency on what is absent.** With unfold-by-default,
  adding a lemma for a helper changes every walk that used to go through
  it. With unfold-on-request, a walk depends only on the lemmas it used.
- **The cost is small and shrinking.** For the cut parser the brackets
  gain `unfold commaListOn, unfold commaListComma, unfold
  commaListAfter`. For code written with its `match` inline (§1) there
  is nothing to unfold.

### 3.5 Inner `if` and `match`

**Keep:** split as the program does, on the compiled case tree, with the
condition as a hypothesis, and a guard split after its pattern.

**Add: what happens to code after a split.** The proposal's rule covers
a `match` that ends the body. When its value is used by later code
(`let x := if c then a() else b()` and then more), the rest runs after
every arm. Lean copies the rest into each arm by default and warns of
"exponential blowup"; Why3's manual says the same of the classic method.
For stage 1: copy the rest into each arm, cap the number of paths (64,
say), and at the cap stop with `E-WALK` suggesting the usual cure: make
the split a function with its own lemma. That lemma is the meeting
point's fact, written once.

**Note:** `a || b` and `if f() then …` with effectful operands are a
bind and then a split. The walk handles them as such, so helper lemmas
like `followsAtEither` (`FollowsBase.sw:650`) stop being needed.

### 3.6 Recursion and fuel

**Keep:** the walk does no induction; a recursive call of the theorem's
own head uses the theorem; loops and `recursiveWith` go by their lemmas.

State three limits:

- **The generated proof must pass the termination check as a hand proof
  does.** It does when the smaller argument is a pattern variable of the
  walk's own `match` (`Succ more`), as in both comma-list probes. A
  recursion justified by `decreasing` stops with `E-WALK` in stage 1.
- **Higher-order callees.** `Parse.loop (() => …)` is called 17 times in
  `Parser.sw` [measured], and its lemma has a premise that is itself a
  walk goal about the thunk. Stage 1 leaves that premise as a named
  leftover goal, to be given in the brackets. Walking it in place is a
  later step.
- **Fuel is ordinary.** Nothing in the walk knows about fuel. It is a
  `match` scrutinee like any other.

### 3.7 Effects

**Keep** stage 1 as proposed: one closed row, and `handle`,
`translate`, `match reify` and effect-polymorphic code stop the walk.
Every formatter parser is `{Parse Item}`. Failure needs nothing special
here, unlike Lean's exception postconditions: `Parse.Gives` speaks only
of successful runs, so a `fatal` arm is closed by its lemma.

### 3.8 Failure messages and expanding

**Keep** `E-WALK` as drawn: it names the call, its place in the program,
the path taken, and the goal. That is better than `mvcgen`'s "No specs
found".

**Add:**

1. **A command-line expand, in the first lane.** Agents write these
   proofs and have no editor. `rewrite repeatedly` has
   `stitchwort check --expand-repeatedly FILE` [read: `docs/syntax.md`,
   "Expanding"]; the walk needs the same (`--expand-walk`). The proposal
   has it only as an editor action, in the last lane.
2. **Expand a walk that failed.** It should write the chain as far as it
   got, with the stuck goal left open. Otherwise a walk that fails at
   the ninth step of ten is rewritten by hand from nothing, and the
   escape hatch is no help when it is needed.
3. **A trace on success** (which lemma at which call) from the same
   command. seL4's `wp (trace)` exists because people needed it.
4. **Leftovers of different kinds.** `then t` runs one term in every
   leftover goal. A walk with two different hard leaves has to be
   expanded. Don't add labelled alternatives yet; count such walks in
   the pilot (§4).

`then t` has the meaning D3694 gives an or-pattern's body: `t` is
checked once in each goal, and an error says which path it is in. Say so
in the guide, since the two will be learnt together.

### 3.9 Check time and brittleness

**Check time: keep** the bar (within 1.5 times the hand proof). With the
walk defined as its expansion (§3.1) the kernel's work is the hand
proof's. Two things to watch, both seen today:

- A failed inference is slow. A theorem with an unrelated error took
  12 s where the corrected one takes 0.5 s [measured:
  `comma-list-two-run` with an unknown name in a leaf]. The walk knows
  `p` and `j` and should pass them, not rely on a retry.
- Closers run at every leaf. Cap each attempt, and record which closer
  closed which goal so the expansion can say so.

**Brittleness: add a test.** My SW-4222 note was that automation's
proofs break when something unrelated changes. The design's answers are
good: names from the program, one lemma per call, no search. With §3.4
a walk depends only on what it names or looks up. What is left:

- renaming a binder in the parser renames a fact that `then t` may use.
  That is visible and local;
- changing a registered lemma's statement changes every walk through it.
  That is true of hand proofs too;
- a closer that gets weaker breaks walks. Closers are few and built in.

Measure it instead of arguing: the pilot applies three small scripted
edits to the parser and counts which proofs break, walks against hand
proofs (§4, bar 5).

### 3.10 Two-run families

The proposal puts the two-run walk in its own lane, "beside" the pilot.

**Change: it is in the pilot's bars.** `Parse.Follows` has 529 lemmas
at a named function against `Parse.Gives`'s 455, and 201 of the 729
spelled steps [measured]. Its callee lemmas take the long argument lists
(fourteen for `followsCommaListFrom`). It is also the one place where
Stitchwort would be ahead of Lean and Rocq, not level.

**Keep** lockstep only, and stopping when the two bodies differ in
shape. The formatter's two runs are one parser on two inputs, so the
shapes agree.

### 3.11 The cache gap

The proposal: "a lemma *added* to an imported module can change a later
choice … the key should include the walk lemmas in scope".

**For project code there is no gap.** A namespace's cache key includes
"the keys of the namespaces it imports", so "an edit anywhere changes
the key of that namespace and of everything that depends on it" [read:
`check-cache.md` §4.2]. A lemma added to an imported namespace
re-elaborates the importer.

**The gap is in std's lazy loading.** Library files "load on demand, in
an order that depends on what the program uses" [read: `check-cache.md`
§4.4]. `reading.rs` says what follows for anything found by registry:
"a pattern mentions no reading, so a reading anywhere else could be
missing from a run that needs it, and the check cache … could miss a
change to it" [read: `crates/elab/src/reading.rs:11-15`]; hence a
reading must live in its head's module. Walk lemmas can't follow that
rule: `Parse.token`'s are in `Parse/ReadsTokens.sw`, the function in
`Parse/Tokens.sw`. A walk that meets `Parse.token` would find its lemma
only if something else had already loaded that file.

**Change:** std's name index gains the walk entries (family and head to
lemma name), built with the index. A lookup then loads the file, as
mentioning a name does, the result no longer depends on load order, and
the cache records the lemma as it records any library reference (by path
and content hash, §4.4). With §3.4 there is no "absent lemma" to record.
One note for later: when declarations are reused one at a time in the
editor (planned in `check-cache.md` §4.1), a walk's lookups are among
its dependencies.

### 3.12 Or-patterns and functional induction

- **D3694 (or-patterns that bind).** No conflict. The walk follows the
  compiled case tree, where an or-pattern is already one arm per
  alternative. Two small uses once it is built: the expansion can join
  arms with the same proof (the comma list's four `givesDone` leaves),
  and `then t` shares its "checked once per case" wording.
- **SW-4229 (`f.induct`).** They don't overlap in use: `f.induct` is
  for facts about a pure recursive function, the walk for effectful
  code, and the walk does no induction. They share one piece of
  machinery: a definition's case tree with each guard as a hypothesis
  (also SW-4047's missing step). Whichever lane lands first builds it in
  `induct_match.rs`'s neighbourhood and the other uses it. Neither waits
  for the other.

### 3.13 Syntax

**Keep** `walk [lemmas] then t` and `unfold f` in the brackets.

One point for the orchestrator: `walk` is a word only before `[`, and
"no program writes `walk [` today". But a function called `walk` applied
to a list is ordinary code, and 426 uses of the name exist. `byWalking
[…]`, beside `byComputing`, has no such clash. It is user-visible
wording, so Matt's if he cares; I would use `byWalking`.

## 4. The pilot

**Scope: adjust.** Add a baseline lane first, and judge against it.

**W0, the baseline** (new; Sonnet, 30 min; it checks only the namespaces
it edits):

1. In the comma lists and brackets of `ParseWalk.sw` (the proposal's 40
   walks) and their twins in `FollowsBase.sw`, delete every `[p := …]
   [q := …] [j := …] [k := …]` and keep each deletion that checks.
   Report how many were needed, and the shape of each that was.
2. Merge the four comma-list functions into one, as in
   `comma-list-one-function`, and re-prove its `Gives`, `ReadsAt` and
   `Follows` lemmas by hand. Report whether each family allows it.
3. Record proof lines (statements excluded) and check time. This text is
   the "before" for every bar below.

W0 also answers SW-4220 ("helpers … or say why inference can't").

**Bars,** on the pilot's walks after the walk is built:

| # | Bar | Was |
|---|---|---|
| 1 | Proof lines, statements excluded, at most half of W0's; at least 80% of the pilot's walks are shorter as walks | "at most half" of today's text |
| 2 | Check time of each converted file within 1.5 times W0's; no theorem more than 3 times | the same, per file only |
| 3 | Reject examples (missing lemma, false leaf, two lemmas, unsupported construct, path cap) each name the call and show the goal | the same, plus the cap |
| 4 | Every converted walk's expansion checks, from the command line | new; replaces "the parser can be un-cut", which W0 settles |
| 5 | Three scripted edits to the parser (rename a binder; add a step inside a callee whose lemma is unchanged; add a `match` arm): walks break no more often than W0's hand proofs | new |
| 6 | Ten two-run walks converted, to the same bars | new |
| 7 | Count of walks that needed expanding because two leaves needed different proofs | new; a measure, no threshold |

**What means "stop".** After the walk lane and the pilot, close the
remaining lanes and keep W0's gains if any of these holds:

- fewer than 60% of the pilot's walks are shorter as walks;
- the median saving in proof lines is under 30% of W0's text;
- check time is over 2 times W0's after one tuning lane;
- more than 30% of walks need expanding to be finished.

And one early stop: if W0 shows the real files need their spellings for
a reason the probes missed, the walk lane waits until that reason is
understood, since the walk as amended relies on the same inference.

## 5. End state and lanes

**End state, in plain words.**

- A parser function is written once, with its `match` and `if`s inline.
  Functions are split where the grammar has a rule, not for the proofs.
- Each function has one lemma per property family, tagged `@[walk]`.
  For most, the proof is one line: `walk []`, or `walk [..] then t` when
  a leaf needs a fact the closers don't find.
- Std's sequencing lemmas are tagged once per family, and a new family
  (a state invariant, a new two-run relation) needs no compiler change.
- A walk that can't go on says where in the program it stopped and what
  it needed. Any walk can be turned into the chain it stands for, by a
  command, and that chain is the proof a lane writes today.
- The kernel sees only applications of std lemmas, as now.

It will not make the lemmas disappear (no system does), and the leaves
that carry real content (`ParseKept`'s regrouping) stay as long as they
are.

**Lanes.** Estimates in agent time, from the proposal's cited actuals
[read there].

| Lane | What | Model | Estimate | Board |
|---|---|---|---|---|
| W0 | Baseline: delete spellings, un-cut the comma list by hand, measure | Sonnet | 30 min | new; takes SW-4220's question |
| W1 | The walk for one-run families: binds, calls (brackets, own theorem, local hypotheses, registry), `unfold` on request, `if`/`match` with the path cap, values, weaken, closers, names, `E-WALK`, the attributes, std's index entries, `--expand-walk` and the trace; guide and `syntax.md`; accept and reject examples | Opus | 120 min | SW-4239, widened (it was part (a)) |
| W2 | Review of W1 (it generates kernel terms, D2364) | Opus, paper | 20 min | new |
| W3 | Two-run families in lockstep | Opus | 60 min | SW-4240, repurposed (part (b) is in W1) |
| W4 | Pilot: tag and convert the 40 walks and ten two-run walks; measure bars 1 to 7 | Sonnet | 60 min | new |
| W5 | Editor: goals at `walk`, hover trace, Expand walk | Sonnet | 30 min | new |
| W6 | Check time, only if bar 2 is missed; one lane | Opus | 0 to 45 min | new, on need |

About **5 to 6 agent hours**, against the proposal's 6 to 7. W1 is
smaller than the proposal's W1 and W2 together (175 min) because the
inner-`match` machinery is the elaborator's own [estimated]. Order: W0,
then W1, W2, then W3 and W4 (W4's two-run bar needs W3), W5 any time
after W1. The rollout over slice 1's 920 walks stays a separate,
mechanical job, as proposed.

## 6. One decision for Matt

**Build the walk step as amended by this review, about 5 to 6 agent
hours in six lanes, starting with the 30-minute baseline, and stop at the
points in §4 if the pilot misses? [rec: yes]** (The orchestrator numbers
it; it replaces the proposal's D3695.)

- **The problem.** A parser function's lemma is written by hand as a
  chain that follows the function step by step. On the comma list that is
  28 proof lines even after everything unnecessary is deleted
  [measured on a copy]. Lean's tool did the same job in 3 to 7 (SW-4222 §3.2).
  Slices 2 to 7 need about 2,100 to 2,500 more such lemmas.
- **The change.** A proof step that follows the function's body, uses
  the lemma registered for each function it calls, splits where the
  program splits, and leaves only the facts that need thought. It writes
  the same chain a lane writes now, so the kernel checks what it always
  did. Against the proposal: it unfolds a called function only when
  asked, takes one registered lemma per function, covers the two-run
  proofs in the pilot, and can always be turned back into the
  hand-written chain from the command line.
- **What it should do.** The comma list's proof becomes 2 lines from 28;
  the proposal's other two examples become about 10 and 27 from 26 and
  55 [its sketch, unchecked]. The pilot must show at most half the proof
  lines over 50 real walks at no more than 1.5 times the check time, or
  the work stops with the baseline's clean-up kept. No statement changes
  and no theorem gets weaker.

Not for Matt unless he wants them: the word (`walk [` or `byWalking [`),
lane order, models, the path cap, the closers.

## 7. Findings for tickets

1. **Spelled arguments that may no longer be needed.** 192 of 254
   `givesAfter0` uses and 135 of 589 `Parse.givesThen` uses spell `p`
   and `j`; on a copy none is needed. W0 measures the real files. If it
   holds, the sweep over all 729 steps is mechanical (DeepSeek, by
   file).
2. **A slow, misleading second error.** In `comma-list-two-run`, with an
   unknown name in three leaves, the check took 12 s and also reported a
   type mismatch at a correct `followsThenEq` step ("they first differ at
   `_j₂ False` …"). With the name fixed it checks in 0.5 s. A failed
   theorem should not make a sound step fail slowly.
3. **A spelled `j` holding a `match` does not check**
   (`inline-match-spelled-j`): the message blames `holds`. Either it
   should check or the message should say the `match` in `j` is not the
   definition's.
4. **The parser can probably be un-cut today.** If W0's step 2 passes in
   all three families, new parser code (slice 2 on) should be written
   with its `match`es inline, and a brief line should say so.
5. **A wrong attribution** in SW-4222 §3.2 and the proposal's §1:
   `NOTES.md:1213` is about `Rules.sw`, not the parser.
6. **Lemma statements with long explicit argument lists** that the calls
   determine (`followsCommaListFrom`'s fourteen): making them implicit
   shortens hand proofs now, with or without the walk (SW-4222 §3.5 said
   the same of the printer's triples).

## 8. Sources

- **Stitchwort** at `735541c03`: `docs/proposals/proof-walk-step.md`;
  `docs/reviews/SW-4222-lean-rocq-comparison.md`;
  `docs/proposals/parse-proof-library.md` §4 ("As built");
  `docs/proposals/check-cache.md` §4.2 and §4.4;
  `crates/elab/src/reading.rs` (module docs), `library.rs` (the name
  index); `crates/elab/src/std/Parse/{Gives,Follows,Reads}.sw`;
  `tools/fmt/src/Syntax/{Parser,ParseWalk,ParseProofs,FollowsBase}.sw`;
  `tools/fmt/NOTES.md:1203-1213`; `docs/syntax.md` ("Expanding");
  `docs/proposals/proof-match-likewise-prior-art.md` §5 (D3694).
- **Counts** [measured]: two Python scripts over
  `tools/fmt/src/Syntax/*.sw`, run for this note and not committed. One
  groups theorems by family and the head of the thunk in their
  conclusion (1,249 theorems, 1,167 pairs, 62 with more than one). The
  other finds each run of `[p :=`, `[q :=`, `[j :=`, `[k :=` lines and
  the lemma on the line before (729 steps). Both are regular expressions; good to a few per
  cent.
- **Probes** [measured]: `docs/reviews/SW-4238-probes/*.sw.txt`, each
  with its result in its first lines.
- **Lean 4.35.0** (nixpkgs `lean4`, source in the Nix store) [read]:
  `src/lean/Std/Tactic/Do/Syntax.lean` (config, lines 19-71; `spec`,
  76-84; `mvcgen` deprecated "since 2026-08-21", 440);
  `src/lean/Init/Tactics.lean:2336-2520` (both docstrings);
  `src/lean/Lean/Elab/Tactic/Do/{Spec,VCGen,Attr}.lean`;
  `src/lean/Lean/Elab/Tactic/VCGen/{Solve,Context,Frontend}.lean`.
  Release notes: `leanprover/reference-manual`,
  `Manual/Releases/v4_35_0.lean` lines 35-60 and `v4_34_0.lean` lines
  532-570, fetched raw from GitHub.
- **seL4** [read]: `seL4/l4v`, `lib/Monads/wp/WP_README.thy` and
  `WP-method.ML`, raw from GitHub.
- **CFML** [read]: `charguer/cfml`, `lib/coq/WPTactics.v` lines 184-215
  and 1584-1600.
- **Dafny** [read]: `dafny-lang/dafny`, `docs/DafnyRef/Attributes.md`
  §11.2.8.
- **Why3** [read]: `doc/vcgen.rst` from gitlab.inria.fr.
- **[recalled], not re-read today:** Iris's `wp_rec` and `wp_lam`
  (gitlab.mpi-sws.org returned 429 twice); EasyCrypt's `call`, `seq` and
  `inline`; F\*'s and Dafny's call rules.
