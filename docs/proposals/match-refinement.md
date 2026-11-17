# Proposal: what a `match` refines

SW-3754, 17 Nov 2026 (Fable paper lane; asked for by Matt after Toy++).
Covers the friction in SW-3466, SW-3741, SW-3639, SW-3650 and SW-3468.
No code was changed. Each claim is marked **[measured]** (run with the
release binary on a small file, shown in §2), **[checked]** (read in the
elaborator's source or the docs), **[cited]** (another system's docs or
source, fetched today), **[memory]** (not fetched), **[inferred]** or
**[estimated]**.

## Summary

**The problem.** In a proof, `match e with | p => …` is meant to say "from
here on, `e` is `p`". Today that is true of some things and not others:

- The goal and the hypotheses have `e` replaced by `p`, once, where `e`
  can be found when the `match` starts. That search looks through
  definitions, so a hypothesis can change though its text never mentions
  `e` (`good: Good token` after `match token.kind`).
- Anything written inside the arm still says `e`: a lemma's premise, a
  `rewrite` rule, a lemma's conclusion. So a refined hypothesis doesn't fit
  the lemma it is passed to. If the `match` names its equation (`match h:
  e`), proofs are carried across automatically in one situation (an
  argument whose type differs only by `e` against `p`); otherwise it is an
  error.
- A copy of `e` that only appears after the replacement lets a definition
  compute (the `pairKept` case) is left as `e`.
- A lemma's implicit arguments are worked out by comparing its conclusion
  with the goal. The comparison stops at the first place where the lemma
  says `e` and the goal says `p`, before it reaches the parts that would
  have told it the implicits.

Every friction case in the tickets is one of these four, except two
(`readsInPeek`'s `k`, and implicits guessed from an equation), which are
about how unknowns are solved and have their own fixes (§6).

**The proposed rule.** *In an arm, the scrutinee is the pattern, for
everything the arm reads or writes.* Concretely:

1. **What is refined:** the goal, and every hypothesis and earlier `let`
   whose type mentions `e` once computed, as today. Nothing is removed from
   that.
2. **Terms written in the arm are refined too.** Wherever the checker
   compares two types in the arm and one has `e` where the other has `p`,
   it treats them as the same and carries the proof along the arm's
   equation. This holds whether or not the `match` names the equation, and
   in every comparison: an argument, a lemma's conclusion against the goal,
   a `rewrite` rule's left side, and `byComputing`.
3. **Definitions are looked through**, as today, and again afterwards: if
   the replacement lets something compute and that uncovers another `e`,
   that one is replaced as well.
4. **A refinement is visible.** The goal view marks each refined
   hypothesis and says what replaced what; every error in an arm that
   involves `e`, `p` or a refined hypothesis says which `match` did it.
5. **Implicits after a refinement** are worked out as they would be
   outside the `match`: point 2 lets the comparison carry on past `e`
   against `p`, so the rest of the conclusion is read.

**What it fixes.** All of SW-3466, SW-3741, SW-3639, SW-3468, and the first
and fourth items of SW-3650; the 50 `(rewrite e then fine)` and the "about
10 extra lemmas" of T1c go with them **[inferred from the small repros;
not run on the toy]**. The other two items of SW-3650 get their own fixes.

**What it costs.** About 4 to 5 hours of agent time in six pieces, mostly
Opus (it is `match` and the unifier) **[estimated]**. Every piece but one
acts only where a proof fails today, so proofs that check now keep their
terms and hashes **[inferred]**. The exception is optional (question 2):
keeping an arm's goal in its written form, which changes generated helper
types and needs a whole-project measurement on Overmind first. Trust is
unchanged: every step is a rewrite along an equation that the kernel
checks, and no kernel rule changes.

**Questions for Matt** (§8): (1) adopt this rule, rather than Lean's
("only the goal is refined; you rewrite the rest yourself")? Recommended:
yes. (2) Should an arm's goal also keep its written form, with definitions
folded, measured on Overmind before deciding? Recommended: yes to the
measurement, after the rest is built.

## 1. What Stitchwort does today

From `crates/elab/src/matching.rs` (module doc, `lifted`, `generalised_now`,
`bind_generalised`), `matching/as_written.rs`, `rewrite.rs`
(`replaced_by_match`) and docs/syntax.md "`match`" (the paragraphs "The
goal, as written first", "Hypotheses", "The equation", "Terms written in
the branch"). **[checked]** unless marked.

There are two kinds of scrutinee.

**A variable** (unnamed, not a `let`, not already split): a real case
split. The variable becomes the pattern everywhere: the goal, every
hypothesis, and terms written in the arm, since the name now stands for
the pattern. There is no equation and none is needed. This case causes no
friction in the tickets.

**Anything else** (an expression, a named scrutinee `h: e`, a `let`'s
name, a variable already split) is *generalised*, once, when the `match` is
elaborated:

- **Where `e` is looked for.** In the goal and in the type of every
  variable in scope, *as they compute*: both are read back from their
  values, so non-recursive definitions are already unfolded and recursive
  ones are unfolded as far as their arguments allow. An as-written search
  runs first (goal-as-written.md stage 2) and its result is used only if
  it replaces every occurrence the computed search would; otherwise the
  computed search's result is used and the arm's goal is the computed
  form.
- **Which hypotheses.** Every parameter, lambda variable and `let` whose
  computed type contains `e`, and every one whose type mentions one of
  those. Each gets a copy with `p` for `e`, which hides the original. A
  `let` loses its value in the arm.
- **`match h: e`** also binds `h: e = p`, about the original expression.
  It enables one more thing: where an argument's type and the expected
  type differ only by `e` against `p`, the proof is rewritten along `h`
  ("transport", SW-1538). Proofs only. An unnamed `match` has no equation,
  so no transport, except for decided propositions, which get a hidden one
  (`%tested`).
- **Not refined:** terms written in the arm; occurrences under a binder
  that use its variable; anything that appears only after the replacement
  computes.
- **Several scrutinees:** none may occur in another or in another's type
  (`E-MATCH-MOTIVE`, "this version can't generalise").

This is Agda's `with`, plus the as-written preference and the transport.

## 2. The friction cases under that rule

Each was reproduced small with
`~/repos/mdr/stitchwort/target/release/stitchwort check`. The files are
given in full so the lanes that build this can use them as tests.

### 2.1 Too much: SW-3466 **[measured]**

```
type Kind = | Name | Other
type Token = { kind: Kind, text: Nat }

def Good (t: Token): Prop := match t.kind with
  | Name => 0 < t.text
  | Other => t.text = 0

def weight (t: Token): Nat := match t.kind with
  | Name => t.text
  | Other => 1

theorem goodWeighs ∀ (t: Token) (good: Good t): 0 < weight t + 1 := ?

theorem unnamed ∀ (token: Token) (good: Good token): 0 < weight token + 1 := match token.kind with
  | Name => goodWeighs token good
  | Other => goodWeighs token good
```

Both arms fail: "expected `(match token.kind with …)`, but this has type
`0 < token.text`". `good`'s text never mentions `token.kind`; it was found
through `Good`'s definition and replaced. The lemma written in the arm
still wants `Good token`. With `match k: token.kind` both arms check (the
transport), and so does a `let done := goodWeighs token good` before the
`match`. So "too much" is really "the hypotheses are refined and the arm's
own terms aren't, and the cure depends on whether the `match` has a name".
The error's notes already say all of this; the cost in Toy++ was 26 errors
before reading them.

A second repro, with `among: List.All Good state.rest`, `match e:
state.rest with | [{ kind = Name, text }, ..later] => …` and a lemma that
takes `among`, checks today: nested patterns and computed hypotheses
transport correctly when the equation is named **[measured]**.

### 2.2 Too little: SW-3741 **[measured]**

```
def spare (n: Nat): Bool := 10 < n
def drop (n: Nat): Option Nat := if spare n then None else Some n
def kept (x: Option Nat): Bool := match x with
  | Some n => not (spare n)
  | None => True

theorem keptAfter ∀ (n: Nat): kept (drop n) = True := match isSpare: spare n with
  | True => byComputing
  | False => byComputing
```

The `False` arm fails: "`(spare n).not` and `True` aren't equal". A hole
there shows the goal `kept (if False then None else Some n)`, "computes to
`(spare n).not`". When the `match` started, `spare n` occurred once in the
computed goal, in `drop`'s `if`: `kept` was stuck on that `if`, so the copy
inside `kept` wasn't there to find. Replacing the `if`'s test lets `kept`
compute, and the copy appears after the replacement was made. `rewrite
isSpare` in the arm proves it (the toy used `Eq.cong`). This is the
limitation Agda's manual states for `with`: "only occurrences of the term
that are visible at the time of the abstraction are generalised over"
**[cited, A1]**. It is not about which definitions are unfolded: everything
that could compute had.

### 2.3 Silent: SW-3639 **[measured]**

`rewrite c at found`, where `c` is the `match`'s own equation, already
gets a label and a note ("this `match` replaced `isBig n` with `False` …
`found` is already refined: use it as it is"); `replaced_by_match` fires
when the rule's left side *is* a scrutinee. It is silent when the left side
only *contains* it:

```
def isBig (n: Nat): Bool := 10 < n
def cost (big: Bool) (n: Nat): Nat := if big then n + n else n
theorem costIs ∀ (n: Nat): cost (isBig n) n = n + cost (isBig n) 0 := ?

theorem contains ∀ (n m: Nat) (h: cost (isBig n) n = m): m = m := match c: isBig n with
  | True => (let g := rewrite costIs n at h; byComputing)
  | False => byComputing
```

"`rewrite` found no `cost (isBig n) n` in the type of `h`", with `h` shown
as `cost True n = m` and no mention of the `match`. The rule was written in
the arm, so it still says `isBig n`; `h` was refined. Same asymmetry as
2.1.

### 2.4 Implicits read off a refined goal: SW-3650, first item **[measured]**

```
type Mark = { rest: List Nat }
def Spec (measure: Nat → Nat) (v: Nat): Prop := measure v = 0
def ReadsAt (start: Mark) (v: Nat) (spec: Nat → Prop): Prop :=
  ∀ (k: Nat) => start.rest.length ≤ k → spec v
def ReadsFlat (start: Mark) (v: Nat) (spec: Nat → Prop): Prop :=
  ∀ (k: Nat) => 0 ≤ k → spec v
def pickFirst (x: Option Nat): Nat := match x with
  | None => 0
  | Some n => n - n
def twice (n: Nat): Nat := n + n

theorem done ∀ [measure: Nat → Nat] [x: Nat] (start: Mark) (same: measure x = 0):
    ReadsAt start x (Spec measure) := k short => same
theorem doneFlat ∀ [measure: Nat → Nat] [x: Nat] (start: Mark) (same: measure x = 0):
    ReadsFlat start x (Spec measure) := k short => same

theorem outside ∀ (start: Mark): ReadsAt start 0 (Spec twice) := done start byComputing

theorem hidden ∀ (start: Mark): ReadsAt start (pickFirst start.rest.head) (Spec twice) :=
  match e: start.rest with
    | [] => done start byComputing
    | [n, ..later] => ?

theorem flat ∀ (start: Mark): ReadsFlat start (pickFirst start.rest.head) (Spec twice) :=
  match e: start.rest with
    | [] => doneFlat start byComputing
    | [n, ..later] => ?
```

`outside` and `flat` check. `hidden`'s `[]` arm fails with "`_measure _x`
and `0` aren't equal" on `byComputing`; with `[measure := twice] [x := 0]`
it checks. The only difference between `hidden` and `flat` is that
`ReadsAt`'s definition holds a copy of `start.rest`. In the arm the goal is
`∀ k => [].length ≤ k → Spec twice …`; the lemma, written in the arm, has
the type `∀ k => start.rest.length ≤ k → Spec ?measure ?x`. The comparison
fails at `start.rest.length` against `[].length`, before it reaches `Spec
?measure ?x`, so the implicits stay unknown **[inferred from the pair of
results]**. The error then lands on the first argument that needed them,
which is the "headline blames the wrong thing" of the fourth item: nothing
says that the cause is `start.rest` against `[]`.

The copy of `start.rest` inside the definition is also why the arm's goal
is shown unfolded (`∀ (k: Nat) => …` rather than `ReadsAt start …`): the
as-written result didn't replace everything the computed search would, so
the computed form was used **[checked: the rule; measured: the goal
shown]**. Toy++'s `Parse.ReadsAt` has exactly this shape.

### 2.5 `readsInPeek` can't find `k`: SW-3650, second item **[measured]**

```
def Holds (v: Nat) (spec: Nat → Prop): Prop := spec v
def small (n: Nat): Prop := n ≤ 5
theorem pass ∀ (spec: Nat → Prop) (v: Nat) (h: Holds v spec): Holds v spec := h

theorem a ∀ (g: Holds 3 small): Holds 3 small := pass _ _ g
```

"expected `_spec _v`, but this has type `Holds 3 small`". There is no
`match` here at all. Types are compared as they compute, and `Holds`, a
non-recursive definition, has already unfolded: the parameter's type is
`?spec ?v` and the argument's is `3 ≤ 5`. An unknown function applied to
something that isn't a variable can't be solved by the unifier's ordinary
rule, though the written forms, `Holds ?v ?spec` and `Holds 3 small`,
match argument by argument. With `Parse.readsInPeek`, `k (Parse.peek())`
against a body where `peek()` is inside a `let … := match peek() with` is
harder still: no written form has `k` applied, and `k` has to be made by
abstracting `peek()` out of the body. Giving `k` explicitly is the
workaround. This is a limit of solving unknowns, not of refinement.

### 2.6 Implicits solved wrongly from an equation: SW-3650, third item **[measured]**

```
def kept (layout: Nat) (token: List Nat): List Nat := match token with
  | [] => [layout]
  | [n, ..rest] => [n, ..kept layout rest]
def optionKept (found: Option (List Nat)): List Nat := match found with
  | None => []
  | Some token => kept 0 token

type Reads (a: Type) (x: a) (before: List Nat → List Nat) (measure: a → List Nat) = | Read

def ontoDone [measure: a → List Nat] [before: List Nat → List Nat] [x: a]
    (same: measure x = before []): Reads a x before measure := Read

def use (token: List Nat): Reads (Option (List Nat)) (Some token) (past => kept 0 token ++ past) optionKept :=
  ontoDone (List.appendNil (kept 0 token)).flipped

def useLater (token: List Nat): Reads (Option (List Nat)) (Some token) (past => kept 0 token ++ past) optionKept :=
  let made := ontoDone (List.appendNil (kept 0 token)).flipped
  made
```

`use` checks: the expected type gives `measure`, `before` and `x`.
`useLater` fails on the last line: "`token` here, but `Some token` is
expected", found `Reads … token (List.append (kept 0 token)) (kept 0)`.
With no expected type, `?measure ?x = ?before []` was compared with `kept
0 token = kept 0 token ++ []` and solved by splitting each side at its last
argument: `measure := kept 0`, `x := token`. That is one of several
solutions and the wrong one. The error comes where the result is used, and
its headline names the first place the two types differ, not that
`measure` was a guess. In Toy++ the expected type was there, but it was an
arm's refined goal, which the conclusion couldn't be compared with (2.4),
so the equation decided **[inferred]**.

### 2.7 A `let`-bound second scrutinee: SW-3468 **[measured]**

```
def isBig (n: Nat): Bool := 10 < n
theorem bigOrSmall ∀ (n: Nat): isBig n = True ∨ isBig n = False := ?

theorem param ∀ (n: Nat) (known: isBig n = True ∨ isBig n = False): 0 = 0 :=
  match waiting: isBig n, known with
    | True, _ => byComputing
    | False, _ => byComputing

theorem letBound ∀ (n: Nat): 0 = 0 :=
  let known := bigOrSmall n
  match waiting: isBig n, known with
    | True, _ => byComputing
    | False, _ => byComputing
```

`param` checks; `letBound` is `E-MATCH-MOTIVE`, "the type of one scrutinee
of this `match` mentions another". In `lifted`, a scrutinee is a variable
only if its value is itself (`is_var`); a `let`'s name has its bound value,
so it is treated as an expression, and two expression scrutinees can't
depend on each other **[checked]**. Yet the same `let`, when it is *not* a
scrutinee, is copied as an opaque hypothesis exactly like a parameter (the
"Hypotheses" paragraph of docs/syntax.md). The two halves of the rule
disagree about what a `let` is.

## 3. What other systems do

Sources are listed in §9. goal-as-written.md §3 and
match-generalisation-evaluation.md cover how each *finds* occurrences;
this section is about what gets refined and how visible it is.

| | Goal | Hypotheses | Looks through definitions | Equation | Terms written in the branch |
|---|---|---|---|---|---|
| **Lean 4 `match`** | occurrences of the discriminant in the expected type, found as written by head symbol **[cited, L1, L3]** | "occurrences of the discriminants in the types of variables in the context are generalized and substituted by default"; off with `(generalizing := false)` **[cited, L1]**. The source limits it: "Only discriminants that are free variables are considered during specialization", and `let`s are skipped **[cited, L2]** | only as far as the head-keyed comparison unfolds a candidate **[cited, L3]** | `match h : e with` gives `h : e = p` **[cited, L1]** | not refined; `h ▸ t`, `rw [h] at …`, `simp [h]` by hand **[memory]** |
| **Lean 4 `split`** | finds an `if` or `match` in the goal or a hypothesis and splits on its discriminant; error "Could not split an `if` or `match` expression in the goal" **[cited, L4]** | `split at h`; `split at *` skips "non-propositional hypotheses or those on which other hypotheses depend" **[cited, L4]** | no: `unfold`/`simp only [f]` first **[memory]** | hypotheses named automatically **[memory]** | n/a |
| **Agda `with`** | "the goal type and the type of the original arguments are generalised over the value of the scrutinee" **[cited, A1]** | all arguments of the clause, i.e. everything in scope **[cited, A1]** | yes: it "needs to normalise the scrutinee and the goal and argument types" **[cited, A1]** | lost by default ("you lose the connection between `t` and the new argument"); kept with `with t in eq` **[cited, A1]** | not refined; `rewrite eq` or `subst` by hand **[memory]** |
| **Rocq `destruct`** | "In each new subgoal, the tactic replaces the selected subterm with the associated constructor" **[cited, R1]**; for a term that isn't a variable, only the goal unless `in` names hypotheses **[memory]** | by an `occurrences` clause: "Selects specific subterms of the goal and/or hypotheses" **[cited, R1]** | no: occurrences are matched as written **[memory]** | `eqn:` "Generates a new hypothesis in each new subgoal that is an equality between the term being case-analyzed and the associated constructor" **[cited, R1]** | not refined. The idiom is spelled out for `destauto`: "If `t` is not a variable, the tactic does `case_eq t;intros ... heq;rewrite heq in *|-`" **[cited, R1]** |
| **Rocq `match … return`**, `dependent destruction` | the user writes the motive (`as … in … return`); `dependent destruction` generalises indices with equations and needs an axiom-backed library **[cited, R1, for the library; rest memory]** | only what the written motive abstracts ("the convoy pattern") **[memory]** | no | by hand | no |
| **Idris 2 `with`** | "the result can affect the forms of other arguments" **[cited, I1]**; the with-value is normalised and replaced in the goal **[cited in match-generalisation-evaluation.md]** | the clause's arguments **[memory]** | by normalising **[as above]** | `with (e) proof prf` **[memory; not on the pages fetched]** | not refined |

What to take from this:

- **Nobody refines terms written in the branch.** Every system leaves the
  user to rewrite with the equation. Rocq's `destauto` documents the
  idiom: split, name the equation, rewrite with it everywhere. That idiom
  is what Stitchwort's transport automates for one situation; the proposal
  is to automate it for all of them.
- **Everyone has 2.2** (a copy uncovered by the refinement). Agda's manual
  says so in words. In Lean and Rocq the answer is `simp [h]` or `rewrite
  h` after the split.
- **Who refines hypotheses** divides the systems. Agda and Idris refine
  everything in scope, by normalising, and are the ones with the "it
  changed and I can't see why" complaint and with ill-typed abstractions
  ("generalisation does not always produce well-typed results" **[cited,
  A1]**). Lean refines hypotheses only for a variable, and Rocq only where
  asked: predictable, and more writing.
- **Visibility.** None marks a refined hypothesis in the goal view. Lean's
  `generalizing` and Rocq's `in` are the only controls. Agda keeps the
  equation only on request, which its manual treats as the idiom to know.

Stitchwort already sits with Agda on reach and with Lean on the equation.
The friction is at the edges of that mix, so the rule below finishes it
instead of retreating to Lean's.

## 4. The rule

> **In an arm of `match e with | p => …`, `e` is `p`.** Everything the arm
> sees is shown with `p`; everything the arm writes may say either; the
> checker never reports a difference that is only `e` against `p`.

In detail, answering the brief's four parts.

**R1. Which hypotheses are refined: all that mention `e` once computed, as
today.** Parameters, lambda variables and `let`s alike, and those that
depend on them. This is what Toy++ called friction 45's "pleasant side":
`found: pick n = Some m` simply is `Some n = Some m`. A `let`'s name is a
hypothesis for this purpose everywhere, including when it is itself a
scrutinee (fixes 2.7): it is copied as the opaque hypothesis it would be
anyway, then matched as a variable.

**R2. Terms written in the arm are refined, by rewriting along the arm's
equation at every comparison.** The equation exists for every expression
`match`, named or not; a name only lets the user refer to it. An unnamed
`match` gets a hidden one when an arm first needs it, as decided
propositions already do. The comparisons:

- *an argument against a parameter* (today's transport, now also unnamed):
  fixes 2.1;
- *a lemma's conclusion against the goal, with implicits still unknown*:
  when the comparison meets `e` against `p` it notes the pair and carries
  on, so the rest is compared and the implicits are solved; the noted
  pairs are then discharged by one rewrite along the equation: fixes 2.4;
- *a `rewrite` rule's left side* that contains `e`, when nothing is found:
  the rule is rewritten along the equation and tried again: fixes 2.3;
- *`byComputing`, `cases` and other closers* whose goal still contains `e`
  once computed: R3.

Proofs only, as today. A data term whose type differs by `e` against `p`
stays an error, with the note of R4.

**R3. Definitions are looked through, and again after the refinement
computes.** The search over computed types stays, so a copy inside a
definition that has unfolded is refined. Additionally, if replacing `e`
lets the goal or a hypothesis compute further and the result contains `e`,
it is rewritten along the equation, and so on until none is left (two
rounds in every case seen; stop with an error naming the `match` after
eight). Fixes 2.2. What is never looked into: a call that hasn't computed
because its arguments are unknown, and occurrences under a binder that use
its variable. Those copies are still `e`, and R2 covers any place where
that matters.

**R4. How a refinement shows.**

- *In the goal view* (`?`, the editor): a refined hypothesis is marked,
  and one line says what the arm knows, including for an unnamed `match`:

  ```
  good: 0 < token.text        (was `Good token`; refined by the `match` on line 17)
  here: token.kind is Name
  ```

  This replaces today's "1 earlier hypothesis hidden by a later one of the
  same name … isn't listed".
- *In errors*: one shared check, used by `E-TYPE-MISMATCH`,
  `E-REWRITE-NOTHING` and `E-REFL` in an arm. If either side contains an
  enclosing `match`'s `e` or `p`, or the term is a refined hypothesis, the
  error labels the `match` ("this `match` replaced `e` with `p`") and that
  cause leads the message. Today's two notes (`replaced_by_match`, and the
  mismatch notes in 2.1) fire only when the left side *is* `e` or the
  mismatch has one exact shape.
- *`W-MATCH-NOT-FOUND`* stays as it is.

**R5. Implicits after a refinement** are solved as outside the `match`:
R2's second bullet is the whole of it. Two further rules about unknowns
are independent of `match` and are in §6.

### What the rule does to each case

| Case | Today | Under the rule |
|---|---|---|
| SW-3466 (2.1) | 26 mismatches until the equation is named or a `let` added | checks as written; no name needed (R2) |
| SW-3741 (2.2) | `Eq.cong (kept => not kept) isSpare` | `byComputing` (R3) |
| SW-3639 (2.3) | `E-REWRITE-NOTHING`, no mention of the `match` | the `rewrite` works (R2); where it can't, the error names the `match` (R4) |
| SW-3650 item 1 (2.4) | implicits written out, or a lemma with none: about 10 extra lemmas and 50 `(rewrite e then fine)` in T1c | implicits read off; `fine` passed as it is (R2) |
| SW-3650 item 4 (2.4) | the error is on an argument that needed the implicit | the `e`-against-`p` cause leads (R4) |
| SW-3650 item 2 (2.5) | `k` given by hand | own fix, §6.1 |
| SW-3650 item 3 (2.6) | wrong guess, error lines away | mostly gone, since the goal now decides first (R2); own fix for the rest, §6.2 |
| SW-3468 (2.7) | `E-MATCH-MOTIVE`; helper lemma | checks (R1) |

All **[inferred]** from the repros and the code read; none was built.

## 5. The alternative considered: Lean's rule

Refine only the goal, as written; leave hypotheses and anything inside a
definition to an explicit `rewrite h at …`. It is the most predictable
rule: nothing changes that the user can't see. It would remove 2.1 and 2.3
by removing the refinement they trip over, and leave 2.2 and 2.4 as they
are.

Against it: every proof that uses a hypothesis about `e` in an arm gains a
`rewrite h at …` line. That is most arms: T1c's 50 `(rewrite e then fine)`
are exactly this cost, paid in the other direction. It gives up "the
hypothesis simply is the refined fact", which the notes single out as
pleasant, and it would be Lean's known friction, for which Lean users reach
for `split` and `simp [h] at *`, tools Stitchwort doesn't have. Judged by
the end state, a rule where the user never writes the bookkeeping beats a
rule where the bookkeeping is predictable.

## 6. SW-3650's other two items

### 6.1 `k` in `readsInPeek`: an unknown function applied to a term

*Diagnosis* (2.5): two separate things.

1. Types are compared computed, and a non-recursive definition (`Holds`,
   and Toy++'s `Onto`, `Inner`) has unfolded before the comparison, so an
   unknown that was an argument of it is now an unknown function applied
   to something. *Fix:* when a parameter's type and an argument's type are
   both calls of the same definition as written, compare their arguments
   first, and fall back to the computed forms if that fails. The unifier
   already does this for recursive definitions and dictionaries
   (`unify.rs`, the `is_folded` paths, SW-1506) **[checked]**; this
   extends it to the written form of a stated type.
2. `?k (peek())` against a body in which `peek()` occurs but `k` doesn't.
   *Fix:* as a last resort, after the call's other arguments and its
   expected type have been tried, solve `?k` by abstracting the argument
   out of the other side, with the search `rewrite` uses for its motive.
   If the argument doesn't occur, refuse (a constant function is never
   what was meant) and say "`k` can't be worked out: `Parse.peek()` isn't
   in …; give it with `(seen => …)`". Lean does this only for lemmas marked
   `elab_as_elim`, and Rocq's `apply` does it heuristically **[memory]**.
   Being a last resort, it changes no solution found today **[inferred]**.

### 6.2 Implicits guessed from an equation

*Diagnosis* (2.6): the unifier solves `?measure ?x` against `kept 0 token`
by splitting at the last argument, at once, and commits. It is a guess: it
picks one of several solutions.

*Fix:* (a) hold such a guess back until the call's other arguments and its
expected type have been compared, and make it only if the unknowns are
still open then; (b) remember that an unknown was guessed, and where; a
mismatch that involves it says so first: "`measure` was guessed as `kept 0`
from this argument; give it with `[measure := …]`". Agda never guesses
here and leaves the constraint open; Lean guesses as a fallback after
postponing **[memory]**. (b) is cheap and worth having on its own.

The headline of the fourth item ("`Tok` here, but `Parse.Located Token`
expected") is the same message as 2.6's "`token` here, but `Some token` is
expected": the first place two types differ. The order should be: an
unknown not worked out, then `e` against `p` (R4), then a guessed unknown,
then the first difference.

## 7. Cost

### Pieces **[estimated, in agent time, from the code read; none built]**

| | Piece | Model | Time | Acts on proofs that check today? |
|---|---|---|---|---|
| S1 | Hidden equation for an unnamed `match`, made when an arm needs it (R2, arguments). The mechanism is `%tested`'s retry | Opus | 30 to 45 min | no: tried only after a failure |
| S2 | Rewrite along the equation when a closer's or comparison's computed goal still has `e` (R3) | Opus | 45 to 60 min | no |
| S3 | Comparison carries on past `e` against `p`; `rewrite` rules retried (R2, conclusions and rules) | Opus, with an Opus review: it makes kernel terms | 60 to 90 min | no: only where the comparison fails today |
| S4 | A `let`'s name as a scrutinee is a hypothesis (R1) | Opus | 20 to 30 min | no: `E-MATCH-MOTIVE` today |
| S5 | Messages: the shared refinement check, the goal view's marks, the headline order, the "guessed" note (R4, §6.2 b) | Sonnet or DeepSeek, from a spec | 40 to 60 min | messages and snapshots only |
| S6 | Unknowns: written forms first; abstraction as a last resort; guesses held back (§6.1, §6.2 a) | Opus | 60 to 90 min | (a) of 6.2 can change which solution is found; the rest no |
| S7 | Optional, question 2: an arm's goal keeps its written form | Opus, after a measurement | 60 min and a sweep | yes |

About 4 to 5 hours without S7. Each piece also updates docs/syntax.md's
`match` section and the guide, and S1 to S4 each carry the repro of §2 as
an accept example.

### Churn

S1 to S4 and most of S6 act only where elaboration fails today, so no
term, hash or snapshot of a checking proof changes **[inferred: each is a
fallback after a failure, the pattern `generalised_now` already uses for
`%tested`]**. S5 changes message snapshots. Afterwards the toy's
workarounds can be deleted (the 50 `(rewrite e then fine)`, the lemmas with
every argument explicit, `Eq.cong` in `dropReaches`, the helper lemmas of
`writeStart`): a DeepSeek-sized sweep, not needed for correctness. S7 is
the only piece with real churn (below).

### Soundness

No kernel change. Every refinement is either the motive of a generated
helper, whose type and uses the kernel checks as today, or a rewrite of a
proof along `h: e = p`, an ordinary `Eq` elimination the kernel checks.
"Treating `e` and `p` as the same" happens only in the elaborator; what it
produces contains the rewrite explicitly. A wrong decision there can make a
proof fail to check, never make a false one check **[inferred, by
construction]**. S3 generates kernel terms in a new place, so it gets the
review D2364 asks for and the soundness examples.

Two things to watch, neither a soundness matter: R3's rounds must be
bounded (a cap and an error), and S3 must not solve an unknown *to* `e` or
`p` on the strength of the equation alone (it only skips the pair), or
implicits would depend on which arm they are in.

### S1/S2 measured (SW-3758, 17 Nov 2026)

Built on Opus in about 35 minutes of agent time. **[measured]** unless marked.

- **Size.** `crates/elab`: +325 −14 lines over three files (`check.rs`
  +224, `matching.rs` +105 −14, `state/decl.rs` +10), 55 of the added
  lines comments.
- **One mechanism or several.** Two pieces, each used once.
  *S1* is one wrapper around a generalised `match`'s arms
  (`matching::with_hidden_equation`): if the arms fail and an arm noted
  that an unnamed scrutinee was on one side of a failed proof comparison
  (`Ctx::note_equation_wanted`, called from the existing transport in
  `compare` and from S2), the arms are checked again with the scrutinee
  named `%tested`, the name the decision retry already used. Everything
  that reads a named equation then works unchanged; nothing new is done at
  any comparison site. If the second check fails, the first is run again
  so the error and goals are exactly today's (three checks of the arms, on
  that failure path only). *S2* is one function, `Ctx::refined_again`
  (rewrite the goal along the innermost equation whose scrutinee it
  contains, try the closer, carry the proof back with the existing
  `transport_along`; at most 8 rounds, then `E-MATCH-ROUNDS`), called from
  one site, `byComputing`. Other closers (`cases`, `arithmetic`) would each
  be one more call of the same function; not done.
- **Hashes.** `hash_stability::prelude` unchanged, and
  `hash_stability::examples` with `EXAMPLES=match` changed no existing
  snapshot (only the new accept examples' were added).
- **Steps.** `import_cost` before → after: List 1,210,272 → 1,210,272;
  Nat 14,586,205 → 14,586,205; Int 20,460,978 → 20,462,225 (+0.006%);
  Text 12,873,979 → 12,873,979; Map 35,034,451 → 35,035,698 (+0.004%). The
  +1,247 in Int and Map is the read-back that `note_equation_wanted` and
  `refined_again` do on a std proof's failed comparison inside an arm
  **[inferred]**. AoC: no step counter on the command line, so wall time:
  `check --no-cache Aoc.Year2024.Day24` (the 2024 day with the most named
  `match`es), user time 7.21 s
  and 7.91 s against main's binary's 7.18 s and 7.92 s, flat.
- **Cap and internal errors.** No internal error seen. The cap was hit
  only by the example built to hit it
  (`examples/reject/match-refine-rounds.sw`: 20 nested copies); its
  3-round twin checks.
- **Five reject examples now check**, all of them cases the rule says
  should: `match-lemma-unnamed-equation`, `match-written-argument-not-refined`
  (S1), `match-equation-not-rfl`, `match-refines-goal-once`,
  `match-scrutinee-from-lemma-under-lambda` (S2). They were moved to
  `examples/accept/` under new names. Reject examples whose names don't
  contain `match` weren't run; the verifier's examples run covers them.

## 8. Questions for Matt

The orchestrator numbers these.

**Question 1: adopt "in an arm, the scrutinee is the pattern, for
everything"?** *The problem:* refinement reaches hypotheses but not what
the arm writes, so proofs need a named equation, a `let` before the
`match`, `rewrite e then …`, or lemmas with every argument explicit.
*The change:* R1 to R5 (pieces S1 to S6): the checker carries proofs along
the equation wherever the only difference is `e` against `p`, and says so
in goals and errors. *What it should do:* remove all five tickets'
friction; about 4 to 5 hours of agent time **[estimated]**; no churn in
proofs that check today **[inferred]**. The alternative is Lean's rule
(§5): refine only the goal and write the rewrites by hand.
**[rec: yes, adopt it]**

**Question 2: should an arm's goal keep its written form, measured first?**
*The problem:* when a definition in the goal hides a copy of `e`, the arm's
goal is shown and compared unfolded (`∀ (k: Nat) => [].length ≤ k → …`
instead of `ReadsAt start …`), which is harder to read. *The change:* use
the as-written result even when a hidden copy stays unrefined (option F of
goal-as-written.md, then set aside because the hidden copy would be left
behind; R2 and R3 now cover it). *What it should do:* arms' goals read like
the statement. It changes generated helper types wherever the two results
differ, so hashes move and some proofs that lean on the unfolded goal may
need a line; how many is unknown. `STITCHWORT_MATCH_METRICS` already
counts the outcomes, so one Overmind run over std, `aoc/` and the toy would
say. **[rec: yes to the measurement, once S1 to S3 are in; decide S7 on
its numbers]**

## 9. Sources

Fetched 17 Nov 2026 unless marked.

- **L1** Lean 4 reference, "Pattern Matching" (§§ Types, Pattern Equality
  Proofs, Explicit Motives, Generalization):
  <https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/>.
- **L2** `src/Lean/Elab/Match.lean` (`generalize`'s docstring and remarks;
  `let gen := if let some g := generalizing? then g else true`;
  `getFVarsToGeneralize discrExprs (ignoreLetDecls := true)`; `withEqs`):
  <https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Match.lean>;
  and `src/Lean/Meta/GeneralizeVars.lean` (`getFVarSetToGeneralize`:
  "Collect forward dependencies that are not in the forbidden set, and
  depend on some variable in `targets`").
- **L3** `kabstract`, as cited in match-generalisation-evaluation.md and
  goal-as-written.md [L2, L8] (not fetched again).
- **L4** `src/Lean/Elab/Tactic/Split.lean` (error texts; the `split at *`
  note):
  <https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Split.lean>.
- **A1** Agda manual, "With-Abstraction" (§§ Generalisation,
  With-abstraction equality, Rewrite, Ill-typed with-abstractions,
  Performance considerations):
  <https://agda.readthedocs.io/en/latest/language/with-abstraction.html>.
- **R1** Rocq 9.0 reference manual, "Reasoning with inductive types"
  (`destruct`, `eqn:`, `occurrences`, `case_eq`, `destauto`, `dependent
  destruction`):
  <https://rocq-prover.org/doc/V9.0.0/refman/proofs/writing-proofs/reasoning-inductives.html>.
  The page doesn't say what `destruct` of a non-variable term does to
  hypotheses; that row is from memory.
- **I1** Idris 2 tutorial, "Views and the 'with' rule":
  <https://idris2.readthedocs.io/en/latest/tutorial/views.html>. `with …
  proof` is not on it nor on the "updates" page; from memory.

## 10. What this note didn't do

- Nothing was built, and no repro was run on the toy itself: the "fixes"
  column of §4 is inferred from the small files.
- SW-3466's original proof no longer exists in the toy (it was rewritten),
  so 2.1 reproduces its description, not its 26 errors.
- 2.5's second half (`peek()` inside a `let … := match`) wasn't reproduced
  with `Parse`'s abilities, only its pure analogue.
- The as-written and computed motives weren't counted anywhere (question
  2's measurement).
- The language guide (`docs/guide/`) wasn't read for its `match` wording;
  docs/syntax.md was.
