# SW-3359 (recursion through `map`): soundness review of the three termination rules

**Reviewed:** [docs/proposals/recursion-through-map.md](../proposals/recursion-through-map.md)
draft 1 (15 November 2026), against `crates/core/src/termination.rs`, `crates/core/src/value.rs`
(the unfolding policy) and `docs/core.md` at `8021f2664`. Paper review by Fable, 15 November 2026;
nothing built. **[run]** means probed with the release CLI on scratch files; **[argued]** means
reasoned from the source and spec, not runnable today because today's checker refuses the program;
**[fetched]** means read from the public page today; **[memory]** means recalled, not rechecked.

## 0. Verdicts

| Rule | Closed programs (can it loop or prove `False`?) | Checking (can the kernel's own evaluation run for ever?) | Verdict |
|---|---|---|---|
| 1. A field reached with a dot is a part (§2.1) | Sound | Sound for records with eta; a hazard for recursive records (§2.3 below) | **Sound with restrictions**, but the mechanism as written doesn't fire: it must be restated (finding F1) |
| 2. Callback signatures (§2.2) | Sound once four gaps in the wording are closed (R1-R4); one of them is a real loop as worded (F3) | **Not sound as stated**: it admits recursion with no `case` of its own, which the unfolding policy relies on (F2) | **Sound with restrictions**; one is a design decision the proposal doesn't mention |
| 3. One-field wrapper around a strict part (§3) | Sound as stated | Sound as stated | **Sound as stated**, provided "strictly inside" stays "reached through matched fields" (R7) |

I found no program that proves `False` under the rules as written with the obvious reading. I
found one closed program that loops under a plausible reading of "weakest seen" (F3), and a family
of accepted programs on which the kernel's evaluator no longer stops on open terms (F2), which
breaks a stated kernel invariant ("this keeps comparison from unfolding recursive definitions
forever", `value.rs:5`; `docs/core.md` "Unfolding policy": "That makes conversion terminate").
That is not an inconsistency: the budget turns it into `E-RESOURCE`. It is a kernel property the
proposal changes without saying so.

**Recommendations (§7 below):** D3612 (text's rest) is safe to recommend with one sentence
tightened. D3611 (through `map`) is not safe to recommend as worded: it should come back as draft
2 with F1-F3 answered, and then it is a reasonable yes.

## 1. What I checked first

- Field access is not `Term::Proj` in the kernel's terms. `docs/core.md` (Terms table): "The
  elaborator writes field access as a call of the record's accessor; a `Proj` comes from reading
  back a projection stuck on an unknown". `crates/elab/src/records.rs:6`: "a projection per field,
  `Person.name : Person -> Text`, generated as an ordinary definition". And `Proj(D, i, t)` is
  only well formed when `D` has record eta, which needs `D` alone in its group and not recursive
  (`docs/core.md` "Record eta", condition 3).
- The unfolding policy (`value.rs` `case_tree`, `stuck_tree`): a definition with all its
  arguments runs its case tree; it stays folded only if a `case` in the tree is stuck. A tree with
  no `case` always unfolds. A `case` on an unknown value of a type with eta is not stuck: it takes
  its branch with the fields as projections (eta rule 2).
- Today every accepted recursive cycle has a `case` that is stuck on an unknown argument: `<`
  comes only from a variable bound by a `case` on a parameter or its parts, and a type with eta
  can't be recursive, so getting from a value back to a value of its own type crosses a `case` on
  a type without eta. **[argued]** This is the invariant the unfolding policy rests on, though
  neither `termination.rs` nor `docs/core.md` states it as one.
- Probes of today's checker **[run]**: `sizeKids r.kids` on a recursive record, `t.forChildren
  (c => size c)`, `depthTree e.value` on a record with eta, and `drop1 (MkWrap cs)` are all
  refused, as the proposal says. (`| "ab" ++ rest` doesn't parse in the release binary at
  `8021f2664`; the proposal's text-prefix probes were on the SW-3288 lane's build.)

## 2. Rule 1: a field reached with a dot

### 2.1 Closed programs: sound

If `x`'s value is the parameter's or a part of it, the value of `x.f` is a field of `x`'s value,
so a proper part. This is the record pattern by another route, as the proposal says. A proof field
or an erased field is still a field. No objection.

### 2.2 F1: the rule as written doesn't apply to the running example

The proposal says: "In `relate`, a `Term::Proj` whose target relates gives `Lt`. … About 20
lines." But:

1. `item.value` reaches the kernel as `Item.value item`, a call of a generated definition, not a
   `Term::Proj` (§1 above). `relate` sees an application headed by a `Def` and gives nothing.
2. `Item` is one of five types defined together, so it has no eta, so no `Proj` on it is even
   well formed.

So the rule needs one of: (a) the kernel recognises an accessor by the shape of its checked body
(after its parameters, one `case` on the last parameter, one branch, whose body is a field
variable) and treats a saturated call of it as a part of that argument; or (b) the elaborator
emits `Proj` and `Proj` is allowed on types without eta, which changes `infer_proj` and the eta
section. (a) is a small "this definition returns a part of its argument" summary, the kind §6 of
the proposal defers; it is sound **[argued]** (in a closed run the call returns that field), and
it must be read from the body, never from a flag the elaborator sets. Either is more than 20
lines and belongs in the kernel spec. The estimate and the description in D3611 should change.

### 2.3 Restriction for recursive records (R6)

With (a), a recursion can descend through an accessor with no `case` at all:

```
type R = { child: R, n: Nat }          -- no closed values, but variables of type R exist
def f (x: R): Nat := f x.child         -- accepted under rule 1: x.child < x
theorem t (x: R): f x = 0 := …         -- evaluating `f x`: f (R.child x), f (R.child (R.child x)), …
```

`f` has no `case`, so `f x` unfolds for ever on an unknown `x` (the accessor's `case` is stuck,
`f`'s tree is not). Harmless for closed runs (`R` is empty), an `E-RESOURCE` at every open use.
A function field reached by a dot (`x.rest y`, §6 "add with 2.1 if cheap") has the same shape
and must also read the field's *declared* type, as `is_recursive_fn` does (Agda #6654, already
cited in `docs/core.md`). Covered by the guard rule in §3.2.

## 3. Rule 2: callback signatures

### 3.1 Closed programs: sound, with the wording closed (R1-R4)

The claim ("every call of the callback gets, at a marked index, a part of the carrier") holds by
induction on `G`'s run, and the caller's argument goes through as the proposal says: an infinite
chain of nested calls would be an infinite descent, and `G` itself makes finitely many callback
calls because it was checked. I tried, and could not break it with: a callback that escapes in a
closure `G` returns (it is still only applied to parts); effects (the bind's continuation is a
lambda, the callback is still applied); `foldLeft`'s accumulator (rule 2's "argument `k` relates
to `k`" correctly kills the pair (callback, accumulator)); swapped carriers; higher-rank
callbacks (the caller can't recurse on a value of an abstract type without `J`, which gives no
relation); proofs as carriers (`E-PROP-ELIM` already stops recursion on a proof into data);
a second parameter made equal to the callback by an index equation (the value in that slot was
itself walked at the call site, where a member can't hide: a pending member is opaque and a
bare occurrence is refused); dictionaries (`Functor.map` is not headed by `G`, so no signature).

The wording leaves four gaps. Each needs a sentence in the rule and a must-reject test.

**F3 / R1: an index is only as good as every occurrence that reaches it.** "Recorded as the
weakest seen over all occurrences" doesn't say what an occurrence with fewer arguments means. If
it means "no information", this is accepted and loops:

```
def apply (g: List Nat → Nat) (x: List Nat): Nat := g x

def G: (xs: List Nat) → (big: List Nat) → (f: List Nat → List Nat → Nat) → Nat
  | [], big, f => 0
  | [x, ..rest], big, f => f rest rest + apply (f rest) big

def loop (xs: List Nat): Nat := G xs [0, ..xs] (a b => loop b)
-- loop [1] → apply (f []) [0, 1] → loop [0, 1] → loop [0, 0, 1] → …
```

Both occurrences of `f` are "applied" (rule 1 of the signature). Index 1 is `<` in `f rest rest`
and absent in `f rest`, whose result `apply` then gives `big`. **Required:** an index not
supplied at some occurrence is unknown. (Equivalently: only indices below the shortest
application count.)

**R2: "any other occurrence" means every term form.** In a type, under `J`, as a `let`'s value,
as a `Proj`'s target, as an argument of a constructor, of a quotient form or of any call that
isn't rule 2 or 3: no signature. In particular the callback passed *as the variable itself* to an
earlier signed `H` (`map (map xs f) f`) is "passed anywhere else", not rule 3.

**R3: lifted matches are cross-calls.** A `G` written with an inner `match` or `if` that
contains the recursive call is a group of two (`G`, `G.%match1`), and the helper takes the
callback as a capture. "v1 signs only a definition alone in its group" then refuses it, which is
safe (and means `List.any`, `List.all` may get no signature, contrary to the proposal's
[inferred] list: check before stage 4). The hazard is the half-way implementation: walking `G`
with its helper inlined, collecting applications of `f`, but checking rule 2 only on calls
written in `G`'s own body. Then this passes and loops:

```
def G: (fuel: Nat) → (xs: List Nat) → (f: List Nat → Nat) → Nat
  | Zero, xs, f => 0
  | Succ k, xs, f =>
    match xs
    | [] => 0
    | [x, ..rest] => f rest + G k [0, 0, ..xs] f      -- carrier grows; G still terminates on fuel

def loop (xs: List Nat): Nat := G 5 xs (r => loop r)
-- loop [1] → G 4 [0, 0, 1] → f [0, 1] → loop [0, 1] → f [1] → loop [1] → …
```

This is exactly the shape of the bug in Rocq's version of this feature (§6): the check looked at
self-calls and missed calls through another body. **Required:** either no signature for any
definition whose group has more than one member, or the derivation treats every member of the
group, inlined or not, by rules 1-3, with rule 2 applied to every call of every member.

**R4: only bodies the termination check accepted, and that the kernel actually runs.** No
signature for a definition with a native (`builtins().native`), an axiom, a primitive
(`Effect.pfix`), or from a run body. A `decreasing` definition gets none anyway (its callback is
passed to `f.%go`).

Two smaller notes. The signature's marks must be read as *rank* once rule 3 exists (inside `G`,
`C u` is not a part of the carrier), which is fine since every use is rank-monotone; §2.2's "a
part of" should say so. And a `≤` entry is "at most", not "equal": today `param: Some(i)` means
equal (`termination.rs:33`); I found nothing that relies on equality beyond `rebuilt`, which
resolves to a matched variable, but the implementer should recheck each reader of `param`.

### 3.2 F2: recursion with no `case` of its own, and the unfolding policy

Under rule 2 the evidence of descent is established inside `G`. The caller no longer needs a
`case`:

```
type Tree = | Leaf | Node (left: Tree) (right: Tree)

def Tree.forChildren: (t: Tree) → (f: Tree → Nat) → Nat
  | Leaf, f => 0
  | Node l r, f => f l + f r

def size (t: Tree): Nat := 1 + t.forChildren (c => size c)     -- accepted: c < t
```

Closed runs stop. But `size t` for a variable `t` unfolds (no `case` in `size`) to `1 +
Tree.forChildren t (c => size c)`; `forChildren` is stuck; reading the value back goes under the
lambda, where `size c` on the fresh `c` unfolds again, and so on without end **[argued]**. The
same with std alone needs a callback that receives a value of the carrier's own type (a
"suffixes" or "smaller numbers" combinator: `def tails … | [x, ..rest], f => f rest + tails rest
f`, then `def loop (xs: List Nat): Nat := tails xs (r => loop r)`), or rule 1 on a recursive
record: `type Rose = { label: Nat, kids: List Rose }`, `def size (r: Rose): Nat := 1 +
r.kids.sumBy (k => size k)`, the natural next program after the toy formatter.

Where it bites: any read-back that writes the unfolding (a goal shown to the user, a term that
goes into a checked term), and any comparison the names don't settle (`size t` against a second
definition of the same shape recurses through the two lambdas for ever). Each ends in
`E-RESOURCE` after the whole budget, so a tactic that tries several lemmas pays that several
times. The toy formatter's own code is not affected: `Expr.layout` and `Statement.layout` start
with a `case` on a type without eta, so `item.value.layout` under the lambda is stuck.

Rocq doesn't have this problem because a `fix` only unfolds when its structural argument is a
constructor, whatever its body looks like. Stitchwort ties unfolding to the case tree, so the
checker must guarantee a stuck `case` on every cycle, or the evaluator must learn a new rule.
The oracle (§5) cannot see this: B's copy of `forChildren` has the `case`.

Two ways out; the proposal should pick one and argue it (this is an end-state decision, so
Matt's):

- **G1, checker side (my recommendation for v1).** Evidence from a signed lambda's variable, or
  from an accessor on a type without eta, counts for a call only if the member called has, at the
  root of its case tree, a `case` on the parameter that receives it, on a type without eta, and
  the argument is that variable or accessors of it (not a constructor around it). Otherwise the
  error says "match on `t` first". `size` becomes `| Leaf => 1 | t => 1 + t.forChildren …`. The
  toy formatter passes unchanged. It refuses some honest programs; it changes nothing in the
  evaluator. It needs its own short argument that every infinite unfolding would need infinitely
  many fresh lambda variables, each stuck at such a root.
- **G2, evaluator side.** Mark a member accepted through such evidence as folded
  (`Def::fold`, as a `decreasing` definition is: `docs/core.md` "Recursion on a measure" step 3),
  so it stays `size c` under a binder. Read-back then stops, but a comparison that unfolds both
  sides still doesn't, and the flag becomes part of what the kernel computes from a body. More
  programs pass; more to trust.

## 4. Rule 3: a one-field constructor around a strict part

**Sound as stated.** With `s = C v` matched, `u` reached from `v` through at least one matched
field (or a recursive function field applied), and `C` having exactly one field: rank(`C u`) =
rank(`u`) + 1 < rank(`v`) + 1 = rank(`s`) ≤ rank(`i`). Every existing rule is rank-monotone (a
field, a recursive function field applied: rank(`f a`) < sup + 1; a rebuilt value is equal), so
size-change over rank goes through. Rank exists for every closed value under the assumption the
check already makes (well-founded values; for nested types, assumption C1). Checked against:
`Succ` (it agrees with `rebuilt`); a type with other constructors beside `C` (irrelevant); an
indexed one-field constructor (`MkS (l: List Nat): S (length l)`, the index is another, unknown
argument); a wrapper whose field is a function (a function has no parts unless it is a declared
recursive function field, and then `Sup g` is `v n`, already smaller); `Text` literals (a
compact range is never related, and its tail is a `Cons` field as before); proofs (a recursive
proposition can't be matched into data). On open terms it is fine: the rule demands an enclosing
match that reaches `u` from `v`, and that match is stuck on an unknown `v`, also once `Text`
gets eta (SW-1644, eta for one-constructor types): the `case` on `v`'s list is on `List`.

**R7, to keep it so:**

1. "Exactly one field" counts every field: implicit, proof and erased ones. `MkChar code valid`
   has two. (With a proof beside the data field, rank is not determined by the data field.)
2. `u` is strictly inside `v`: reached from `v`, the field of *that* match of `s`, by at least
   one step. "`u` is smaller than the same parameter" is not enough: `| Wrap (Two a (Wrap v)) =>
   f (Wrap (Two a (Wrap v)))` would then be `<` (take `u` = the outer field), and it is the
   parameter itself. `u = v` is `rebuilt`, `≤`.
3. The steps from `v` to `u` are matched fields and recursive function fields applied, as §3
   says, **not** a signed lambda's variable and not an accessor. Otherwise F2 returns in a form
   G1's root test misses, because the argument is a constructor: `type W = | MkW (xs: List Nat)`,
   `def f: W → Nat | MkW v => tails v (u => f (MkW u))` unfolds for ever on `f (MkW n)`
   **[argued]**. If a later program wants that combination, it needs its own argument.

## 5. The oracle stage ("A accepts ⇒ B's copy passes today's check")

Worth having, and the right kind of test: it is Rocq's method (check the unfolded callee) used
as a referee. As a safeguard it is necessary, not sufficient:

- It covers rule 2 only. Rule 1 needs the copy rewritten to record patterns; rule 3 has no B
  form at all (today's check refuses `MkText r`), so it needs its own referee: the worker on the
  field's type (the proposal's T2).
- It finds what its generator writes. F3 and R3's programs need a generator that makes `G`s
  with partial applications of the callback, inner matches, growing carriers, callbacks passed
  to other functions, and callers that pass something bigger. Stage 2's must-reject list (five
  cases) should grow by F3, R2's forms, R3's program and the two in R7.
- It can't see F2 (B's copy has a `case`).
- It shares a failure mode if the specialiser reuses the signature code. The specialiser must be
  written separately, and "couldn't build B's copy" must fail the property, not skip the case.

Two cheap properties cover all three rules and catch what B can't, and I'd add both to stage 6:
**(P1)** every generated program the new check accepts is *run* on random closed inputs under a
step budget (non-termination shows as a budget failure, whatever rule let it in); **(P2)** for
every accepted definition `f`, reading back `x => f x` (and comparing it with a renamed copy)
finishes within budget.

## 6. Comparison

**Rocq, PR #17986** ("Extrude uniform parameters of inner fixpoints in guard condition check",
merged 7 May 2024, in 8.20) **[fetched]**. It lets the guard checker carry the subterm
information through a nested `fix` whose function argument is passed unchanged in recursive
calls: the same idea as rule 2's "passed unchanged". Differences that matter:

- Rocq checks the callee's body, unfolded, at each use; it trusts no summary. Rule 2 trusts a
  summary computed once. That is simpler to state, but it is new trusted code of a kind the
  kernel doesn't have yet.
- Rocq's reduction of a `fix` is guarded by its structural argument, so the change couldn't
  affect normalisation. Stitchwort's can (F2).
- Its record: the reviewer wrote that he did not "understand it enough to predict the
  consequences", it was restricted to a prefix of the uniform arguments to be safe, a first bug
  was fixed in October 2024 (#19661, #19671), and in February 2026 issue #21682 gave a
  non-terminating function and a proof of `False` in every release since 8.20: the uniformity
  test looked at self-calls only and missed calls between bodies of a mutual inner fixpoint
  (fixed by #21684, in 9.2) **[fetched]**. `termination.rs`'s header already cites that lesson
  for groups. R3 above is the same mistake waiting in rule 2, and "alone in its group" is the
  restriction Rocq arrived at afterwards.

**Lean 4** **[memory, except where marked]**. The kernel has only recursors. Structural
recursion, including over nested types (auxiliary types and `brecOn`, since 4.12) and mutual
groups, is compiled by the elaborator to recursors ("the rules … are fundamentally syntactic",
reference manual **[fetched]**), so nothing is trusted, and a function must recurse on the
`List Tree` with a function of its own: the per-list helper Stitchwort has today. Recursion
through `List.map` goes by well-founded recursion with `attach` inserted by `wf_preprocess`
(4.18), the proposal's option C. So Lean chose "nothing new in the kernel, pay in the
elaborator and in how proofs unfold"; the proposal chooses Rocq's side, with Rocq's history.
That is a defensible choice for the benefit claimed (`rfl`, equations and `map` lemmas apply
directly), but it is the costlier one to get wrong, which is why the restrictions above should
be in the design before it is built, not found by the fuzzer.

## 7. D3611 and D3612 as worded

**D3612 (text's rest; one-field wrapper): safe to recommend, [rec: yes] stands**, with the rule
worded as R7: one field counting every field; `u` reached from the matched field through matched
fields only. Add the worker-on-`List Char` referee to stage 6 for it.

**D3611 (through `map`; rules 1 and 2): not safe to recommend as worded.** The decision text
says "about 300 trusted lines, argued against the existing invariant". Three things in it are
not yet true:

1. Rule 1 as described can't fire on the example it is for (F1); what replaces it is a second
   derived fact about definitions (accessors), not 20 lines in `relate`.
2. The existing invariant isn't the only one involved: the unfolding policy depends on recursion
   going through a `case`, and rule 2 removes that (F2). The proposal needs a rule (G1 or G2)
   and Matt needs to see that trade: G1 refuses `def size (t) := 1 + t.forChildren (c => size
   c)` with "match on `t` first"; G2 changes what the evaluator does.
3. The signature rule has a loop as worded (F3) and three gaps (R2-R4).

**Suggested replacement:** draft 2 of the proposal with F1, R1-R4, R6 and the G1/G2 choice
written in, stage 6 extended by P1, P2 and the rule 1 and rule 3 referees, and the
implementation reviewed on Opus or Fable before it merges (it is a kernel change that widens
what is accepted, D2364). Then D3611 becomes "[rec: yes, option A with the guard rule G1]",
with a new small decision beside it for G1 against G2. Stage 1 (rule 3, and rule 1 once
restated with R6) doesn't depend on rule 2 and can go first.

## 8. Not done

No code, builds or test suites. The `[argued]` divergences can't be run until a checker accepts
the programs; they are the first things to run when one does. I did not check which std
functions are alone in their groups after `if` and `match` are lifted (R3), did not read the
Rocq patches themselves (only the PR and issue pages), and the Lean release numbers are from
memory.
