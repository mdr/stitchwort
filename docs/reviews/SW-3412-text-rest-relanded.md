# SW-3412 (the wrapper rule, re-landed with "relevant data only"): soundness review

**Reviewed:** branch `lane/SW-3412` at `0a2c8e8cc` (`git diff main...lane/SW-3412`):
`crates/core/src/termination.rs` (`Binder::relevant`, `Info::parent`, `Walker::wrapped`,
`part_of`, `strictly_inside`, the header's "Relevant data only"), `docs/core.md`,
`docs/proposals/recursion-through-map.md` rule 3 condition 4, the new examples and kernel tests.
Review by Fable, 15 November 2026, for D3613. **[run]** means run with the branch's release
binary, built for this review (`check --no-cache` on a scratch file); **[argued]** means reasoned
from the source and `docs/core.md`, not run. Probe files are in
`/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw3412-review/`;
the ones that matter are quoted in full below.

## 0. Corpus results (run first)

`cargo nextest run --release -E 'binary(running) & test(/examples::(soundness|reject)/)'` on the
branch: **3 tests run, 3 passed, 0 failed** (213 skipped by the filter), 74.5 s.

| Test | Result | Time |
|---|---|---|
| `examples::soundness_examples_fail_for_the_expected_reason` (all 135 files of `examples/soundness/`) | pass | 9.5 s |
| `examples::rejected_examples_fail_for_the_expected_reason` (all of `examples/reject/`) | pass | 74.5 s |
| `examples::rejected_projects_fail_for_the_expected_reason` | pass | 3.5 s |

Also run directly: `stitchwort check --no-cache
examples/soundness/proof-irrelevance-07-descent-through-a-proof.sw` gives `E-TERMINATION` on `f
(MkBox n)` **[run]**, and the lane's three accept examples (`termination-wrapper-honest`,
`termination-wrapper-changing-instance`, `text-patterns-prefix-recursion`) check **[run]**.

Not run: the accept examples as a suite, the kernel's unit tests, anything else.

## 1. Verdict

**Sound.** The condition is enough: I found nothing the branch accepts that loops, makes the
kernel unfold without end, or proves `False`, and every proof-shaped variant of
`proof-irrelevance-07` I could build is refused. Nothing has to change before merging.

The condition is a little stricter than soundness needs (F3), which is the right side to err on.
Three findings, none blocking:

| # | Finding | Kind | Severity |
|---|---|---|---|
| F1 | The header's invariant ("rank on the terms") is false for an accepted program: a pinned proof field lets `C u` hold the whole argument and still be recorded `<`. Safe, but for a reason the text doesn't give | Wrong invariant in `termination.rs` and `docs/core.md`; depends on two positivity rules | Medium (text; a hole if either positivity rule is relaxed) |
| F2 | The lane's open question: descent through a proof's data field by the plain rule is sound, and so is a wrapper that lies wholly inside a proof (accepted today). The header's sentence that a part of a proof "isn't smaller" says more than the checker enforces | Text | Low |
| F3 | Tests cover each condition once at the surface; the variants below aren't pinned, and the user-facing text doesn't say the one field must be data | Tests, docs | Low |

## 2. What the code does

`wrapped(C u)` returns `<` only if all of these hold **[checked against the source]**:

1. `C` has exactly one declared field, of any kind (`ctor.fields.len() != 1` is tested first, so
   `field_erased[0]` can't be out of range);
2. that field isn't erased (not a proof, not a type former), `C`'s type isn't in `Prop`, and the
   field isn't a recursive function field (the SW-3376 review's F3 is fixed);
3. `part_of(u)` is a variable, and `strictly_inside` reaches `C`'s matched field from it by one
   or more `parent` links;
4. `parent` is set only by `case`, and only for a field with `data.sort != Prop && !erased`.

So a chain can't start at a proof (a match on one is a match on a `Prop` type, whose fields get
no parent), can't pass through a proof field, and can't pass through a proposition's data field.
Conditions 2's "field isn't erased" is implied by 3 and 4 (no chain can leave a proof), so it is
defence in depth; 2's "`C` isn't in `Prop`" is not implied and is needed for the squash example.

Whether a field is a proof is read from the declaration, and holds for every instance: a
proposition behind a definition (`a1`), a predicate parameter applied (`a2`) and a `Prop`
parameter (the lane's `changing-proposition`) are all refused **[run]**; a `Type` parameter can't
be given a proposition (`E-UNIVERSE`, the lane's `type-parameter-prop`).

## 3. Why the condition is enough [argued]

Two orders matter, and the header only talks about one.

- **Term rank**: the height of the value's constructor tree as the kernel's evaluator holds it,
  proofs included. The evaluator never swaps one proof for another (comparison skips proofs, but
  evaluation computes with the proof it was given, and a `case` on an unknown proof is stuck:
  propositions have no eta, condition 2 of record eta). The plain field rule keeps term rank.
- **Relevant rank**: the same height with every proof position counted as nothing. This is what
  conversion can see, and what a run sees after erasure.

Rule 3 as re-landed lowers *relevant* rank: `C` is data, its one field is data, and `u` is below
`v` by constructor layers of data, so `C u` and `C v` differ where comparison looks. The reverted
version didn't: with a proof as the one field, `MkBox n` and `MkBox l` have the same relevant
rank (they are one value to conversion), which is exactly `proof-irrelevance-07`.

For a function that returns **data**, relevant rank is the one that counts (its proofs are erased
when it runs, and a `case` on an erased proof takes its branch without looking). There, the only
proofs it can take apart are of propositions whose fields are all proofs and don't mention the
proposition (`E-PROP-ELIM`, D1980), so no data comes out of a proof, and every data argument it
passes was reached through data. For a function that returns a **proof**, nothing runs, and the
kernel's evaluation ends by term rank on closed proofs and at a stuck `case` on open ones.

## 4. Attacks and outcomes

All **[run]** on the branch unless marked.

| Probe | What it tries | Outcome |
|---|---|---|
| `a1` | 07 with the proposition behind `def MyP: Prop := Loop` | `E-TERMINATION` |
| `a2` | 07 with the field's type `p n` for a parameter `p: Nat → Prop` | `E-TERMINATION` |
| `a3` | One field `h: Nat → Loop`, rebuilt as `MkWF (_ => n)` | `E-TERMINATION` |
| `a4` | Data wrapper around a box of a proof, `MkW (MkBox n)` after `MkW (MkBox (MkLoop n))` | `E-TERMINATION` |
| `c1` | 07 split over a mutual pair (`f (MkBox l) = g l`, `g (MkLoop n) = f (MkBox n)`) | `E-TERMINATION` |
| `c2` | Wrapper around a record `{ tag, pf }`, descent only in `pf`, by explicit nested `match`es | `E-TERMINATION` |
| `d2` | The same with a zero-field constructor (`pf = Stop` after `pf = More Stop`) | `E-TERMINATION` |
| `d6` | A proof beside the part one level down: `MkW (MkD xs (MkPBox …))` | `E-TERMINATION` |
| `d3` | Agda #8699's own shape: an index `T (MkSq (More q))` refines the wrapper's proof field, then `f (MkSq q) …` | `E-TERMINATION` |
| `d3b` | The same packed in a record, rebuilt through the pinned field | `E-TERMINATION` (and the unmatched forms don't type-check) |
| `d4` | An index solves the wrapper's data field; nothing is matched out of it | `E-TERMINATION` |
| `d5` | A part of a part re-wrapped in a list, `MkW [r]` | `E-TERMINATION` |
| `b3` (`g`) | Descent only in a pinned proof: `MkW (Mk p x)` after `MkW (Mk (More p) x)` | `E-TERMINATION` ("stays the same") |
| `a6` | The plain rule through a proof's data field, into `Nat` | `E-PROP-ELIM` |
| `c4` | A tower of subsingleton propositions matched into data, `BoxT k` | Accepted only because `k` is matched and gets smaller; honest |
| `d1` | A one-field interface dictionary as the wrapper; `rfl` on an unknown dictionary | Accepted, honest; the `rfl` fails with `E-REFL` at once, no `E-RESOURCE` |
| `a7`, `a5b` | The plain rule through a proof's data field, into a proof | Accepted (as on `main`); see F2 |
| `a5` | A wrapper wholly inside a proof | Accepted; see F2 |
| `b3` (`f`), `b4` | A wrapper around a rebuilt constructor whose pinned proof field is replaced | Accepted; see F1 |
| `b1`, `b2`, `b5` | Making F1's proof able to hold the wrapper's type: directly, by nesting, by nesting twice | `E-POSITIVITY`, all three |

Not probed, argued from the source: quotients (`Quot.lift` isn't a `case`, so it sets no
`parent` and is never on a chain); `let` and lambda variables (`parent` is `None`); an erased type
field as the one field (refused by condition 2, and a type can't be matched anyway). Open-term
unfolding is unchanged from SW-3376 except that less is accepted, so that review's §3.1 stands;
I re-ran only `d1` and the lane's accept examples.

## 5. Findings

### F1. "Rank on the terms" is false where a pinned proof is replaced (medium; text, and a dependency)

```
import Std (Unit)
type Any: Prop = | MkAny [a: Type] (x: a)
type PA (p: Any): Type = | MkPA
type T: Type = | Mk (p: Any) (x: PA p) | In (t: T)
type W: Type = | MkW (t: T)
theorem f: W → Unit
  | MkW (In (Mk p x)) => f (MkW (Mk (MkAny (MkW (In (In (Mk p x))))) x))
  | MkW (In (In t)) => f (MkW (In t))
  | MkW (Mk p x) => Trivial
```

**[run]** (`b4.sw`): accepted. In the first clause the new argument *contains a value bigger than
the old argument*, inside the proof `MkAny …`. `rebuilt` takes `Mk <anything> x` for the matched
`Mk p x` because `p` is pinned by `x`'s type, and `PA`'s parameter is a proof, which comparison
skips (the SW-3376 review's F2); `wrapped` then calls `MkW` of it smaller. So the header's "the
rank argument needs rank(`C u`) = rank(`u`) + 1 on the terms" and `docs/core.md`'s "each rule
keeps it" don't hold of what is accepted: term rank goes up here.

It is safe **[argued]**: relevant rank goes down (§3), and the bigger value can never come back,
because a thread that digs it out of the proof would need the proof's type to be able to hold a
`W`, and a pinned field's type can't mention the type being defined or its group, directly or by
nesting. `b1` (`Mk (p: PBox T) (x: Tag T p)`), `b2` (`W` nested in `T a` with `p: PBox a`) and
`b5` (nested twice, through `W a`) are each `E-POSITIVITY` **[run]**. A proposition that hides
the type (`MkAny [a] (x: a)`) gives back a value of an unknown type, which can't be passed to
`f`; types are never taken apart, and a cyclic type equation fails the occurs check.

**Fix (text, a follow-up ticket; not this lane):** state the invariant as two orders, as in §3:
the plain rule keeps term rank, rule 3 and "rebuilt is equal" hold up to proof positions, and the
two can be mixed only because of the two positivity rules ("no field depends on one holding `D`",
nestable condition 5). Add `b1`, `b2`, `b5` as reject examples whose comments say termination
relies on them, and `b4` as an accept example whose comment says what is being relied on. I did
not check whether the SW-3376 review's F2 was filed as a ticket; this is the same item with a
sharper example.

### F2. The open question: the plain rule through a proof's data field is sound (low; text)

```
import Std (List, Nat, Unit)
type PBox (a: Type): Prop = | MkPBox (x: a)
type D: Type = | Base | MkD (xs: List Nat) (q: PBox D)
theorem t: D → Unit
  | Base => Trivial
  | MkD _ (MkPBox d) => t d
```

**[run]** (`a7.sw`): accepted, as on `main`. With `def t: D → Nat` it is `E-PROP-ELIM` **[run]**
(`a6.sw`). That is the whole argument **[argued]**: `PBox` has a data field, so a match on its
proof can only produce a proof; `t` is therefore never run, and the kernel evaluates it only on a
proof term it actually holds, where `d` really is a part (term rank). Conversion skipping the
proof never makes the evaluator take a different `d`. In the reading where proofs are truth
values the recursion is still valid: it is induction on the stage at which `q` becomes true, and
the body is checked for every `d`, so in particular for one of a lower stage.

The same goes for a wrapper that sits wholly inside a proof:

```
import Std (List, Nat, Unit)
type PBox (a: Type): Prop = | MkPBox (x: a)
type W: Type = | Leaf | Deep (pf: PBox W2)
type W2: Type = | MkW2 (w: List W)
theorem g: W2 → Unit
  | MkW2 [Deep (MkPBox (MkW2 [_, ..r])), .._] => g (MkW2 r)
  | MkW2 _ => Trivial
```

**[run]** (`a5.sw`): accepted. `s` (the inner `MkW2 …`) is below the parameter through a proof by
the plain rule; the wrapper and the chain from `v` to `r` are data. It is no worse than `g w2`
on the inner value, which the plain rule accepts (`a5b.sw`), and again it can only produce a
proof. So the checker's line is: *the wrapper's own shrinking must be visible in data*, while
*where the wrapped value sits* may be inside a proof. That line is sound, but the header's "a
part of a proof isn't smaller than anything conversion can tell apart" and core.md's "never
through a proof" read as if the second were refused too.

**Fix (text):** say that the steps from `v` to `u` are data, that `s` may itself have been
reached through a proof by the first rule, and why that is harmless (`E-PROP-ELIM`: the function
then returns a proof). Add `a5` as an accept example so the line is deliberate. If Matt would
rather refuse it, the change is to require `s`'s own relation to the parameter to go through
relevant fields only; nothing I found needs that.

A note for the record: I could not make 07 itself loop or prove `False` on paper either (its
function returns a proof, and D1980 blocks the data-returning form). The reason to refuse it is
that it breaks the invariant the design keeps (the order agrees with conversion, and with what a
run sees after erasure), so that termination doesn't lean on D1980. Refusing it loses nothing:
`f (MkBox l) = g l` with a separate structural `g: Loop → Void` proves the same thing.

### F3. Tests and user-facing text (low)

- The kernel unit tests cover a proof as the one field and a number as the one field. There is
  no kernel-level test for the other two conditions: `C` in `Prop` with a data field (squash) and
  a chain through a proof field. Both are covered only through the elaborator
  (`reject/termination-wrapper-squash.sw`, `-through-proof.sw`). Add two unit tests in
  `crates/core/tests/it/termination.rs` so each condition fails a kernel test if removed.
- Worth adding as reject examples, each a different way to reach the same refusal: `a1`
  (proposition behind a definition), `a2` (predicate parameter applied), `a4` (wrapper around a
  box of a proof), `c1` (07 over a mutual pair), `d3` (an index refining the proof field, Agda
  #8699's actual mechanism), `d6` (proof beside the part, one level down).
- `docs/syntax.md` and `docs/guide/07-recursion.md` say "a constructor with exactly one field
  (implicit and proof fields count)" and "One-field records work the same way", without saying
  the one field must be data. One clause each would do.

## 6. Probe sources not quoted above

`a1.sw`:

```
import Std (Void)
type Loop: Prop = | MkLoop (next: Loop)
def MyP: Prop := Loop
type Box2: Type = | MkBox2 (h: MyP)
def f (b: Box2): Void := match b with
  | MkBox2 l =>
    match l with
      | MkLoop n => f (MkBox2 n)
```

`a2.sw`:

```
import Std (Nat, Void)
type Loop: Prop = | MkLoop (next: Loop)
type BoxF (p: Nat → Prop) (n: Nat): Type = | MkBoxF (h: p n)
def f (b: BoxF (_ => Loop) 0): Void := match b with
  | MkBoxF l =>
    match l with
      | MkLoop n => f (MkBoxF n)
```

`a4.sw`:

```
import Std (Void)
type Loop: Prop = | MkLoop (next: Loop)
type Box (a: Prop): Type = | MkBox (h: a)
type W: Type = | MkW (b: Box Loop)
def f (w: W): Void := match w with
  | MkW (MkBox l) =>
    match l with
      | MkLoop n => f (MkW (MkBox n))
```

`c1.sw`:

```
import Std (Void)
type Loop: Prop = | MkLoop (next: Loop)
type Box (a: Prop): Type = | MkBox (h: a)
def f: Box Loop → Void
  | MkBox l => g l
def g: Loop → Void
  | MkLoop n => f (MkBox n)
```

`d3.sw`:

```
import Std (Unit)
type Big: Prop = | Stop | More (b: Big)
type Sq: Type = | MkSq (b: Big)
type T: Sq → Type = | Step [q: Big]: T (MkSq (More q))
theorem f: (s: Sq) → T s → Unit
  | MkSq b, Step [q := q] => f (MkSq q) (Step [q := q])
```

`d6.sw`:

```
import Std (List, Nat, Unit)
type PBox (a: Type): Prop = | MkPBox (x: a)
type D: Type = | MkD (xs: List Nat) (q: PBox W)
type W: Type = | MkW (d: D)
theorem t: W → Unit
  | MkW (MkD [_, ..xs] q) => t (MkW (MkD xs (MkPBox (MkW (MkD [0, 0, 0] q)))))
  | MkW (MkD [] (MkPBox w)) => t w
```

`b1.sw` (`E-POSITIVITY`):

```
import Std (List, Nat, Unit)
type PBox (a: Type): Prop = | MkPBox (x: a)
type Tag (a: Type) (p: PBox a): Type = | MkTag
type T: Type = | Mk (p: PBox T) (x: Tag T p) | In (t: T)
```

`b2.sw` (`E-POSITIVITY`) replaces the last line with `type T (a: Type): Type = | Mk (p: PBox a)
(x: Tag a p) | In (t: T a)` and `type W: Type = | MkW (t: T W)`; `b5.sw` adds `type W (a: Type):
Type = | MkW (t: T a)` and `type R: Type = | MkR (w: W R)`.

## 7. Not done

No change to the branch (this file is uncommitted) and no board edits. I did not build or run
the reverted SW-3376 code, so "07 doesn't actually loop there" is argued, not run. §3 and the
"can't come back" argument of F1 are on paper, not mechanised. I did not review the elaborator's
side of prefix patterns, the error wording, or the snapshots beyond the files named above. I did
not run the accept examples as a suite or the kernel's unit tests; the lane and the verifier do.
