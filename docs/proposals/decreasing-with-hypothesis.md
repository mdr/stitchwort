# Proposal: `decreasing` measures that need a fact (SW-2013)

Design note only, 7 Nov 2026. Nothing here is built. It is a design item
for SW-199's remaining stage 3, raised by the friction synthesis
(`docs/research/aoc-friction-synthesis.md`, theme G and §5 item 5).

## 0. Summary

**What users get.** Three AoC days kept a run-time test, a pair of extra
parameters, or a depth bound in a program only so that a recursive call
could be seen to get smaller. With this change, the fact a `match` or an
`if` has just established is there when the decrease is proved, and the
equation that proofs use (`f.unfold`) shows the program as written, with
no trace of it. 2024 day 23 and 2021 day 16 lose their always-true guards
(and the completeness proofs that dismiss them), std's `Graph.searchFrom`
loses two parameters, and 2021 day 12 could have used `decreasing` instead
of a depth bound.

**The premise needs correcting first.** A hypothesis as a *parameter*
already works. The brief's example, `fuel - steps` with `steps ≤ fuel`,
can be written today, and std does it three times (§1.1). What doesn't
work is a fact that comes from *inside* the body:

1. **What a `match` on a computed value found** (`candidates.popMin` was
   `Some (candidate, others)`, so `others` is smaller). Writing `match
   found: …` gives the fact, but then proofs about the function get stuck
   (`E-MATCH-MOTIVE`). Three days and one std function hit this.
2. **What a plain `if` tested** (`if i < bound then f (i + 1) …`). Today
   only `if h: …` gives the fact. This is the small one: the error already
   says to add `h:`.
3. **What the recursive call itself returned** (2021 day 16: the packets
   after a sub-packet are fewer bits than before it). A fact about `f`'s
   result can't be used inside `f`'s own definition. Two days hit this.

**Recommendation.** Make the facts of 1 and 2 available to the decrease
obligation automatically, and state `f.unfold` over the body as written,
so the facts never reach a proof (Lean does the first part for `if`; §3).
For 3, document the result-record pattern now (a small domain record
carrying "no longer than the input") and defer a postcondition clause
(`ensures`, as in Dafny) until a third day needs it. No new syntax.

**D questions:** D2870 to D2872 (§7). **Tickets:** four lanes (§8).

## 1. The problem, in the code

### 1.1 What already works: a hypothesis as a parameter

A `decreasing` measure is a `Nat` of the header's parameters, and every
header parameter is in scope while a call's obligation is proved,
including a proof parameter (`decreasing.rs:976-989` computes the header
as the parameters before the colon; `Plan::tel` keeps all of them,
`decreasing.rs:371-376`). std already relies on this:

- `Nat.iterateUntilStable` takes `shrinks: (y: a) → step y ≠ y → measure
  (step y) < measure y` and proves each call with `shrinks x h`
  (`std/Nat/Iterate.sw:41-47`).
- `List.chunksOfPositive` takes `[auto pos: size ≠ 0]`
  (`std/List/Toolkit.sw:582-588`).
- `Graph.searchFrom` threads an invariant `queued` through every call
  (`std/Graph/Search.sw:273-292`).

So the brief's case reads, today [inferred from the code above; not run,
since this lane runs nothing]:

```
def countUp (fuel: Nat) (steps: Nat) [auto within: steps ≤ fuel]: Nat
    decreasing fuel - steps
:=
  if more: steps < fuel then countUp fuel (steps + 1) else steps
```

`auto` proves `steps + 1 ≤ fuel` from `more`, and the obligation
`fuel - (steps + 1) < fuel - steps` from `more` too. Subtypes as
arguments (`{ steps: Nat, within: steps ≤ fuel }`) also work today, as
records with a proof field, unboxed at run time (`docs/core.md:482`).
Nothing in this note changes that.

What remains on fuel for good reason: 2024 day 17's machine (a program
that may loop), 2024 day 15's `firstFree` and 2020 day 20's `rowAfter`
(a walk bounded by a count, where fuel is the honest bound), and 2020
day 19's matcher, which is mutually recursive (SW-199's mutual-groups
item) as well as case 3.

### 1.2 Case 1: what a `match` on a computed value found

2024 day 23 (`aoc/src/Aoc/Year2024/Day23/Day23.sw:98-110`):

```
    match candidates.popMin with
      | None => clique
      | Some (candidate, others) =>
        -- Always true (`Set.sizePopMin`); the test puts it in scope for the
        -- recursive calls.
        if fewer: others.size < candidates.size then
          …
        else best
```

`Set.sizePopMin` (`std/Set/Spec.sw:131`) proves `others.size <
candidates.size` from `found: candidates.popMin = Some (candidate,
others)`. Writing `match found: candidates.popMin with` gives `found`.
The program doesn't, because of what it does to proofs: a `match e:` is
lifted to a helper that takes the scrutinee and `rfl`, `f.unfold` shows
that helper, and a proof that matches on the same scrutinee can't
generalise the `rfl` (`E-MATCH-MOTIVE`; 2021 day 12, `aoc/NOTES-2021.md:2950-2962`,
and 2024 day 23, SW-809). So the program tests a fact that is always
true, and its completeness proof dismisses the impossible `else`.

The same pattern:

- **2021 day 16**, `readGroups` and `readPackets`
  (`aoc/src/Aoc/Year2021/Day16/Day16.sw:122,165,176,189`): four run-time
  `if shorter: … < reader.length` guards, each after `match
  reader.readBit with` or `match afterType.readNumber …`, whose results
  are always shorter.
- **2021 day 12**: gave up `decreasing` for a depth bound and a
  `stepDecreases` lemma (`aoc/NOTES-2021.md:2959-2961`).
- **std's `Graph.searchFrom`** (`std/Graph/Search.sw:276-292`) does the
  workaround by hand: the popped value and its equation are parameters
  after the colon, `(popped: Option …) → (found: queue.popMin = popped)`,
  so the `match` is on a variable, and each call passes `pushed.popMin
  rfl`. Two parameters that say nothing about Dijkstra.

### 1.3 Case 2: what a plain `if` tested

`if c then a else b` elaborates to `Bool.ifThenElse c (_ => a) (_ => b)`
(`docs/core.md:304`): the branches take a `Unit`, so nothing about `c` is
in scope. `if h: c` elaborates to `Decidable.elim`, with `h`, and that's
the documented guard style (`docs/syntax.md:1016-1021`). The error points
there (`decreasing.rs:2756`), so this costs a newcomer one round trip.
It also costs proofs: they see `Decidable.elim` and need lemmas such as
`Nat.untilStableDecYes` (`std/Nat/Iterate.sw:51-57`) or
`Decidable.elimEq` (`examples/accept/let-proof-pattern-unfold.sw:31`)
where an `if` would do.

### 1.4 Case 3: what the recursive call returned

2021 day 16's `readPackets` reads an operator's sub-packets with a
recursive call, then calls itself on the bits that follow:

```
match readPackets (Packets count.value) after with
  | Some (subPackets, following) => … readPackets later following …
```

`following` is shorter than `reader`, but only because `readPackets`
never returns more bits than it was given: a fact about `readPackets`,
which its own definition can't use. Today: a run-time guard
(`Day16.sw:183,196`). 2020 day 19's `leftAfterAllWith` is the same (what
is left after one rule is a suffix of the message), and it is one reason
the matcher is on fuel (`aoc/NOTES-2020.md:5310-5332`).

2024 day 23's other item, "the program carries a three-line proof for
its measure" (`withinOthers`, `Day23.sw:105-107`), is a missing std lemma
(`Set.sizeIntersect…`, SW-841), not a language gap.

## 2. What a decrease proof sees today

For `def f (x: A): B decreasing m x := body`, the body is elaborated once
as `f.%step x %rec`, where `%rec: (y: A) → [auto decreasing: m y < m x] →
B` stands for each recursive call (`decreasing.rs:9-12`). So a call's
obligation is an ordinary `[auto]` argument: it sees exactly the
variables in scope at the call, which are the header's parameters, the
pattern variables, `let`s, and the hypotheses of `if h:` and `match e:`.
`f.unfold` states `f x = f.%step x (y => f y)` (`decreasing.rs:25-26`),
so whatever the body did to get those hypotheses is in the equation
proofs use. The runtimes run the same `f.%step`, with proofs erased
(`decreasing.rs:28-29`).

That last point is the opening: in `f.unfold`, each recursive call is
`y _ => f y`, which drops its proof. A hypothesis that only fed decrease
proofs is unused there, so `f.unfold` can be stated without it.

## 3. Designs compared

| Design | Case 1 (`match`) | Case 2 (`if`) | Case 3 (result) | Cost |
|---|---|---|---|---|
| (a) Lean's `termination_by` / `decreasing_by` | with `match h:` | yes | subtype result | we already have it, less case 2 |
| (b) Agda's sized types | no | no | yes | kernel change |
| (c) `decreasing m by proof` | no | no | no | syntax only |
| (d) facts reach the obligation, `f.unfold` as written | yes | yes | no | generator work |
| (e) subtypes as arguments and results | (helper results) | no | yes | none to build; verbose |

**(a) Lean.** `termination_by m` gives the measure; `decreasing_by tac`
one proof script for every call, defaulting to `decreasing_tactic`
(`simp_wf`, then `decreasing_trivial`, which tries `omega`). Each
obligation's context holds the local hypotheses. Lean's reference shows a
`Bool` `if n == 0` whose `else` obligation has `¬(n == 0) = true` in
context, so a plain `if`'s condition is there, and it says a `match`
needs `match h : …` written to connect the scrutinee to the pattern
(Lean reference manual, "Well-founded recursion"; read for this fact).
For a decrease that depends on the call's own result, Lean code returns a
subtype, `{ rest // rest.length ≤ bits.length }`. Stitchwort's per-call
`[decreasing := p]`, with `auto` and `omega` tried first
(`docs/guide/07-recursion.md:86`), is Lean's model already. What it lacks
is the `if` condition, and a `match h:` that doesn't hurt proofs. Lean's
equation lemmas are stated for the function as written, so `match h :`
costs Lean proofs less [inferred, not checked].

**(b) Agda's sized types.** A type carries an upper bound on its values'
size: `readPackets : Reader i → Maybe (List Packet × Reader i)` says, in
the type, that the bits left are no more than the bits given. This is the
one design that solves case 3 without proofs. It needs a size sort in the
kernel, size variables in signatures, and a checker for them. The
well-founded recursion note rejected it as option D
(`well-founded-recursion.md` §5) for that reason, and nothing here
changes the trade. Ruled out.

**(c) `decreasing m by proof`.** One proof for every call, Lean's
`decreasing_by`. Stitchwort has no tactic language for the proof to be a
script of, and `auto`, then `omega`, are already tried at every call, so
a shared proof term would rarely fit every call. It adds no facts, so it
solves none of the three cases. Ruled out.

**(d) Facts reach the obligation automatically.** In a `decreasing`
body, when an arm or a branch contains a recursive call:

- an `if c` is elaborated with its condition (`c = True`, or `c = False`
  in the `else`), as `if h:` is today;
- a `match` on a value that isn't a variable is elaborated with its
  equation, `scrutinee = pattern`, as `match e:` is today;
- either way, the hypothesis is anonymous unless the source names it
  (`match found: …`), and `auto` and `omega` see it like any other.

Then `f.unfold` is stated over the body as written, with plain `if`s and
`match`es and no hypotheses, and proved equal to `f.%step x (y => f y)`.
That proof is generated, like `f.%step.%respects` today
(`decreasing.rs:19-23`): copy the case tree, and at each leaf both sides
compute to the same thing, since once each recursive call drops its proof
the hypothesis isn't used. A hypothesis the body uses for anything else (a
record's proof field, say) stays, and `f.unfold` shows it, as today.

Case 3 isn't covered: no `match` or `if` establishes a fact about `f`'s
own result.

**(e) Subtypes as arguments and results.** As arguments, they work today
(§1.1). As results, a helper or the function itself returns a record
that carries its fact. In application code that's a small domain type,
which the house style asks for anyway (`CLAUDE.md`, application code):

```
--| The bits left after reading from `reader`: never more than it had.
type Rest (reader: BitReader) = { bits: BitReader, within: bits.length ≤ reader.length }
```

This needs nothing new and it covers case 3. Every return site has to
build the proof, and every user has to unwrap `.bits`. For a function
that returns in five places, as `readPackets` does, that's real noise.
A postcondition clause, `ensures (r => …)` after `decreasing` (Dafny's
`ensures`, F\*'s refined result type), would generate the record, prove
the returns with `auto`, give each recursive call's result its fact, and
generate `f.ensures` for proofs. It's a new keyword and a larger generator
change, though, and only two days need it.

### Recommendation

**(d) now, (e) as documented practice, and `ensures` on a trigger.**

(d) removes the always-true guards and the hand-made `popped`/`found`
parameters, and it makes the documented guard style unnecessary for an
`if` that already tests the fact. It needs no syntax, and the user-visible
promise is simple: *facts the program checks are there for the decrease,
and proofs see the program as written*. It's the Lean behaviour for `if`,
plus the thing Lean users get from equation lemmas for `match h:`.

What it costs: the generator gets a second equality proof per definition
(the shape of `respects`), and `f.%step`'s term grows a dependent
`if`/`match` where a call sits. Hashes of existing `decreasing`
definitions with a plain `if` around a call change, which doesn't matter
(the end state is what counts). Run time doesn't change, since the
hypotheses are proofs and are erased (`docs/core.md:242`).

What it rules out: nothing. `ensures` can come later on top of it.

Lean is the guide here, not Agda: Stitchwort already chose Lean's model
(a `Nat` measure, a proof per call) in D473/D474, and (d) closes the
gaps that model has here.

## 4. What the obligation looks like to the user

The message keeps its form (`decreasing.rs:2740-2757`), and the list of
what's in scope (`in_scope`, `decreasing.rs:2761`) now includes the new
facts, shown as the source wrote them:

```
[E-DECREASING] Error: can't show `others.size < candidates.size` here, which `decreasing candidates.size` needs for this call
  In scope: candidates.popMin = Some (candidate, others)   (this `match`'s arm)
            clique.size + candidates.size ≤ best.size = False   (the `if`'s `else`)
  Note: name the `match`'s fact to use it in a proof, `match found: candidates.popMin with`,
        then give `[decreasing := omega [Set.sizePopMin candidates candidate others found]]`
```

**How `omega` discharges it.** `omega` reads the arithmetic facts in
scope, including a comparison as a `Bool` equation (`(group <= 15) =
True`, `aoc/NOTES-2021.md:4152`), so an `if`'s condition needs nothing
written: `if i < bound then f (i + 1)` with `decreasing bound - i` is
proved by the default search. A `match` equation such as `popMin s = Some
(k, rest)` isn't arithmetic: a lemma turns it into a fact, and that lemma
needs the equation by name, so the user names it with `found:` and passes
the lemma to `omega`, as above. The decision here is that the name is
optional and `found` doesn't leak into `f.unfold`. A match on arithmetic,
`match n - k with | Succ j`, gives `n - k = Succ j`, which `omega` uses
directly with no name [inferred: that `omega` treats such an equation as
an atom equation; to check in stage 2].

## 5. The AoC workarounds afterwards

**2024 day 23** (`Day23.sw:98-110`): the guard and its comment go, and
the impossible `else` leaves the completeness proof.

```
    match found: candidates.popMin with
      | None => clique
      | Some (candidate, others) =>
        let fewer := Set.sizePopMin candidates candidate others found
        let narrowed := links.neighbours candidate |> .intersect others
        let withinOthers: narrowed.size ≤ others.size := …
        let withIt := links.largestFrom (clique.insert candidate) narrowed best [decreasing := omega [withinOthers, fewer]]
        links.largestFrom clique others withIt
```

`f.unfold` shows `match candidates.popMin with`, and a proof matches on
it as on any other.

**2021 day 16, `readGroups`** (`Day16.sw:112-127`), with two lemmas the
day's proofs would add (`BitReader.readBitShorter`,
`readNumberShorter`; hypothetical names):

```
  match readBit: reader.readBit with
    | None => None
    | Some (more, afterMore) =>
      match readGroup: afterMore.readNumber 4 with
        | None => None
        | Some (group, after) =>
          if more then
            match readGroups after [decreasing := omega [reader.readBitShorter readBit, afterMore.readNumberShorter readGroup]] with
              | None => None
              | Some (groups, rest) => Some (NonEmptyList.cons group groups.toList, rest)
          else Some (NonEmptyList.singleton group, after)
```

**2021 day 16, `readPackets`**: its first guard (after `readGroups`)
goes the same way once `readGroups` returns a `Rest reader`. The guards
after the recursive calls are case 3: either kept (they're linear and
cheap; the day runs in 0.22 s), or removed by returning `Option (List
Packet, Rest reader)`. The guide's worked example (stage 3) shows the
second form on a smaller function.

**std's `Graph.searchFrom`** (`Search.sw:273-292`): `popped` and `found`
come out of the signature. The body is `match found: queue.popMin with`,
the calls pass the queue, and `Graph.distances` loses its `queue.popMin
rfl`.

**2021 day 12** could go back to `decreasing` from its depth bound. Not
worth a lane by itself: only if a lane is in that day anyway.

## 6. Risks

- **The equality proof for `f.unfold`.** The generator already copies
  case trees for `respects` and goes through an `if` with
  `Decidable.elimCong` (`decreasing.rs:19-23`). The new proof equates a
  dependent `match` (with the `rfl` argument) with a plain one, leaf by
  leaf, in a lemma where the scrutinee is a variable. Medium confidence
  that this reuses `respects`'s machinery; it is the part for Opus.
  Fallback, if a shape defeats it: keep today's `f.unfold` for that
  definition and give a note. The kernel would refuse a wrong proof, so
  this is a usability risk, not a soundness one.
- **Lifted `match` helpers.** A `match` lifted out of the body
  (`f.%match1`) would need a plain twin for `f.unfold` to mention. Two
  helpers per lifted `match` with a call in an arm.
- **Which `if`s.** Only an `if` or `match` with a recursive call under
  it changes, so definitions without calls in a branch keep their terms.

## 7. Decisions for Matt

- **D2870:** In a `decreasing` definition, should a `match` or an `if`
  with a recursive call under it give that call its fact automatically,
  with `f.unfold` still showing the program as written? [rec: yes. It
  removes the always-true guards from 2024 day 23 and 2021 day 16 and two
  parameters from `Graph.searchFrom`, with no new syntax and no run-time
  cost.]
- **D2871:** For a decrease that depends on the recursive call's own
  result (2021 day 16, 2020 day 19), document the result-record pattern
  in the guide now, and leave a postcondition clause (`ensures`) until a
  third day needs it? [rec: yes. Two days isn't enough to justify a new
  keyword, and the record pattern already works.]
- **D2872:** Once stages 1 and 2 land, move 2024 day 23, 2021 day 16 and
  `Graph.searchFrom` off their workarounds? [rec: yes. They're the
  evidence the feature works, and they shorten the proofs.]

I've decided the following myself: which `if`s and `match`es change
(only those with a call under them), that the hypothesis is anonymous
unless named, and the order of the stages.

## 8. Tickets to file

In order. Stages 1 and 2 touch the same generator and run one after the
other.

1. **`decreasing`: an `if`'s condition reaches the obligation, and
   `f.unfold` shows the plain `if`.** Opus (core language). 75 min. In
   `decreasing.rs` and the `if` elaboration; the equality proof is the
   new part. Updates `docs/syntax.md` (`decreasing`: the guard style
   becomes optional) and `docs/guide/07-recursion.md` (the `gcd` example's
   "the test is there to give the compiler the fact" paragraph), with
   checked snippets. Tests: `task test:one` on `decreasing`,
   `decreasing-lex`, `decreasing-omega`, `let-proof-pattern-unfold` and a
   new `examples/accept/decreasing-plain-if.sw`; the `E-DECREASING`
   reject snapshots whose note changes; `snap:hashes` and
   `hash_stability` (std terms change); extract's `bound_to_the_prelude`
   tests if a std core definition is touched. Part of SW-199 stage 3.
2. **`decreasing`: a `match`'s equation reaches the obligation, named or
   not, and doesn't appear in `f.unfold`.** Opus. 90 min. Includes the
   plain twin of lifted `match` helpers and the `in_scope` listing of §4.
   Docs as stage 1 (syntax.md's `decreasing` and `match e:` notes, the
   guide). Tests: a new `examples/accept/decreasing-match-fact.sw`
   reproducing 2021 day 12's `E-MATCH-MOTIVE` shape and 2024 day 23's
   `popMin`, now proved about; the decreasing examples above;
   `snap:hashes`, `hash_stability`. Covers SW-809's `match found:` item
   for `decreasing` definitions (ordinary definitions stay with SW-809).
3. **Guide: a recursive call's result that carries its own decrease.**
   Sonnet. 30 min. A worked example in `docs/guide/07-recursion.md` (a
   small reader returning a `Rest reader` record), as 2021 day 16's note
   asked (`aoc/NOTES-2021.md:4140`). Tests: the guide's example checks
   (`task test:one` on the guide snippets). Can run beside stages 1-2.
4. **Move 2024 day 23, 2021 day 16 and `Graph.searchFrom` onto stages 1
   and 2.** Sonnet. 60 min. After stage 2. Tests: those two days'
   `check` and `test` (targeted), `Graph`'s examples and tests,
   `snap:hashes`, `hash_stability`, `task audit:touched` for the days'
   namespaces.

Not filed: `ensures` (D2871's trigger), and 2020 day 19 off fuel, which
needs SW-199's mutual groups as well as case 3.

## What this note didn't cover

- Measures that exist only in a proof (a rank given by `∃`): the fuel
  encoding computes the measure (`decreasing.rs:16`), so it has to be a
  value. No cited day needs one: 2020 day 19 computes its rank
  (`Rules.rank`, `Day19.sw:154`).
- Mutual recursion, which is SW-199's item.
- Whether `omega` uses an equation such as `n - k = Succ j` as it stands
  (§4, to be checked in stage 2).
