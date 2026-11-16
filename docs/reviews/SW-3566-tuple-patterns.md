# SW-3566 review: tuple patterns retargeted in `check_tree`

SW-3670, Opus paper lane, 16 Nov 2026. Reviews merge `880f0dadd` (lane
commit `942c8089e`): a split written with a tuple is marked
(`Tree::Case { tuple: true }`) and retargeted to `∧`/`∃`, or to a test
fact's reading, when `check_tree` finds the column's real type; at an
unknown proposition it fails in place, and `lambda_arg` holds such a lambda
until the later arguments are checked. This implements finding 3 (and
finding 1) of `SW-3516-proof-tuples-l1.md`.

Probes ran against the main checkout's release binary, built at 20:37
after the merge. Line numbers are at `aaeb90144`.

## Verdict

**Sound.** No probe got the kernel to accept a term it shouldn't. The
retarget only ever picks the data type the column's own type has, after
`force`, so the `Case` it builds checks in the kernel or fails there. The
terms are the ones `Both`/`Witness` give. Four findings, none of them
unsound: one accepts source it should refuse (medium), and three are gaps or
rough messages (low).

| # | Severity | What |
|---|---|---|
| 1 | medium | A written `MkPair` in a later row is read as `Both`, depending on row order |
| 2 | low | A nested lambda over an unknown `Prop` still commits to `Pair`: `prop_unknown` relies on optional meta types |
| 3 | low | A tuple row followed by a written `Both` row is refused |
| 4 | low | Fields left unnamed show as `fst✝`/`snd✝`, and a test fact the tuple can't take apart gets "match a `Pair`" instead of `Both`'s reading message |

## Q1. Can a marked split become the wrong constructor?

The retarget (`lib.rs:6909-6917`) switches only when the forced column
type is `Value::Data(d2)` with `d2` `∧` or `∃` (`proof_data`,
`lib.rs:6837`). `Pair`, `And` and `Exists` each have one constructor with
two fields (`core/Data.sw:101`, `core/Logic.sw:18,36`), so the branch list
lines up. The kernel checks the `Case` against the real type in any case.
The cases the brief named:

- **A type that is `∧` only after more splitting** (`P b` with `b` not yet
  split, or the tuple column split first): the type is stuck, so it is not
  `Data`, there is no switch, and you get the old `E-TYPE-MISMATCH`.
  Refused, as it should be.
- **A user type with one constructor and two fields**: `type MyAnd (p q:
  Prop): Prop = | MkMy …` and a data `type Two = | MkTwo (a: Nat) (b:
  Nat)`, each reached through a refined column, are both refused ("match a
  `Pair`, but the argument has type `MyAnd …`"). `proof_data` names only
  the builtins. Right.
- **Aliases**: `def Both2 (p q: Prop): Prop := p ∧ q` reached through
  `P True` is accepted. `force` unfolds it to `∧`. Right.
- **`opaque` defs**: `opaque def OP: Bool → Prop` is refused: `force`
  doesn't open it, as `Both` wouldn't either.
- **Through an earlier arm's refinement**: an indexed family (`type Is:
  Nat → Prop = | IsOne: Is 1`, then `match i, h with | IsOne, (_, s) =>
  s` with `h: Q n`) is accepted, the same as the `Both` version. The
  refined `cx.types` is what `check_tree` forces.
- **Compiled as `∧`/`∃` but meeting the other one**: this can't happen. A
  column whose type is already `Data(And|Exists)` at compile time is still
  that head after substitution.
- **Number patterns in a witness**: `(-1, _)` on `∃ (n: Int) => …` through
  a refined column is accepted. A non-negative number pattern there would
  be compiled for `Nat` (the column's field types are unknown at compile
  time) and refused by `NumCase`'s check. That is a refusal, not a wrong
  term; L1 already noted it.

The one wrong constructor comes from the marker's scope, not from the
switch. The marker is taken from whichever row first splits the column,
and every other row that reaches that split is retargeted with it:

### Finding 1 (medium): a written `MkPair` is read as `Both`, depending on row order

`lib.rs:4844` sets `tuple` from the first splitting row's pattern alone.
At specialisation (`lib.rs:4912-4948`), a later row written `MkPair a b`
has the same data (`Pair`), so it joins the split. `check_tree` then
retargets the whole split, `MkPair` row included:

```
def P: Bool → Prop
  | True => 1 = 1 ∧ 2 = 2
  | False => 3 = 3

theorem mixed (b c: Bool) (h: P b): 2 = 2 := match b, h, c with
  | True, (_, x), True => x
  | True, MkPair _ y, False => y      -- accepted: `MkPair` on a proof of ∧
  | False, _, _ => byComputing
```

`checked`. With the two `True` rows swapped, the `MkPair` row splits first,
`tuple` is false, and you get `E-TYPE-MISMATCH` ("these patterns match a
`Pair`, but the argument has type `1 = 1 ∧ 2 = 2`"). The term is `Both`'s,
so this isn't unsound. But `MkPair` written on a proof is accepted, and the
order of the arms decides whether it is. L1's finding 3 said the mark
should come from tuple syntax, "not from a written `MkPair`".

**Fix:** mark the split only if every row that splits this column wrote a
tuple. A row with a written `MkPair` clears `tuple`, so the split stays a
`Pair` one and `check_tree` refuses it whatever the order. (Carry an
`all_tuples` flag through the specialisation loop and set `tuple` from it.
The loop runs before `Tree::Case` is built at `lib.rs:5048`.) Test: the
program above, in `examples/reject/`.

## Q2. The terms

After the switch, the `Case` arm builds `Term::Case(x, d, branches)` with
`d` the switched data, exactly as for a written `Both`/`Witness`. The
branches' field types come from the switched `data.ctors()`, and the
subtrees are untouched. `read_case` builds the same `Tree::Case` (now
`tuple: false`, with `d` the reading's data) that a `Both` split builds,
around the same `found.forward` term. The hold path in `lambda_arg` puts
the lambda's own checked term back through `fill_placeholder` (as
`explicit_arg`'s postponed path does), so the application term is the one
an in-place check would give.

**Hash test coverage** (`hash_stability.rs:435-443`): `later` (match,
later column, `∧`), `testFact` (match on a test fact read as `∧`) and
`unknown` (lambda over an unknown `Prop`, `∧`) are compared line by line
with their constructor forms. Not compared with a constructor form,
only snapshotted:

- the `∃` retarget through a later column (`boundedBelow` in
  `proof-tuple-later-column.sw`, three deep: `∃` then `∧`);
- a test fact read as `∃`. This one is accepted: `let (n, p) := h` with
  `h: xs.any (n => n == 3) = True`;
- the `let` form of a test fact (`leftTrue`, through `patlet`'s fallback
  to the match);
- the `match | …` clause-lambda form (`viaClause`).

The code path is shared (`proof_data` returns whichever of the two it
finds), so I expect these to match. Still, adding `boundedBelow`, an `∃`
reading and `leftTrue` to the tuple/constructor pair costs three lines
each and would pin it. Small, for the follow-up ticket.

## Q3. `read_case` on a marked split

The gate is now `tuple || readable_data(d)` (`lib.rs:6779`). For a marked
split, `d` is `Pair`, so the first arm (reading's data `== d`) never
matches. The second arm takes a reading that forces to `∧`/`∃` and sets
`d` to it. Anything else returns `None` and falls to the mismatch.
Probes:

| Fact | `Both`/`Witness` | tuple |
|---|---|---|
| `(a && b) = True` (`∧`) | accepted | accepted (`let` and `match`) |
| `(a \|\| b) = False` (`∧`) | accepted | accepted |
| `(a && b && c) = True`, `(_, _, z)` | — | accepted (the nested split reads again) |
| `xs.any … = True` (`∃`) | accepted | accepted (`let` and `match`) |
| `(a && b) = False` (`∨`) | refused, `E-NO-READING` | refused, `E-TYPE-MISMATCH` |
| a test fact in a later column (`F xs a b`, `∧` once `xs` is a cons) | accepted | accepted |

So it takes apart exactly what `Both`/`Witness` take apart and refuses
the rest. Only the message differs (finding 4). The `cx.level() != depth`
gate is shared with `Both`, unchanged.

## Q4. `lambda_arg`'s hold and recheck

`check.rs:3882-3903`. It runs only when `late_able` is false (no expected
type, or a later parameter's type depends on the lambda). There must be a
later explicit or piped argument, no later parameter type may depend on
this one except through lambdas, and the domain's parameter must be a
`prop_unknown`. Then a non-fatal `E-CANNOT-INFER` from the in-place check
restores the snapshot and pushes the lambda onto `held.postponed`, which
`finish_application` checks once, after all the arguments
(`check.rs:4316`).

- **Loops:** none. Each postponed entry is checked once, and its error is
  returned. Nested, each level is checked at most twice per check of its
  parent, so `n` nested lambdas over unknown props cost up to 2^n checks.
  That's the same shape as SW-2638, but it only happens where the first
  check failed. I see no practical risk, and I didn't build a deep case.
- **Overload or instance choice:** the hold only replaces what used to be
  `return Err(e)` (the in-place error went straight up). So it turns a
  failure into a success; it can't change a success. Something above that
  tries alternatives on failure could now take the first alternative where
  it took another before. I found no such caller on this path:
  `retrying` reruns the same application with late literals, and
  `settle_retried` reruns the same declaration. I have no reproducer. The
  error it catches is any non-fatal `E-CANNOT-INFER` in the lambda, not
  only the tuple's. That is broader than the comment says, but harmless: the
  recheck sees more, and if it still fails, its error is reported.
- **Interaction with the existing retry:** with an expected type,
  `late_able` holds and the old after-expected path runs, unchanged. That
  path already rechecks after every argument. The two don't overlap.
  `retrying` reruns the whole application, holds included.
- **Accepts what fails without it:** only what checks once the later
  arguments are in, and the lambda's term is still checked against the
  same domain. Probed: `applyP ((_, b) => b) h`, the clause form, an `∃`
  (`applyP ((n, e) => (n, e)) h`), two lambdas (`flipP ((a, _) => _ => a)
  k h`), a lambda whose later argument is itself an application with a
  held lambda, and a partial application `applyP ((_, b) => b)` against
  `(p ∧ q) → q`. All are accepted. With a `_` as the later argument,
  `E-CANNOT-INFER` ("can't tell which proof this tuple takes apart") is
  reported at the tuple, as intended.

### Finding 2 (low): a lambda nested in a lambda still commits to `Pair`

```
def applyP [p q: Prop] (f: p → q) (x: p): q := f x
theorem inner (p q: Prop) (h: p ∧ q): q := applyP (x => applyP ((_, b) => b) x) h
```

You get `E-TYPE-MISMATCH` at `h`: "expected `(_, _q)`, but this has type
`p ∧ q`". That is L1's finding 1 message, so a `Prop`-sorted unknown was
still unified with `Pair`. The same program with `Both _ b`, with `let (_,
b) := x`, or with `match x with | (_, b) => b` is accepted.

**Cause (from reading the code, not traced):** `prop_unknown`
(`lib.rs:6850`) asks the meta's recorded type, which is optional ("may be
missing", `state/metas.rs:34-39`). When the inner `?p'` (in scope of `x`)
is unified with the outer `?p`, pruning makes a fresh meta with no type
(`unify.rs:3257`). `prop_unknown` then says no, and the meta arm of
`check_tree` (`lib.rs:6935`) unifies a `Prop` unknown with `Pair ?a ?b`, a
`Type`. The kernel would refuse anything built on that, so it isn't
unsound, but it is the same wrong commitment L1 finding 1 was about.

**Fix (either):** give the pruned meta the pruned one's type where its
spine is a prefix of the old one's (cheap, and it helps SW-919's check
too). Or have the tuple branch of `check_tree` decide "proposition or not"
from the sort of `cx.types[x]` as the variable was bound (the lambda's
domain), not from the meta store. Test: the program above, in
`examples/accept/proof-tuple-prop-unknown.sw`.

## Q5. Anything accepted that shouldn't be

Only finding 1. Nothing gets a term past the kernel that it shouldn't
accept. Every retargeted `Case` names the data the column's type
actually has. A `Prop`-sorted unknown wrongly unified with `Pair` (finding
2) ends in a mismatch or `E-UNIVERSE`. I tried `applyP ((a, _) => a) (1,
2)` at `Nat`, and it is refused with `E-UNIVERSE`.

### Finding 3 (low): a tuple row followed by `Both` is refused

```
theorem mixed3 (b c: Bool) (h: P b): 2 = 2 := match b, h, c with
  | True, (_, x), True => x
  | True, Both _ y, False => y
  | False, _, _ => byComputing
```

You get `E-TYPE-MISMATCH`: "this pattern is an `And`, but other patterns
here are `Pair`" (`lib.rs:4918`). With the `Both` row first, the tuple row
is compiled as `Pair` against the stale type and refused in the same way.
Mixing the two spellings in one column is unusual, so this is low. The fix
is the other half of finding 1's: if a later row in a tuple-marked `Pair`
split names `And`/`Exists`, adopt that data for the split at compile time.
If a row names `Pair`, drop the mark.

### Finding 4 (low): messages and names after a retarget

- **Names:** a field left as `_` takes `Pair`'s field name
  (`lib.rs:5044`), so the arm's goal shows `fst✝: 1 = 1`, `snd✝: 2 = 2`.
  With `Both _ _` it shows `left✝`/`right✝`. Fix: in `check_tree`, when
  `switched` is `Some`, replace names that came from the default with the
  new constructor's field names. This needs the compiler to record which
  names were defaulted, or it can compare each name with `Pair`'s field
  name. The hashes are unaffected.
- **A test fact with no `∧`/`∃` reading:** `let (x, _) := h` with
  `h: (a && b) = False` says "these patterns match a `Pair`, but the
  argument has type `(a && b) = False`". `Both` says `E-NO-READING` and
  shows the reading (`a = False ∨ b = False`, `Bool.andReadsFalse`).
  `read_case`'s `_ if tuple => return Ok(None)` (`lib.rs:6798`) throws
  away the read result that would explain it. Fix: when the read is
  `Found` but isn't `∧`/`∃` (or there is no reading), report `no_reading`
  with "taken apart with a tuple". SW-3664 (tuple messages, DeepSeek) is
  the natural home.

## Tickets to file

1. **[Sonnet]** Tuple split marker: set `tuple` only when every row
   splitting the column wrote a tuple, and adopt a written `Both`/`Witness`
   in a marked split (findings 1 and 3). Reproducers above, as one reject
   and one accept example.
2. **[Opus or Sonnet]** `prop_unknown` misses pruned metas: the nested
   lambda `applyP (x => applyP ((_, b) => b) x) h` (finding 2). It touches
   the unifier's pruning or `check_tree`'s sort test.
3. **[DeepSeek, with SW-3664]** Retargeted field names (`fst✝` to
   `left✝`), and `E-NO-READING` for a tuple on a test fact with no `∧`/`∃`
   reading (finding 4), plus three more tuple/constructor lines in
   `proof_tuples_hash_as_witness_and_both` (Q2).
