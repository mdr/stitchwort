# SW-3516 review: proof tuples, lane 1

Opus paper review (SW-3517, D2364) of merge `196d60a03`: tuples that build
and take apart `∃`/`∧` proofs by the expected type
(docs/proposals/proof-tuples.md, D3631 (a), D3632). Read against `main` at
`1c4902de0`, which also has L3 (SW-3518) and L4 (SW-3519). Every probe was
run with the main checkout's release binary (`stitchwort check`); the
reproducers are below, with the output cut to the message.

## Verdict

**No soundness finding.** Nothing the lane generates is trusted: every term
is an ordinary constructor application or `match` the kernel checks, and
where the elaborator commits to a wrong reading the result is an error,
never an accepted program. The reading rules can't confuse a pair with a
proof, because `Pair`'s parameters are `Type` and `∧`'s are `Prop`. The
gaps are completeness (the postponed case was left out, as the lane said)
and messages, several of which now say something false.

Ranked:

| # | Severity | Finding | Ticket |
|---|---|---|---|
| 1 | completeness | a tuple *pattern* at an unknown of sort `Prop` commits to `Pair`, which can never be right | new |
| 2 | completeness | a tuple *expression* whose type an argument after it fixes is not postponed (§5's "subtle part", left out) | new |
| 3 | completeness | SW-3566 and SW-3526 have one root and one fix point (`check_tree`) | note on both |
| 4 | message | the `check_tree` note "with more parts than the proof has" is given for every tuple-on-`Pair` mismatch, including where the type shown *is* `∧` | new |
| 5 | message | a tuple against a known data type that isn't a pair (a record with a proof field) says "which `∃`? give the type" | new |
| 6 | message | §6's "read as a pair because nothing said what it proves" was not implemented; the mismatch shows `(_, _)` | with 1 |
| 7 | message | `patlet`'s own note still says "a tuple pattern matches a pair" | with 4 |
| 8 | message | `E-PROP-ELIM` doesn't show the tuple form (§6) | with 4 |
| 9 | coverage | the hash test never takes `patlet`'s `∧` projection path | none (checked by reading) |
| 10 | pre-existing | an unknown of sort `Prop` can be solved by a `Type` (caught later as `E-UNIVERSE`) | low, optional |

## Q1. Pair or proof?

**A pair is never read as a proof, nor the reverse, where the type is
known.** Checking dispatches on the forced expected type
(`crates/elab/src/check.rs:5965`): `Pair` goes to `pair_literal`, `∧`/`∃`
to `proof_tuple`, a universe to `tuple_type`; those are distinct data types,
so there is no overlap. Patterns pick the constructor from the column's
forced type (`crates/elab/src/lib.rs:5515-5519`, `proof_tuple` at
`lib.rs:5838`).

**Inferring** (`check.rs:9079-9110`): a first part that is a proof makes
`∧`; data then a proof is `E-CANNOT-INFER`; otherwise a pair. Both rules
rest on "a pair's parts are never proofs", which holds: `Pair (a: Type) (b:
Type)` (`std/core/Data.sw:101`) and `Prop` is not a `Type`:

```
-- p01-pair-of-proofs.sw
def ok (h: 1 = 1): Pair (1 = 1) Nat := (h, 2)
```
```
[E-UNIVERSE] expected something of type `Type`, but this has type `Prop`
```

So the inferred `∧` can't displace a pair that would have type-checked, and
`Exists (a: Type)` (`Logic.sw:36`) means a witness is never a proof either,
so "first part a proof ⇒ `∧`" can't displace an `∃`. `is_proof_type`
(`rewrite.rs:722`) answers false for a type that is still an unknown, so
such a part falls to the pair path, and a later conflict is a mismatch.

**Definitions and aliases.** The expected type is forced (`check.rs`,
`check_special`), so a `def` that unfolds to `∧` takes a tuple, in both
directions:

```
-- p03-alias.sw: checks
def Both2 (p q: Prop): Prop := p ∧ q
theorem t ∀ (p q: Prop) (a: p) (b: q): Both2 p q := (a, b)
theorem u ∀ (p q: Prop) (h: Both2 p q): q ∧ p :=
  let (a, b) := h
  (b, a)
theorem v ∀ (p q: Prop) (h: Both2 p q): q ∧ p := match h with
  | (a, b) => (b, a)
```

An `opaque` one doesn't unfold, and the message says so, as for `Both`:

```
-- p18-opaque.sw
opaque def Both2 (p q: Prop): Prop := p ∧ q
theorem t (p q: Prop) (a: p) (b: q): Both2 p q := (a, b)
```
```
[E-TYPE-MISMATCH] expected `Both2 p q`, but this has type `p ∧ q`
Note 1: `Both2` is opaque, so its body isn't used here
```

**`Prop` versus `Type` at an unknown.** This is where a wrong reading
happens (finding 1, below): a tuple pattern whose column is an unknown is
read as a pair even when that unknown has sort `Prop`.

## Q2. The postponed case

L1 did not postpone (its notes say so): a tuple checked against an unknown
falls through to inference. **That is sound**: the inferred type is
unified with the unknown, so a later refinement to something else is a
mismatch, never a different term. **It is incomplete** where the unknown is
fixed by an argument *after* the tuple. Where the application's result type
fixes it, it already works, because the result is compared first:

```
-- p05-prop-poly.sw: checks
def idp [p: Prop] (x: p): p := x
theorem a1 ∀ (p q: Prop) (a: p) (b: q): p ∧ q := idp (a, b)
theorem a2 ∀ (h: 7 * 7 = 49): ∃ (n: Nat) => n * n = 49 := idp (7, h)
```

```
-- p13-postponed.sw
def takeFirst [p: Prop] (x: p) (k: p → 1 = 1): 1 = 1 := k x
theorem e1 ∀ (h: 7 * 7 = 49): 1 = 1 :=
  takeFirst (7, h) ((w: ∃ (n: Nat) => n * n = 49) => byComputing)
theorem e2: 1 = 1 :=
  takeFirst (7, byComputing) ((w: ∃ (n: Nat) => n * n = 49) => byComputing)
theorem a1 ∀ (a: 1 = 1) (b: 2 = 2): 1 = 1 :=
  takeFirst (a, b) ((w: 1 = 1 ∧ 2 = 2) => byComputing)
theorem a2 ∀ (a: 1 = 1): 1 = 1 :=
  takeFirst (a, byComputing) ((w: 1 = 1 ∧ 2 = 2) => byComputing)
```
```
e1: [E-CANNOT-INFER] can't tell which statement this tuple proves
e2: [E-CANNOT-INFER] can't work out what `byComputing` proves here
a1: checks
a2: [E-CANNOT-INFER] can't work out what `byComputing` proves here
```

`apply_args_with` (`check.rs:3440-3460`) already holds back a lambda whose
parameter type is unknown, and retries an argument that fails in place
after comparing the result type; neither covers "fixed by a later
argument" for a tuple. Adding tuple arguments whose parameter type is an
unknown to the lambda's rule (check them after the later arguments) would
cover e1, e2 and a2. The proposal (§5) expected this; it is rare in
practice (most tuples are checked where the goal is known), so it can wait
until a day's friction asks for it.

**Inside the chain** (`check.rs:6198-6229`): when the rest of the goal
forces to an unknown, `E-TUPLE-PARTS` is skipped (`check.rs:6215`) and the
rest is checked against the unknown, which infers. Sound for the same
reason.

## Q3. The terms

`proof_tuple` builds `Term::ctor(d, 0, [first, rest])` from the inside out
(`check.rs:6248-6250`); `pair_literal` builds pairs the same way
(`check.rs:6274-6279`), and `And` and `Exists` each have one constructor,
`Both`/`Witness` at index 0 (`Logic.sw:18`, `:36-37`). The witness is
evaluated before the proof part is checked against `p witness`
(`check.rs:6202-6208`), exactly the constructor's field type. Inferred `∧`
is annotated with its type (`check.rs:9093-9094`), so the kernel needs no
expected type for it. Patterns use constructor 0 of the forced type
(`lib.rs:5517`), and `patlet` projects `∧` through `And.left`/`And.right`
as `let Both a b` does (`patlet.rs:288-306`).

Nothing is left to the kernel that the elaborator assumed beyond what the
written constructor assumes: the kernel checks these terms as it would
`Both a b`. `crates/driver/tests/library/hash_stability.rs:421`
(`proof_tuples_hash_as_witness_and_both`) compares 13 declarations with
their constructor forms. **Gap (finding 9):** every one of them has a
proposition as its goal, and `patlet::applies` declines a proposition goal
(`patlet.rs:148-166`), so the new `∧` projection branch of `destructure`
(`patlet.rs:288-306`) is never hashed. By reading it does what the `Ctor`
branch does (same accessors, same wildcard skip), and both forms check:

```
-- p15-hash-tuple.sw (and p15-hash-ctor.sw with `let Both a _ := h`): both check
def dataGoal (p q: Prop) (h: p ∧ q) (n: Nat): Nat :=
  let (a, _) := h
  n
```

A one-line addition to that test would close it; not worth a ticket of its
own (fold it into finding 4's lane).

## Q4. Patterns

Right: the tail binds the rest, dependent parts see the bound witness, a
witness that is itself a pair nests on the left, and `∃` into data is
refused exactly as `Witness` is:

```
-- p17-dependent.sw: checks
theorem dep (pred: Nat → Prop) (h: ∃ (n: Nat) => pred n ∧ n = 3): pred 3 := match h with
  | (n, p, e) => rewrite <- e then p

-- p16-pair-witness.sw: `good` checks; `flat` is the misreading a user would make
theorem good (h: ∃ (x: (Nat, Nat)) => x.fst = 1): ∃ (y: (Nat, Nat)) => y.fst = 1 := match h with
  | ((a, b), e) => ((a, b), e)
theorem flat (h: ∃ (x: (Nat, Nat)) => x.fst = 1): 1 = 1 := match h with
  | (a, b, e) => byComputing
```
```
flat: [E-TYPE-MISMATCH] these patterns match a `Pair`, but the argument has type `a.fst = 1`
```

```
-- p09-exists-into-data.sw: both give the same E-PROP-ELIM
def viaTuple (h: ∃ (n: Nat) => n > 2): Nat :=
  let (n, _) := h
  n
def viaWitness (h: ∃ (n: Nat) => n > 2): Nat :=
  let Witness n _ := h
  n
```

`patlet`'s `∃` fallback is sound: `opens_exists` (`patlet.rs:171`) is only
a shortcut, and when it misses (a non-variable scrutinee, a record
pattern), `destructure` returns false on meeting `∃`, `check_let` restores
its snapshot (`patlet.rs:238`) and `check_match` matches instead
(`matching.rs:392-396`).

### Finding 1: a tuple pattern at an unknown of sort `Prop` becomes a pair

`check_tree`, meeting a constructor pattern on a variable whose type is an
unknown, unifies that unknown with the constructor's type
(`lib.rs:6863-6872`); for a tuple that is always `Pair`, since the column
type was unknown when the pattern was compiled. `patlet::destructure` does
the same (`patlet.rs:310-321`). When the unknown has sort `Prop`, `Pair` is
impossible, yet it is committed:

```
-- p10-lambda-prop-meta.sw
def applyP [p q: Prop] (f: p → q) (x: p): q := f x
theorem t1 ∀ (p q: Prop) (h: p ∧ q): q := applyP ((a, b) => b) h
theorem t2 ∀ (p q: Prop) (h: p ∧ q): q := applyP (match | (a, b) => b) h
theorem t3 ∀ (p q: Prop) (h: p ∧ q): q := applyP (x => x.right) h
```
```
t1: [E-TYPE-MISMATCH] expected `(_, _q)`, but this has type `p ∧ q`
    Note: `_q` is `applyP`'s implicit `q`, not worked out
t2: the same
t3: checks
```

**Suggested fix:** in both places, when the unknown's own type is `Prop`,
don't unify it with `Pair`; fail in place instead. `apply_args_with` then
checks the lambda again after `h` (its rule for a lambda that fails in
place, `check.rs:3446-3452`), by which time the column is `p ∧ q` and the
tuple reads as `Both`. Where nothing later fixes it, the error should be
§6's "read as a pair because nothing said what it proves; give the
parameter's type" (finding 6), not `expected (_, _q)`.

## Q5. Messages

### Finding 4: the `check_tree` note is false in most of the cases it is given

`lib.rs:6905-6912` adds "with more parts than the proof has, the last ones
meet a part that is none of these" to *every* mismatch of a `Pair` split.
That is right only for a surplus part (p16 `flat` above). It is also given
for a two-part tuple on `∨`, on a test fact (SW-3526), and on SW-3566's
shape, where the type it prints *is* `∧`:

```
-- p20-pattern-neither.sw
theorem orP (p q: Prop) (h: p ∨ q): q ∨ p := match h with
  | (a, b) => Inl b
```
```
[E-TYPE-MISMATCH] these patterns match a `Pair`, but the argument has type `p ∨ q`
Note: a tuple pattern opens a pair, a proof of `∧` or a proof of `∃`; with more
parts than the proof has, the last ones meet a part that is none of these
```

```
-- p06-multi-column.sw (SW-3566)
def P: Bool → Prop
  | True => 1 = 1 ∧ 2 = 2
  | False => 3 = 3
theorem t ∀ (b: Bool) (h: P b): 1 = 1 := match b, h with
  | True, (x, _) => x
  | False, _ => byComputing
```
```
[E-TYPE-MISMATCH] these patterns match a `Pair`, but the argument has type `1 = 1 ∧ 2 = 2`
Note: a tuple pattern opens a pair, a proof of `∧` or a proof of `∃`; ...none of these
```

**Suggested fix:** split the note by what the argument's type is: `∧`/`∃`
(the column's type wasn't known when the pattern was read: write
`Both`/`Witness` here, until SW-3566); `∨` or another type with several
constructors (split it with its constructors, `Inl`/`Inr`); a test fact
(until SW-3526); the surplus note only when the tuple sits inside a
proof-tuple split.

### Finding 7: `patlet`'s note was not updated

```
-- p20-pattern-neither.sw
theorem iffP (p: Prop) (h: p ↔ p): p → p :=
  let (f, _) := h
  f
```
```
[E-TYPE-MISMATCH] expected `p ↔ p`, but this has type `(_, _)`
Note: a tuple pattern matches a pair
```

`patlet.rs:321`. It should list the three readings as `check_tree` does
(and, for `↔`, which is a record, point at `{ forward, backward }`).

### Finding 5: "which `∃`?" where the type is known

A tuple checked against a known data type that is none of `Pair`/`∧`/`∃`
falls through to inference, whose `∃` message then asks for a type that is
right there:

```
-- p22-record-with-proof.sw
type Pos = { n: Nat, pos: n > 0 }
def one (h: 1 > 0): Pos := (1, h)
```
```
[E-CANNOT-INFER] can't tell which statement this tuple proves
  a value and then a proof: a proof of an `∃`, but of which one?
Note: a witness and a proof fit many `∃` statements: give the type, ...
```

Before L1 this was an `E-UNIVERSE` (a pair of a proof), also poor. With
the expected type known, the message should be a mismatch that says a
tuple builds a pair or an `∃`/`∧` proof, and for a record, to write the
record literal (`{ n = 1, pos = h }`). The same fallthrough gives `(a, b)`
against `p ∨ q` "expected `p ∨ q`, but this has type `p ∧ q`" (p19 `orT`),
which is fair, and could name `Inl`/`Inr`.

### Finding 8: `E-PROP-ELIM` doesn't show the tuple form

§6 asked for it; p09 above shows the note unchanged. Small.

### Messages that are right

`E-TUPLE-PARTS`, the last-part note and the inferred-`∃` message match §6
(their reject examples are in the diff). Too many parts in a *pattern*
gets the mismatch rather than a count; SW-3518 left that out on purpose.

## Finding 3: SW-3566 and SW-3526 share a root

Both are a tuple pattern compiled as `Pair` because the column's type, at
compile time, isn't yet `∧`/`∃`:

- **SW-3566**: `compile` carries the later columns' types unchanged into a
  branch (`lib.rs:4888-4893`), so `h: P b` is still `P b` when `(x, _)` is
  read; `check_tree` sees `1 = 1 ∧ 2 = 2` (p06's message shows it).
- **SW-3526**: the column is `(a && b) = True`; `read_case` (`lib.rs:6756`)
  could read it as `∧`, but it only runs for a split whose data type has a
  reading (`readable_data`, `lib.rs:6767`), and `Pair` has none.

Both fail at the same place, the mismatch arm of `Tree::Case` in
`check_tree` (`lib.rs:6880-6915`), where the real type is known. So one
mechanism fixes both: mark a `Case` built from tuple syntax (not from a
written `MkPair`), and in `check_tree`, when the argument's type is `∧` or
`∃` (SW-3566), or a test fact whose reading is one (SW-3526), retarget the
split to that type. `Pair`, `And` and `Exists` each have one constructor
with two fields, so the tree's shape, its exhaustiveness and its bound
names are unchanged; nested tuples under it were compiled with unknown
field types and so are `Pair` cases too, retargeted the same way when
reached. (A number pattern in a witness position was compiled for an
unknown type and defaults to `Nat`; an `Int` witness would need care.)
The meta branch of the same `match` (`lib.rs:6863`) is finding 1's place.

**Recommendation:** one Opus lane for SW-3566 + SW-3526 + finding 1, or
SW-3566 first and SW-3526 built on its marker; two lanes in parallel would
both edit `check_tree`'s `Case` arm.

## Finding 10 (pre-existing, low)

An unknown of sort `Prop` is solved with a `Type` (p10's `_q` is
`applyP`'s `q: Prop` set to `Pair`'s second parameter). It is caught at the
application, as `E-UNIVERSE`, with or without tuples:

```
-- p12b-ill-sorted-meta-written.sw
def applyP [p q: Prop] (f: p → q) (x: p): q := f x
def bad: Nat := applyP (match | MkPair a b => b) (MkPair 1 2)
```
```
[E-UNIVERSE] expected something of type `Prop`, but this has type `Type`
```

Not a soundness hole (the application's type check and the kernel both
refuse it), and finding 1's fix removes the tuple route to it.

## Tickets to file

1. **[Opus]** Proof tuples: a tuple pattern whose column type is an unknown
   of sort `Prop` unifies it with `Pair` (`lib.rs:6863`, `patlet.rs:310`);
   fail in place so the lambda is retried after later arguments, and give
   §6's "read as a pair because nothing said what it proves" otherwise.
   Repro p10. Best with SW-3566 (finding 3).
2. **[Sonnet]** Proof tuples: postpone a tuple argument whose parameter
   type is an unknown until after the later arguments, as a lambda is
   (`check.rs:3440`). Repro p13 (e1, e2, a2). Low priority.
3. **[DeepSeek]** Proof tuples messages: split `check_tree`'s Pair note
   (`lib.rs:6905`) by the argument's type (∧/∃ not known yet, ∨,
   test fact, surplus part); update `patlet.rs:321`'s note; a tuple against
   a known non-pair data type is a mismatch, not "which `∃`?"
   (`check.rs:9098`; record: suggest the literal); `E-PROP-ELIM`'s note
   shows the tuple form; add `dataGoal` (p15) to
   `proof_tuples_hash_as_witness_and_both`. Repros p20, p06, p22, p09, p15.
4. Notes on **SW-3566** and **SW-3526**: finding 3 (one root, one fix point
   in `check_tree`'s `Case` arm; don't run them as parallel lanes).

Probes: `/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw3517/p*.sw`
(not kept; every one is quoted above).
