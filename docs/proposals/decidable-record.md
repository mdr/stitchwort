# `Decidable` as a `Bool` with its two proofs (SW-2703)

**Status:** draft 1, 10 November 2026. Design only; nothing built. Follows
D3480 (bool-and-prop.md §7.2). Open decisions: D3483 to D3485
([§6](#6-decisions-for-matt)). Code read at `f55b2381b`. Migration cost is
not counted (D2303).

How claims are marked:

- **[measured]**: run today with the release CLI (built 14:18, 10 November)
  on the probes in [decidable-record/](decidable-record/), or counted with
  `grep` at that commit;
- **[checked]**: read in the code, at the file and line given;
- **[inferred]**: my reasoning; not run.

## 1. The problem, and the change

Today a decision is `Yes (proof) | No (refutation)`
(`std/core/Decidable.sw:11`). Its `Bool` is stuck until the decision is a
constructor, so an `if h: p` and an `if p` are different terms that nothing
computes together (SW-1688; bool-and-prop.md §2.3). The elaborator works
round this in a dozen places (§2), and the kernel computes every proof
inside a decision when it checks one.

The change is D3480's: a decision is a record of the test and two proofs.

```
type Decidable (p: Prop) = {
  does: Bool,
  sound: does = True → p,
  complete: p → does = True
}
```

What it should do:

- every `if`, `&&`, `==` and `filter` on a decidable proposition is its test,
  by computation, whether or not a branch uses the proof (measured, §3.1);
- the kernel runs only the test when it checks `auto` and `byDecision`:
  membership in a 300-element list checks in 0.5 s, against 2.2 s today
  (10.4 s through `byDecision`) **[measured, `membership.sw`,
  `membership-today.sw`]**;
- at run time a decision is just its `Bool` (§4.1);
- the elaborator code that chooses between the two forms of `if` goes
  (about 400 lines in `check.rs` and `logic.rs`, and the `if` half of
  `decreasing/plain.rs`, §5.1), and so does one kernel native.

## 2. The type

### 2.1 Field names

`test` would read best but is a keyword. Candidates, read in the places a
user meets them (an instance, a hover, a goal not yet folded):

| Name | Instance | Use | Note |
|---|---|---|---|
| `does` | `{ does = Nat.leq m n, … }` | `d.does` | Agda's name ("does it hold?"); not a noun |
| `holds` | `{ holds = Nat.leq m n, … }` | `d.holds` | everyday; says what the `Bool` means |
| `answer` | `{ answer = Nat.leq m n, … }` | `d.answer` | a noun; less clear in `sound: answer = True → p` |

Few users will write it: `if`, `&&`, `==` and `auto` hide it, and goals print
the proposition. Instance authors and std see it. This is D3483. The rest of
this note writes `does`.

### 2.2 Two proof fields, not one `reflects`

Agda's `Dec` is `does: Bool` with `proof: Reflects P does`, an inductive
family `ofʸ: P → Reflects P true | ofⁿ: ¬P → Reflects P false`
(bool-and-prop.md, A2). Matching on `proof` refines `does` at once.

Stitchwort gets that refinement without the family: `match e: d.does with
| True => d.sound e | False => d.refute e` does the same job, and
`Decidable.refute: d.does = False → ¬p` is a one-line theorem from
`complete` (measured, `one-if.sw`). Against `Reflects`:

- Building an instance for a test is `sound = h => h, complete = h => h`
  (measured), with no family to construct;
- `Reflects` would be a two-constructor proposition, which can only be
  matched in proofs (`E-PROP-ELIM`), so a program's `if h:` still goes
  through a theorem to get `p`;
- one family fewer in std core and in what the kernel validators recognise
  (§2.4).

So `sound` and `complete`, as D3480 says. A `Decidable.reflect` view is
easy to add later if a proof wants it **[inferred]**.

### 2.3 Universe and erasure

`Decidable p: Type` for `p: Prop`. The proof fields are erased (their types
are propositions), so the record has one run-time field. The fast runtime
stores such a record as that field, unboxed (`Data::unboxed_field`,
`core/src/globals.rs:553`; `rt/src/lower.rs:221`) **[checked]**: a decision
is a `Bool` at run time, as it is a tag today. The JS backend unboxes a
one-field record only when it is marked `@[js.unboxed]`, which refuses type
parameters today (`examples/reject/attribute-unboxed-parameterised.sw`); §4.1.

The type has record eta (one constructor, not in `Prop`, not recursive, a
non-proof field; `docs/core.md`, "Record eta"), and proof fields are skipped
in comparison. So two decisions with the same test are equal by `rfl`,
however their proofs were written **[measured, `sameDecision`]**. Instances
that agree are interchangeable, and `auto` never has to care which one it
found.

### 2.4 Constructors and helpers

All measured in `one-if.sw` as a library type:

```
theorem Decidable.refute (d: Decidable p) (e: d.does = False): ¬p
def Decidable.yes (h: p): Decidable p := { does = True, sound = e => h, complete = x => rfl }
def Decidable.no (r: ¬p): Decidable p := { does = False, … }
def Decidable.map (d: Decidable p) (e: p ↔ q): Decidable q :=
  { does = d.does, sound = h => e.forward (d.sound h), complete = h => d.complete (e.backward h) }
def Decidable.elim (d: Decidable p) (yes: p → a) (no: ¬p → a): a  -- by a match on d.does
theorem Decidable.elimProof …                                       -- the same at a Prop result
def Decidable.and / or / not / andThen                              -- does = the Bool &&, ||, not
```

`map` keeps the `Bool`, so a decision moved along an `↔` still computes to
the same test. `yes` and `no` are for decisions whose answer is known; an
instance whose `Bool` should compute with unknowns is written test first,
`{ does = <test>, … }`, not `if h: … then yes … else no …` (whose `does` is
stuck on the `if`) **[inferred from eta and projection rules,
`docs/core.md`, "Projection"]**.

## 3. What a user writes

### 3.1 `if h:` and the plain `if`

The surface doesn't change: `if h: a ≤ b then … else …` and `if a ≤ b`.
What changes is that they are one term. Measured in `one-if.sw`:

- `Decidable.elim (decLe a b) (h => x) (r => y) = Bool.ifThenElse (Nat.leq a b) (u => x) (u => y)`
  by `rfl` (`elimIsPlainIf`): once `elim` unfolds, both are case trees
  stuck on `Nat.leq a b`, and they compare equal. So `Bool.ifThenElse`
  can keep its `Unit` thunks;
- a function written with an `if h:` equals one written with a plain `if`
  by `rfl` (`sameFunction`);
- a hypothesis `h: b ≤ a` rewrites the `if h:` (`safeSubLe`), and
  `match h: Nat.leq 1 n` splits one whose branch passes the proof on to a
  function that needs it (`gLe`).

The one thing found: the split finds `Nat.leq b a` only if the term holds
it in place. A body that calls `Decidable.elim (decLe b a)` without
unfolding hid it (`W-MATCH-NOT-FOUND`); the same body with the instance's
`does` written in (`safeSub2Split`) splits. So the elaborator writes the
instance's `does` directly, as `bind.rs:212` already does for comparisons
(§2.5, item 3).

### 3.2 A `match` on a decision

Today: `match Nat.decLessThan 9 value with | Yes h => … | No r => …`
(66 `Yes` arms in `aoc/`, 77 in std; §5.2). A record has no constructors to
match, so this goes. Written instead:

```
if h: 9 < value then … else …               -- h: 9 < value, or ¬(9 < value)
match h: 9 < value with | True => … | False => …   -- h: the test's equation
```

Both refine the program's `if`, written either way (§3.1). How the `False`
arm's `h` prints, and whether `match h: p` gives `h: p` and `h: ¬p` in its
arms, is the reader SW-2704 designs (D3482); this note needs only that the
scrutinee is the decision's `does`. D3485 asks to drop the `Yes`/`No`
patterns.

### 3.3 `auto` and `byDecision`

The surface doesn't change. `auto` writes `d.sound rfl`, and the kernel
checks `rfl: d.does = True`, which runs the test only
(`Dec.decide (decLt 3 5) rfl`, and a 30-digit equation, measured in
`one-if.sw`). Today it writes `Decidable.fromYes d Trivial`, whose check
computes the decision with its proofs. `Decidable.IsYes` and `fromYes` go.

### 3.4 An instance for a new type

```
def Colour.decEq (x y: Colour): Decidable (x = y) :=
  { does = Colour.same x y, sound = Colour.sameSound x y, complete = h => rewrite h in Colour.sameRefl y }
```

The test is an ordinary function, and `x == y` computes to it with the
colours unknown (`eqIsSame`, measured in `instance.sw`). The proofs are a
`match` each. `deriving (DecEq)` would write the same three parts
(§5.3).

## 4. Risks

### 4.1 Performance

- **Run time.** In the fast runtime a decision is its `Bool`, as above, the
  same as a tag. The simplifier's rules for `toBool (decTrue b)`
  (`rt/src/opt.rs:3-30`) have nothing left to do **[checked; inferred that
  nothing is lost]**. In JS a record is an object today, so unless the
  backend unboxes it every decision allocates. The backend should store a
  record with one run-time field as that field, as `rt` does (a call made,
  §7), and `js/src/lib.rs`'s `Yes`-tag code (`:4273`, `:4824`) goes.
- **Checking.** Measured above: 0.5 s against 2.2 s for 300 elements; 1,000
  elements check in 0.6 s with the record and don't finish in 25 s through
  today's `byDecision`. 3,000 take 8.3 s with the record, so the cost isn't
  linear yet; where it goes isn't known **[measured; not profiled]**.
- **Laziness.** The proof fields are lambdas or folded theorem calls, so
  building a decision doesn't compute a proof (`docs/core.md`, "Theorems
  stay folded") **[checked]**. `Decidable.and` computes both sides, as
  today; `andThen`, whose `does` is `if dp.does then (dq …).does else False`,
  decides the right side only when the left holds, and is then the same
  term as the `Bool` `&&` (`andThenIsAnd`, measured).

### 4.2 Soundness

No kernel rule changes: no new term form, conversion or reduction rule
**[checked against `docs/core.md`]**. The kernel's code does change in three
places, all smaller:

1. `register_decidable` (`core/src/native.rs:448`) checks the shape
   `Yes p | No ¬p` so that the `Nat.decEq` native can build `Yes rfl` and
   `No (natNeq …)`. With the record, `Nat.decEq` is a record literal whose
   `does` is `Nat.equal`, already native, so the `DecEqNat` native, its pin
   and the pin on `Nat.equalFalse` go. The trusted base shrinks.
2. Validators (`core/src/check.rs:4232-4366`, `shaped_like_decidable`):
   extracted JS runs a precondition's decision and trusts "first
   constructor" to mean the proposition holds. The shape test becomes "a
   record whose first field is a `Bool` and whose second has type `does =
   True → p`", and JS tests `does`. The kernel still type-checks the
   decision as `Decidable P`, so a `True` it accepts has a proof behind it.
3. `Nat.equalRefl` and `Nat.equalSound`'s natives make `J` along a decided
   equation compute at large numbers; `J` computes only on `rfl`
   (`docs/core.md:143`). Nothing in a decision needs them any more, but a
   program that transports along `DecEq.sound h` at check time still
   might. Keep them; measure before removing (D3484).

`docs/core.md` changes with item 1 and 2 (D3210).

### 4.3 What the record form makes harder

- **A `match` on `d.does` while the goal mentions `d.sound`** is
  `E-MATCH-MOTIVE`: generalising `d.does` leaves `d.sound`'s type behind
  (measured, writing `Dec.andThenSound`). The fix in a proof is to take the
  record apart first, `match d with | { does = True, sound = s, … }`
  (measured). Generic lemmas about decisions meet this; users splitting a
  concrete test don't (`gLe`). The elaborator could generalise `d` by eta
  when it generalises `d.does` (a finding, §8).
- **Large elimination** still works: `match d.does with | True => Nat |
  False => Bool` is a type (measured, `Answer`). An `if` can't choose a
  type, but that is `Bool.ifThenElse [a: Type]`'s universe, as today.
- **Matching a decision's proof out** (`| Yes h =>`) becomes `if h:` or a
  record pattern. Hedberg's argument (`Bool.canon`, `DecEq.canon`,
  `std/core/DecEq.sw:51-72`) is restated with `match d.does`; with axiom K
  in the kernel it may not be needed at all (§8).
- **Printing.** A decision not folded shows `(List.decMem x xs).does`. The
  printer folds it to `x ∈ xs`, as it folds `toBool` to `==` today
  (`core/src/pretty.rs:1734`, `:1809`, `:1924`).

## 5. Every use of `Yes | No`, and what it becomes

Counts are `grep` at `f55b2381b` **[measured]**. "Goes" means nothing
replaces it; the `if` it handled is one term already.

### 5.1 Elaborator

| Place | Today | After |
|---|---|---|
| `check.rs:5352` `unused_proof_if`, `kept_if`, `tagged_if`, `Unused` (≈170 lines) | rewrites an `if` whose branches don't use the proof to `Bool.ifThenElse` on the decision's `Bool` | goes: both forms are one term (§3.1) |
| `check.rs:5469` `decided_if`, `:5147` `check_proof_if` | `Decidable.elim` / `elimProof` | the same library functions, now defined by a match on `does` |
| `logic.rs:700-800` `%conj` and `%plain` tags, `settle_tagged` | keep the plain `Bool` beside a decision until the branches are known | go |
| `logic.rs:171` `conjunction`, `short_circuit` | `Decidable.andThen`; chooses `elim` or `ifThenElse` by whether `b` needs `a`'s proof | `andThen` stays; the choice goes |
| `bind.rs:212` `comparison` | six comparisons' decisions written as their `Bool` | generalised: any instance whose body is a record literal has its `does` written in place |
| `bind.rs:180` `into_bool` | `Decidable.toBool d` | `d.does` (or the inlined test) |
| `matching.rs:588` `tested_bool` | reads `toBool (decTrue b)` as `b` | goes: `(Bool.decTrue b).does` is `b` |
| `matching.rs:1265`, `:1731` `W-MATCH-DECISION-IF` | warns that a decision match misses an `if` | goes, with `examples/{accept,reject}/match-decision-if.sw` |
| `auto.rs:347` `from_yes`, `cases.rs:394-474` | `Decidable.fromYes d Trivial` | `d.sound rfl` |
| `omega.rs:30`, `:145`, `:662` | reads `toBool d = True` through `toBoolSound`, `toBoolFalse`, `toBoolOf`, `toBoolOfNot`, `notNotOf` | reads `d.does = True` through `d.sound`, `Decidable.refute` |
| `equations.rs` (39 mentions; `:58`, `:866-1536`) | one `J` per `Bool` `if`, `Decidable.elimEq` per `if h:`, plus `andBool…` lemmas | one path: every `if` is on a `Bool` |
| `decreasing/plain.rs` (1,234 lines) | `f.%plain` over `Decidable.elimIf` / `Bool.elimDecTrueIf` / `elimCong` | the `if` half goes; dropping recursive calls' proofs stays |
| `decreasing.rs:613`, `:750` (`decreasing (m1, m2)`) | `Decidable.elim(Proof) (Nat.decLessThan …)` | unchanged: `elim` and `elimProof` keep their signatures |
| `congruence.rs:94`, `:267`; `counterexample/mod.rs:1053`; `tailrec.rs:611` | know `Decidable.elim` by name | `elim` unfolds to `ifThenElse`'s shape; keep or drop the special case |
| `derive.rs:1078-1089` (`deriving (DecEq)`), `derive_decide.rs` (records of propositions) | write `Yes`/`No` under `if h:` | write the test, then the two proofs (§5.3) |

### 5.2 Std, `aoc/`, examples

| | Std | `aoc/` | rogue | examples |
|---|---|---|---|---|
| files mentioning `Decidable` | 30 | 27 | 4 | 51 |
| `\| Yes` / `\| No` arms | 77 / 70 | 66 / 65 | 0 | 8 / 8 |
| `Yes …` / `No …` built | 76 | 0 | 0 | 16 |
| `instance … Decidable` | 16 | 0 | 0 | 26 |
| `Decidable.toBool` | 28 | 45 | 1 | 6 |
| `Decidable.toBoolSound`, `…Of`, `…OfNot`, `…False` | 52 | 29 | 1 | 5 |
| `Decidable.elim`, `elimEq`, `elimProof`, `elimCong`, `elimIf` | 17 | 15 | 0 | 7 |
| `Bool.elimDecTrueIf` | 2 | 0 | 0 | 0 |

`aoc/`'s `Yes` arms split on `DecEq.decide` (24), `Nat.decLessThan` (16),
`Nat.decEq` (14), `Nat.decLessEq` (5) and others; Day12's `Rules.sw` has 12.

What each becomes:

- **`core/Decidable.sw`** (187 lines): the type; `IsYes`, `fromYes`,
  `toBool` go (`toBool d` is `d.does`); `elim`, `elimProof` stay, by a
  match on `does`; `elimCong`, `elimEq` stay as one-line proofs (generated
  `decreasing` proofs name them); `Bool.ifThenElseCong` stays; `elimIf` and
  `Bool.elimDecTrueIf` go (`rfl` now); `andYes` goes; `and`, `or`, `not`,
  `andThen`, `Bool.decTrue`, `Nat.decLessEq`, `Void.dec`, `Unit.dec` become
  record literals; `Nat.decEq` and `Nat.decEqFrom` become one literal
  (`does = Nat.equal m n`).
- **`Decidable/Decidable.sw`** (135 lines): `toBoolSound` is `d.sound`,
  `toBoolOf` is `d.complete`, `toBoolFalse` is `refute`; the four
  `andBool…` lemmas and `Bool.decTrueToBool` are `rfl` and go.
  `DecEq.sound`, `refl`, `neTrue` and the rest stay, each a line.
- **`core/DecEq.sw`, `core/Ord.sw`**: the interfaces keep their shape
  (`decide`, `decLessThan`, `decLessEq` return the record). `Ord.fromCompare`'s
  decisions become `does = compare x y == Less` and so on. `DecEq.canon`
  and its three lemmas are restated (§4.3).
- **The other `instance`s** (`Int`, `Float`, `Nat.decPowSuccNotZero`,
  `List.decLeHead`, `List.decSorted`, `List.decMem`, `List.decDistinct`):
  record literals; `List.decMem`'s `does` is the `||` chain, which is what
  `List.contains` computes.
- **Bridging lemmas that go:** `Decidable.elimIf`, `Bool.elimDecTrueIf`,
  `Decidable.andBoolOf`, `andBoolOfNot`, `andBoolSound`, `andBoolFalse`,
  `andBoolDec`, `Bool.decTrueToBool`, `Nat.decEqFromToBool`
  (`Nat/Arith.sw:638`), `Option.decSomeToBool` (`Option/Lemmas.sw:131`),
  `Nat.untilStableDecYes`/`No` (`Nat/Iterate.sw:54`, `:59`) and
  `Fin.ofNatCheckDec` become `rfl` or a rewrite.
- **`aoc/` and examples**: each `match d with | Yes | No` becomes `if h:`
  or `match h: <test>`; each `Decidable.toBool…` becomes a field.

### 5.3 Generated code, natives, runtimes, docs

- **`deriving (DecEq)`** writes `T.%same` (the structural test, fields by
  `==`), `T.%sameSound`, `T.%sameRefl`, and `T.%decEq := { does = T.%same r
  s, … }`, as `instance.sw` does by hand. Then `r == s` on known
  constructors computes to the fields' `&&`, which proofs can rewrite.
  Writing it as today's `if h: … then yes … else no …` would compile but
  leave `==` stuck on the `if` with unknown fields (§2.4).
- **Records of propositions** (`derive_decide.rs`): `does` is the fields'
  tests joined by `&&`; the proofs by `Both` and `.field`.
- **`decreasing (m1, m2)`**'s proofs call `Decidable.elimProof` and
  `elimEq` (`decreasing.rs:385-387`), which keep their signatures, so
  nothing changes there **[checked]**.
- **Natives** (§4.2): `Nat.decEq`'s goes; `Nat.equalRefl` and
  `Nat.equalSound` stay until measured (D3484).
- **Runtimes**: `rt/src/lower.rs:183` registers `Decidable` for the
  simplifier; `rt/src/clauses.rs:715` and `fusion.rs:411` treat
  `Decidable.elim` as a branch; `js/src/lib.rs:2132`, `:4273`, `:4351`,
  `:4824` know its tags. All shrink to `Bool.ifThenElse` once `elim`
  unfolds, or keep `elim` as a known two-branch call. A lambda over an
  erased proof stays a closure at run time (`rt/src/lower.rs:1138`), so
  branches stay lazy **[checked]**.
- **Docs**: `docs/core.md` (`if`, auto, natives, preconditions, validators:
  lines 12-13, 347-349, 388-399, 580); `docs/syntax.md:304-305`, `:506`,
  `:1531`, `:2070` (the trap `W-MATCH-DECISION-IF` warns of), `:2363`;
  `docs/guide/10-proofs.md:571`. The surface (`if h:`, `==`, `auto`)
  doesn't change, so the feature tour doesn't either.

## 6. Decisions for Matt

- **D3483:** Name the test field `holds` (`{ holds = Nat.leq m n, sound,
  complete }`, `d.holds`) rather than Agda's `does`? **[rec: `holds`]** It
  says what the `Bool` means in everyday words. `does` is the name Agda
  users know; `answer` is a noun but reads worse in `sound`'s type. Few
  users write it either way (§2.1).
- **D3484:** Remove the `Nat.decEq` native, with its pins and the kernel's
  check of `Decidable`'s shape for natives, and keep `Nat.equalRefl` and
  `Nat.equalSound` until a probe shows nothing needs them? **[rec: yes]**
  It shrinks the trusted base; the two kept natives cost nothing to keep
  (§4.2).
- **D3485:** Drop `Yes` and `No` as patterns: a split on a decision is
  written `if h: p` or `match h: <test>`, as the program is, and
  `Decidable.yes h` / `.no r` remain only as functions? **[rec: yes]** The
  alternative, record patterns `| { does = True, sound, … }`, is what
  std's generic lemmas use internally, but nobody should have to write it
  in a proof about a program (§3.2).

## 7. Calls made (the orchestrator's)

- `sound` and `complete`, not one `reflects` field (D3480 as decided; §2.2).
- `Bool.ifThenElse` keeps its `Unit` thunks: the probe shows the two `if`s
  are equal without changing it (§3.1).
- `Decidable.elim`, `elimProof`, `elimEq` and `elimCong` stay as library
  functions with today's signatures, so `decreasing`, congruence and the
  runtimes keep working through the switch.
- The elaborator writes an instance's `does` in place when the instance's
  body is a record literal, generalising `bind.rs:212`.
- Instances are written test first; `deriving` too (§5.3).
- The JS backend stores a record with one run-time field as that field,
  as `rt` does (or special-cases `Decidable` if that is smaller).

## 8. A staged plan

Each stage leaves `main` green. Estimates are mine, untested.

| Stage | What | Model | Est. |
|---|---|---|---|
| 1 | **Stop naming the constructors.** With the type still `Yes \| No`, add `Decidable.yes`, `.no`, `.refute` and `.does` (today `toBool`) as functions, and rewrite every `Yes`/`No` arm and construction in `aoc/`, std outside `core/Decidable.sw`, examples and `derive*.rs`'s generated source to `if h:`, `match h: <test>` or the functions (about 320 sites outside `core/Decidable.sw`, §5.2). Pure sweep; hashes change, statements don't. | Sonnet | 3 h |
| 2 | **Flip the type.** `core/Decidable.sw`, `Decidable/Decidable.sw`, the 16 std instances as record literals; `register_decidable`, `DecEqNat`, pins, validator shape (`core/src/check.rs`, `native.rs`, `pins.rs`), `docs/core.md`; `rt` and `js` tag code; `auto` writes `d.sound rfl`. Elaborator otherwise untouched: `unused_proof_if` and the tags still run, now harmlessly. | Opus (kernel, std core) | 5 h |
| 3 | **Remove what had to choose.** `unused_proof_if` and friends, `%conj`/`%plain`, `tested_bool`, `W-MATCH-DECISION-IF` and its examples, `bind.rs`'s comparison case generalised, `omega` and `equations.rs` on `does`, the `if` half of `decreasing/plain.rs`; `docs/syntax.md`, guide. | Opus (elaborator core) | 6 h |
| 4 | **Std cleanup.** Delete or `rfl` the bridging lemmas (§5.2), restate Hedberg's lemmas, `deriving (DecEq)` test first (`T.%same`). | Sonnet | 3 h |
| 5 | **Measure.** Natives `Nat.equalRefl`/`equalSound` (D3484); JS allocation; the 3,000-element checking curve (§4.1). | Sonnet, paper plus probes | 1 h |

Stages 1 and 2 can't be one lane without a long-lived branch; 1 is the
large diff and is mechanical. Stage 3 can split by file if it runs long.

## 9. Where this meets SW-2704 (a `Bool` standing for a proposition)

- SW-2704's reader, "which proposition does this `Bool` decide?", looks for
  instances whose `does` computes to the `Bool`. With the record that is a
  field of a literal, found by computing; with `Yes | No` it couldn't be.
- `match h: p` on a proposition (§3.2): this note makes the scrutinee
  `does`; SW-2704 decides what `h` is called and how it prints in each arm.
- Goals printing `d.does = True` as `p` is SW-2704's printer, and covers
  this note's `(List.decMem x xs).does` (§4.3).

## 10. Findings, not built

- `match e: d.does` can't generalise while `d.sound` is in the goal
  (`E-MATCH-MOTIVE`, §4.3): the elaborator could generalise `d` through
  eta instead.
- With axiom K, Hedberg's lemmas (`Bool.uniqueEq`, `DecEq.uniqueEq` and
  their `canon` helpers, `core/Decidable.sw:152-177`, `core/DecEq.sw:47-72`;
  `deriving (DecEq)` uses them for proof fields) may be replaceable by K
  directly.
- A K-like reduction for `J` (Lean reduces `Eq.rec` on any proof when the
  endpoints convert) would make `Nat.equalRefl`/`equalSound`'s natives
  unnecessary; that is a kernel rule change and would need its own note.
- `byDecision` on 300 elements spends 8 of its 10.4 s in the elaborator,
  running the decision before the kernel does (`membership-today.sw` with
  and without it, measured).

## Probes

In [decidable-record/](decidable-record/), all checked with the release CLI:

- `one-if.sw`: the type, helpers, one `if`, `&&`, `==`, `auto`, eta, large
  elimination, a split on a proof-using `if`.
- `instance.sw`: a `DecEq`-style instance for a new type, test first.
- `membership.sw` (0.5 s) and `membership-today.sw` (2.2 s): the same fact
  both ways.
