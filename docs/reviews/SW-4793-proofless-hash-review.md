# SW-4793: is the hash without proofs complete?

Fable paper review, 25 Nov 2026 (D3741). Read from the code and the docs at
`10bb8e5f6`; nothing was built or run. Where a claim rests on reading alone
and a test would settle it, it says so.

**Answer.** The hash itself has no further hole of SW-4786's kind: I found
no other place where it drops something that no hashed part fixes. It does
rest on one property of the kernel, "which proof is given never changes
what anything computes", and that property has a gap in rule S that the
hash inherits (finding 1, to be confirmed by a test). Nothing is cached or
trusted by this hash today, so the worst outcome of a collision is a
refactoring tool calling an edit safe that changes what a definition is
equal to.

## Findings, ranked

### 1. Rule S declines where a parameter's type is not written as a function type; a literal proof then computes and a sealed one is stuck (moderate; by reading only)

The hash marks the argument at a definition's proof parameter as "proof"
(`hash.rs:542`, `proof_argument`), reading the parameters from the
definition's type *evaluated in its own view* (`erase.rs:292`,
`check::proof_telescope`), so it sees through a type alias. The kernel's
rule S, for a proposition with indices, reads the scrutinee's type from the
definition's type *as written* (`value.rs:3053`, `parameter_type`: a chain
of `Term::Pi`) and declines when the type isn't written as a function type
that far (`value.rs:2937-2939`, `2982-2984`). When it declines, a `case` on
a literal constructor still takes its branch by iota (`value.rs:2761`),
and a `case` on a sealed proof is stuck. So, if the elaborator keeps the
signature as written:

```
type Q2: Nat → Prop = | MkQ2 (w: 0 = 0): Q2 0
def Reader: Type := (x: Nat) → Q2 x → Nat
def f: Reader
  | x, MkQ2 w => 5
def pf: Q2 0 := MkQ2 byComputing

def a: Nat := f 0 (MkQ2 byComputing)   -- iota: 5
def b: Nat := f 0 pf                    -- rule S declines: stuck
```

`a` and `b` share a proofless hash, and `theorem ta: a = 5 := byComputing`
checks where `tb: b = 5` would not. It is first a kernel gap, whatever the
hash does: `a` and `b` are equal (same call, proofs equal by rule I), `a`
is `5`, `b` is not `5`, so conversion is not transitive, which is what
D3727 fixed for the written-out signature
(`examples/accept/proof-irrelevance-39-indexed-field-transitive.sw`). The
same reading says a signature behind an opaque nickname the definition
unfolds (`f: Fun unfolding Fun`) declines too. `docs/core.md:310` names
only the other decline (a `case` node reached by two paths).

- **Not verified:** that the elaborator leaves `f`'s case tree in `f` with
  the type stored as `Reader`. If it lifts the match to a helper with a
  written-out type, or stores the type unfolded, there is no gap.
- **Fix:** in the kernel, not the hash: `field_type` reads a parameter's
  type from the definition's type evaluated in its own view (as
  `check::telescope` does), falling back to today's decline only when that
  is not a function type either. Test first: example 39 with `f: Reader`.
- **Severity:** moderate as a kernel completeness gap (it only loses
  equalities, never proves a false one); for the hash, a `ProofsOnly` trial
  could accept replacing `MkQ2 byComputing` by `pf` when no declaration in
  the project happens to compute through it.

### 2. An open goal or a failed proof's stand-in at a proof position hashes as any proof (minor today; a precondition for any later use)

A reference to a definition whose result is a proof is the marker before
`def_ref` is reached (`hash.rs:786`, `is_proof` at `:529`). An assumption
whose type is a proposition is such a definition, so in this mode its label
is never hashed and the `unfinished` flag for an error stand-in
(`hash.rs:725-730`) is never set. The content hash promises the opposite
("filling the gap changes every user's hash", `hash.rs:187-188`). Example:
`def a: Sub := MkSub 5 (lemma)` and `def b: Sub := MkSub 5 ?` share a
proofless hash. To the kernel they are the same (both sealed constants), so
this is not a hole in the table's argument; it is a trust difference. Today
the trial also compares diagnostics, and a `?` or a failed proof reports
one, so nothing slips. If this hash ever keys a test result, a pin or a
cache entry, the goals a definition relies on must be in the key beside it,
as the test-result cache already does for the content hash
(proofless-definition-references.md, section 1). **Fix:** a sentence in
`proofless_hash`'s doc; no code.

### 3. The term diff does not look at a cast's ends, which the hash now covers (minor; a report)

`term_diff.rs:701-706` compares two `J`s by motive and base only. Since
SW-4786 two definitions that differ only in a cast's ends have different
proofless hashes, so a `ProofsOnly` trial reports the declaration as
changed with no `difference` (`trial.rs:198-200`). **Fix:** compare the
equations under the hash's own guard (`hash.rs:931-938`).

### Not findings

- **`J` whose proof computes to `byComputing` while its ends differ**
  (`value.rs:2292`, `2337`): the ends are the proof's own type
  (`check.rs:1214-1221`), so a proof that is `byComputing` has ends that
  met when it was checked. They could fail to meet later only under a
  smaller transparency set, and rule 3 of opaque definitions ("no escape",
  `docs/core.md:171`) means a body is only unfolded where everything it
  unfolds is. Types are checked with nothing unfolded, so they are safe
  everywhere.
- **Marks.** A stored body is the kernel's checked term
  (`check.rs:2792-2802`), in which every mark is decided and every `J` into
  data carries ends, so the arm's fallback (`hash.rs:940`, the whole proof
  as the marker) is reached only for a `J` into a proposition.
- **A proposition typed in `Type`.** There is no cumulativity
  (`docs/core.md:66`), and "is a proof" is the sort of the type
  everywhere (`check.rs:5499-5505`, `Def::proof`, `field_sorts`,
  `proof_params`), so the hash and the kernel agree on what is a proof. An
  alias changes only how many parameters are visible, and the hash errs
  towards hashing more (`hash.rs:551`: a parameter past the telescope is
  not a proof).
- **Run bodies and `Def::fold`** are in neither hash (`docs/core.md:252`):
  out of scope here, and both are generated from hashed text.

## The argument, restated

SW-4786's table says "a proof left out has its type fixed by hashed
context". The form I checked: take the largest proof subterm `M` around
each marker. `M`'s parent is not a proof, and every way a term that is not
a proof can hold a proof gives `M` a type from hashed parts. Any two proofs
of one type are then the same to the kernel by rules I, K, S and F, so what
is inside `M`, hashed or not, cannot matter. Whether the rules deliver that
is the kernel's property (finding 1 is a gap in it), not the hash's.

| Where `M` sits (parent is not a proof) | Type of `M` fixed by | Verdict |
|---|---|---|
| Argument of an application (`hash.rs:868-871`) | the head's type, inferred from hashed parts | safe; marker only when the head is a definition and the parameter is a proof, else hashed in full |
| Data type's parameter, constructor's field (`:808-822`) | the declaration, by its own proofless hash (`data_hash_in`, `:321`), and earlier arguments | safe; a proof *index* is hashed in full (`proof_params` covers parameters) |
| `let` value, annotated term (`:873-881`) | the written type, hashed | safe |
| `J` into data, its proof (`:929-941`) | the ends, since SW-4786 | fixed; the guard is rule K's (`value.rs:2039-2040`) |
| `Quot.lift`'s fifth argument (`:957-964`) | arguments 0 to 3 (`check.rs` C6); evaluation applies argument 3 and never reads 4 (`value.rs:2215`) | safe |
| Side of an equation between proofs (`:907-914`) | the equation's type, filled in by the checker | safe |
| A definition's body when its result is a proof; a stated theorem (`:499-505`, `:221-230`) | its statement; rule F freezes every call (`value.rs:3437`) | safe; the two encodings agree, so stated and proved hash alike |
| Proof members of a recursive group (`:239-250`) | their statements; computing members mention them only under the marker | safe; no cycle, since a statement never needs a proof member's body |
| Name of an opaque proof definition in an `unfolding` list (`:664-681`) | its statement | safe: frozen whether listed or not |

Positions where the kernel *infers* a type and a proof could hide it: the
head of an application (a proof applied is a proof, so the parent is still
inside `M`); a projection's subject (`check.rs:1248-1257`: data with eta in
`Type`, or a record of proofs whose fields are proofs, so no data comes out
of a proof); `J`'s proof (above); a `case`'s scrutinee (always a variable,
typed by a hashed binder). Rule S on a parameter or an enclosing field
reads the definition's type and the constructor's declaration
(`value.rs:2940-2996`), both hashed, never the proof. A lambda's domain is
in neither hash; it comes from the type the lambda is checked against.

## Where the proofless hash carries trust today

| User | What it decides | A collision would |
|---|---|---|
| `Promise::ProofsOnly` (`crates/driver/src/live/trial.rs:109-111`), reached by `stitchwort trial --proofs-only` (`crates/cli/src/trial_cmd.rs:65`) | whether a declaration whose content hash moved "kept its meaning" | call an edit safe that changed what a definition equals (moderate). The kernel still checks every declaration, and new diagnostics are compared separately |
| `stitchwort oracle readings\|builds` (`crates/cli/src/oracle_cmd.rs:104`) | "redundant/removable" against "changed" for a deleted `.read` or build helper; "removable" is a sweep's work list | put a meaning-changing deletion on the work list (moderate); each is checked again when applied |
| `DeclHash.proofless` (`crates/driver/src/declhash.rs:144`, `161`), `prooflessHash` in trial JSON (`trial_cmd.rs:366`) | nothing; carried for the two above and `--std` child comparisons | a wrong report (minor) |
| `term_diff.rs` | where two terms first differ, for the message | a missing or misplaced location (minor) |
| `caches.rs:27`, `globals.rs:978` | the memo table and its rewind | none |

It reaches none of: the check cache's key or interface digest, stage 3's
interface entries (`crates/elab/src/cache/`, `deferral.rs`: no mention),
native pins, the test-result cache. `hash.rs:142-145` ("it decides nothing
the kernel accepts, and nothing is cached by it") is accurate. So no
collision can cause a wrong cache hit today.

## Not checked

- Finding 1 by a run: the two-line test above decides it.
- The elaborator's own evaluation of unchecked terms (unknown marks, the
  unifier's condition D): the hash is only taken of final declarations.
- That conversion is monotone in the transparency set, which the
  `byComputing` argument above assumes; it is the design's stated intent
  (opaque-definitions.md, section 6), not something I traced.
