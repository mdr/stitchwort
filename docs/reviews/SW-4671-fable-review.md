# SW-4671 (proof marks, full proof irrelevance stage 3): Fable review

23 Nov 2026. Reviewed: `lane/SW-4671` at 4bef20dab (d504310cb, d5bdab8e0) against `main` at
91f46bf04. Read: the lane's brief and notes (`SW-4671-notes.md`), `docs/core.md` "Proof
marks", the audit (`full-proof-irrelevance-audit.md`, conditions A to G), and the diffs of
`crates/core` (`term.rs`, `check.rs`, `value.rs`, `reference.rs`, `hash.rs`, `inert.rs`,
`proof_counts.rs`), `crates/elab/src/unify.rs` and `crates/elab/src/cache/`. Built the
branch's release binary and compared it with main's on probe files.

## Verdict

**Merge after one fix (F1).** The design is right and I found no way for a stored mark to say
"proof" on data and survive checking. But the lane's promise, "no change to what's accepted",
is broken: the branch refuses, with `E-RESOURCE`, definitions that main accepts. The second
regression the lane fixed (computing a mark must not write out a huge type) is fixed for
three shapes of type only; the others still fall back to reading the type back.

Everything else is for stages 4 and 5 to carry, not a reason to hold this lane.

## Findings

| # | Finding | Severity | Confidence | Size |
|---|---|---|---|---|
| F1 | A lambda whose parameter type is a stuck projection, a stuck `J` or a quotient type holding a huge call: `E-RESOURCE` on the branch, accepted on main | high (breaks the lane's contract) | high (reproduced) | S to M |
| F2 | `prop_mark` labels the variable it binds with the function type's own mark, which may be the elaborator's; and `m1.or(m2)` takes the first mark when two disagree | none today; medium at stage 5 | medium | S |
| F3 | The unifier's `meta_mark` forces a type, applies closures and turns a resource error into "unknown": not constant time, and its answer depends on the budget left | none today (counters only); medium at stage 5 | high | S |
| F4 | The memo tables ignore marks, and one comparison reuses a level under different binders | none today; needs an argument or a key at stage 5 | medium | S to M |
| F5 | The reference validator re-derives outer marks only | fine for stage 3; stage 5 needs more (below) | high | M |
| F6 | Test gaps: no refusal test for a wrong `Quot` mark or wrong `J` motive binder marks; no test that a given mark can't steer the derived one | low | high | S |
| F7 | `docs/core.md`: "constant time" is not quite true; three things missing | low | high | S |
| F8 | `reference::is_proof` indexes `field_sorts[*i]` (panics out of range) where `value::is_proof` uses `get` | low | high | S |

### F1. The mark of a lambda's binder can still write out a huge type (high)

`check.rs`, `prop_mark` (line 749) answers without reading the type back only for a call, a
definition applied to arguments and a variable applied to arguments. Anything else goes to
`sort_of`, which has arms for an equation, a data type and an applied variable, and otherwise
`quote_kept` plus `check_type` (line 1009). On main a lambda checked against a function type
never asked for its domain's sort, so this is a new computation at every `Lam ⇐ Pi`.

Repro (`b1.sw`; main: `checked`, branch: `E-RESOURCE ... a value was too large to write out
(over 2,000,000 parts) ... while unfolding grow`):

```
import Std (Eq, Nat)

type Tree = | Leaf (n: Nat) | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

type Fam: Type 1 = { fam: Tree → Type, n: Nat }

def size (f: Fam) (x: Nat) (w: f.fam (grow 22 (Leaf x))): Nat := x
```

Also refused on the branch and accepted on main (same prelude, one line each):

- `def later (f: Fam) (x: Nat): f.fam (grow 22 (Leaf x)) → Nat := w => x` (a lambda below the parameters)
- `theorem t (f: Fam) (x: Nat) (w: f.fam (grow 22 (Leaf x))): x = x := byComputing`
- `def sortdom (f: Fam) (x: Nat) (k: (t: Type) → f.fam (grow 22 (Leaf x))): Nat := x` (the projection under a function type's codomain)
- `def quotDom (x: Nat) (q: Quot (Wrap (grow 22 (Leaf x))) (Rel x)): Nat := x` (a quotient type)
- `def castDom (x: Nat) (h: Nat = Nat) (w: J (y p => Type) (Wrap (grow 22 (Leaf x))) h): Nat := x` (a stuck cast)

Accepted by both: the same with `grow 3`; `Wrap (grow 22 (Leaf x))` (a data type);
`grow 22 (Leaf x) = grow 22 (Leaf x)`; `Nat → Wrap (grow 22 (Leaf x))`; and
`def ty ...: Type := f.fam (grow 22 (Leaf x)) → Nat` (no lambda has that domain). So the
path is `check_form`'s `Lam ⇐ Pi` arm → `prop_mark(dom)` → `sort_of` → `quote_kept`, not
`def_mark`.

Why it matters beyond the huge case: every lambda whose domain is one of these shapes
(a record's type field, as dictionaries with a type member have; a type made by a cast; a
quotient type that has been unfolded) now pays a read-back and a second check of its domain.
I couldn't measure that on std (see "Not checked").

Recommended fix: give `prop_mark` (better: `sort_of`, which every caller shares) a way to
read the sort of a stuck type without reading back its arguments, for the remaining heads:
a projection (the field's type from the scrutinee's type, then the applied arguments, as
`sort_of_applied` does), `Head::Quot(Type)` (the carrier's sort), a stuck `J` (the motive
applied, which is a sort), a stuck `Quot.lift`. A `type_of_neutral` that walks the spine and
never quotes an argument covers all four. Add the six lines above as an accept example
beside `large-hypothesis-parameter.sw`. The fix must not use the function type's stored mark
as the answer: that is the one thing the lane rightly refuses to trust.

### F2. Marks the kernel didn't derive can reach a kernel context (stage 5)

- `prop_mark` (line 765) binds the variable under a function type with that `Value::Pi`'s
  own mark. The lane's argument, that a label can't change a sort because `sort_of` reads
  types and not marks, holds today. At stage 5 `sort_of`'s fallback runs `check_type`, which
  compares, and comparison will read marks. Use `ProofMark::Unknown` there (free), or derive
  it (`prop_mark(dom)`).
- `conv_step` gives the fresh variable under two lambdas or two function types `m1.or(m2)`:
  the first mark if both are known and differ. For two values of one type they agree, and
  for function types the domains are compared first. At stage 5: if both are known and
  differ, use `NotProof` (and `debug_assert` in the kernel), so a wrong pair can only lose an
  equality.
- The same for the remaining `Value::var(level)` sites that go under a binder with no mark
  (`push_eta`/`underapplied` at `value.rs:4804`, `is_type_former`, `reference.rs:1438`):
  `Unknown` is the safe side, and should stay the default.

### F3. The elaborator's `is_proof` is not a read (stage 5)

`unify.rs`, `meta_mark`: `force` on the unknown's type, up to 32 `cod.apply` calls on made-up
levels (`scope + 1_000_000 + depth`), and `Err(_) => Unknown`. Today it runs only under
`STITCHWORT_PROOF_COUNTS`. If rule I decides by it, an answer would depend on how much budget
is left (D2543: limits fail, never choose), and the made-up levels are the audit's condition
A in another place. Stage 5 should compute an unknown's mark once, when the unknown is made
or its type's sort is solved, with errors passed on; condition G (derived or trailed on
undo) then applies to it. The kernel's `value::is_proof` forces nothing: confirmed.

### F4. Memo keys ignore marks (stage 5)

Confirmed that nothing keyed or compared reads a mark: `Head`'s `PartialEq`/`Hash`,
`same_layer`, `same_term_layer`, `shape_hash`, `spine_pairs`, the term hasher (`hash.rs`),
and so `CallMemo` and the case-tree memo. That is right for stage 3, and it is why no hash
moved. At stage 5 a remembered "equal" may rest on rule I, and within one comparison level
`L` is reused for fresh variables under different binders, so the same key can meet a
variable marked a proof in one place and data in another. I believe it is still sound (two
structurally identical calls put the variable at positions of one type, and a type has one
sort), but stage 5's note should state that argument, or add the mode-like key the shortcut
mode already has. The same goes for any cache that outlives one comparison.

### F5. How independent the validator is, and what stage 5 must add

`reference::validate_marks` re-derives: each definition type's binders (by `check_type` of
the domain), parameter lambdas against those, `J`'s proof binder, the quotient forms' fixed
marks, and `Def::proof` from the whole type's sort. Deeper marks (lambdas in arguments and
branches, `let`, `J`'s and `Quot.lift`'s result, `J`'s `y` binder) are only checked to be
decided. It uses the kernel's own `check_type` for sorts, so it is independent of
`prop_mark`/`settle_mark`, not of sort computation; that is the right line, since sorts are
the base everything rests on.

Enough for stage 3: nothing reads the marks. Not enough for stage 5, where the deep marks are
exactly the ones rule I reads (the fresh variable under two lambdas, a stuck `J`'s result).
Stage 5 should add, under the `reference` feature:

1. **A check at the point of use.** Where the kernel's comparison is about to answer "equal"
   by rule I and the caller has a context (`Ctx::conv`), read both sides back, infer their
   type and assert its sort is `Prop`. This validates deep marks where they matter, and is
   the audit's tripwire (condition C) armed for the kernel only.
2. **Strip and re-check.** For each admitted body, set every mark to `Unknown`, check it
   again, and assert the marks returned equal the stored ones. Cheap in the fuzzer and the
   differential tests; it shows a given mark can't steer a derived one, and catches a term
   transformation that kept a stale mark.
3. Unit tests for `E-MALFORMED` on a wrong `Quot` mark and wrong motive binder marks (F6).

### F6 to F8

As in the table. For F7, the spec paragraph is accurate on what is marked, who derives it,
the refusal, hashing and the cache. Corrections: (a) `is_proof` is not constant time, it
walks back over trailing applications (`spine.iter().rev()`), so say "no forcing, at most the
spine's trailing applications"; (b) say that *unknown* counts as "not a proof" for every
reader; (c) say which variables stay unmarked (eta for a partial application, helper walks),
and that a `case` branch's field variables take `Ctor::field_sorts`; (d) after F1's fix, say
that deriving a mark never reads a type back.

## The brief's questions

1. **Can a stored mark be wrong and survive?** Not that I could find. Every mark in a term
   `check`/`infer` returns comes from `settle_mark` with a sort from `check_type` or
   `prop_mark`: `Pi` (line 438), `Lam ⇐ Pi` (675; a lambda is checked nowhere else, and never
   inferred), `let` (971), `J`'s result and both motive binders (1063 to 1077), `Quot` (1325).
   The constants are right: `J`'s `p` binds an equation, always a proposition; a quotient's
   carrier is refused if it is a proposition (`E-UNIVERSE`, 1198), so `Quot`, `Quot.mk` and
   the synthetic binders are data, and `r` is a proof of a relation into `Prop`. Constructor
   field variables take `field_sorts`, recomputed on the trusted path. `Def::proof` is
   `prop_mark` of the kept type on both paths. Substitution, `shift`, `eval` and `quote`
   copy marks; stability under substitution holds because there is no cumulativity and no
   sort polymorphism (`docs/core.md` "Universes"), so a type's sort is fixed by its head's
   type. Marks from the elaborator (`Ctx::with_variables`, `kcx.bind(.., Unknown/Proof)` in
   `elab/check.rs:2268` and `rewrite.rs:2731`, both binding an equation) never reach an
   admitted term: `admit_group` checks each body in a fresh `Ctx` against the kernel's own
   `ty_value`.
2. **The cache trusting stored marks: accept.** A hit installs the whole body unchecked
   (`admit_trusted_group`), so the marks add no trust the cache didn't already have; the
   comparison with `let`'s erasure flag undersells it. A stale entry can't carry marks from
   another derivation: an entry is trusted only when its kernel stamp (a fingerprint of
   `crates/core`) is this build's, and otherwise it is re-checked, which recomputes every
   mark. An edited file can already install any body. Recomputing on a hit would mean
   re-inferring every body, which is the cache. Two notes for stage 5: the decode self-check
   on carried-over entries compares hashes, which don't cover marks (acceptable: same
   kernel, checksummed entry); and on the re-check path a stored mark that differs from a
   later kernel's derivation is refused (`E-MALFORMED`), which counts as an unexpected
   refusal. Clearing marks to `Unknown` before a re-check would make that a quiet miss.
3. **Validator independence:** F5.
4. **`is_proof` in three places:** the kernel's and the reference's agree arm by arm (last
   non-application elimination, else head; constructor by its type's sort; `byComputing`;
   types are not proofs; lambda and resumption unknown), force nothing, and say `Unknown`
   for an unknown at the head. Nothing in them can say `Proof` for data given right marks.
   F3 and F8 are the exceptions to "constant time, agreeing".
5. **The two regressions:** `def_mark` (glued, peels by `prop_mark`) is fine. `prop_mark`'s
   fix is incomplete: F1.
6. **Term format and hashes:** marks aren't hashed (`hash.rs`), no memo or cache key reads
   them, and the cache format went 39 → 40. F4 for stage 5.
7. **`docs/core.md`:** F7.

## Checked and found sound

- The soundness set passes on the branch binary (`examples::soundness`, 1 test, 1.5 s).
- Small probes agree with main: a record's type and proposition fields as domains, a cast
  as a domain, `J` into data, with and without `STITCHWORT_PROOF_COUNTS=1` (the table
  prints; counters are all behind `proof_counts::on()`).
- `inert.rs`'s use of `sort_of` is unchanged in meaning.
- `Unknown`-marked terms the kernel builds for natives (`float.rs`, `native.rs`,
  `nat_add.rs`, `partial.rs`) are compared with types, not installed.

## To carry into stages 4 and 5

1. F1's no-read-back sort for every stuck type, before anything reads marks.
2. F2: no mark the kernel didn't derive labels a variable in a kernel context; disagreeing
   marks mean "not a proof".
3. F3: an unknown's mark computed once, errors passed on, undone with the trail (audit G).
4. F4: the argument, or a key, for memo tables under rule I.
5. F5: the point-of-use check and strip-and-re-check under `reference`.
6. A changed derivation changes `crates/core`, so the kernel stamp; if marks ever come from
   outside `crates/core`, bump `FORMAT`.

## Not checked

- Whether the elaborator ever asks the kernel to check a lambda against a function type
  whose domain is an unsolved unknown. `prop_mark` would then fail in `sort_of`'s fallback
  (the kernel rejects a term with an unknown) where main succeeded. I found no such call by
  reading and built no repro; the wide suites would show it as a new error.
- Whether any elaborator transformation keeps a known mark on a binder whose type's sort it
  changed (the kernel would refuse it, `E-MALFORMED`: a new refusal, not unsoundness).
- Cost on std, AoC, the roguelike and `tools/fmt`: a one-line file's check takes 0.30 s on
  both binaries with and without `--no-cache`, so it doesn't measure the prelude. The
  verifier should compare an uncached whole-project time, and the test builds (which run
  `validate_marks` on every admitted group, and panic on any `Unknown`) have only been run
  for the lane's few tests.
- The unifier's diff (`unify.rs`, 326 lines) beyond `is_proof`, `meta_mark` and the counter
  hooks; the 100-odd elaborator files that only thread `ProofMark::Unknown` through.

## Tickets to file

- (Opus, S to M, before merge) F1: sort of a stuck type without reading back, with the six
  repro lines as an accept example.
- (Sonnet, S) F6 and F8: the missing refusal tests; `get` in `reference::is_proof`.
- (Sonnet, S) F7: the four corrections to `docs/core.md`.
- (stage 5's brief) F2 to F5.
