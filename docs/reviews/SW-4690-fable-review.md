# SW-4690: Fable review (rule S on a proof field bound by an enclosing match)

Reviewed: commit 6709754a1 on `lane/SW-4690`, against its merge base with
`main`. 23 Nov 2026.

**Verdict: sound; merge.** No soundness finding and nothing that checked
before is refused. Three small findings: two examples say "record eta" but
don't exercise it (F1), the walk costs time in proportion to the tree's
size on every firing (F2), and the "found exactly once" guard has no test
(F3). None blocks the merge.

## Findings

### F1 (low, tests and wording): the record-eta examples don't use a record

`examples/accept/proof-irrelevance-42-enclosing-field.sw` (`c3`) and
`examples/soundness/proof-irrelevance-42-enclosing-field-indices-differ.sw`
(`unknown`) declare `type Box = | MkBox (n: Nat) (q: Q2 n)` and describe it
as "a record taken apart by record eta". A type written with `|` has no
eta (`check::qualifies_for_eta` needs `Data::record`), so:

- `c3` (`gb (MkBox 0 q)`) takes the enclosing branch by iota; its comment
  is wrong, and the notes' table entry for it is right ("taken apart by
  iota") while the file's comment isn't.
- `unknown` (`∀ (b: Box): gb b = 3`) is refused because the *enclosing*
  match is stuck on `b` (the error says so), not because `q: Q2 b.n`
  differs from `Q2 0`. It would be refused whatever rule S did with the
  inner match, so it guards nothing about this change.

The eta path itself is right: with real records (`type RecK (k: Nat) =
{ n: Nat, m: Nat, q: Q2 k }`, `type RecM = { n: Nat, m: Nat, q: Q2 m }`,
and a record inside a record) I get the expected answers, glued and
unglued, and in the reference evaluator (below). Fix: declare `Box` with
braces in both examples, so that `unknown` is stuck at the inner match and
`c3` can also be stated for an unknown record at a parameter-indexed field.

### F2 (low, performance): a whole-tree walk per firing

`slot_type` walks the definition's entire case tree on each firing for a
bound field (it can't stop at the first find, since it counts them). The
cost is linear in the tree, per firing:

| Probe | Time |
|---|---|
| a field 61 matches deep (61 nested one-constructor propositions), one call | 0.64 s for the whole check: no blow-up |
| 300-arm definition, each arm matching `o` then its field `q`, recursing 300,000 times | 6.0 s |
| the same with `q` a parameter (the old path) | 1.2 s |

So about 16 µs a firing on a 600-node tree, five times the cost of the
call around it in that contrived case, and nothing on realistic code. If
it ever shows in a profile: remember per definition a map from node
address to its path (or its count), built once. Not worth doing now.

### F3 (low, tests): the "found exactly once" guard is never exercised

No test builds a tree with a node reached by two paths, and I found no way
to get the elaborator to make one: a clause copied to several constructors
(`| Red, o => 1 | c, MkOuter q => match q with …`) gives each copy its own
nodes, and rule S fires in each (`hc Green o = 5`, `hc Blue o = 5` and the
indexed variant all check; refused on `main`). The guard is right by
reading (two paths could bind different things at the same levels, so
declining is the only safe answer), and declining only loses an equality.
A kernel unit test with a hand-built shared subtree would pin it.

## What I checked and found sound

**The argument** (docs/reviews/SW-4690-notes.md). The induction holds. The
points I pressed on:

- *The type is computed from the values in the environment, not from the
  refined context the branch was checked in.* That is the right choice: an
  enclosing branch is entered by iota (the values satisfy the refinement),
  by rule S (only after its own indices were found `≡`), by record eta (no
  indices), or by a number's or text's split (no indices), so the declared
  field type over the actual parameters and earlier fields is a type of
  the bound value in each case.
- *Which node, which path.* Every entry that runs a tree with `stuck =
  Some(id)` peels `g.def(id).body` by `def.arity` (`case_tree`,
  `unfold_for`, the field and comparison entries); `Control::Tree` keeps
  `stuck` only while it steps through `Case`/`NumCase` nodes, and a `case`
  met inside a leaf is run with `stuck = None` (`value.rs`, `eval`'s
  `Term::Case` arm), where `one_shape` answers no before looking at
  anything. So a node that asks was reached along a root path of `Case`
  and `NumCase` nodes only, which is what `bound_fields` walks. An
  occurrence of the same node inside a leaf isn't counted, and needn't be,
  for that reason.
- *Field count.* The kernel refuses a branch whose `names` differ in
  number from the constructor's fields (`check.rs`, the `ctor.fields.len()
  != branch.names.len()` test), so the levels `bound_fields` assigns are
  the ones `branch` extends the environment with, for every way a branch
  is taken (iota, Nat split: one field for `Succ`; text split; erased
  proof; eta; rule S).
- *Type mismatch falls out as "no".* `field_type` requires the enclosing
  scrutinee's type to be `Value::Data` of the `case`'s own type with at
  least its parameters, so a type that is stuck, or a compact value at
  another type, gives no answer.
- *Indices are dropped correctly*: `args[..params]`, then earlier fields,
  the environment `infer_proj` uses.
- *Nothing refused.* For `level < arity` the code path is the old one
  (`parameter_type` over `env[..level]`); the field path only replaces a
  `false`.
- *Termination*: unchanged; the walk is over a finite term and evaluates
  only declared field types.

**Probes** (lane binary, each with and without
`STITCHWORT_DEBUG_FORCE_UNGLUED=1`; files in the review scratch folder).
Every "must refuse" theorem was refused with `E-REFL` and every "must
check" one checked:

| Shape | Checks | Refused |
|---|---|---|
| nested rule S, index through two parameters (`Top k` → `Mid k` → `Q2 k`) | `k = 0` | `k = 1`, `k` unknown |
| two constructors with different field types (`A (q: Q2 0)`, `B (q: Q2 k)`) | `A q`, `B q` at 0 | `B q` at 1 |
| two fields (`MkP2 (x: Q2 a) (y: Q2 b)`), matching each | the one at 0 | the one at 1 |
| earlier data fields in order (`MkBox2 n m (q: Q2 m)`) | `1 0` | `0 1`, unknown box |
| a number's split before the match (`Succ m, k, MkAround q`) | literal and `Succ n`, `k = 0` | `k = 1` |
| enclosing indexed data family (`MkV k (q: Q2 k): V k`) | literal at 0 | literal at 1, unknown `v` |
| indexed proposition inside an indexed proposition | `W 0` | `W 1` |
| parameter and index (`MkW2 (q: Q2 k): W2 k k`) | `0 0` | `1 1`, `0 1`, `1 0` |
| two matches on one scrutinee (on the field, and on the enclosing proof) | 0 | 1 |
| real records by eta, parameter index, earlier-field index, record in record | parameter 0; literal `m = 0` | parameter 1 or unknown; unknown record; literal `m = 1` |
| a `let` before the match, a match as a call's argument, a match under a lambda | 0 (also on `main`: these matches are lifted to their own definitions, so the proof is a parameter) | 1 |
| a clause copied to several constructors | each copy | index 1 |
| a mutual pair, each matching a different argument's field | both at 0 | either at 1 |

**Kernel against reference.** I added 20 of these as pairs to
`proof_masks.rs`'s four-way test (glued, no shortcuts, unglued,
`reference::conv`) in the worktree, ran
`every_case_gets_its_answer_four_ways`, and reverted the file: all four
agree on all 20, records by eta included. The additions are kept as a
patch (`proof_masks-extra-cases.patch` in the review scratch folder) and
are worth committing with the F1 fix.

**Tests run.** `examples::soundness_examples_fail_for_the_expected_reason`
(pass); `proof_masks::every_case_gets_its_answer_four_ways` with the extra
cases (pass); `check --no-cache` of accept examples 39 and 42 (pass).

**docs/core.md.** The three passages agree with the code. "The corner
left" and "except in the corner above" are gone from the proof-irrelevance
paragraph, the running paragraph and rule S's entry; no other file under
`docs/core.md`, `docs/guide`, `docs/syntax.md` or the two crates mentions
the corner. One sentence overclaims slightly: "where a literal constructor
computes, rule S computes the same on any proof of its type" is true of
every tree the elaborator builds, but the kernel declines on a node shared
between two paths (F3). A clause there ("unless the same `case` node is
reached by two paths, which the elaborator never builds") would make it
exact; optional.

## What I didn't check

- A tree with a genuinely shared node (F3): by reading only.
- The text split (`Value::Chars`) as the enclosing branch: by reading
  only (`List`'s fields aren't proofs, so a proof field can only come from
  a further match, which the other probes cover).
- The elaborator's own evaluation of ill-typed terms before the kernel
  sees them (as SW-4686: the kernel re-checks every result).
- Whole suites, the std audit and the AoC checks: the verifier's and
  Overmind's.
