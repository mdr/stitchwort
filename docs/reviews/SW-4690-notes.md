# SW-4690: rule S on a proof field bound by an enclosing match

For a Fable review. Closes the corner the SW-4686 Fable review's F1 named
(docs/reviews/SW-4686-fable-review.md): a match on an indexed proposition's
proof that is a field bound by an enclosing match stayed stuck on anything
but a literal constructor, so conversion wasn't transitive there and a
closed instance of a checked universal statement could fail.

## Where the closed instance was refused

`b1c: gk 5 po = gk 5 (MkOuter (MkQ2 byComputing))` failed in the
elaborator's `byComputing` (`elab/src/check.rs` `rfl_against_equation`,
`E-REFL`), before the kernel saw the declaration. The stuck computation
underneath is the shared evaluator's (`core/src/value.rs` `branch`, used by
the elaborator and the kernel alike): the outer `case` on the frozen `po`
fires rule S (no indices), binding `q := Proj(Outer, 0, po)`, and the inner
`case` on `q: Q2 0` couldn't fire because its type wasn't read off the
definition's type. The open `b1` passes because both sides stay calls of
`gk` and are compared by their arguments (rule I on `po` against the
literal); in `b1c` the right side computes to `5` and the left doesn't.
The fix is in the evaluators only; nothing in the elaborator changed, and
`b1c` now checks.

## The change

| Where | What |
|---|---|
| `value.rs` `one_shape` | the scrutinee's type comes from `slot_type`, not only from the definition's type |
| `value.rs` `slot_type`, `field_type`, `bound_fields` | a parameter's type as before; for a variable past the parameters, the definition's case tree is walked from its root to this `case` node (by pointer), recording what each `case` on the way binds (data type, scrutinee's level, constructor, field index, first field's level); the field's type is its declared type evaluated over the enclosing scrutinee's type's parameters (found the same way, recursively) and the fields before it |
| `reference.rs` `eval_tree`, `rule_s`, `type_at` | the same, written apart: `eval_tree` carries a `Bound` per variable past the parameters down its recursion, pushed as each `case` takes a branch; `type_at` computes the type from those |

Unchanged: one constructor; every field a proof; the definition's result is
data; the indices must be `≡` (compared as before, index by index);
`E-PROP-ELIM` still refuses data fields and recursive, nested or grouped
propositions; a `case` with no possible branch stays stuck; a `case`
outside a definition's tree (`stuck` is `None`) never fires.

## Soundness argument

SW-4686's argument (docs/reviews/SW-4686-notes.md, steps 1 to 4) uses the
scrutinee's type only through one fact: `n : D ps is`, for the `ps` and
`is` the index test reads. It never needs the type to come from the
definition's signature. So it carries over once `slot_type` is shown to
give *a* correct type for the scrutinee's value.

**Claim.** In a well-typed definition's case tree, at a `case` node reached
by evaluation with environment `env`, `slot_type(level)` (when it answers)
is a type of `env[level]`.

- *Parameters* (`level < arity`): the declared domain over the earlier
  arguments, as SW-4686 used.
- *Fields.* Suppose the variable is field `k` of constructor `c` of `D'`,
  bound by the `case` on level `s`, whose fields occupy levels `first ..`.
  By induction (`s < level`), `env[s] : D' ps' is'`. Every way `branch`
  takes branch `c` binds, at `first + j`, a value of `A_j[ps', fields <j]`,
  the constructor's declared field type:
  - *iota* on `Ctor(D', c, fs)`: `C_c ps fs : D' ps r` is `≡ D' ps' is'`,
    so `ps ≡ ps'` (parameters are uniform), and `fs_k : A_k[ps, fs_<k]`;
  - *rule S* and *record eta*: `Proj(D', k, env[s]) : A_k[ps', Proj(D', j<k, env[s])]`
    (SW-4686 step 1; record-eta.md §6.2 for eta), and the earlier fields in
    `env` are exactly those projections (or, for eta on a glued call,
    `(f x).j`, equal to them by definition);
  - *a number's split* (`Succ`'s field) and *a text's split* (`Cons`'s
    fields of a compact list): the same constructors' fields, `Nat`, and
    `Char` and `List Char`.

  `field_type` evaluates exactly `A_k` over `ps'` (the first
  `params` arguments of the forced `D' ps' is'`) and `env[first .. first+k]`.
  Field types are written over the parameters and earlier fields only,
  never the indices, so dropping `is'` is right (as in `infer_proj`).

**Which `case` bound the variable.** A case tree binds variables only at
`Term::Case` branches (`NumCase` arms and leaves bind none), so the path
from the tree's root to a node fixes what every variable past the
parameters is. The kernel finds the node by pointer identity in the body of
the definition `stuck` names (the tree being run is always that body,
peeled of its lambdas: `case_tree`, `unfold_for` and the other entry points
all take it from `g.def(id).body`). It answers only if the node is found
exactly once and the path's binders plus the arity equal `env.len()`, so a
subtree shared between two branches, or a tree from elsewhere, gives no
answer and the rule doesn't fire (only completeness is lost). The
reference doesn't search: it records each branch's binders as it takes the
branch, so the two implementations agree only if both are right.

With the claim, steps 2 to 4 of SW-4686 apply unchanged: the rule fires
only when `r(ps', Proj(D, ·, n)) ≡ is'`, so `C ps' (Proj …) : D ps' is'`,
rule I makes `n` that constructor, and the branch's refinement holds.

**Termination.** Unchanged: the step removes a `case` and adds none, and
`E-PROP-ELIM` still refuses recursive propositions into data. The walk is
finite (a tree is a finite term) and only runs for an indexed proposition
whose scrutinee is past the parameters.

**What stays stuck, and must:** indices that differ
(`examples/soundness/proof-irrelevance-42-enclosing-field-indices-differ.sw`:
`q: Q2 1` through the enclosing type's parameter, and `q: Q2 n` for an
unknown earlier data field `n` of a record taken apart by eta); a data
field in the inner proposition (`E-PROP-ELIM`, `-43`).

**Nothing that computed before is stuck now:** the parameter path is the
same code path (`field_type` with no binders), and the field path only
adds cases where the old code returned `false`.

## Examples and tests

- `examples/accept/proof-irrelevance-42-enclosing-field.sw`: the `g`/`Outer`
  triple and `a4`, the `gk`/`po` pair (`b1`, `b1c`), a field typed over the
  enclosing type's parameter (`c1`), a field two matches deep (`c2`), and a
  field of a record taken apart by iota whose index is an earlier data field
  (`c3`). On `main` `a3`, `a4`, `b1c`, `c1`, `c2` and `c3` are refused; all
  check here, also with `STITCHWORT_DEBUG_FORCE_UNGLUED=1`.
- `examples/soundness/proof-irrelevance-42-…` and `-43-…`: refused, as on
  `main`.
- `proof_masks.rs` test 42 (`Around39`, true at index 0, false at 1), four
  ways. With the reference change reverted it fails as
  `[true, true, true, false]` (the reference alone stuck), so the reference
  path is exercised.
