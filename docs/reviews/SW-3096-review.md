# SW-3096 review: pattern `let`s read test facts on the projection path

Opus review (D2364: changes how proof terms are built from test facts), 13 Nov 2026.
Branch `lane/SW-3096`, commit 228e41fd4.

**Verdict: merge.** The term is built exactly as the `match` path and the
constructor path build theirs, and every case I tried agrees with the `match`
path, in what's accepted and in the errors. Two test gaps are worth closing
in a follow-up or before merging. Neither is a soundness question.

## The term

`read_fact` (`crates/elab/src/patlet.rs:319`) does the same as `read_case`
(`crates/elab/src/lib.rs:5385`), in the same order:

1. `variable_as_written`
2. `test_fact`
3. `read_through`
4. a guard that the reading's data is the pattern's data
5. `found.forward(Var h)`

It differs from `read_case` in two ways:

- It binds the result as a hidden `let` (`%p : found.prop := forward h`)
  instead of a hidden variable that is split.
- It drops the `readable_data` check. That check only tests for `Prop`, and
  `proof_ctor` already requires `Prop`, so dropping it changes nothing.

Why the term is well-typed:

- **The `let`'s value.** `forward` chains `Iff.forward fact prop (r args)`, or
  for a decision step `Decidable.sound`/`refute`, step by step, ending at
  the last step's `prop`. `read_through` sets `found.prop` to that same
  `prop`.
- **The `let`'s type annotation.** It is `quote_folded(found.prop)`, which
  matches the value's type.
- **The first step's `fact`.** It comes from the test that `as_written`
  checked by `conv` against `h`'s type, so the kernel accepts `h` as that
  argument.
- **The projections.** They use the parameters of the *forced* `found.prop`
  (`Data(And, [A, B])`). These are the same parameters as the constructor and
  `match` readings use.

So the term is well-typed by the kernel's rules, by construction. It is the
same construction as `reading::for_ctor` and `read_case`.

A term like this was never accepted on this path before: a test fact's
type is an `Eq` and never unified with `And`. So the change only turns
errors into acceptances or into better errors. No previously accepted term
changes, and std's terms are unchanged. Std's `let Both` sites either take
the `match` path or aren't test facts.

## Probes (lane's release CLI, rebuilt at the branch head)

All of these check, with goals that aren't evidently propositions
(membership, a `Nat` result):

| Probe | Result |
|---|---|
| Nested `let Both _ (Both less below) := h`, with the parts used | checks |
| A `= False` fact: `(a == 0 \|\| b == 0) = False` taken apart with `Both` | checks |
| A two-step reading: `Bool.not (a \|\| b) = True` read to `a = False ∧ b = False` | checks |
| An expression scrutinee: `let Both rowIn _ := And.right h` (hidden `%p`, then read) | checks |
| A scrutinee that is a test fact only through a `Prop` definition (`def Inside a b: Prop := both a b = True`), on both paths | checks |
| A lambda pattern `(Both x y) => …` on a test-fact parameter, in a `def` into `Nat` and in a theorem | checks |
| A `def` into `Nat` and a `def` into an equation projecting a read fact | checks |

The errors are the same on both paths (projection goal against `match`
goal):

| Case | Both paths give |
|---|---|
| A test with no reading (`opaque def mystery`) | `E-NO-READING` "`mystery n` has no reading, so it has no parts", the same span |
| A reading of the wrong shape (`a \|\| b`) taken apart with `Both` | `E-NO-READING` "reads as `a ∨ b` … this pattern matches an `And`" |
| `let Inl x := h` on `(a \|\| b) = True`, `let Inr x := h` on `(a && b) = False` | still `E-LET-REFUTABLE` |
| A record pattern `{ left, right }` on a test fact | `E-NOT-A-RECORD` |

`Or` isn't a `proof_ctor` (it has two constructors), so `Inl` and `Inr` never
reach this path. `Witness` doesn't reach it either, because `Exists`'s
witness field has no accessor. Both stay `match`es, unchanged.

## Findings

### Blockers

None.

### Should fix

1. **The accept example never uses a part read on the projection path**
   (`examples/accept/readings-unfold-defs.sw:25-41`). In `membershipGoal`,
   `existsGoal` and `methodGoal`, the bound `same` and `rowIn` are never used.
   The body returns `member` or `Witness …` unchanged. `membershipFromPart`
   uses only `here`, which isn't from a reading. So the example shows that the
   `let` elaborates, but not that the parts have the right types.
   - Make each body consume the part, as in
     `(m: sameRow a b = True → b ∈ spots) … m same`.
   - Add a nested case whose inner part is used (`let Both _ (Both less
     below) := h; m less below`).
   - Add a lambda-pattern case and a `= False` case.

   All four check (probes above).
2. **No reject example for `E-NO-READING` on the projection path.** The new
   branch in `read_fact` (`patlet.rs:339-353`) is not covered by any test. A
   `reject/` example with a membership goal and `let Both x _ := h` on an
   `opaque` test would pin it (probe `e1` above gives the expected output).

### Notes

3. **The debug `E-RESOURCE` on `reject/reads-nested-binds-unknown-field.sw`
   is not this lane's.**
   - That file has no pattern `let` and no pattern lambda: every lambda
     parameter is a plain variable. So `patlet::applies` returns false at
     `parts`, and `read_fact` is never reached.
   - The std terms it loads are unchanged (see "The term").
   - The lane's debug CLI checks the file correctly in 68 s, with
     `E-UNKNOWN-FIELD`.
   - The examples harness runs under `Limits::for_stack(16 MiB)`. The likely
     cause is debug-build frame sizes, or debug slowness against a limit, on
     this 12-deep nest. That is pre-existing.
   - I didn't build main's debug test binary to confirm, because that is
     outside a review's budget. If it matters, it is worth a backlog ticket:
     "reads-nested-binds-unknown-field hits E-RESOURCE in debug builds".
4. **`patlet::proposition` misclassifies `x ∈ xs` (`List.Mem …`, a call into
   `Prop`) elsewhere.** This is pre-existing, and there is a real bug outside
   this lane:
   - **The bug.** `crates/elab/src/induct_match.rs:151` rejects `match induct`
     on a membership goal with `E-MATCH-MOTIVE` ("`match induct` proves a
     proposition, and this isn't one"). Main's release build does the same.
     Repro:

     ```
     def keepBig: List Nat → List Nat
       | [] => []
       | [x, ..rest] => if 5 < x then [x, ..keepBig rest] else keepBig rest
     theorem bigIn (xs: List Nat) (y: Nat) (h: y ∈ keepBig xs): y ∈ xs :=
       match induct (keepBig xs) with
         | eq1 => ?
         | eq2IfTrue x rest c ih => ?
         | eq2IfFalse x rest c ih => ?
     ```

   - **Other uses.**
     - `check.rs:4721` doesn't record a `_` against a membership goal as a
       proof hole.
     - `matching.rs:1724` skips its check for such goals.
   - **Better classifiers that exist.** `cases::is_proposition` (it asks the
     kernel for the sort) and `rewrite::is_proof_type` both classify these
     goals correctly.
   - **Recommendation.** File a ticket to switch `induct_match.rs` (at
     least) to `cases::is_proposition`, and to audit the other callers. Keep
     patlet's cheap check for `applies`: there, a wrong "not a proposition"
     now only means projections in place of a `match`, and after this lane the
     two agree on test facts.
5. **History in the design doc.**
   `docs/proposals/bool-as-proposition.md` (the paragraph added after
   §6.1's list) says "Before SW-3096 that path skipped the reading, so …".
   A proposal states the design. Better: "a `let` that binds projections …
   reads the same way", with the history left to the commit message. This is
   minor.
6. **A pre-existing grammar slip.** `crates/elab/src/records.rs:223` prints
   "matches a `And`". `no_reading` already chooses between "a" and "an";
   this message doesn't. This is a small ticket.
7. **The hidden binding's name.** The hidden `let` is named `%p`, the same as
   patlet's other hidden lets, where `read_case` names its variable `read`.
   Neither can be written or shown, so this is harmless.

## Tests run

- I rebuilt the lane's release CLI (`cargo build --release -p stitchwort-cli`,
  58 s, `nice -n 19`), then ran `stitchwort check` on the scratch probes listed
  above. They are summarised here, not committed.
- I ran the lane's debug CLI on
  `examples/reject/reads-nested-binds-unknown-field.sw`. It gave the expected
  `E-UNKNOWN-FIELD`, in 68 s.
- I ran main's release CLI on the `match induct` repro, which confirmed that
  finding 4 exists on main.
- I ran no test binaries.
