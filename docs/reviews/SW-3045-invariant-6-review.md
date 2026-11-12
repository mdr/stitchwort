# SW-3045 review: invariant 6 and a kept receiver's generic dictionary

Opus paper review (no builds or tests), 12 Nov 2026, of `lane/SW-3045`
(cf990e5e6, 151a46df6). The lane narrowed `queue::kept_receiver`'s
assertion and its `kept chose` counter to number literals defaulted, dropping
the clause "an operator left with a generic dictionary", on the argument that
since stage 1's projection at the end such a dictionary is no choice from an
unknown.

**Verdict: the argument is right and narrowing is the right end state. No D
question is needed. postponement.md and the assertion's own doc should be
updated before or with the merge (Medium); the code change can merge as is.**

## 1. Can a late dictionary in a kept receiver give a different term?

A generic dictionary can change four things. I traced each one, and none
differs from the term elaborated with the type known.

- **Which instance.** The dictionary is an `Auto` unknown solved by instance
  search (`method_call`, `interfaces.rs:1902-1903`). Search is in §5.10's
  "wait" class (`postponement.md:858`): it returns `Attempt::Wait` on an
  unknown, and in its own saved scope it finds the instance it would find
  with the type known. Local dictionaries are noted in
  `local_dictionaries` (`interfaces.rs:955-960`) and are never projected
  (`:1981`). Elaborated at once, a dictionary found in scope is not a
  record literal, so it stays generic too (`:1914-1928`). Both routes agree.
- **The projection.** `projected` (`interfaces.rs:2013-2030`) uses
  `method_call`'s own match: `unfold_folded` and then `Ctor(_, 0, fields)`
  with `fields[i]` headed by a `Def`. So a user type whose `Mul` field is a
  definition becomes `T.mul x x` on both routes, and one whose field is a
  lambda stays `Mul.mul [T] [T.instMul] x x` on both. For `Nat` and `Int`
  at once, `numbers::operator` skips the dictionary and builds the builtin
  (`numbers.rs:1890-1942`). The library instances' fields are those same
  definitions (`std/core/AddMul.sw:34-41`, `std/core/Ord.sw:65-83`), so the
  late projection gives the same term. The lane's test checks exactly this
  for `Nat.mul`.
- **The receiver's type, and so `.toInt`'s namespace.** Every operator
  that goes through a dictionary has a homogeneous type: `add`/`mul: a → a →
  a`, `lessThan`/`lessEq: a → a → Prop`, and `DecEq`'s `Bool`. The result
  type never depends on which dictionary is found, so the dot call resolves
  from the operands' type alone. A heterogeneous or output-typed operator
  interface would break this. None exists, and adding one would also break
  §5.10's "the choice changes the term but not the meaning". That is the
  risk to record (below).
- **Coercions and term-shape consumers before the end.** Choosing a
  dictionary fixes no type, so no coercion (`effects::coerce`, the
  `decide` coercion) sees anything different. A consumer that reads term
  shape before `finish` could see the generic form, but the ones that
  matter specialise first: `Decide`/`DecideTerm` (`check.rs:5976`,
  `:6025`, `:6038`), lifting (`lift.rs:1067-1069`), and fills
  (`specialise_fills`, `queue.rs:1306`), which carries a kept receiver's
  term, held in its `DotCall`'s fill, to the hash. Values agree anyway: the
  generic call with a solved dictionary reduces to the field.

**Counterexamples tried, none found:**

- **A user `Mul`, fixed later by unification, not by a default**
  (`((x => x * x) 3).toInt` where `3`'s unknown is later solved as a user
  numeric type by another use). Search waits, then finds the user instance,
  and the end projects it by the same rule as at once.
- **Numbers that default to something other than `Nat`.** `-k` is `Int`
  at once (`numbers.rs:326-332`), so it fixes the type before any dot and
  makes no kept receiver. The ladder's default is always `Nat`.
- **An operator whose dictionary decides the receiver's type.** None
  exists (above).
- **The prelude's bootstrap phase.** Before `Nat.instMul` is ready, the
  annotated route uses the builtin while the late route searches and finds
  nothing. That is an error, not a different meaning, and it only affects
  `std/core` files that come before the instances.

The only change the late route makes is that an *unfound* dictionary
reports through the stuck-obligation path rather than as `E-INSTANCE-NONE`
with the operator's note (`numbers.rs:1903-1914`). That is an error
message, not an accepted meaning, and it is not this lane's concern.

## 2. Narrowing, or make the operator wait?

Narrowing is right. §5.10's table already puts `+ * < <=` and `==` in
**decided at finish** (`postponement.md:860-861`, classes at `:868-871`).
Invariant 8 names that class explicitly: a choice "is made at `finish` where
only the term, not the meaning, depends on it" (`:455-460`). §5.5's rule for
a receiver kept as a term that is an application says the same: its choices
"are §5.10's, and invariant 8 makes each of them wait **or not depend on
time**" (`:606-607`). The assertion was stricter than §5.5. Its clause came
from §5.5's pre-stage-1 list, "operator dictionaries (specialised only if
found at once)" (`:566-567`), written before the projection at the end
(as built in stage 1, `:1432-1446`). The record at `:1593-1597` copied that
list. Making the operator wait instead would add an item for every operator
on an unknown type, about 486 generic fallbacks in the corpus (`:869`). The
end result would be the same term, since the dictionary is found by the same
search and projected by the same rule. It would add queue load and nothing
else.

**D question: not needed.** Read literally, invariant 6 says "that
subterm's elaboration can't change with what is learnt later" (`:430-434`),
and the generic call does become the projection at `finish`. But invariant
8, §5.5 and §5.10 are already Matt's design, and they all admit
"decided at finish". The lane brings the assertion into line with them and
changes no end state. If the orchestrator would still rather ask, a draft:

> D3542: Invariant 6 (kept subterms are stable) is read as "the subterm's
> *final* term can't change": a kept receiver may hold an operator whose
> dictionary is projected at `finish` (§5.10's decided-at-finish class), as
> invariant 8 already allows. Record this in postponement.md? [rec: yes]

## 3. Findings

### Medium

1. **postponement.md contradicts the code after this lane.** Update in the
   same lane (paper, about 10 min):
   - §5.5, `:565-567`: operator dictionaries are now "decided at finish
     (§5.10)", not "specialised only if found at once". The bullet at
     `:606-608` should say the debug assertion checks literals defaulted,
     and that operators are excluded because they are decided at `finish`.
   - Invariant 6 (`:430-434`): add "(its final term: a choice §5.10
     decides at `finish` is allowed, as for invariant 8)".
   - Stage 2's as-built record of the assertion (`:1593-1597`) and
     deviation 4 (`:1712-1714`): add a dated note that SW-3045 dropped the
     generic-dictionary clause and why, naming `Int.toIntSumBy`
     (`std/Int/Sums.sw`) and the minimal repro. Also note that stage 2's
     "`kept chose` is 0 everywhere" (`:1654`) predates std's
     `Int.toIntSumBy` case: that count was 0 because the test didn't exist
     yet, or because the clause wasn't reached then.
   - §5.10, add a line to the decided-at-finish class: what the class needs
     is that each such operator's result type doesn't depend on the
     dictionary (homogeneous `a → a → a`, `Prop`, `Bool`). An operator
     interface with an output type would have to wait instead. This is the
     one way a future change could make the narrowed assertion unsound, so
     it should be written where the next interface designer will read it.

### Low

2. **The narrowed assertion's doc is stale and the check is nearly
   vacuous.** `kept_receiver`'s doc (`queue.rs:1852-1855`) and
   `Defaulted`'s own doc (`numbers.rs:29-31`) say a literal "made `Nat` at
   once". Since K4, `attempt.defaulted` is pushed only by the ladder's
   `apply_default` (`numbers.rs:427`, `:1415`, `:1452`), each asserting
   `settling()`. So the clause can only fire if a default was applied while
   the receiver was inferred. That happens only at a closed pattern (a
   `rewrite` rule, or a fact for `omega`/`ring`, `queue.rs:85-92`) inside the
   receiver. Suggested rewording: "no default applied (a closed pattern's)
   while the receiver was inferred: the receiver's own literals wait (K4)".
   Keep the assertion: §9 row 6 (`:1246`) requires it, and it is a cheap
   tripwire if at-once defaulting comes back.
3. **A possible false positive in the remaining clause.** A kept receiver
   containing a closed pattern whose own literals are defaulted (an
   application with a `by omega [3 ≤ n]`-style argument, plus a literal that
   blocks a `.field` on the result) would fire in debug. Invariant 7
   sanctions it, and a closed pattern doesn't depend on outer unknowns. It
   is rare and not seen in the corpus. If it ever fires, exclude defaults
   made inside a closed pattern (the snapshot could record the closed
   pattern's depth). Don't act on it now.
4. **Unrecorded at-once choices are outside the counter.** `-k` and a group
   with `-` are made `Int` at once (`numbers.rs:326-332`, group step 4).
   These are §5.10-style choices from an unknown's shape, but they are
   missing from §5.10's table and from `defaulted`. A wrong guess is a type
   error (`Nat` can't be negative, and `Float` would mismatch), so they
   belong in the "allowed" class. Add a row to §5.10's table and make no
   code change. Pre-existing, not this lane's.
5. **The lane's test is good.** It compares the kept form with the
   annotated form by `body_of`, which is §9's must-hold shape, and checks
   for `Nat.mul` and against `Mul.mul`. Optional: a second case on a
   user type with its own `Mul`, if a receiver whose blocker is made
   inside it can be written for one (with K4 a bare literal ends as `Nat`,
   so it may not be expressible).

## Findings to file (from the lane's board notes, not this review)

- `queue::tests::an_undone_attempt_restores_*` (3 tests) fail in a debug
  build on unchanged code ("an item waits again only on an unknown head").
  It is a debug-only assertion, so release CI doesn't see it.
- SW-3046's `E-RESOURCE` (`SortLemmas.sw:343`) is now the first thing the
  debug std test stops at.
