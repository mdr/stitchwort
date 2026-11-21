# SW-4474 review: `cases x, y then t` (SW-4492)

Opus review (D2364) of `lane/SW-4474` at 239b93f09, before merge. Read: the
whole diff, `crates/elab/src/cases.rs` around the new code (`node`,
`split_on`, `split_disjunction`, `substitute`, `Finder::is_known`), the
parser and lowering, the self-hosted parser's `casesExpr`, the docs. Probed
with the lane's release binary on scratch files (each named below; all
under a minute, one at a time).

**Verdict: no must-fix.** Mergeable as is; finding 1 should be fixed in this
lane or filed at once, since it is the first thing a user of the new form
will hit.

## Should fix

**1. `t` can't name the variable it split; the docs don't say so.** In a
case of the named split of `d`, the goal has `False` in place of `d`, but
`d` written in `t` is still the variable, so a `t` that mentions it fails
with a type mismatch. `cases then t`, which doesn't split `d` before `t`,
proves the same theorem with the same `t`:

```
type Code = | C0 | C1 | C2
theorem w14 ∀ (p: Bool → Code → Prop) (q: Code → Prop) (ok: ∀ (d: Bool) (k: Code) => q k → p d k)
    (d: Bool) (k: Code) (hk: q k): p d k := cases d then ok d k hk
-- E-TYPE-MISMATCH: expected `p False k`, but this has type `p d k`
--   in the case d = False, this is what the term after `then` gave
```

Hypotheses are fine (the generalising `match` copies them, which is why
`cases edge then free first` works); it is the split variable itself.
The proving guide says to write `_` for "the fields the split doesn't
name", which a reader takes to mean the named value itself can be
written. Since the user named `x`, `t` mentioning `x` is the common
case. Options, in order of preference: (a) in each case of a named split,
let the target's name in `t` stand for its constructor form (a `let x :=
C a b` around `t`, or resolving the name to the case's value); (b) a note
on `t`'s mismatch when the expected type has a constructor where `t`'s type
has a named target ("in this case `d` is `False`: write `False` or `_`"),
plus a sentence in syntax.md and the proving guide. (a) is the end state;
(b) is the cheap minimum. Orchestrator's call which.

A variant shows up with the written-fact substitution: in
`cases d then ok d k hk` with `hk: k = C1`, `t` fails first for the reason
above, then `k` is substituted and `t` is tried again, and the error shown
is the second one, `expected C1 = C1, but this has type k✝ = C1`, naming
neither `d` nor the substitution (scratch `wf11.sw`). Fixing (a) removes
it; with (b) the note should be on the first failure.

**2. Inside a record or tuple literal, the name after `cases x,` is
taken as a second target.** `{ left = a => cases a, right = b => cases b }`
reads `right` as a target and fails with `E-PARSE expected , or }, but
found =` at the `=`, with no hint (scratch `p2.sw`; a tuple,
`(a => cases a, b => cases b)`, fails the same way at `=>`). Not a
regression, since `cases a` was a parse error before (checked with
`main`'s binary), but the error points away from the cause.
`crates/syntax/src/parser.rs` `cases_expr`: stop the comma list when the
name after the comma is followed by `=`, `:=`, `=>` or `:`, or give the
error a note ("`cases a, right` names two values to split; bracket the
`cases` to end it there"). The first keeps the self-hosted parser's later
port simpler.

**3. No reject example for a proposition other than `∨`.** The four reject
examples cover not in scope, an equation, the budget and `t` failing. The
limit the docs and the ticket stress, `h: A ∧ B` can't be named, has none;
its message is good (`` `h` can't be split: it is a proof of `a ∧ b`, a
proposition other than an `∨` ``, at the name; scratch `tree.sw` t3). Add
`examples/reject/cases-named-proposition.sw` with its snapshot. An indexed
family has none either; lower priority.

**4. The language guide leaves out the limits.** `docs/guide/10-proofs.md`'s
new paragraph says "splits nothing else" and that a stuck field is split,
but not that a field of a recursive type isn't, or that only data and `∨`
can be named. syntax.md has both. One sentence in the guide.

## Notes

**5. Soundness: nothing new is trusted.** Every split goes through the
existing `split_on` (a generalised `match`) or `split_disjunction`, and the
written facts through the existing `substitute`, whose motive is
elaborated and checked as before; the result is an ordinary term the
kernel re-checks. No path returns a term that skips checking, and no new
term former or reduction is used, so `docs/core.md` needs nothing. The
case equations are the ones `split_on` always made; `named_fields` only
reads them (left side a found variable, right side a constructor form) to
choose what to split next.

**6. Termination.** A named data target is split only while
`!finder.is_known(var)`, an `∨` only while its name isn't in `split_ors`,
nested `∨` sides likewise; field candidates are non-recursive, not known
yet, and each is split at most once per path; the 64-case and step
budgets still apply. A one-constructor record (adds no case) is
recognised as known after its split (scratch `rec.sw`: `cases p then …`
closes, and a false one gives an open case, not a hang). Nested recursion
(`Tree = Leaf | Node (child: Option Tree)`) stops at the inner `Tree`
(`tree.sw`). A cyclic written fact (`h: xs = [a, ..xs]`) is not
substituted (`wf5.sw`); `n = n + 1` is closed by `arithmetic` as a
contradiction, which is right.

**7. The written-fact substitution.** Checked: a variable on either side
(`k = C1`, `C1 = k`), a hypothesis depending on `k` and `k` used in several
(`g: Good k`, `j: isC1 k = True`), a variable whose type depends on the
substituted one (`i: Fin n` with `h: n = 3`), the named target itself having
a written fact, two contradictory facts (`wf2.sw`, `wf7.sw`): all check or
fail as they should. The facts it uses exclude `cases`' own equations
(`is_equation`) and anything already substituted.

**8. Plain `cases` and `cases then t` are unchanged, by reading as well as
by hashes.** With `targets` empty: `node` skips both new branches;
`split_disjunction(…, None)` adds nothing to `named_facts`; `substitute`'s
`written` is false, so its early return and its fact filter are the old
ones (the `written && written_fact(cx, l)?` short-circuits before the
`?`); the new "`name` says they are equal" message is only for a fact not
in `injected`, which plain `cases` never uses; `budget_error` adds no note
(`splitting` is `None`) and keeps the old closing note; `run.limit()` is
the old expression. Lowering of `cases then t` still finds `then` as the
second leaf. I found no path the tests wouldn't reach that differs.

**9. The parser: no existing program changes meaning.** The names are read
only in `cases_expr`, reached from `expr_inline` when `cases` starts an
expression; there `cases x` was a parse error on `main` (`main`'s binary:
"expected the end of the declaration, but found `a`"). As an argument,
`cases` is still a bare atom (`bare_cases`), so `f cases x` is unchanged.
A grep of every `.sw` file on `main` for `cases` followed by a name on one
line finds only argument uses (`pairNoneParts … cases none`,
`Point.ext … cases cases`, `solidChars first others cases cases`) and
`cases then`; none changes meaning.

**10. A second name may be on the next line.** The first name must be on
`cases`' line (`line_start` check) but the comma loop doesn't check later
ones, so `cases a,⏎ b then t` parses. Harmless (the comma says it
continues); syntax.md's "the names are on `cases`' own line" is slightly
stronger than what's built.

**11. Errors are at the right spans.** Not in scope and not splittable
label the name; the budget labels the whole `cases` and names the split
that went over (`` it went over splitting `c` ``, and for a field
`` `o : Option Text`, a field of `edge` ``); `t`'s failure is `t`'s error at
`t`, with the case path. The open-case path in a field-split case shows
fields as `a✝ = False, p = { … }, b✝ = False` (field equations before the
target's), readable enough. The existing "stuck on `value✝` … (or `cases
value✝`)" hint suggests a split by a name that can't be written; old text,
but more visible now that `cases x` exists (`tree.sw` t1). Could say "a
`match` on the field" when the name is inaccessible.

**12. A side of a named `∨` that is an `∨` is always split.** No way to
keep `B ∨ C` whole for `t`. Fine for now (a `t` that wants it whole can be
the hand `match`); worth a line if anyone asks.

**13. Shadowing.** After `introduce`, a goal binder with a target's name
is what the name finds next (`∀ (x: Bool): ∀ (x: Bool) => …` with `cases
x` splits the inner one, `let.sw` l3). Reasonable: the name means what it
means in scope.

**14. Self-hosted formatter.** `tools/fmt/src/Syntax/Statements.sw`
`casesThen` makes `cases` an atom when no `then` follows, leaving the name
to its caller, which refuses it as `main`'s Rust parser did; the lane
changes nothing under `tools/fmt/src/Syntax`, so nothing it accepted is now
refused. The new form is new syntax, so refusing it narrows nothing. Not
run (`task fmt:twin` builds; outside a paper lane). Taking it into slice
6a is Matt's question. The three `JoinProofs` conversions change proofs
only, not statements.

## The lane's decisions

- `cases x` without `then`: agree; it mirrors `cases`.
- Named splits before `t`: agree, that is the feature; but see finding 1.
- Field splits only after `t` fails, the stuck-on field before
  `arithmetic`: agree; it keeps `t`'s cases as the proof's.
- One try: agree; there is nothing to choose differently.
- Recursive fields never split: agree; that would be induction.
- No `tools/fmt` change: agree (finding 14).
- No new keyword: agree; `cases` is already reserved, and the names are
  told apart by position.
- Written-fact substitution only in the named form: agree for this merge,
  since in plain `cases` it moved 10 proofs' terms; it does make the two
  forms differ in more than what they split. The follow-up to let plain
  `cases` do it too should be filed (hash churn doesn't count against it,
  D2303).

## Docs

syntax.md describes it as built, with the limits (nothing unnamed split,
recursive fields not split, propositions other than `∨` refused); it lists
`arithmetic` and deciding before the other fields but not introducing
binders and applying an implication, which `named_rest` also tries
(minor). The proving guide's entry is accurate. The language guide: finding
4. The ticket's "data declarations called 'data'" wording: not found in
syntax.md in two minutes either; it reads "data type" throughout, which
is right.
