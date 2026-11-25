# SW-4784 (termination: `match k + 0`) — Fable review

Reviewed: `git diff main...lane/SW-4784` (commit dbb886858), `crates/core/src/termination.rs`
(`without_plus_zero`, `relate`, `rebuilt`, `inline`, `wrapped`, `part_of`), `nat_add.rs`,
`check.rs` (define_group), `docs/core.md` step 4. Probes run with the lane's release binary
(files a..l.sw beside this note). No test suites run.

## Verdict

**Sound, but don't merge it: drop the kernel change (option b).** If it is merged anyway,
it needs the three changes under "If merged".

## 1. Soundness: no hole found

- **Meaning.** The rule claims `a + 0` is equal to `a`. With the rule bound, `Nat.add a 0 ≡ a`
  by conversion in both evaluators for every `a` (R3 when `a` is stuck, R1/R2 then R3 when
  it isn't), and in every run (`Nat.addZero`). So rank, relevant rank and the open-term size
  are those of `a`; `≤`/`<` are kept. A `case` on an inlined parameter given `x + 0` fires
  exactly when `x` is a constructor or number, so "every `<` comes from a case that fired"
  still holds.
- **Whose `+`.** The head is compared by `DefId` with `builtins().nat_add_rule`, which is set
  only in `nat_add::register` after the pin and the `addZero`/`addSucc` type checks. A user
  `myAdd`, a shadowing name or a copy of `Nat.add` has another id: probe c (`match myAdd k 0`)
  is refused. With the rule off (`None`) nothing is stripped.
- **Arity.** `Nat.add` is `Nat → Nat → Nat`, no implicit or level arguments in the spine;
  `[a, b] = args[..]` is exact, so partial and over-applied spines are left alone. The body
  has been type-checked before `check_group` runs (`check.rs` ~2866-2876), so `a : Nat`.
- **Literal.** `Term::Nat(Rc<BigUint>)`; `bits() == 0` iff zero. `Zero` as `Term::Ctor` is not
  recognised (conservative; see F3).
- **Calls inside `a`.** `walk` still walks the original arguments, so a member call inside
  `a + 0` is still recorded.
- **Other users of relate/rebuilt** (`let`, call arcs, `alias`, `part_of`, pinned fields): all
  only need "equal to that variable / rebuilt constructor", which holds. Pins: `pins_var`
  needs the later field's type to be `Term::Data`; a field that can hold `x + 0` is `Nat`,
  which has no arguments, so `Pins::All` passed through pins nothing new.
- **Probes.** `f (Succ m + 0)` and `f (Succ (m + 0) + 0)` under `match n + 0` are reported
  "stays the same" (d, e); `f ((m + 0) + 0)` accepted (g); `let j := k + 0; f (j + 0)`
  accepted (k) — all correct.
- **Second checker.** There is none: `termination::check_group` is called only from
  `check.rs`; `reference.rs` is an evaluator only.
- **Cache.** Trusted replay never re-runs termination; the kernel-side fingerprint covers
  `crates/core`, so entries cross this change only through the re-check. Accepting more is
  safe in that direction.

Not verified: I did not run `examples::soundness` (paper lane), and the lane's ticket note
doesn't say it did. A kernel change should have that set run before merge.

## 2. Is it the right fix? No — recommend (b)

- **Nobody writes it.** `match k + 0` exists only because SW-4775's fixture used `+ 0` as a
  throwaway way to get a non-variable scrutinee. Repo search finds it only in this lane's
  two new examples.
- **The rule is arbitrary from outside.** Same binary: `k + 0` accepted, but `k + Zero` (a),
  `0 + k` (b), `k - 0` (i), `id2 k` (h) refused, all convertible to `k`. A user can't
  predict it and the E-TERMINATION notes don't explain it.
- **It breaks the checker's stated principle.** `core.md` step 4: other functions' results
  are unknown, and relations are "decided from the terms, never by conversion". This is the
  first rule justified by a conversion rule, and it ties the termination checker to
  `nat_add.rs`.
- **Precedent goes the other way.** The shape people do write, `match (k, a) with`, is also
  refused (probe l), and is handled by a diagnostic note ("match them directly"), not by a
  kernel rule.
- **(c) general rule** (argument normalises to a variable/constructor): the walker has no
  value environment, so it needs one mirroring `vars` (inlined parameters, branch
  refinement), evaluation + readback of arguments under the member's transparency set, a
  budget path (E-RESOURCE from termination), and a restated open-terms argument. Cost is an
  evaluation of most call arguments (most are "unknown" today) unless restricted to lifted
  matches. Est. 150-300 trusted lines plus spec. It still wouldn't cover the tuple case.
  Not worth it for the demand shown.
- **What (b) is.** Leave the kernel alone. Close SW-4784 as by design; keep
  `examples/reject/termination-match-plus-one.sw` if wanted, and turn
  `termination-match-plus-zero.sw` into a reject example. If the shape should work one day,
  do it in the elaborator, untrusted: a scrutinee whose weak head normal form is a variable
  is matched as that variable (no lifting). That covers `0 + k`, `k + Zero`, `id k` as well
  and adds nothing to the kernel. (I did not read the elaborator's lifting code; the size
  of that change is unestimated.)
- The walk test SW-4775 wanted (byWalking under a lifted match) needs a scrutinee whose
  pieces the recursion doesn't use; I did not work out why the walk's recursive call lands
  on `m` here rather than `more`.

## 3. docs/core.md

Yes, it specifies the accepted shapes exactly (Definitions step 4, lines 155-160, and the
"Termination" bullet near line 278), and `termination.rs`'s header does too. The lane
updated neither, so both are now wrong ("other functions' results" are unknown; "never by
conversion"). D3210 requires the update in the same lane.

## If merged (required)

1. `docs/core.md` step 4, after the `≤` bullet: "An argument `a + 0`, with `+` the library's
   `Nat.add` while its rules R3/R4 are bound and `0` the number literal, has the relation
   `a` has, and is rebuilt as `a` is: it equals `a` by R3. This is the one place a relation
   rests on a conversion rule; no other function's result is looked through (`0 + a`,
   `a + Zero` and `a - 0` stay unknown)." Amend "never by conversion" in the `let`
   sentence, and the same in `termination.rs`'s header ("unknown: anything else").
2. Either accept `Zero` (`Term::Ctor(nat, 0, [])`) as the second argument too or say in
   the doc comment why not.
3. Run `examples::soundness` (kernel change).

## Findings, ranked

- F1 (decision): special-cases one identity in the trusted checker for a fixture-only
  shape; recommend drop.
- F2 (required if merged): `docs/core.md` and the module header not updated; both now
  contradict the code.
- F3 (minor): `k + Zero` refused where `k + 0` accepted (probe a).
- F4 (follow-up ticket): a lifted match on any non-variable scrutinee gets only the generic
  E-TERMINATION text; the tuple case has a tailored note. Generalise the note: "`match e
  with` matches a computed value, so what it binds isn't seen as a part of `k`; match `k`
  itself".
- F5 (optional ticket): elaborator matches a scrutinee that normalises to a variable as
  that variable.
