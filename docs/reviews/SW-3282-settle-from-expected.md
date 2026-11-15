# SW-3282 review: `settle_from_expected`, a call's ability type arguments from its expected type

Reviewer: Opus, 15 Nov 2026. Branch `lane/SW-3282` (81d55a3ed), elaborator
commits d975482b7 and 7faa9d088 only. Probes ran on two binaries:

- **BR**: the branch's release binary (built 01:36, after the last edit
  to `check.rs` at 01:25).
- **NOSETTLE**: `main`'s release binary (654879cd5, which has stage 0)
  run with `--std-dir` on the branch's std. That is the branch without
  `settle_from_expected`.

Where it mattered I also ran `main` on its own std. The probe files are in
the review's scratch folder (`g*.sw`, `t*.sw`, `r1.sw`, `c3*.sw`, `run.sh`).

## The change

`settle_from_expected` applies when an application is elaborated by
`fallback_inferred` with a known expected type. That means its result
depends on an explicit argument, so `propagation_plan` has no plan, or a
by-arguments plan failed (`after_arguments_failed`). It also needs the
first argument to be explicit, no named arguments, and an empty supply.
Then, if the head's result (past every binder) is a call of the same
definition as the unforced expected type, with the same number of
arguments, each leading `Implicit` parameter `t` is given the expected
type's argument at that position, as `[t := …]` would. The parameter must
be a `Sort`, appear alone at some position of the result's spine, and
appear alone as an argument of an ability in a row of some later
parameter's type. The other leading implicits get unknowns, as
`insert_with` would give them. `readsThen`, `readsWeaken` and other
lemmas whose result mentions only implicits never reach it: they go
through stage 0's plan.

## Verdict

Sound, general, and safe in every program shape that std, `aoc/` and the
examples use. The kernel re-checks everything, and the final comparison
still checks the whole type, so nothing wrong can be accepted. The gain
is real and confirmed: 2020 day 2's `runsPieces` takes 6.16M steps on
BR, 9.34M on NOSETTLE and 5.41M on main before generic Parse. The node
counts are identical between BR and NOSETTLE (1660 for `runsPieces`, 8952
for the namespace), so the elaborated terms are the same.

There is one theoretical regression. Unlike stage 0's plan and the plain
plan, the early commitment has no fall-back when it fails. So a program
whose expected type matches the lemma's result only by unfolding
definitions, not argument by argument, is rejected where main accepts it
(S1). That needs a definition whose type parameter doesn't matter to its
unfolding. None of the gates hit one. I'd merge and ticket it.

Errors on mismatches move from the whole call to the offending argument,
which is mostly better (S2 for one misleading note). Stage 0's failure
path still reports the real slip, for characters and for tokens. The rule
keys on rows, not on names. Q5 has a large measured win available (giving
`b` too: day 2's `runsPieces` drops to 4.46M, below main), blocked by a
pre-existing bug (S3).

## Must-fix

None.

## Should-fix (ticket)

**S1. The early commitment has no fall-back, so a match found only by
unfolding is rejected.** Probe `g5.sw`:

```
def Ph3 (u: Type) (n: Nat): Prop := n = n
theorem ph3 ∀ (p: () → {Src t} a) (n: Nat): Ph3 t n := rfl
theorem usePh3: Ph3 Char 0 := ph3 natSrc 0      -- natSrc: {Src Nat} Nat
```

- main and NOSETTLE accept it: `t := Nat` from `natSrc`, and then
  `Ph3 Nat 0` and `Ph3 Char 0` unfold to the same thing.
- BR rejects it with E-TYPE-MISMATCH at `natSrc`: "expected
  `() → {Src Char} ?0`".

`g6.sw` is the dependent version: `def Dep (k: Type 1) (x: k) (n: Nat)`,
lemma result `Dep Type t n`, goal `Dep (Type → Type) ((b: Type) =>
List b) 0`. There `t` is given `b => List b`, which isn't a `Type`, and
the error shows the ill-kinded row `{Src (b => List b)}`. No panic, and
the kernel would catch anything worse, but d975482b7's commit message
claim ("what is given has the parameter's type whenever the call's type
matches at all") holds only for argument-wise matches.

The plain propagation plan has the same early guess, but it recovers:
`g3.sw` (`Ph t` with no explicit argument in the result) goes through the
plan, fails, is re-elaborated, and is accepted on BR. The stage-0 plan
recovers through `after_arguments_failed`.

Realistically this needs a result head whose type parameter doesn't
affect its unfolding. In a well-typed goal `Parse.Runs [Char] q …`,
`q`'s type pins the `t` position, and `Runs` unfolds over `State t`. So
no std or AoC shape hits it.

Suggested fix: take a snapshot before settling. If the application then
fails, restore it and elaborate without settling, with a counter, as
`no_argument_propagation` does, so a failing nested chain isn't
elaborated twice at every level. That restores "anything main accepts is
accepted by construction". Which error to report when both fail is a
choice. The settled error is usually the clearer one (S2), but main's
keeps messages unchanged. I'd report the settled one.

**S2. The mismatch error is better placed, but it carries a misleading
note.** Probes `g2.sw`, `g8.sw` and `r1.sw` (`bad2`) pass a parser whose
`t` differs from the goal's:

- BR reports at the parser argument: "expected `() → {Parse Tok} ?0`,
  but this has type `() → {Parse Char} Nat`". The row clash is plain to
  see.
- NOSETTLE reports at the whole call, with the expected type printed
  unfolded ("expected `∀ (state: Parse.State Tok) … => …`, but this has
  type `Parse.Reads (arg => Std.Effect.bind …) …`, they first differ at
  `Tok` against `Char`"), or at an unrelated argument (`g8`: "expected
  `Bool`, but this has type `Nat`" at the numeral `5`, when the parser's
  `St Bool` row is the slip).

So BR is better in all three. But each BR error adds "Note: `?0` is the
implicit argument `a` of `Parse.readsMap`, which wasn't worked out …;
give it with `[a := …]`", which sends the reader after `a` when the
clash is `Tok` against `Char`. This is pre-existing (any partly-known
expected type does it), but settling makes it common in this error.
Small ticket: drop the unsolved-implicit note when the two types already
differ at a solved position, or when the unknown is in a position that
matches anything.

**S3. The large remaining win (Q5) is blocked by a pre-existing bug: a
correct `readsThen` chain with `[b := …]` written fails.**

Measured on `runsPieces`, with NOSETTLE and hand-written implicits on the
seven `runsBind` calls, then put back:

| | steps |
|---|---|
| main, before generic Parse | 5.41M |
| BR (settles `t`) | 6.16M |
| NOSETTLE, `[t := Char]` by hand | 6.13M (settling `t` = writing it) |
| NOSETTLE, `[t := Char] [b := Entry]` by hand | **4.46M** |

So also giving `runsBind`'s `b` (alone in the result `Runs [t] [b] …`,
not in a row) would put day 2 about 18% *under* its pre-generic figure,
not 13.7% over. Day 2's `j` and `value` are `_`, so `b` stays unknown
until the end today.

But `c3tb.sw` (the stage-0 three-step `readsNat` chain, correct, with
`[t := Char] [b := List Nat]` at each level) fails on both BR and
NOSETTLE. The error is E-TYPE-MISMATCH at the second level's
`Parse.readsNat`, with expected `∀ (state: Parse.State Char) …` (the
unfolded `Reads ?p ?first`). With `[t := Char]` alone (`c3t.sw`) it
checks. This is the finding the lane noted, and the reason its first
version broke `readsThen` chains.

My hypothesis, not traced: with `b` known, the inner `readsThen`'s plain
unification in `propagation_plan` succeeds by a flex-flex or pattern
guess on `?j x0`. That makes the plan plain rather than by-arguments, so
its failure goes through `propagate_failed` (bare `infer`,
`no_propagation`), the path behind M1 in the SW-3281 review, instead of
`after_arguments_failed`.

Ticket: root-cause `c3tb`. Then re-try settling every type parameter
that is alone in the result, as d975482b7 did, against the same gates.

## Nits

**N1.** d975482b7's commit message says what is given always has the
parameter's type whenever the call matches. Not when it matches by
unfolding (S1). The code comment after 7faa9d088 doesn't repeat the
claim, so nothing to change in code.

**N2.** `row_arguments` looks through function types only. A row under a
type constructor is missed, so `Parse.readsOneOf`'s `t` (in
`alternatives: List (() → {Parse t} a)`) isn't settled. That only costs
speed, which is fine. Worth one line in the doc comment ("rows in
parameter types and their function types").

**N3.** `call_parts(expected)` looks at the unforced value. An expected
type that is a solved unknown (`Value::Flex`) is skipped, even when its
solution is the right call. Again this only costs speed.

**N4.** `stitchwort_core::value::Elim::App` is spelled out in full twice.
A `use` would read better.

**N5.** Stage 0's reject example `reads-chain-unknown-name-last-step.sw`
has a second error hidden behind `xBad`. Its `Spec … := True` is the
`Bool`, so the final `Trivial` fails with E-NO-READING ("`True` has no
reading") once `xBad` is fixed. The test checks the first error, so it
passes. The example would read better with a provable spec (`made =
made` with `rfl`, as in `c3ok.sw`).

## Questions from the brief

1. **Wrong commitments.**
   - *Expected type an unknown:* `call_parts` gives `None`, so nothing is
     settled.
   - *Partly known:* the `t` position may be an unknown, and giving it is
     the same as a fresh unknown unified later.
   - *Several abilities:* `{Src t, St s}` (`g7.sw`, `g8.sw`) settles
     both, accepts the correct use, and blames the parser for a wrong
     `s`.
   - *`t` inferred from an argument instead of the goal:* the error moves
     to that argument (S2).
   - *Polymorphic recursion:* a recursive use at a different `t` can only
     meet a goal at the original `t` through unfolding, which is S1's
     case. At the same `t` there's nothing to settle wrongly.
   - *Non-`Char` `t`:* the token chains `t1ok`, `t2ok` (`readsThen` over
     `Tok` with `readsSatisfy`) check, the same on both binaries.
   - *Wrong acceptance:* impossible. The final comparison and the kernel
     both run.
   - *Rejection of a program main accepts:* only S1's shape.
2. **Errors.** Better placed and shorter than NOSETTLE and main, apart
   from the misleading `?0` note (S2).
3. **Stage 0's fall-back.** `reads-chain-unknown-name-last-step` and
   `reads-chain-swapped-pair` give identical errors at identical places
   on BR and NOSETTLE. So do their `Tok` versions (`t1bad.sw`:
   E-UNKNOWN-NAME at `xBad`; `t2.sw`: E-TYPE-MISMATCH at the inner
   `rfl`). Settling runs inside `after_arguments_failed`'s re-elaboration
   and doesn't move the blame. It adds no re-elaboration, so there's no
   blow-up. The swapped-pair message itself (`rfl` against `?25 [first]
   …`, an unsolved spec) is still poor on both, as before.
4. **General?** Yes. It keys on `Sort`-typed implicits, `Value::Pi`
   structure and `comp_parts_at` rows, with no names. The probes use two
   abilities declared in the probe file (`Src`, `St`).
5. **Day 2's margin.** The measured win is `b` (S3: 6.16M to 4.46M). It
   isn't safe today: hand-written `[b := …]` already breaks a correct
   `readsThen` chain. "Give `b` only when the call has no lambda
   argument" would probably exclude `readsThen`'s `rest`, and `runsBind`
   has none. But the first version's breakage wasn't traced to a
   particular call, so I wouldn't call that safe without rerunning the
   gates. Fixing `c3tb` first is the clean route.
