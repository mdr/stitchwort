# SW-4728: Fable review of "eta reads only a body that may be seen"

Reviewed: `6ed5c9aa3` on `lane/SW-4728`, against its merge base with `main`.
Paper review with two small probe files; no suites run.

## Verdict

**Merge.** The change closes the rule 6 hole and does not make the kernel
or the unifier accept less: I found no comparison that succeeded before
and fails now, by argument over every arm of `conv_step` and
`unify_shapes`, and by probe. No decision for Matt (no narrowing). Two
things for stage 2 and one follow-up audit are listed below.

## 1. Does conversion accept less? No

The only behaviour removed is: one side is a sealed call `s` (a theorem,
or an opaque definition outside the transparency set) with fewer
arguments than its body has lambdas, and eta was started from *that*
side. I went through what the other side `o` can be when `push_eta` is
reached (`value.rs` `conv_step`: the `_` arm, the same-head arm, and
`Recursion::Underapplied`):

| Other side `o` | Before the fix | Now |
|---|---|---|
| a lambda | lambda eta arm, earlier in the match; `next_parameter` not consulted | same |
| a glued `Call` | forced first, compared again | same |
| a folded dictionary or folded head | unfolded at `Stage::Unfold`, earlier | same |
| same sealed head, same spine length | `Recursion::Sealed`: by arguments, no eta | same |
| same sealed head, other length | eta, then still unequal lengths: false | false |
| a visible definition with too few arguments (`def w n := f n`) | eta with `s`'s parameter | eta with `w`'s parameter: same pushed pair |
| a variable, an axiom, another sealed call, a full call stuck on a `case`, a quotient form | `s v` against `o v`: two neutrals with different heads, `opens_by_tree` false for the sealed side, so false (after at most arity more rounds) | false at once |
| (theorem only) anything marked a proof | rule I at the top of `conv_step`, before any of this | same |

A neutral applied to a fresh variable stays neutral with the same head,
so the last row can't turn true after eta; the record eta arm needs a
constructor, which a function-typed `o v` can only be if `o` is a
lambda. The unifier adds unknowns (their arms are above `push_eta`) and
`same_heads`, whose sealed branch compares arguments and never reached
eta. So the lane's "nothing is lost" holds for hidden opaque
definitions as well as theorems.

Probes (lane release binary, and `main`'s pre-fix binary for comparison;
files in the session scratchpad, `sw4728/review/p1.sw` and `p2.sw`):

- Accepted by both, no difference: `f = (x => f x)`, `f = w` and
  `w = f` for `def w n := f n`, `g2 a = (x => g2 a x)`, `g2 a = w2 a`,
  `g2 = w2` (opaque `f`, `g2` hidden); the same through unification
  (`Holder f` against `Holder w`, `Holder (y => f y)`); inside
  `unfolding f`: `f = (x => f x)`, `f = w`, `f = (x => x + 1)`,
  `g2 a = (x => a + x)`; a polymorphic opaque `keep 1` against
  `y => keep 1 y` and against a wrapper definition; a theorem `pAll`
  (proof `n => MkP`) against `n => pAll n`, `n => MkP`, a variable, and
  an implicit solved from it.
- Refused by both, same six errors: `f` against a different opaque
  `f2`, against a variable `h`, against `y => y + 1` (hidden), against
  `pick b` (a function-valued definition stuck on a `case`), and
  `g2 1` against `g2 2`.

## 2. The two evaluators agree

`reference::seen` and `value::body_seen` are the same predicate written
twice (`hidden` already requires `opaque`; both test `proof` and "no
program running"). The two `next` functions are now line for line the
same after that read. Both evaluators' other raw `def.body` reads
(`value.rs` `case_tree`, `slot_type`, the `expect("checked by …")`
sites; `reference.rs` `unfold`) sit behind `hidden`/`frozen`,
`is_folded`, `opens_by_tree` or `body_seen`. I read each; none is
reachable for a sealed definition.

## 3. A frozen theorem's answer is unchanged

Sound, and simpler than the notes put it in the kernel: every value the
kernel checked carries a mark, so anything of a theorem's type other
than a lambda is marked a proof and rule I answers at the top of
`conv_step`. Eta from a theorem's side was reachable only against an
unmarked value, which only the elaborator makes (an unknown-marked
variable); there the table's last-but-one row applies. When both sides
are under-applied and the visible one now supplies `(icit, mark)`: the
kernel checks a lambda's implicitness against its type's, and lambda
marks against the type's binders (`validate_pi_marks`), so both bodies
give the same pair for one type. In `first_order` (types may differ)
the result is re-checked by the kernel, and the read now depends on
less, not more.

## 4. A theorem's arity (for stage 2)

`Def::arity` is still the proof's count of leading lambdas. With no
program running I found no reader that reaches it for a frozen theorem:
`quick`/`eval_step`, `unfold_now`, `is_folded`, `folded_call`,
`unfolds_head`, `opens_by_tree`, `stuck_on_variable`, the elaborator's
`cases::blocker` and `dot.rs` all test `body_seen`/`frozen` first. The
interface digest doesn't include arity (the only cache read is the
dump). Three places do see it, and stage 2's stated theorem (no body,
arity 0) must deal with each:

- **F1 (stage 2, must do).** While a program runs a theorem isn't
  frozen, and `unfold_now` erases a proof call only when
  `spine.len() == arity`; `erases_result` also needs a body or an
  assumption. A stated theorem reached by a running program would stay
  a neutral instead of `erased()`. Stage 2 should erase any call whose
  head is a `proof` definition whatever its arity and whether or not
  it has a body (the design note already lists `erases_result`).
- **F2 (stage 2, must do).** `cache/dump.rs` `declarations` prints
  every definition's arity, theorems included. A session holding a
  stated theorem and one holding its proof would dump differently, so
  any cold-against-cached comparison of dumps must leave a theorem's
  arity out (or stage 2 sets a theorem's arity to 0 always, which is
  the cleaner end state: nothing with no program running may read it).
- **F3 (low).** `pretty.rs` `lifted_match` reads the arity of a
  `.%match` helper to print it as a `match`; a theorem's helper is
  itself a proof definition and appears only in its own group's
  messages, so no other declaration sees it. No action.

Not audited: `crates/rt` and `crates/js` (about 60 arity reads). They
lower what erasure kept; stage 2 should confirm neither walks a stated
theorem.

## 5. docs/core.md

Both edited paragraphs are accurate. One wording point (low, no change
needed to merge): "a call that can't unfold equals only a call of the
same definition with equal arguments, or … any proof" leaves out the
lambda and the visible wrapper, which the sentence before covers with
"eta is tried from the other side only".

## Findings

| | Severity | What |
|---|---|---|
| F1 | stage 2 | erase proof-headed calls independent of arity and body |
| F2 | stage 2 | theorem arity in the canonical dump |
| F4 | medium, own ticket | the notes' item 3: about 40 raw `.body()` reads in `crates/elab` are not audited; any reachable with a theorem other than the one being elaborated is the same kind of hole. I agree it should be its own audit |
| F5 | low | the new test checks `underapplied` directly; no `.sw` example pins "opaque `f` equals its wrapper outside the set". `p1.sw` above would do as `examples/accept/` |

## Not checked

- The elaborator's raw `.body()` reads (F4), `rt` and `js`.
- No test suites; the lane reports soundness, core `it`, a proofs
  subset and erasure.
- Unknown-marked values in the unifier beyond the cases probed: argued
  from the arms, not exhaustively probed.
