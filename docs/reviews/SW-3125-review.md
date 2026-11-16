# Review: SW-3125 (`!=` note) and SW-3078 (derive waits for a failed field instance)

Opus review, 16 Nov 2026, of the DeepSeek run in scratch clone
`.claude/worktrees/scratch-sw-3125`: a48627d5f (SW-3125) and 55c6d90d6
(SW-3078). Paper review: no builds or tests run.

## SW-3125: the `!=` note only where the source wrote `!=`

**Verdict: merge with small fixes (below).**

### What it does

- `BinOp::Ne` becomes `BinOp::Ne(NeForm)`, `Ascii` or `Unicode`, from the
  operator token's byte length (`!=` is 2 bytes, `≠` 3; the lexer has no
  other spelling of `Tok::NotEq`). A parser unit test pins both.
- `numbers::equation` records `cx.span` in `Decl::ne_ascii` whenever an
  ASCII `!=` is elaborated as the proposition. `cx.span` there is the span
  of the number group being checked, which `infer`/`check` wrap as
  `Term::Loc(span, …)`, so the recorded span appears as a `Loc` in the
  elaborated goal.
- The type-mismatch note (`ne_read_as_prop_here`) now needs, besides the
  old text tests: the found type is `Eq Bool _ _`, the term is not a written
  `.read`, and `goal_wrote_ne`: the expected type is convertible with the
  declaration's body goal (same level) and that goal term contains a `Loc`
  whose span was recorded as ASCII `!=`.
- `rewrite`'s E-REWRITE-NOTHING note uses the per-declaration
  `wrote_ascii_ne()` and `goal_wrote_ne`; the E-REWRITE-MOTIVE note
  (`ne_note` in `check_motive`) uses only the per-declaration flag.

### Correctness

- Only notes change; nothing about what is accepted or rejected, or any
  elaborated term. `NeForm` is ignored everywhere except `equation`; every
  other match is `Ne(_)`. `BinOp` has no `Hash`, so no hash or cache key
  moves. (`Expr` equality now tells the spellings apart; spans already make
  two written expressions unequal, so nothing relies on that.)
- State: `ne_ascii` lives in `Decl`, which `glued` resets before and after
  each declaration or component, `rewind` clears, and `leftover()` lists, so
  a mark can't be taken with it set. Spans are only ever added during a
  declaration; one recorded during an attempt that was undone (the SW-944
  retry as `Bool`) still marks a place where the source wrote `!=`, which is
  what it claims. Nothing session-level, so the check cache and the LSP are
  unaffected: a declaration's type and body are checked in the same `glued`
  call, which the doc comment relies on and `bool-ne-read-as-prop` exercises.
- **Wrong note, E-REWRITE-MOTIVE (fix 1).** `ne_note` asks only "did this
  declaration write an ASCII `!=` anywhere". A declaration with `(h: a != c)`
  in a hypothesis and a goal written with `≠`, whose rewrite motive fails
  with a `….holds` left side, gets the note though the goal never says
  `!=`: the same bug class as the reverted first attempt, just rarer.
  E-REWRITE-NOTHING is protected because it also calls `goal_wrote_ne`.
- **Missing notes (accepted).** `goal_wrote_ne` needs the expected type to
  be the whole body goal at the declaration's level. So the note is no
  longer given for a mismatch in a sub-goal: one side of an `∧`, a `match`
  arm (the goal is refined), under a lambda or `let`, a `rewrite … at h`
  on a hypothesis, or an argument whose parameter was written `!=`. That is
  narrower than before, but it's a hint, and erring towards silence is the
  right side for a note that says "you wrote X". Not worth a redo; file as
  a follow-up only if a real case turns up.
- **Same bug, nearby (fix 3, optional).** `numbers::prop_not_equal` matches
  `Ne(_)` and says "in a statement, `!=` is the proposition" and "this
  `!=` is `Not (… = …)`" for an expression written `≠`. With `NeForm` in
  hand it should quote what was written (or match `Ne(NeForm::Ascii)` only
  if the error is meant only for `!=`; it is an error that replaces another,
  so quoting the written spelling is the safer fix).
- The derive's synthesized `sameReadsFalse` statement uses
  `Ne(NeForm::Ascii)`; nobody wrote it, so `Unicode` would be more honest.
  Harmless either way (its span never reaches a user goal). Optional.

### Design questions

- **AST spelling vs a span-text lookup.** The AST change is the right
  place: the parser knows the spelling, the elaborator doesn't hold file
  text in `Ctx`, and a text lookup would need it plumbed in for one note.
  The churn is mechanical (`Ne` → `Ne(_)`). The byte-length test is a little
  implicit but pinned by the unit test; carrying the form on `Tok::NotEq`
  would be tidier but isn't needed.
- **Is the per-declaration `wrote_ascii_ne` needed?** No. Once the motive
  path also asks `goal_wrote_ne`, every caller of `ne_read_as_prop` also
  calls `goal_wrote_ne`, which implies the flag. Delete `wrote_ascii_ne`
  and the `cx` parameter it brought to `ne_read_as_prop`.

### Tests

The new `bool-ne-read-as-bool-test` (no note through `.read`), the kept
`bool-ne-read-as-prop` and `rewrite-nothing-bool-ne` (note stays) and the two
`reading-needs-read-ne-*` (note gone, correctly: their aims are written `≠`)
cover the `.read` half. The `≠` half, which is what broke last time, is
covered only indirectly by `match-not-found-goal-as-written`. Add (fix 2):

- `bool-ne-unicode-no-note.sw`: the twin of `bool-ne-read-as-prop` with the
  goal written `(a ≠ b) = (b ≠ a)`; mismatch, no note.
- a twin of `rewrite-nothing-bool-ne` with the goal written `≠`; no note.
- for fix 1, a motive failure in a declaration that writes `!=` only in a
  hypothesis; no note. If a motive failure with a `.holds` left side is
  awkward to provoke, skip this one and rely on the code being the same
  `goal_wrote_ne` call.

### Fixes

1. `check_motive`'s `ne_note`: also require `goal_wrote_ne(cx, goal)` (pass
   the goal value it rewrites in down to it; when the place isn't the goal,
   give no note). Then delete `Decl::wrote_ascii_ne`.
2. The two `≠` twin reject examples above (and the motive one if easy).
3. Optional: `prop_not_equal` quotes the spelling written; the derive's
   synthesized `≠` uses `NeForm::Unicode`.

## SW-3078: a derive waits for a field's failed instance

**Verdict: merge with small fixes (below).**

### What it does

- `interfaces::attempt`, on reaching an instance whose definition failed,
  also stores the def in `Decl::failed_instance`; `findable` clears it first.
- The four derives (`derive.rs` for DecEq/Ord, `derive_show.rs`,
  `derive_finite.rs`), when `findable` for a field's type returns
  E-FAILED-DEPENDENCY, call `note_derive_waiting`, which takes
  `failed_instance` and records `(type, derived interface) → def` in
  `Session::derive_waiting`.
- `interfaces::none`, the E-INSTANCE-NONE builder, first looks the goal's
  head up in that map; if the recorded def is still `Failed`, it returns
  `failed_name` (E-FAILED-DEPENDENCY) instead, and notes the use as failed.
- `derive_waiting` is saved in the session `Mark` and restored on rewind.

### Correctness

- **Can it accept something that was rejected, or change a term?** No.
  All the new code is on failure paths: `attempt` only sets the field just
  before returning an error, and `none` only swaps one error diagnostic for
  another. No success path reads the new state, so no elaborated term
  changes. The use is still a failed declaration (E-FAILED-DEPENDENCY is
  an error; `module.rs` drops its text only when every error is one, and
  the declaration stays failed), and the root error at the instance is
  still reported, so the module is still rejected.
- **Callers that branch on the code.** Swapping E-INSTANCE-NONE for
  E-FAILED-DEPENDENCY reaches these: `numbers.rs:805` already turns
  E-FAILED-DEPENDENCY into a wait (that's the operator case, now working);
  `derive*.rs` add the `: <message>` suffix to their reason (unseen, since
  the use now waits); `numbers.rs:1913` only adds a note to
  E-INSTANCE-NONE; `goals::unfinished_dependency` now treats it as a
  failed dependency, which is the point. `logic.rs:362` (a condition that
  is neither a `Bool` nor decidable) falls back to `Ok(None)` only for
  E-AUTO-NONE/E-INSTANCE-NONE; with E-FAILED-DEPENDENCY it goes on to
  `decide`, which may give "nothing decides it" for something like
  `if redThing < greenThing`. That would still be rejected, only with a
  worse message than the wait. Worth one reject example (fix 3), not a
  blocker.
- **Transitive derives aren't covered (fix 1).** For
  `type Outer = { thing: Thing }` deriving Ord, `findable(Ord Thing)` now
  returns E-FAILED-DEPENDENCY from `none`, but `none` doesn't set
  `failed_instance`, so `note_derive_waiting` finds nothing and a use of
  `Ord Outer` still says "no instance": the second error this ticket is
  about, one level down. `none`'s early return should also do
  `cx.e.decl.failed_instance.replace(Some(def))`.
- **Stale or wrong entries.** The `Failed` state check makes an entry
  harmless once the instance is fixed, and rewind restores the map, so
  DefIds reused after a rewind can't be read through a stale entry.
  `failed_instance` is `Decl` state, reset by `glued` (derives run inside
  `check_component` / `derive_pending_ord`, both glued) and listed in
  `leftover()`, so the mark-time panic can't fire from it. `failed_instance`
  records the last failed instance any search reached, which may be a
  candidate's sub-goal rather than the field's own instance; the use then
  waits on a failed declaration that isn't the direct cause. The
  diagnostic is silent either way, so this doesn't show.
- **Check cache.** The map isn't in the check cache: when the module that
  declares the type comes from the cache, its derive isn't re-run, and a
  use in another module gets the old E-INSTANCE-NONE. Only a message
  differs, and only for a module importing one with errors; accept, and
  mention in the code comment on `derive_waiting`.
- **LSP.** Session state rewound with the mark, as the other session
  fields are; nothing else to do.
- Small: `none` names the instance from the kernel path's last segment,
  while `attempt` uses `info.name`; both give the declared name today, but
  reusing the instance table's name would keep them the same. The `Mark`
  clones the map on every mark; it's almost always empty, so this is free,
  but an `Rc` like `library_reach` would match its neighbours.

### Tests

Only Ord has an example (`derive-field-instance-failed`, whose snapshot
proves the single error). The four derive sites are copies; each needs its
own example, since a missed call site is exactly what these would catch.
Add (fix 2):

- DecEq: the same setup with `deriving DecEq` (or whatever the type uses)
  and a `==` use.
- Show: a failed `Show Color` instance and `show redThing` (or
  interpolation).
- Finite: optional, if a failed `Finite` field instance is easy to write.
- The transitive `Outer` case, after fix 1.

Each should snapshot exactly one error, at the failed instance.

### Fixes

1. `interfaces::none`: on the `derive_waiting` hit, also set
   `cx.e.decl.failed_instance` to the def, so a derive over the waiting type
   waits too; add the `Outer` example.
2. Reject examples for DecEq (`==`) and Show, one error each; Finite if easy.
3. A reject example for `if redThing < greenThing then …`: if it gives a
   second error through `logic.rs:362`, add E-FAILED-DEPENDENCY there
   (return it as the error).
4. Optional: a sentence on `Session::derive_waiting` that it isn't cached;
   the instance name from the instance table.
