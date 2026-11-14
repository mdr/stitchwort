# SW-3105: should the compiler insert `.read` silently? (D3549b)

Analysed on `main` at `b6bc36d26` (13 Nov 2026), read-only. Labels:
**[checked]** = a small program run through today's release binary (all in
`sw3105/`, listed in §8); **[read]** = read in the elaborator's source, at the
line given; **[inferred]** = follows from what was read, not run;
**[SW-3101]** = a number from `docs/reviews/SW-3101-measure.md`;
**[memory]** = prior art recalled, not looked up again; **[estimated]**.

## 0. The short answer

**The problem.** A fact from a program is a test: `found: xs.contains x`.
Where the proposition it decides is wanted (`x ∈ xs`), you write
`found.read`. The compiler already knows this: its error says "this is the
test fact `xs.contains x`, which reads as `x ∈ xs`: add `.read`". So why not
let it add the word itself?

**What it would buy.** About 95 words across std and AoC: 45 of the 358
`.read`s, plus about 50 helper calls (36 of them `Nat.leqFalse`) that a
plain `.read` already shortens **[SW-3101]**. Three quarters of `.read`s
(about 265) sit where no silent rule can reach: rewrite rules, untyped
`let`s, `omega` hints, a fact applied like a function, or a wanted equation
**[SW-3101]**. So `.read` stays an everyday word either way.

**What it would risk.** Nothing about soundness: the inserted term is a call
of a proved std theorem and the kernel checks it. The risks are to meaning
and predictability:

1. **The compiler sometimes uses a type error as a signal to try something
   else.** If `.read` is inserted at the error, the "something else" no
   longer happens, and a program that checks today quietly means something
   different. I found one place where this really happens today (a record
   update that changes the record's type, §2.1, shown with a program that
   checks today), one that changes only a proof (`cases in t`), and about
   fifteen kinds of place where it can't. I read about 70 of roughly 100 such places; the
   rest are listed in §8.
2. **A test fact is also an equation**, and unification takes it as one
   before any mismatch is seen. `Eq.sym same` and `useEq same` check today
   as statements about `Bool`s (§3). No silent rule can fix these, so "facts
   are read for you" would be true in some positions and false in the ones
   that look most alike.
3. **Whether there is a mismatch at the fact depends on the order things are
   elaborated in.** `Both found k` would be fixed and `both found k` (a
   lemma that does the same) would not, because the lemma's argument is
   elaborated before the goal is looked at (§2.3). The user can't predict
   which without knowing the callee's implicit parameters.

**Recommendation: (c), keep `.read` explicit, and make the hint a one-key
fix in the editor.** If you still want it implicit, there is a form, (b) in
§4.2, that has none of risk 1 by construction: the compiler adds `.read`
only after a declaration has *failed* with exactly that error, and then
checks it again as if you had written it. I'd build that form or none; not
a hook inside the type comparison. The decision can wait for D3549a
(building a fact from a proof), which meets the same three risks from the
other side and should be built the same careful way: §4.4 shows its own
program that checks today and would change.

## 1. What is proposed

Today **[checked: `x3.sw`, `x9.sw`]**:

```
theorem apart (x y: Nat) (h: (x == y) = False): x ≠ y := h
  expected `x ≠ y`, but this has type `(x.decEq y).holds = False`
  Note: this is the test fact …, which reads as `x ≠ y`: add `.read` to use it as that
```

D3549b: accept it, elaborating `h` as `h.read`. §7 of
`docs/proposals/bool-as-proposition.md` sketched a restricted form: only
where the wanted type's head is known and isn't `=`, and only outside the
elaborator's try-and-fall-back paths.

Two things already read facts silently, and are not in question:
`auto` and `cases` read the facts in scope (SW-3059,
`auto.rs:609-620`, `reading.rs:1301`), and a pattern or a field (`h.left`)
reads the fact it takes apart. Those are driven by a goal or a pattern. This
proposal is about a *written term* being given a different meaning.

## 2. The risks, concretely

The natural hook is `check::compare` (`check.rs:6074`), the one place a term
of one type is fitted to an expected type. It already tries, in order: plain
unification with instances, an effect coercion, three kinds of waiting, and
`along_match_equation` (`check.rs:1403`), which silently transports a proof
along a `match`'s equation. So a silent proof conversion at a mismatch has a
precedent there. The question is who is watching for `compare` to fail.

A program that checks today can change only if (i) some path A fails today
at a fact-against-its-reading mismatch, (ii) the elaborator catches that
failure and tries a path B, and (iii) B succeeds. With the hook, A succeeds
and B is never tried. For (iii), B must not hit the same mismatch, so B must
either check the same fact against a *different* expected type or not check
it at all. Most fall-backs retry the same sub-terms against the same types,
and so fail in B too; those are harmless.

### 2.1 Real: a record update that changes the record's type

`records.rs:1182` **[read]**: an update is tried "as written first"; "only if
that fails may the parameters its new fields mention change". Path B gives
the field a fresh type. So this checks today **[checked: `x4.sw`]**:

```
type Checked (p: Prop) = { item: Nat, why: p }

def recheck (x: Nat) (xs: List Nat) (c: Checked (x ∈ xs)) (found: xs.contains x): Nat :=
  let again := { c | why = found }               -- today: a `Checked (xs.contains x = True)`
  let fact: xs.contains x = True := again.why    -- and this line relies on it
  again.item
```

With a hook in `compare`, the update as written succeeds (`why =
found.read`), `again` stays a `Checked (x ∈ xs)`, and the next line is a
type error; or, with D3549a also on, it is silently rebuilt back into the
fact. Either way a program that checks today changes, with no message at the
update. The mirror image, for D3549a, also checks today **[checked:
`x13.sw`]**.

This is contrived (a record with a proposition parameter, updated with a
fact). I found no such code in std or AoC by reading; nobody has grepped for
it. It is the proof that the class of hazard is not empty, and it was found
by reading about 70 fall-back sites, not by any test.

### 2.2 Real, but only a proof changes: `cases in t`

`cases.rs:356` **[read]**: in each case `cases` tries the body `t` against
the goal; if that fails it goes on to split further, to `omega`, to a
decision. With the hook, a body that mentions a fact can succeed in a case
where it fails today, so the proof has fewer splits. The statement is the
same; the proof term and its hash differ. Harmless to meaning, but it breaks
the acceptance check "no example's hash changes" that stage 2 relied on.

### 2.3 Real: acceptance depends on elaboration order

These are not programs that change meaning; they are the reason a user
could not predict when the word is needed.

- **A lemma versus a constructor** **[checked: `x8.sw`, `x9.sw`]**. With
  `theorem both [p q: Prop] (a: p) (b: q): p ∧ q`, the call `both found k`
  against `x ∈ xs ∧ x < 3` elaborates the arguments first, so `p` becomes
  the fact's own type and the mismatch is reported at the whole call, as
  `xs.contains x ∧ x < 3` against `x ∈ xs ∧ x < 3`: no fact at the head,
  no note, nothing to hook. `Both found k` checks `found` against `x ∈ xs`
  directly and gets the note. Same goal, same fact, same shape.
- **A mismatch one step away** **[checked: `x6.sw`]**. `pick found` (with
  `pick [p: Prop] (h: p): p`) against `x ∈ xs` reports the mismatch at
  `pick found`, not at `found`. A hook would produce `(pick found).read`.
  If the goal's type were propagated first it would be `pick found.read`.
  Both are fine, but which one you get is the elaborator's business.
- **A comparison that waits** **[read: `queue.rs:1036-1076`]**. When a
  comparison is stuck on an unknown the queue hasn't settled, `compare`
  returns the term *as it is* and queues the comparison. If it later fails,
  the term has already been placed, so nothing can be inserted. A fact
  whose wanted type is settled late would need `.read` where the same fact,
  with the type settled early, wouldn't. Fixable (queue a placeholder
  instead, as `DecideTerm` does, `check.rs:6010`), but it is more work than
  "one more step in `compare`".
- **An argument tried in place, then after the goal**
  **[read: `check.rs:3171-3195`]**. An argument that fails while its
  parameter's type has unknowns is undone and checked again once the
  expected type is known. The hook is safe here only if it refuses to fire
  while the wanted type's head is blocked on an unknown: otherwise a
  parameter type that would later compute to the fact's own type could be
  "read" too early. With that condition (§4.1, condition 3) this path
  can't flip **[inferred]**.

### 2.4 Theoretical: looked at, and can't flip

Each of these catches a failure and tries another way, but the other way
checks the same sub-terms against the same types, so a fact that mismatches
in A mismatches in B too. Nothing that checks today changes **[inferred
from reading each]**.

| Path | Where | Why it can't flip |
|---|---|---|
| `if c`, `while`: `Bool` first, then a decided proposition | `logic.rs:255-295` | the condition is checked against `Bool`, which is not a proposition, so the hook never fires at the top; a fact nested in it (`f h`) is checked against `f`'s parameter both ways |
| `&&`, `\|\|`, `!` with nothing expected | `logic.rs:685-699` | same: operands are checked against `Bool`, or as types |
| `if`/`let`/`match` against `Prop`: per branch, then as a whole test | `check.rs:7313-7337` | results are types or `Bool`s, never proofs |
| a list of number literals checked last | `check.rs:2975-3003` | same arguments, same types, later |
| the goal's type compared first, then "the old way" | `check.rs:6201-6300`, `:6445` | same arguments; only the order differs (§2.3) |
| method section `.f a` as a partial application, else a lambda | `dot.rs:1071-1140` | same call either way |
| `x.f a` as `T.f … x`, else by dot notation | `dot.rs:2213-2222` | "the call is wrong either way" |
| a call run as plain calls first, else in the empty row | `check.rs:1891-1912`, `effects.rs:2896-2900` | the alternative type is a computation type, not a proposition |
| a `let`-bound argument tried, else inlined | `bind.rs:76-95` | same use |
| `match` scrutinee generalised as written, else the usual way | `matching.rs:1100-1150`, `:1252` | only motives are compared; no user proof is checked |
| `rewrite`'s search; "would the body check without this rule?" | `rewrite.rs:832-915`, `:2216` | the rule is inferred with nothing expected, so no hook; the body check feeds only an error's note |
| `omega`'s hints and attempts | `omega.rs:1260-1270`, `:1404` | hints are inferred; goals are read by `omega`'s own table |
| instance search, `auto` | `auto.rs:269`, `interfaces.rs:1515`, `:1622` | proofs are found by unifying hypotheses, not through `compare`; `auto` already reads facts |
| number-literal defaulting | `numbers.rs:877`, `defaults.rs:933`, `:1082` | no proofs involved; `defaults.rs` only builds a note |

### 2.5 Not a risk

- **Soundness.** The inserted term is `reading.forward h` (or the `= False`
  refutation), checked by the kernel like the hand-written one
  (`reading.rs:1252`).
- **The 390 sites that use a fact as an equation** (`rewrite same in`,
  `Eq.sym same`) **[SW-3101]**: nothing mismatches there, so no hook of any
  design touches them. They are a predictability problem (§3), not a
  breakage.
- **Folded versus unfolded tests.** The reading depends on the test as
  written; the hook would use the same `term_as_written` that `.read` does
  (`reading.rs:206`, `:1258`) and fire only when the one-layer reading is
  exactly the wanted type, as the note does today (`reading.rs:1650`). A
  test that a `rewrite` has unfolded simply doesn't get the insertion.

## 3. Equations

A test fact `same: (x == y) = True` is an equation between `Bool`s. Today
**[checked: `x1.sw`, all four theorems check]**:

```
Eq.sym same            : True = (x == y)
useEq same             : True = (x == y)     -- useEq [a] [u v: a] (e: u = v): v = u, with a := Bool
rewrite same in rfl    -- rewrites `x == y` to `True` in the goal
```

and these fail, with the error far from the fact and no "add `.read`" note
**[checked: `x2.sw`, `x12.sw`]**:

```
theorem viaLemma … : y = x := useEq same
  expected `y = x`, but this has type `True = (x.decEq y).holds`
let e := same in Eq.sym e          -- the same error, at `Eq.sym e`
```

What a user would expect, if told "a fact is read for you": that `Eq.sym
same` is `y = x`, and that `rewrite same in` turns `x` into `y`. Neither can
happen. The equation fits as it stands, unification solves the lemma's
type as `Bool` before any goal is consulted, and the `rewrite` that turns
`x == y` into `True` is the commonest use of such a fact in the tree (about
229 sites **[SW-3101]**) and must keep working. SSReflect has the same two
meanings and keeps both, chosen by the user: `rewrite h` against `rewrite
(eqP h)` **[memory]**.

**Is there a principled rule?** Two candidates:

- **Never when the wanted type is `=`, or its head isn't known yet** (§7 of
  the design note). Simple to say and always safe. It leaves out about 60
  `.read`s whose reading is an equation at `Nat` or the like **[SW-3101]**,
  and it makes D3549a lopsided: a proof of `a = b` would be accepted where
  `(a == b) = True` is wanted, but not the reverse.
- **Never when the wanted type is an equation between `Bool`s or at a type
  not known yet.** An equation at `Nat` can never be the fact itself, so
  reading is unambiguous *once the type is known*. But whether it is known
  when the argument is checked is exactly the order question of §2.3:
  `useEq same` fixes the type from the fact first. So `Inl same` against
  `x = y ∨ …` would work and `Eq.trans same k` would not. This rule is
  sound and unpredictable.

I'd take the first. It can be said in one sentence a user can apply without
knowing how the callee is declared: *for an equation, say `.read`*.

## 4. The safest implicit design

### 4.1 Form C: a step in `compare` (not recommended)

Where: `check.rs:6074`, after `along_match_equation` and before the final
`cx.unify` that builds the error. Fires only if all of:

1. everything `compare` tries today has failed, and `compare_waiting` said
   "no", not "blocked";
2. `found`, as written, is a test fact that `.read` accepts (a reading, a
   stuck decision, or `e = False` at a leaf);
3. `expected`, in weak-head normal form, is not blocked on an unknown and is
   not an `=`. A function type is allowed: `¬`, `≠` and `∀ x ∈ xs` are
   function types, and they are 24 of the 39 firm sites **[SW-3101]**;
4. the one-layer reading is convertible with `expected` *without solving
   anything* (the note's own test). Then the hook can't steer inference;
5. no trial is in progress: a counter raised by every speculative scope;
6. one layer, and never followed by D3549a's build on the result.

The weak point is condition 5. There are about 100 places that take a
snapshot and may restore it **[read: `grep` of `undo::transaction`,
`undo::attempt`, `Snapshot::take`]**; 33 use the scoped helpers and 70
restore by hand. Each must be bracketed, and one missed bracket is a silent
change of meaning that only a test designed for it would find. §2.1 was
found by reading, not by the suite.

### 4.2 Form R: repair after failure (the form I'd build, if any)

**The rule, in one sentence:** *a declaration that fails with the "add
`.read`" error is checked again as if the `.read` had been written there.*

How:

- The mismatch error already knows when a `.read` fits
  (`reading::read_note`, `reading.rs:1636`). Give the diagnostic a
  structured field for it (as `Detail.import` carries the import a quick fix
  adds, `crates/syntax/src/diagnostic.rs:51`): the address of the expression.
  Apply conditions 2, 3 and 4 above before setting it.
- Where a declaration's body is elaborated, catch a failure that carries the
  field, add the expression to a per-declaration set of "read here" sites,
  and elaborate the body again from clean state. `infer` wraps an expression
  in the set exactly as `dot_read` would. The loop exists already for local
  definitions: `with_local_retries`, `lib.rs:2687` **[read]**. Cap it (say 4
  rounds), then report the error as today.

What this gives:

- **A program that checks today is never touched**, by construction: the
  repair runs only after a failure. §2.1's record update keeps today's
  meaning. No audit of the 100 sites, and the hash check passes trivially.
- **The meaning is one the user can write.** The result is exactly the
  program with `.read` at the places the compiler names. Every fall-back
  then behaves as it would for that written program.
- **No order question inside one run.** The retry is an ordinary
  elaboration.

What it doesn't fix: §2.3's first two bullets and all of §3. Where today's
error isn't at the fact, there is no note and no repair; the user writes
`.read`. And a declaration with k silent sites is elaborated up to k+1 times
(errors surface one at a time), which is a cost in exactly the long proofs
where time matters. The cap bounds it; a quick fix that writes the word
removes it.

### 4.3 How the inserted word is shown

- **Hover** on the expression: `found.read : x ∈ xs`, "read from the test
  fact `xs.contains x` by `List.containsReads`".
- **Inlay hint** in the editor: a greyed `.read` after the expression, with
  an action to write it. `stitchwort fmt` never writes or removes one.
- **Goals and hypotheses**: unchanged. `found` is still shown as the test
  fact; that is what `rewrite found in` uses.
- **Errors**: a later mismatch at a repaired site says so: "`found` was read
  as `x ∈ xs` here".

### 4.4 D3549a (building a fact from a proof)

D3549a is the mirror: `expected` is a test fact, `found` is its reading,
wrap in `reading.backward`. SW-3101 proposed it as "one more place in
`compare`". It inherits everything above:

- **The same flip, mirrored** **[checked: `x13.sw` checks today]**: `{ c |
  why = m }` with `c: Checked (xs.contains x = True)` and `m: x ∈ xs` is a
  `Checked (x ∈ xs)` today and would silently stay a `Checked (xs.contains
  x = True)`. So D3549a needs form R, or form C's condition 5, just as much.
- **With both directions on, a type can depend on order** where nothing is
  expected **[checked: `x14.sw`, `x15.sw`, both errors today]**: `let w :=
  if c then found else m` would make `w` the test fact (the second branch
  built), and `if c then m else found` would make it `x ∈ xs` (the second
  branch read). It matters when `w` is next used in a `rewrite`.
- **Never chain them.** Read-then-build would convert between two different
  tests with the same reading, a silent `simp`. One step, one direction.
- **`=`**: under §3's first rule, D3549a accepts `a = b` for `(a == b) =
  True` but the reverse needs `.read`. That asymmetry is the price of the
  equation rule and should be documented as such.

### 4.5 The check cache

Either form is a function of the unit's text and its dependencies. Readings
live with their tests, which are always among the dependencies (§5.7 of the
design note), so no new key input. The set of repaired sites goes in the
cache entry so hover and inlay hints survive a replay. A switch used for
differential runs (below) must be in the key or run with `--no-cache`.

### 4.6 What would make it safe to ship

Whole-corpus runs; these belong to the verifier or Overmind, not a lane.

1. **Differential oracle.** An environment switch (as `STITCHWORT_GLUE` and
   `STITCHWORT_DECIDE_BOTH` are, `auto.rs:1006`): every declaration that
   checks with it off has the same hash with it on. True by construction
   for R; for C it is the test of condition 5.
2. **Deletion oracle.** For each of the 412 `.read`s in std, AoC and the
   examples **[SW-3101]**, delete it and check that one file. Allowed
   outcomes: an error, or a check in which every declaration has the same
   type and every `def` the same hash (a theorem's proof may differ). Any
   other outcome is a silent change of meaning. This is the test that would
   have found §2.1.
3. **One example per fall-back path** in §2: the record update keeps
   today's type (`x4.sw`, `x13.sw`); `both found k` stays an error with a
   useful note; `Eq.sym same` stays a `Bool` equation; the same results
   with `STITCHWORT_GLUE=0`.
4. `fuzz:elab` with the switch on (no new panics or timeouts), and
   `reject/reading-needs-read.sw` moved to accept on purpose.

## 5. Prior art, briefly

- **Lean 4.** `Bool` coerces to `Prop` as `b = true` in *statements*; the
  other way is `decide p` with a `Decidable` instance. There is no coercion
  between *proofs* of `decide p = true` and of `p`: users write
  `of_decide_eq_true`, `decide_eq_true_eq` or `simpa` **[memory]**. Coercions
  in general are inserted when unification fails and are postponed while
  the types have unknowns; the known trouble is that where the coercion
  lands depends on elaboration order (`↑(n + m)` against `↑n + ↑m`, both
  well typed, different terms), which Mathlib answered with a dedicated
  elaborator for arithmetic (`binop%`) and a family of `norm_cast` lemmas
  to move coercions afterwards **[memory]**. That is §2.3 at scale.
- **SSReflect.** `is_true` is a hidden coercion for statements. Between
  proofs the user always names a view: `move/andP`, `apply/eqP`,
  `rewrite (eqP h)`. Two conveniences: a `reflect` lemma coerces to a
  function, so `eqP h` is a term, and view hints pick the direction
  **[memory; R1 in the design note for views]**. Nothing is inserted
  without a view being named. Coq's own coercions are keyed on the head of
  both types and are not tried while the target is an unknown, which is
  condition 3 **[memory]**.
- **Agda.** No coercions by design. `T b`, `Dec`, `toWitness` and
  `fromWitness` are explicit; `True (m ≤? n)` as an implicit argument lets
  closed cases be found by computing **[memory; A4 for `Reflects`]**.
- **Outside proof assistants.** Rust inserts `&`/deref only at a fixed list
  of "coercion sites" where the wanted type is written, never where it is
  inferred, for the reason in §2.3; Scala 3 put implicit conversions behind
  an import after a decade of "what does this line call?" **[memory]**.

None of the three provers inserts a proof-level crossing silently. All three
have the statement-level coercion Stitchwort already has (stage 1).

## 6. Recommendation

**(c): keep `.read` explicit, and make the hint do the work.**

- *Benefit forgone:* about 95 words (45 `.read`s, 50 helper calls that
  become nothing instead of `.read`) of the 358 + 414 crossing sites
  **[SW-3101]**. The other 265 `.read`s can't go under any rule.
- *Risk avoided:* one demonstrated silent change of meaning and an unknown
  number in the 30 or so sites not read (form C); a second regime to teach,
  whose boundary (§2.3, §3) a user can't predict without knowing the
  callee's implicit parameters (any form).
- *Instead* **[estimated, about half a lane-day]**: the editor's quick fix
  "add `.read`", from the same structured field form R needs
  (`crates/lsp/src/lib.rs:1410` already offers "add the import" and "add
  the missing arms"); and the three hint gaps in §7. Together with SW-3101's
  sweep (about 200 helper uses) and reading gaps (about 95), which remove
  three times as many words as this decision could.

**If you want it implicit anyway: (b), form R with the equation rule.** A
declaration that fails only with "add `.read`" is rechecked as if it were
written; never for a wanted `=`; one layer; hover and inlay hint show it.
About one to two lane-days on Opus **[estimated]**, plus the two oracle runs.
It is safe for existing code by construction. Its costs are the repeated
elaboration and the boundary in §2.3. Build D3549a the same way, and decide
this one when D3549a's oracle runs are in: they exercise the same paths.

**Not (a)**, a hook in `compare`: its safety rests on bracketing about 100
speculative sites by hand, for 95 words.

**What would change my mind.**

- After the sweep and the reading gaps, a re-measure showing the crossable
  share well above today's 12 to 13 % (say a third of what is left).
- Friction notes from new AoC days naming the *error* as friction (not the
  word): the fix is in the message today, so I'd expect not.
- D3549a shipping silently with clean oracles. Then the mechanism exists,
  the marginal cost is small, and "proofs flow into facts but not back"
  becomes its own surprise. I'd then say (b).
- Against: any deletion-oracle finding beyond §2.1.

## 7. Findings worth filing

1. **D3549a must not be a bare step in `compare`.** `x13.sw` checks today
   and would change. Use form R or condition 5, and the two oracles (§4.6).
2. **Quick fix "add `.read`"** in the LSP, from a structured field on the
   mismatch diagnostic.
3. **No note when the fact is under the head** **[checked: `x8.sw`]**:
   `xs.contains x ∧ x < 3` against `x ∈ xs ∧ x < 3`. The note could compare
   the parts and say which argument is a test fact.
4. **No note when a fact was taken as a `Bool` equation**
   **[checked: `x2.sw`, `x12.sw`]**: "expected `y = x`, but this has type
   `True = (x.decEq y).holds`". A note: "`same` is a test fact, used here as
   an equation between `Bool`s; `same.read` is `x = y`".
5. **No note when a fact is applied** **[checked: `x7.sw`]**:
   `E-NOT-A-FUNCTION` on `h y m` for `h: xs.all p`, whose reading is a
   function. 42 `.read` sites are of this shape **[SW-3101]**.
6. **The deletion oracle** (§4.6, item 2) is worth having whatever is
   decided: it tests that `.read` is never silently optional today.

## 8. Method and limits

- Programs, all under
  `/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw3105/`,
  each run once with `target/release/stitchwort check`:
  `x1` (facts as equations: checks), `x2` (`useEq same` against `y = x`:
  error, no note), `x3` (`≠` from `= False`: error with note), `x4` (record
  update: **checks**), `x4b` (its reading wanted afterwards: error), `x6`
  (`pick found`: error at the call), `x7` (fact applied: not a function),
  `x8`/`x9` (lemma versus constructor), `x10` (build direction: error, no
  note), `x11` (`=` between `Bool`s: note fires), `x12` (untyped `let`),
  `x13` (mirrored record update: **checks**), `x14`/`x15` (branch order).
- Read in full: `compare` and `unifies_with_instances`; `logic.rs`'s
  condition, `infer` and `check_against`; `whole_test`; `retrying` and the
  in-place argument trials; `records.rs:1170-1190`; `cases.rs:331-420`;
  `compare_waiting`; `reading.rs`'s `read_note`, `dot_read`, `as_written`.
  Read at the snapshot only (20 to 40 lines each): the sites in `dot.rs`,
  `named.rs`, `defaults.rs`, `matching.rs`, `rewrite.rs`, `effects.rs`,
  `bind.rs`, `auto.rs`, `interfaces.rs`, `membership.rs`, `no_effect.rs`.
- **Not read:** the queue's resume paths (`queue.rs:906-941`, `:1724`,
  `:2026-3103`), `omega.rs:303-322` and `:2562-3101`, `lift.rs:277`,
  `rows.rs:232`, `equations.rs`, `decreasing.rs:2889`, `quot.rs`,
  `interfaces.rs:1340`, `:1823`, `effects.rs:3291-4826`, `lib.rs:5103`. About
  30 sites. Form C would need them; form R doesn't.
- No hook was built, so every statement about what a hook *would* do is
  **[inferred]**. The cost estimates are guesses from the size of
  `with_local_retries` and the existing quick fixes.
- Prior art is from memory except where the design note's sources are
  named; no web lookup was made.
