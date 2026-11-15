# SW-3288 review: text prefix patterns `"lit" ++ rest` (text-patterns stage 2)

Opus review lane, 15 Nov 2026, of `git diff main...lane/SW-3288` (commits
fb38f0cc2, 603d0aecc, e8973e008). Probes were run with the lane's release
binary (built 09:30, after the code commit) on scratch files; no test
suites were run. The probe files are in the scratchpad, not the repo.

**Verdict: merge after fixes 1 to 4.** The match compilation is sound and
works well in the cases that matter most (variable or `_` rest, nested in
constructors and tuples, clause lambdas, multi-column function clauses,
guards falling through to the next prefix arm, two text rests in one
guarded row, JS output). The kernel sees only ordinary `let`s and `case`s,
and the hashes of existing definitions are unchanged. But a chained prefix
on a `Text` gives `rest` the wrong type, which contradicts the docs and the
example's own comment, and guarded prefix arms lose their arm equations.
Both are small fixes.

## Findings, ranked

### 1. High: on a `Text`, a rest that isn't a variable is typed as `List Char`, so `"a" ++ "b" ++ rest` binds `rest : List Char`

`crates/syntax/src/ast.rs`, `Pattern::prefix_chars` (around line 958):
`Pattern::Var(x) if on_text => TextRest`, `other => other.clone()`. The rest
pattern is put as the tail of the character list, so the column below it is
a `List Char`. A nested `Prefix` there is expanded *on a list*
(`prefix_pattern` with `on_list = true`), and its own variable is bound to
the list:

```
def chained: Text → Text
  | "a" ++ "b" ++ rest => rest     -- E-TYPE-MISMATCH: expected Text, has List Char
  | _ => ""
```

The same goes for any other rest pattern on a `Text`: `"->" ++ [c, ..cs]`
on a `Text` column is accepted with no error and matches characters, though
docs/syntax.md and §4.2 say the rest is "any pattern of the same type". The
lane's example `chained` returns `rest.length`, which works on either type,
so it hides the bug. The arm equation shows it too: `chained ("ab" ++ MkText
rest) = rest.length`, where `rest` is the list.

A second symptom: the missing-case list prints only the outer literal, so
`"a" ++ "b" ++ _` shows as `"a" ++ _` (`lib.rs` ~4233, `format!("{} ++ _",
quoted_text(text))`). That suggests `"ac"` is covered.

**Fix.** In `prefix_chars(on_text = true)`, when the rest is a `Prefix`,
splice in its `prefix_chars(true)` (recursively, so its variable becomes a
`TextRest`), keeping each character's own span. A `Text` rest is fine as it
is: a text pattern on the list column gives the same characters. `_` is fine
too. Refuse any other rest pattern on a `Text` (list, `Cons`, constructor)
with `E-TYPE-MISMATCH` ("the rest of a `Text` is a `Text`: write a variable,
`_`, a text or another prefix"), or as the end state, bind a hidden list
variable and match `MkText r` against the pattern in a new column. Refusing
is enough for now. Make the missing-case text concatenate the whole chain
(`"ab" ++ _`; for a `Text` rest, the exact text `"ab"`). Change the
example's `chained` to return `rest` as a `Text`, and add a test.

### 2. Medium: a guarded prefix arm on a `Text` loses its arm equation, and so does the arm after it

The `let rest := MkText r` that `check_guard` puts around the whole `if`
(`lib.rs` ~5995–6069) hides the `if` from the equation generator.

```
def g1: Text → Nat
  | "-" ++ r if r.length > 0 => 1
  | _ => 0
```

`stitchwort doc g1` gives `g1.eq1: an arm's condition isn't elaborated as
Bool.ifThenElse or Decidable.elim …` and `g1.eq2: the overlap with arm 1
can't be stated`. The same guard on `List Char`, or with `_` as the rest,
gets both equations. The lane's own hash snapshot
(`library__hash_stability__text-patterns-prefix.snap`) has only
`Main.Arg.read.eq1` and `eq2`: `eq3` (the guarded `Short` arm) and `eq4` are
missing for this reason.

**Fix (either):**

- (a) In `equations.rs`, where a row's guard is read, peel the leading
  `let`s of the arm's term by substituting their values, then read the `if`.
  The equation then states the guard over `MkText r`, which the printer
  shows as the rest's name.
- (b) Emit the `let`s inside the condition and inside the then branch
  rather than around the `if`. This also removes the `shifted(otherwise)`
  loop.

I'd take (a): it keeps one `let` per arm, and the runtimes build the text
once. Regenerate the hash snapshot, which should gain `Arg.read.eq3` and
`eq4`.

### 3. Medium: the goal printer shows `rest` even when the user's arm has shadowed `rest`

`crates/core/src/pretty.rs:773` and `:1021` turn any variable named
`%text x` into `x` (or `x.toList`) by its name alone, bypassing the
`✝` disambiguation:

```
theorem viaLet ∀ (t: Text): t = t := match t with
  | "ab" ++ rest => (let rest := 1; ?)
  | _ => rfl
```

The goal lists `rest✝: Text` and `rest: Nat := 1`, but prints `⊢ "ab" ++ rest
= "ab" ++ rest`, where `rest` reads as the `Nat`. Error messages behave the
same way (`rest.toList` with `rest` shadowed).

**On the marker itself (focus 3):** the name `%text <rest>` can't collide
with user names, since source identifiers can't contain `%` or a space, and
names starting with `%` already mean "compiler's own" across the elaborator
(`%match1`, `%tag`; `equations.rs` treats `%…` as unnamed). So the name is a
reasonable marker, in keeping with existing practice. A structured marker
would mean either widening `Name` or passing side tables to every printer
call, which costs more than it gains. The fragile part is resolving the
*display* name by string. **Fix:** resolve `%text x` at level `l` to the
name of the first binder above `l` whose base name is `x` (the
`let rest`, which `bind_text_rests` always puts above it, with duplicate
binders in one arm already refused), printed as that binder would be, `✝`
included. About ten lines. A goals example with a shadowing `let` would pin
it.

### 4. Low: the doc comment of `pretty::term` now belongs to `TEXT_REST`

`crates/core/src/pretty.rs:68–76`. The new constant was inserted between
`/// Prints \`term\`, whose free variables …` and `pub fn term`, so rustdoc
gives the constant a two-paragraph doc that starts with "Prints `term`", and
`term` has no doc. Move the constant above that line.

### 5. Low (ticket, not for this lane): arm equations state a prefix arm over the hidden list, named `x1`

`Arg.read.eq2: x1 ≠ [] → Arg.read ("--" ++ MkText x1) = Long (MkText x1)`
and `setting.eq3: (∀ (x1: List Char) => line ≠ Some ("set " ++ MkText x1)) →
…`. These are sound (each is a kernel-checked theorem) but show the
representation. `x1` comes from `equations.rs:2633`/`2946`, which names
every `%…` binder `x{n}`. Renaming it to `name` alone would be misleading,
since it's a list. The right end state is to quantify over the text:
`∀ (name: Text), name ≠ "" → Arg.read ("--" ++ name) = Long name`, proved by
a case on `name`. Stage 3 (catch-all equations as `t ∉ […]` and `¬
t.startsWith`) reworks these statements anyway. File it there, and leave
`x1` until then.

### 6. Low (ticket): recursion on a `Text` rest fails the termination check

```
def count: Text → Nat
  | "ab" ++ rest => 1 + count rest     -- E-TERMINATION: `rest` isn't seen as smaller
  | _ => 0
```

The `List Char` version passes. This limitation predates the lane (a `Text`
is a wrapper with no structural order), but prefix patterns make this the
first thing a lexer author writes on a `Text`. It needs a design (Opus): read
`MkText r` with `r` a strict subterm of the scrutinee's characters as
smaller, or compile through an auxiliary on the list. Until then, the
guide's prefix paragraph could say that a recursive lexer works on a `List
Char`.

### 7. Low (finding): the goal index gives no lemma for a goal that mentions the matched text

`server__goal_index__goal_index__lemmas.snap`: `text-patterns-prefix goal 1:
no lemma` (the `startAndRest` goal `"--" ++ rest = "--" ++ rest`). It is
likely blocked by the hidden list variable. A lemma `theorem
startAndRestGoal1 (rest: Text): "--" ++ rest = "--" ++ rest` would check.
Small ticket.

### 8. Polish

- `web/guide/40-text-patterns.sw`: the `token` example above the new one
  still spells `['-', '-', .._]`, and could be `"--" ++ _` now.
- In JS, an arm after a guarded prefix arm rebuilds the same text
  (`textOfChars(v3)` twice). This is harmless, and goes away with the slice
  change below.

## What was checked and found right

- **Match compilation.** Overlapping prefixes (`"-" ++ r` then `"--" ++ n`,
  with and without a guard on the first), an exact text before and after a
  covering prefix (`"ab"`, `"a" ++ r`, `"a"`), `Some (Some ("p" ++ r))`,
  `("set " ++ x, 0)` in a tuple, clause lambdas (`filterMap (match | "k=" ++
  v => …)`), a second column in function clauses (`| 0, "a" ++ r`), and two
  guards in a row with the same rest name all compute correctly on the
  machine. In the guarded path, the `let`s around the `if` and the shifted
  `otherwise` are right: `fall` (guard fails, next prefix arm rebinds `r`),
  `twoRests` (two text `let`s, `otherwise` shifted twice) and `shadow` (the
  rest shadows the function's own parameter, which the else branch sees
  again) all pass. The guard is pure, so evaluation order and effects don't
  change: `let rest := MkText r` has no effects, and the JS evaluates it once
  before the test. Or-alternatives that bind are refused as before
  (`E-OR-PATTERN-BINDS`), and `"a" ++ _ | "#" ++ _` works.
- **JS** (`build --js`, run under node): `"-ab"`, `"-a"`, `"x"`, `"-"` and
  a non-ASCII rest give the expected results. The generated code is a
  `switch` on the code point, then `textOfChars` of the tail.
- **Kernel and hashes.** The match compiler emits only `case`s and `let x :
  Text := MkText r`. There is no new term form and no `docs/core.md` change
  is needed. The only existing snapshot that changed is the interpolation
  error's note. `ctor_args` now stops at `++` in patterns, but `++` in a
  pattern was a parse error before, so no existing source parses
  differently.
- **Exhaustiveness and `W-REDUNDANT`.** `subsumes` (`redundant.rs` ~227) is
  correct for Prefix-vs-Text (strip the prefix, then the rest must be a
  variable or `_`, or exactly the tail) and Prefix-vs-Prefix (the longer
  starts with the shorter, and the general rest is a variable or `_`).
  Guarded rows aren't treated as covering. Probes found no false redundancy
  and no false missing case. "Certainly missing" for a column of only exact
  texts and prefixes is right, because the lowering turns `"" ++ p` into `p`,
  so every prefix fixes at least one character. One false *negative* is
  possible: `"ab" ++ _` doesn't see `"a" ++ "b" ++ _` as redundant. Fix 1
  removes that.
- **E-TEXT-PATTERN.** `Some "a" ++ rest` at the top of an arm, inside a
  tuple, and inside a list gets the brackets note. `name ++ ".sw"` and `a ++
  "-" ++ b` get the fixed-start note. An interpolated literal before `++`
  still gets the interpolation error first. The formatter keeps
  `"a"++r` → `"a" ++ r`.
- **The hand-written goal_index snapshot.** `check --index - text-patterns-prefix.sw
  --no-cache` from `examples/goals`, with its `diagnostics` compared to the
  snapshot body under `jq -S`, is identical. The lemma summary's counts
  (+2 lemmas, +1 without) match its three new lines.
- **Goals.** `rest: Text` is listed without its value. The hidden list and
  the `valid` proofs aren't listed. `goals.rs::text_rest_let` indexes the
  `let`'s value correctly relative to its own level.

## Rest as a slice, now that fast text (SW-3337) is on main

Yes, it should, and in the runtimes alone, as the lane's note at
`bind_text_rests` and §4.6 say. The kernel term keeps `let rest := MkText
r`. The kernel can't use `Text.drop`, which would make `rfl` proofs of `t =
"--" ++ rest` depend on unfolding `drop`.

How big: SW-3337 left `MatchKind::Text` and `Instr::TextChars` as they
were. Matching a `Text` still builds its whole character list, and `MkText
r` is `TextFromList`. The change is a peephole in `crates/rt/src/lower.rs`
(and the same in `crates/js`): recognise `TextFromList(v)` where `v` is the
tail slot k `Cons` levels below a `Match(Text)` on `t`, with only
character switches between them, and emit `Text.drop k t`, a
constant-time slice since SW-3337. It would be about 100 lines plus
differential tests, around 2–3 lane hours [estimated]. On its own it saves
one of the two O(length) passes per match. The whole list is still built by
`TextChars` until stage 5 reads characters lazily, so it is best done
together with stage 5. It shouldn't block this merge.

## Tests run

None from the suites. Only CLI probes with the lane's release binary
(`check`, `test`, `doc`, `fmt`, `build --js` plus node, `check --index`) on
scratch files.
