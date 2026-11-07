# Goals that print forms the source doesn't have: the parts outside bounded read-back

**SW-2143**, 7 Nov 2026. Design only: nothing was built or run. It covers gap 4 of
[aoc-gaps-status-2026-11-07.md](../reviews/aoc-gaps-status-2026-11-07.md) ("goals print forms
the source doesn't have", 24+ days), where that gap lies outside
[bounded-readback-remaining.md](bounded-readback-remaining.md): SW-1004 (`f.%match1`),
SW-1469 (middle spreads, `sumBy` and `count`), SW-2076 (record updates after record eta) and
SW-2102 (an expected type printed unfolded). Its question is D3090 (§7).

Written against `main` at `b2794ebc0`. Labels: **[checked]** (read at the line given),
**[cited]** (from the ticket, note or review named), **[inferred]** (my reasoning from what I
read; not run).

## 0. Summary

What a user gets, case by case:

| Today | After | Fixed by |
|---|---|---|
| `[0, ..chain ++ [highest + 3]]` (2020 day 10; `..List.append …` before SW-1674) | `[0, ..chain, highest + 3]` | **this note, stage A**: the printer reads an `append` inside brackets as spreads. Same term, so nothing else changes |
| `{ hp = state.hp, gold = state.gold, …, message = m }` once a goal has opened an update | `{ state \| message = m }` | **stage B** (SW-2076): the printer counts a `Proj` field as "taken from `state`", as it already counts `State.hp state` |
| `expected (x: Nat) → x ∈ image.flip.rotate.rows → x ∈ image.rotate.rows, but this has type Within image.flip image.flip.rotate` | `expected Within image.rotate image.flip.rotate, but this has type Within image.flip image.flip.rotate` | **stage C** (SW-2102): the error shows the expected type as it was before being forced. The cause is in `check.rs`, not in record eta |
| `other ∈ next cave ∧ Aoc.Year2021.Day12.Proofs.Follows.%match1 next other tail (step unvisited spare cave other)` | `other ∈ next cave ∧ (match step unvisited spare cave other with …)` | **stage D** (SW-1004): a lifted `match` prints as the `match`, with its scrutinees, as messages already say `(match …)` (D229) |
| `List.foldLeft xs Add.zero (acc x => acc + f x)` where the source says `xs.sumBy f`; `Map.contains.%match1 () (Map.get group.items box)` where it says `group.contains box` | `xs.sumBy f`, `group.contains box` | **bounded read-back**: 1c, 5, and 6a/6b. Not a printer change (D3090) |

The rule behind the split (D3090): **the printer may write a term in another notation for the
same term, but it doesn't refold a definition.** Spreads, updates and the `match` form are
notation: what's printed elaborates to the term that's there, or one that differs only in how a
field is reached. `sumBy` folded back would show a call that isn't in the term. Since D2542,
`rewrite` and `match` search the goal as it is shown. A printed `xs.sumBy f` over a term that
holds `foldLeft` would make a `sumBy` lemma fail on a goal that seems to contain `sumBy`, while
a `foldLeft` lemma that the user can't see would succeed. Keeping the call is read-back's job,
and the bounded read-back plan already does it.

Four lanes, about 165 minutes: A (DeepSeek, 30), B (Sonnet, 30), C (Sonnet, 45), D (Sonnet, 60),
plus a 20-minute check after read-back stages 6a and 6b (§8).

## 1. How a goal gets printed

A goal is a `Value`. `pretty::value_for_goal` (`core/src/pretty.rs:320`) reads it back with
`quote_shown` and prints the term (`value_within`, `:340`). **[checked]** `quote_shown`
(`core/src/value.rs:2570`) keeps a glued call as a call. The exception is a call that
"matches at once", because its definition starts with a case on an argument that is
already a constructor (`matches_at_once`, `:682`). Such a call is written as its one step
(`:2802-2806`). Elaborated terms use `quote_folded`, which forces that step instead of writing
it. **[checked]** So a goal shows definitions folded, except:

1. where the term was built by an **unfolded** read-back (`quote`) somewhere upstream: a
   `match` motive, `cases`' pieces, `rewrite`'s next goal, a message site. That is the ~200
   sites of bounded-readback-remaining §1.2;
2. where a call **matched at once**, and its step is shown instead (`List.length [x, ..xs]` is
   `Succ xs.length`);
3. where the printer has no notation for a term the elaborator built (an `append` tail, a
   literal of `Proj` fields).

Kind 1 is bounded read-back's. Kinds 2 and 3 are this note's.

## 2. The cases, traced

### 2.1 SW-1469 (a): a spread in the middle of a list

**The problem.** 2020 day 10's spec says `[0, ..chain, highest + 3]`, and the goal said
`[0, ..List.append chain [highest + 3]]` (NOTES-2020 §5, line 2727). **[cited]** Since SW-1674
(6 Nov, after day 10) `List.append` prints as `++` (`arithmetic`, `pretty.rs:1361-1369`), so
today it should read `[0, ..chain ++ [highest + 3]]` **[inferred: not run]**. That's still not
what was written.

**Why.** A spread that isn't last elaborates to `List.append` (docs/syntax.md:204:
`[a, ..xs, b, ..ys]` is `Cons a (xs ++ Cons b ys)`). The printer turns an open `Cons` chain
into `[a, b, ..t]` (`open_list`, `pretty.rs:2934`, used at `:836-845` and for `NonEmptyList`
at `:734-757`) and prints the tail `t` as an ordinary term. **[checked]**

**Fix: the printer (notation).** Inside brackets, a tail that is the library's `append l r`
(`Builtin::Append`) is printed as `..l` and then whatever `r` is: more items, another
`append`, a closed list, which ends the brackets, or an open tail. So `Cons 0 (append chain
(Cons (highest + 3) Nil))` prints as `[0, ..chain, highest + 3]`. That is exactly the term the
source elaborates to. `[0, ..xs ++ ys]` and `[0, ..xs, ..ys]` elaborate to the same term too,
so printing either is faithful. Long literals cut into `append`ed chunks (SW-62,
list-spread.md §4.2) print as one literal again.

At the top of a term, `xs ++ [y]` stays `xs ++ [y]`, as syntax.md promises. The term doesn't
say whether `[..xs, y]` or `xs ++ [y]` was written, and `++` is the form people reach for. The
alternative is keeping the form written: a marker on the `append` term (a `Term::Loc`-like
wrapper, or a flag), which every term operation would have to carry and hashes would see. That
buys nothing a reader needs, so the printer fix is the one.

**How we'd know.** A goal of `examples/accept/list-spread.sw`, or a new
`examples/goals/list-spread-middle.sw`, prints `[0, ..xs, y]`, and unit tests in
`crates/core/tests/it/pretty.rs` cover `[a, ..xs, b, ..ys]`, `[..xs, y]` (stays `xs ++ [y]`)
and a chunked long literal.

### 2.2 SW-1469 (b): `sumBy`, `count` and `sum` in their `foldLeft` form

**The problem.** "Every goal about `sumBy` showed `List.foldLeft … Add.zero [add :=
Nat.instAdd] (acc x => acc + …)`" (NOTES-2020:2729). **[cited]**

**Why.** `List.sumBy xs f := List.foldLeft xs Add.zero (acc x => acc + f x)` and `List.count
xs p := List.foldLeft xs 0 (n x => Nat.succIf n (p x))` (`std/List/Toolkit.sw:90`, `:216`).
**[checked]** Neither body starts with a case, so `matches_at_once` is false and a folded
read-back keeps `xs.sumBy f` whatever `xs` is (`value.rs:696-698`). **[checked]** The `foldLeft`
form can therefore only come from kind 1, an unfolded read-back. Day 10's goals were after a
`match near: …` that refined copies inside `onwardFrom` (NOTES-2020 §1, line 2652). That is a
`match` motive read back unfolded, stage 6b's site (`matching.rs`; §1.2 "motives unfolded").
`search --at`'s "leaves" (2021 day 14, NOTES-2021:3452) come from `enter_snapshot`, which reads
each hypothesis type back unfolded (`goals.rs:1180`, `:1184`). That is a stage 1c site.
**[checked: the sites; inferred: that these are the ones day 10 and day 14 hit]** The rest
arise only when the user unfolds `sumBy` themselves (`rewrite List.sumBy`) or uses a lemma
whose other side is the fold (`List.sumByFrom`, `Lemmas.sw:334`). There the fold is what's
in the term, and showing it is right.

**Fix: read-back, already planned.** A printer fold-back is possible: match the term against
`sumBy`'s body, with the parameters as pattern variables. But it would show a call that isn't
in the term, and since D2542 that misleads `rewrite` (§0). So this case is left to stages 1c
(`cases`, `search --at`), 5 (messages) and 6a/6b (next goals after `rewrite` and `match`). No
lane here. §8's check confirms it after 6b.

**What this rules out.** It rules out seeing `xs.sumBy f` after the user unfolded `sumBy`. That
is intended: the unfolding is what they asked for.

### 2.3 SW-2076: a record update opened by record eta

**The problem.** The roguelike's `resolveOutOfWalls` goal showed `State`'s every field written
out where `{ state | message = … }` was shown before record eta (record-eta-as-merged.md F2).
**[cited]**

**Why.** An update elaborates to a helper call that prints as the update through
`UpdateShown` (`pretty.rs:2069-2101`, `globals.rs:129-137`). Once that helper is read back
unfolded on an unknown `state`, rule 2 opens its record pattern, and the fields come back as
`Term::Proj(State, i, state)`. `record_update` (`pretty.rs:2109-2154`) treats a field as taken
from `x` only if it is an accessor *call* `State.f x` (`:2117-2129`). So a constructor of
`Proj` fields prints as a full literal, while the same value with accessor calls prints as an
update. **[checked]** Float's `of_bits` (`:1620-1628`) has the same gap: a `Proj` `x.bits`
inside `Float.keyOf` isn't recognised, so `x < y` on floats prints as its key.

**Fix: both.** The printer half is notation: `Proj(d, i, x)`, with `d` the record and `i` the
field's index, is field `i` of `x`. Accept it in `taken_from` and in `of_bits`. That fixes
every site at once, whichever read-back made the term. Read-back stages 6b and 1c remove most
of the occurrences anyway, by keeping the update's helper call (it then prints through
`UpdateShown`). The printer half is still needed: a `Proj` form can come from anywhere rule 2
fires (kernel terms, `cases` on an eta record), and one value should not have two printed
forms.

**How we'd know.** A goals snapshot of an update on an unknown record after `cases` (or
`match`) prints `{ state | message = m }`. The two existing `examples/goals/record-update.sw`
goals don't move.

### 2.4 SW-2102: an expected type printed unfolded

**The problem.** In `examples/reject/implicit-record-from-field-of-unknown-differs.sw` the
error reads "expected `(x: Nat) → x ∈ image.flip.rotate.rows → x ∈ image.rotate.rows`, but
this has type `Within image.flip image.flip.rotate`" (snapshot in
`crates/cli/tests/running/snapshots/`). **[checked]** The review that filed it hadn't found the
cause (SW-2094 review, U5). **[cited]**

**Why.** `check_inner` keeps the expected type as given in `named`, and forces it into
`expected` (`elab/src/check.rs:4172-4173`). **[checked]** For a glued call, `force` returns the
call's unfolding (`core/src/value.rs:574-599`). `Within ?b ?c` becomes its `Pi`. **[checked]**
`check_value` then passes the forced `expected` to `fallback_named` (`check.rs:4561`, `4683`, `4693`), and that
passes it to `compare` (`:5386`, `:5390`), which reports `cx.mismatch(expected, found)`
(`:5801`). `named` is passed alongside but used only to name an unknown (`:5381`).
**[checked]** So any mismatch reached this way, against an expected type that is a call of a
definition, prints the definition's unfolding: `Within`, `Sorted xs`, any `def … : Prop`.
Record eta isn't the cause. This example just happens to have the first snapshot of it.
**[inferred: that other snapshots show it too; I didn't grep them all]**

**Fix: keep the source form.** The written form is still in hand (`named`), so no fold-back is
needed. `compare` takes a second value, the expected type as shown, and `mismatch` prints that.
The same goes for the other `cx.mismatch(&expected, …)` arms of `check_value`
(`check.rs:4348`, `4390`, `4690`, and the rest of the function). Unification keeps the forced
value, so nothing but the message changes. The existing "Note: `X` is `…`" line, which spells
out the actual's unfolding, should spell out the expected's too when it was a call. Then
nothing the old message showed is lost.

**How we'd know.** The reject example reads "expected `Within image.rotate image.flip.rotate`",
with a note giving `Within`'s unfolding. The other mismatch snapshots that move are ones whose
expected type was a definition's call. The lane lists them, and each should read closer to its
source.

### 2.5 SW-1004: lifted `match` helpers by their internal name

**The problem.** Six days hit it (NOTES-2021:2912, 3452, 3790, 4584; NOTES-2024:1900, 4600,
8050). **[cited]** Some examples:

- `Aoc.Year2021.Day12.Proofs.Follows.%match1 next other tail (step …)`;
- `Map.contains.%match1 () (Map.get group.items box) = True`;
- a hypothesis `Aoc.Year2021.Day18.split.%match1 left right (split left) = None`, which,
  pasted back, is `E-PARSE`.

**Why.** A `match` inside a definition is lifted to a helper named `owner.%matchN`
(`elab/src/lift.rs:579`). The printer shows a name with `%` as it is (`def_name`,
`pretty.rs:519-525`; `def_display` only renames `%body`). **[checked]** Messages don't show it:
`explain_lifted` replaces it with `(match …)` and adds the D229 note (`lift.rs:1574-1660`).
But that rewrites only a diagnostic's message, labels and notes. A goal's `GoalData` (target
and hypotheses, `syntax/src/diagnostic.rs:100`) is untouched. **[checked]** Three ways a helper
call reaches a goal:

1. **Its owner was read back unfolded** (kind 1). `Map.contains m k`'s body is the helper call
   with no case before it, so a folded read-back keeps `group.contains box`, and only an
   unfolded site shows the helper. Day 11 (2024) and day 15 (2021, after `match h:`) are
   `match`-motive cases. **[inferred]** *Read-back fixes these* (1c, 5, 6b).
2. **Its owner matched at once, and the step landed in the helper** (kind 2). `Follows next
   [other, ..tail]` matches its list argument, and the `Cons` arm is `other ∈ next cave ∧
   match step … with …`. That inner `match` is the stuck helper call. Read-back writes the
   step by design (`value.rs:2802`), and needs it: it's the step that lets the next `match e:
   step unvisited spare cave other` find its scrutinee. *No read-back stage changes this.*
3. **The statement itself has a `match`** (2024 day 7's `undoCorrect.%match1 …`: a lemma
   whose statement copied the program's `match operator with`). The helper is the lemma's own.
   *No read-back stage changes this.*

**Options.**

- **(a) Fold back to the owner** (`Follows next [other, ..tail]`). SW-1000 found this needs
  higher-order matching, since not all of the owner's parameters reach the helper. Worse, in
  case 2 it would undo a step the user relies on. Rejected.
- **(b) Print the helper's whole `match`, arms and all.** Lean does this: its auxiliary
  `foo.match_1` is delaborated as `match x with | … => …`. It's faithful, but long, and
  pasting it back makes a different helper, not equal to this one (the E-REFL of SW-980; D229's
  note says so). Arms in a goal are rarely what's being proved.
- **(c) Print it as the `match` with its scrutinees and the arms elided:** `(match step
  unvisited spare cave other with …)`. It shows what is being matched, which is the term the
  next `match` or `rewrite` looks for (it's an argument of the helper call, so D2542's "search
  what you see" holds). It is what messages already say, `(match …)`, with the scrutinee
  added. **Recommended.**
- **(d) Status quo, the internal name.** Not source, and it breaks pasting.

**Fix: keep the source form beside the term, as updates do.** The elaborator already records
which of a helper's parameters are its scrutinees (`MatchColumns`, `lift.rs:101-108`;
`tables.match_columns`). **[checked]** A new hook, `Shown::match_shown(id)`, mirrors
`Shown::update_shown` (`core/src/ev.rs:73`, `elab/src/lib.rs:361`). The printer uses it to write
a call of the helper as `(match s₁, s₂ with …)`. The terms don't change. Two details, which are
mine to settle:

- The goal's paste-as-lemma form is dropped when a `(match …)` is printed. It already is:
  `lemma_of` refuses text with `…` (`goals.rs:843-852`). **[checked]**
- Messages print through the same printer. Today `explain_lifted` finds `owner.%matchN` in a
  message to add its "this `match`" label and D229 note (`lift.rs:1596-1660`). The hook should
  record which helpers it printed (as `note_failed_mentioned` does, `ev.rs:89`). Then
  `explain_lifted` reads that record instead of searching the text. Its string replacement
  stays for kernel messages that name a helper by key (termination).

**Open point for the lane.** Is `match_columns` there for helpers of modules loaded from the
cache (std's `Map.contains.%match1`)? I found `tables.match_columns` filled only in `lift.rs`
and read in `equations.rs` (grep), and didn't trace what the module cache keeps.
**[not checked]** If they aren't kept, the fallback is `(match …)` without scrutinees, as
messages have now. Keeping them in the cache is part of stage D only if it's under 20 lines.

**How we'd know.** A new `examples/goals/lifted-match.sw` covers cases 2 and 3: a `Follows`-
shaped definition after `match` on its list, and a lemma whose statement has a `match`.
Neither goal shows `%match`. 2021 day 18's `leavesSmall` hypothesis would now print `(match
split left with …) = None`, which isn't pasted (the lemma form is dropped), rather than
`E-PARSE`.

## 3. What bounded read-back already covers

| Case | Covered by | Why there |
|---|---|---|
| `sumBy`/`count`/`sum` as `foldLeft` (§2.2) | 6b (`match` motives), 6a (`rewrite`'s next goal), 1c (`cases` `take_apart`, `cases.rs:953-1072`; `search --at`'s `enter_snapshot`, `goals.rs:1180-1184`), 5 (message sides) | only an unfolded read-back produces them |
| `%match` via an unfolded owner (§2.5, case 1) | the same stages | the same |
| `Nat.divFuel …` past its first step (2024 day 24, NOTES-2024:8050) | 6b and O | an unfolded `testBit` in a motive or an `omega` atom; the printer already folds the first step back (`quotient`, `pretty.rs:1385-1447`) |
| Most opened updates (§2.3) | 6b, 1c | the helper call kept folded prints through `UpdateShown` |

Stages 1c and 5 alone are not enough for these. Day 10's and day 15's goals followed a `match`,
so they wait for **6b**. That is sixth in bounded-readback-remaining §5.1, behind D2610.

## 4. Prior art

- **Lean 4.** Its delaborator prints auxiliary matchers (`foo.match_1`) as `match` syntax, and
  `app_unexpander`s give notation back to function applications. Both are printer-side, and
  both print only what elaborates back to the term. Lean doesn't refold definitions in goals:
  a goal after `unfold` shows the unfolding. That is the rule of D3090. **[cited from memory;
  not re-checked for this note]**
- **Agda** prints `with`-helpers by their generated names (`f.with-12`), a long-standing
  complaint. That is our status quo.
- **Coq** has `match` in the core language, so there is no helper to name.

## 5. Designs compared, overall

1. **Printer fold-back everywhere**, definitions included (sumBy, the owner of a `%match`).
   It gives the most readable goals soonest. But the printed goal and the searched goal part
   ways, contrary to D2541/D2542. It needs higher-order matching for the owner case. And it
   hides an unfolding the user asked for.
2. **Notation in the printer, definitions kept by read-back** (recommended). Every printed form
   is either the term or another notation for it, so `rewrite` finds what's shown. The cost is
   waiting for 6b for the `sumBy` case.
3. **Keep source forms in terms** (markers for spreads, `match` syntax in terms). That changes
   hashes and every term operation, to record what's already recoverable. Used here only where
   the form is already kept beside the term: `MatchColumns` (§2.5) and `named` (§2.4).

The printer already does some definition fold-back: `n % d` from `n - n / d * d` and
`Nat.divFuel n n d` as `n / d` (`pretty.rs:1343-1353`, `:1385`), and `Float.keyOf` as
`orderKey` (`:1609`). These predate D2542. Under D3090 they stay for now, and §8's check looks
at whether `rewrite` on such goals finds what's printed.

## 6. Calls I made

- A top-level `append` prints as `++`, and only an `append` inside brackets prints as spreads
  (§2.1).
- A `match` helper prints as `(match scrutinees with …)`, arms elided, in goals and messages
  alike (§2.5). That extends D229's `(match …)` to goals, with the scrutinee added.
- SW-2102's fix covers every `check_value` mismatch, not only the record-from-field one
  (§2.4).
- Stage order: A, B and C side by side, then D. B and D both touch `pretty.rs`, but in
  different functions.

## 7. Question for Matt

- **D3090: the goal printer writes another notation for the same term, but doesn't refold a
  definition.** So `sumBy` shown as its `foldLeft` waits for read-back stages 1c, 5 and 6a/6b,
  which keep the call, rather than the printer matching the fold and printing `sumBy`. [rec:
  yes. Since D2542, `rewrite` and `match` search the goal as it's shown, so a printed call
  that isn't in the term would make a `sumBy` lemma fail on a goal that seems to contain
  `sumBy`. The cost is that day 10's `sumBy` goals stay as folds until 6b. The existing
  fold-backs (`%`, `/`, `orderKey`) stay until §8's check.]

## 8. Tickets to file

| Order | Stage | Model | Est. | Absorbs | Targeted tests |
|---|---|---|---|---|---|
| 1 | **A. Middle spreads print as written** (§2.1). `open_list` flattens a `Builtin::Append` tail, for `List` and `NonEmptyList` brackets. Update docs/syntax.md:204 ("`++` stays `++`" now means "at the top") and the guide's spread section | DeepSeek | 30 | SW-1469 (a) | new cases in `crates/core/tests/it/pretty.rs` (`task test:one -- pretty`); `task test:lane AREA=goals`; the `list-spread` example (`task test:lane AREA=examples NAME=list-spread`) |
| 1 | **B. `Proj` in `record_update` and `of_bits`** (§2.3). Add a goals example of an update on an unknown record after `cases` | Sonnet | 30 | SW-2076 | `task test:one -- pretty`; the new goals snapshot and `record-update` (`task test:lane AREA=goals`) |
| 1 | **C. Mismatches show the expected type as written** (§2.4). `compare` and `check_value`'s arms print `named`. The note spells out a call's unfolding on both sides. List every snapshot that moves | Sonnet | 45 | SW-2102 | `task test:lane AREA=examples NAME=implicit-record-from-field`; the `E-TYPE-MISMATCH` example snapshots that move, rerun by name. No term changes, so no `hash_stability` |
| 2 | **D. Lifted `match`es print as `(match s with …)`** (§2.5). `Shown::match_shown` from `match_columns`. `explain_lifted` reads the printer's record of the helpers shown. First check whether cached modules keep `match_columns` | Sonnet | 60 | SW-1004 | new `examples/goals/lifted-match.sw` (`task test:lane AREA=goals`); the `explain_lifted` message snapshots (`task test:one -- match` on the reject examples that print `(match …)`); `task test:one -- pretty` |
| after 6b | **E. Check what read-back left** (§2.2, §3). Grep the goal snapshots and a day 10, 2021 day 14 and 2024 day 11 run for `%match`, `foldLeft … Add.zero` and `Proj` literals. Check whether `rewrite` finds what `%` and `/` print. Close SW-1469 (b) or file what's left | DeepSeek | 20 | SW-1469 (b) | only the three days' proof namespaces, with Matt's OK for the AoC run (CLAUDE.md, lane test scope) |

A, B and C change no terms, so `hash_stability` and `snap:hashes` aren't needed. D changes no
terms either, unless it adds `match_columns` to the module cache. If it does, it runs the
cache's round-trip test (`task test:lane AREA=elab`).

## 9. What this note did not do

- It ran nothing. "Prints today" for spreads is inferred from the code after SW-1674. The
  2020 day 10 note predates it.
- It didn't trace every unfolded read-back that day 10, 2021 day 15 and 2024 day 11 went
  through. It names the likeliest site from the notes' context (§2.2, §2.5 case 1).
- It didn't check whether the module cache keeps `match_columns` (§2.5).
- It didn't grep all mismatch snapshots for SW-2102's pattern. Stage C lists them.
