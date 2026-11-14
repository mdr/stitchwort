# SW-3284 review: text patterns, stage 1

Opus review, 14 November 2026, of `lane/SW-3284` (3 commits, `df5ec23b9`,
`bffb452b0`, `78d073dbd`) against `docs/proposals/text-patterns.md` stage 1
and D3591. I read the diff and ran probes with the branch's release binary
(small files in a scratch folder; no suites). The probes are listed at the end.

**Verdict: merge as is.** I found nothing that must be fixed first. The
expansion produces exactly the spelled-out terms (hashes compared
directly, below). The type-directed choice falls back to `Text` only where
D3591 says it should. The text missing-case message can't hide a case or
make a possible one definite, and the redundancy check is the same tree
check as before. The findings below are follow-ups and nits, most of them
behaviours that number and character patterns already have.

## Soundness and meaning

- **Same terms as the spelled-out form [measured].** I wrote two small
  projects, one with text patterns and one with the same patterns spelled
  out (`MkText [...]`, `[...]`), and compared every declaration's hash with
  the `hash_stability::dump` test. They were **identical for all 6,154
  lines**: a `Text` table with an or-pattern, `"é→"` and `""`; a `List Char`
  literal mixed with a `[..]` list pattern; a tuple of `Option Text` and
  `Nat` with `Some "on"` and an escaped `"\n\"x"`; a text block; a
  `rfl` theorem; and all the arm equations (`eq1`…, `eq2.or1/or2`,
  `eq.altN`). (The text block first differed because my spelled-out form
  left out the block's final newline. With `'\n'` added it matches, and
  `blk "ab\n"` is true, as text blocks are elsewhere.) Nothing reaches the
  kernel that it doesn't already check, so a wrong expansion could at
  worst change what a program means, and the hashes show it doesn't.
- **The type-directed choice** (`text_kind`, which forces the column type
  first):
  - A `def Word: Type := Text` alias, or `def Chars: Type := List Char`,
    is unfolded and picks the right meaning (tested by running).
  - A metavariable scrutinee (`let f := match | "a" => 1 | _ => 0` then
    `f cs` with `cs: List Char`) falls back to `Text`. As D3591 says, the
    later use is then a type error: "expected `Text`, but this has type
    `List Char`". The program is refused, never misread.
  - A polymorphic `x: a` gets `MkText` and then "these patterns match a
    `Text`, but the argument has type `a`". It is refused, and can't
    match some other way once instantiated.
  - `List a` with `a` a variable is read as `List Char`, and the
    character patterns then refuse it ("match a `Char`, but … `a`").
  - `List (Option Char)` and `Char` each get the new
    `E-TYPE-MISMATCH`.
  - So a wrong choice always ends in an error, never in a program that
    compiles but means something else.
- **Character spans** (`span.start + 1 + byte offset in the decoded
  text`) are not the source positions of the characters when the literal
  has escapes or is a text block. They are only used as keys of
  `text_spans`/`char_patterns`. The decoded text is never longer than its
  source, so the keys stay inside the literal and can't clash with another
  pattern's span. No message I could provoke points at one.

## Coverage and redundancy

- A column of text literals alone reports "no arm matches texts other than
  …" (or "character lists"). A column that mixes them with `MkText [...]`,
  `[...]` or `_` falls back to the existing messages. This is as designed.
- **Can't hide a missing case.** `mark_text_gaps` rewrites only a `Missing`
  whose `text_gap` is non-empty and lies within one column's literal
  spans. `text_gap` is set only on arms that were already definite
  (`Arm::definite()` in a constructor split, `other_numbers` at a number
  default), so nothing that `may_be_impossible` would have checked becomes
  definite. Missing cases on other columns keep their own messages. Only
  one missing case is reported at a time (`"a", True | "b", _` reports the
  texts, not `"a", False`), but the number patterns already do the same
  (probe c2n). Adding a catch-all covers all of them in either case.
- **Redundancy is right in the probes.** These were warned:
  - `"ab"` listed twice;
  - `MkText ['a']` after `"a"`;
  - `"a"` after `['a']` on a `List Char`;
  - `"b" | "b"`;
  - `_` after `[]`/`[_, .._]` coverage.

  `""` after `[_, .._]` was correctly *not* warned. `subsumes(Text,
  Text)` compares the strings, which is right. Pairs of `Text` and
  `Ctor`/`MkText` aren't compared there, which can only leave out a
  warning, never add a wrong one.
- `let "a" := t` gets `E-LET-REFUTABLE` "doesn't match texts other than
  "a"", which is good.

## Hidden `Char.isScalar n = True` hypotheses

These are only hidden from the goal display: the hypotheses stay in the
context for tactics, and only `✝` names are hidden, which a user can't
write anyway. Outside char and text patterns, the same hypotheses also
appear from shadowing, or after a later split turns a `valid✝` into a
literal. Both are trivial facts, so hiding them there is harmless too.
One small gap (nit 4).

## Parser

- `Tok::Str` is a pattern atom, so it works:
  - as a constructor argument (`Some "on"`);
  - in tuples, or-patterns, clause lambdas and `matches`;
  - in function clauses with several columns.
- An interpolated literal is refused with `E-TEXT-PATTERN` across the
  whole literal, and the rest of the file still checks (probe s3: a later
  test runs). An unclosed `"a${t"` is the lexer's existing error.
- `"--" ++ rest` gets a generic `E-PARSE` "expected `=>`, but found `++`"
  (nit 3). Stage 2 handles `++` after the atom, and nothing here is in its
  way.
- `stitchwort fmt` keeps text patterns and text-block patterns as written,
  and tidies spacing around them.

## Docs and examples

- These pass with the branch's binary:
  - `examples/accept/text-patterns.sw` (16 tests);
  - `web/guide/40-text-patterns.sw`;
  - `docs/guide/examples/proofs.sw`.
- `docs/guide/examples/errors/text-missing-case.sw` gives the output the
  guide shows.
- The four reject snapshots read well.
- `Text.startsWith` in a guard and `Text.stripPrefix` exist and work as the
  note says.
- No existing snapshot or hash changed, which meets stage 1's gate.
- `docs/syntax.md` and both guide chapters are accurate. The tour page is
  short, a newcomer can follow it, and it is listed in `guide.html`.

## Must-fix before merge

None.

## Should-fix (tickets)

1. **Catch-all goals in a text match show the expansion's insides.** In a
   proof's `| _ => ?` after text literals, the goal lists `tail✝: List
   Char`, `code✝: Nat`, `valid✝: Std.Char.isScalar code✝` (probes h1 and
   dep). These are the cells of the leaf the goal was taken from, which the
   user never wrote and can't name. This already happens for spelled-out
   patterns, but text patterns will make it common. Suggest hiding the
   variables that a text column's split introduced, in a leaf reached
   through a catch-all. A proof-UX ticket, with stage 3.
2. **Text missing-case messages drop the other columns.** For `True, "a" |
   False, _` the message is "texts other than "a"", with nothing to say it's
   only when the first value is `True`; and the same applies for c8.
   Number messages behave the same (c6n), so one ticket for both: for
   example "… other than "a" (with `True, _`)".
3. **Metavariable fallback gives no pointer.** When a `Text` fallback later
   meets a `List Char`, the error is a plain type mismatch at the use. A
   note naming the text pattern that fixed the type to `Text` (and
   suggesting a type annotation) would save a search. Numbers falling back
   to `Nat` have the same issue.

## Nits

1. `compile` checks for an all-text column even when `rows` is empty (an
   empty `collect` is `Some([])`), and then calls `text_kind` on any
   column type. This is harmless, because no gap can be inside an empty
   set, but `!rows.is_empty()` would say what's meant.
2. Witnesses for a `Text` column that isn't all literals print an unknown
   text as `_` next to a known `""`. For `"a", True | … | _, False` the
   missing cases are listed as `"", True` and `_, True`, where one `_,
   True` would do; `_` also overlaps texts that are covered. Pasting both
   arms is still correct.
3. `"--" ++ rest` in stage 1 gives a generic `E-PARSE`. If stage 2 is
   delayed, an `E-TEXT-PATTERN` pointing to a guard would be friendlier.
4. `known_char_proof` hides `Char.isScalar n = True` without checking that
   `n` is a scalar. That matters only for a spelled-out `MkChar 55296 _`,
   whose hidden hypothesis is false: exactly what a user closing that
   branch would want to see. Evaluating `isScalar n` before hiding would
   make the rule exact.
5. The doc comment on `Decl::text_spans` says it is "written and read
   while one pattern match is compiled", but it is cleared per
   declaration (`Decl::reset`), as `char_patterns` is (and that field's
   doc has the same wording).
6. The error for `List` of a non-character says "a `List` of something
   other than characters". It could name the type (`List (Option
   Char)`). A polymorphic `a` gets the generic "these patterns match a
   `Text`" message rather than the text-pattern one.
7. In `docs/guide/03-data.md`, `arrowAhead` has `| "->" => True` straight
   above `| ['-', '>', .._] => True`. The first arm adds nothing, which is
   an odd thing to teach. The accept example's `arrow` (`Some []` against
   `Some more`) shows the difference better.

## Probes

The probe files are in the reviewer's scratch folder: `p/*.sw`, plus
`proja`/`projb` for the hash comparison. Each was run with
`stitchwort check` or `test` from the branch's release binary, and the
hashes with `HASH_DUMP=… cargo test --release -p stitchwort-driver --test
library -- --ignored --exact hash_stability::dump`.

| Probe | What | Result |
|---|---|---|
| proja/projb | hashes, text against spelled-out | identical (6,154 lines) |
| t1 | `Text` and `List Char` aliases | right meaning, tests pass |
| t2, k2 | polymorphic `a`, `List a` | refused |
| m1 | metavariable scrutinee used as `List Char` | refused at the use (should-fix 3) |
| k3, k5 | `List (Option Char)`, `Char` | `E-TYPE-MISMATCH` |
| c1–c9, g1–g4 | missing cases: nested, several columns, mixed, guards | as described above |
| r1, c5 | redundancy | right |
| h1, dep | goals, dependent match `T t` | arm types compute; noise (should-fix 1) |
| s1–s7 | `++`, interpolation, recovery, or-patterns | as described above |
| l1 | refutable `let` | `E-LET-REFUTABLE` with the text message |
| fm, tbf, pf | `fmt` | kept as written |
