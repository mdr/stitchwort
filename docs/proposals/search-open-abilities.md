# Search patterns with abilities left open

SW-4937. Status: proposal, waiting for Matt's decisions (end of the note).
Implementation follows them, after SW-4935 (search speed), which works in
the same code.

Matt, 27 Nov 2026: "Is there a way to search for something where you're not
quite sure what abilities might be involved?"

## The problem

`stitchwort search` takes a pattern that reads like a type. Abilities are
part of a type, so a pattern has to say them, and today there is no way to
say "some abilities, I don't know which". Everything tried, against the
library (release CLI at `main`, `search --in Std`):

| Pattern | What happens |
|---|---|
| `() → {Parse _} Int` | finds `Std.Parse.int`, `() → {Parse Char} Int`. Works, when you know the ability. |
| `() → {_} Int` | refused: `E-ABILITY` "expected an ability". |
| `() → _ Int` | refused: `E-NOT-A-TYPE` "this has type `_ Int`, so it isn't a type". |
| `() → {e} Int`, `() → {?e} Int` | accepted, but the only result is `Std.Effect.bindIn` (relaxed pass, with the "weaker" warning). `Parse.int` isn't found. |
| `() → {Parse _ \| e} Int` | accepted; `Parse.int` isn't found among its matches. |
| `() → {Parse _ \| _} Int` | refused: `E-PARSE` "expected a row variable, but found `_`". |
| `() → {Parse _, _} Int` | refused: `E-ABILITY` "expected an ability". |
| `Text → {e} Nat` | only `bindIn` again; misses `Std.Text.toNatOrFail`, `Text → {Fail} Nat`. |
| `() → Int` | no `Parse.int` (right: it's a pure type), and the relaxed pass lists 11 unrelated premise matches instead. |

Two things stand out. The search already prints a row hole as `{_}`: the
JSON of `() → {e} Int` says `"elaborated": "() → {_} Int"`, a spelling it
refuses as input. And `{e}`, the one spelling that is accepted, is meant to
work: the unifier has a rule for exactly this (below) and would match
`Parse.int`; the candidate is thrown out before it gets there.

### Why `{e}` misses `{Parse Char}`

A computation type is one of four terms in the core (docs/core.md,
"Abilities"; `crates/elab/src/effects.rs`, `comp_type`):

- `{A, B} t` (abilities, closed): `Effect.Comp ops res t`;
- `{e} t` (a bare row variable): `Effect.CompIn e t`, which computes to `t`
  at the empty row and to a `Comp` at any other;
- a row with `Partial`: `Effect.Delay ops res t`;
- a signature's bare `{e}` with its divergence index: `Effect.CompD d e t`.

The pattern `() → {e} Int` elaborates to `() → CompIn ?e Int`. The unifier's
row rule (`crates/elab/src/unify.rs`, `row_rule`, design C of
effect-polymorphism.md) solves `CompIn ?e Int ≟ Comp ops res Int` with
`?e := Ops ops res`, and `CompIn ?e Int ≟ Int` with `?e := Empty`. So the
match would succeed. But the filter (`search.rs`, `passes`) only compares a
candidate whose type names every definition the pattern names, and the
pattern names `Effect.CompIn`, which `Parse.int`'s type doesn't. The relaxed
pass for a function pattern still asks for a definition in common
(`overlaps`), so `Parse.int` is never compared; `bindIn` is, because its type
mentions `CompIn`.

`{Parse _ | e}` fails for a second reason: it elaborates to
`Comp (Plus (Parse ?t) (rowOp ?e)) … Int`, and plain unification can't solve
`rowOp ?e ≟ NoOp` (`rowOp` is defined by cases; `Empty` is the answer but
the unifier doesn't invert definitions), nor reorder a `Plus` chain against
`{Fail, Parse Char}`. The elaborator handles open rows by taking them apart
into labels and a tail (`effects.rs`, `comp_parts`, `solve_tail`); search
uses plain unification only.

## What other tools do

Checked 27 Nov 2026. None of these languages has abilities quite like
Stitchwort's; the nearest things are effect rows (Unison, Koka) and type
class constraints (Haskell, Idris, Lean), which candidates carry and queries
often leave out.

- **Hoogle** (Haskell). Its design note on type search
  ([docs/TypeSearch.md](https://github.com/ndmitchell/hoogle/blob/master/docs/TypeSearch.md))
  matches a query against a candidate by rewrites, each with a cost, and
  lists "**RHS only:** _[Context delete]_ `C x => y ~> y`": a constraint the
  candidate has and the query doesn't can be dropped, at a cost. So a query
  without `Monad m =>` still finds functions that need it, ranked lower. The
  note is a design document (it says `Cost` "is probably a synonym for
  `Double`"), so it describes the intent rather than guaranteeing the
  shipped behaviour. In Haskell, effects are a type constructor (`IO Int`,
  `m Int`), so a type variable in the query covers "some effect", the habit
  behind trying `_ Int`.
- **Idris 1**, `:search`
  ([type-directed search](https://hackage-content.haskell.org/package/idris-0.99/src/docs/reference/type-directed-search.rst)):
  a candidate with a constraint the query lacks is reported as more specific
  (`>`), e.g. `delete : Eq a => a -> List a -> List a`; "type class
  introduction" and "type class application" are scored moves (2 and 6, 4
  and 12), and results are sorted by score. It tries "all possible subsets
  of type class constraints", which the page calls "probably the biggest
  bottleneck".
- **Lean 4.** `exact?` and `rw?` find lemmas through discrimination trees,
  which leave instance arguments out of the index: "We ignore instance
  implicit arguments (e.g., `[Add α]`) because they are 'morally' canonical"
  ([`DiscrTree/Main.lean`](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/DiscrTree/Main.lean),
  lines 69–80). **Loogle** ([loogle.lean-lang.org](https://loogle.lean-lang.org/))
  has `_` and non-linear `?a` holes, `⊢` for conclusions, and matches a
  pattern's parameters against a lemma's hypotheses in any order; its page
  says nothing about instance arguments. Stitchwort's search took `_`, `?x`
  and `⊢` from Loogle (search.md).
- **Unison.** In the language, `A -> B` written without braces "is really
  syntactic sugar for a type `A ->{e} B`", where `e` "is some set of
  abilities, possibly empty", and `A ->{} B` is the way to say none
  ([abilities reference](https://www.unison-lang.org/docs/language-reference/abilities-and-ability-handlers/)).
  Its type search on Share
  ([blog post](https://www.unison-lang.org/blog/type-based-search/)) turns
  a signature into tokens and gives abilities "no special treatment": an
  ability is one more type mention (the post's example is
  `a -> {Exception} b`). Every token in the query must appear in a match,
  and "types with more tokens are ranked lower", so a query that leaves an
  ability out still finds functions that perform it, ranked after the ones
  that don't. `find :` in UCM takes a signature
  ([`find`](https://unison-lang.org/docs/ucm-commands/find)); the page
  documents no wildcard syntax.
- **Koka** writes rows as `<exn|e>` (abilities, then `|` and a tail
  variable, like Stitchwort's `{Fail | e}`) and has a wildcard for a row in
  an annotation: "A wildcard type is denoted by writing an identifier
  prefixed with an underscore, or even just an underscore by itself", as in
  `fun square6( x : int ) : _e int`
  ([the Koka book](https://koka-lang.github.io/koka/doc/book.html), "Effect
  types"). I found no type search tool for Koka.
- **Agda** has no library-wide type search I could find beyond editor
  commands; not relevant here.

What this says for Stitchwort: every tool lets a query leave the
candidate's effects or constraints out and still find it (Hoogle at a cost,
Idris as "more specific", Lean by ignoring them, Unison by ranking extra
tokens lower). None makes the user spell out what they don't know. Koka,
closest to Stitchwort's row syntax, spells "some row" as `_`.

## Options

### Syntax: how a pattern says "some abilities"

1. **`{_}`: any row.** `_` already means "any term" in a pattern, and the
   search already prints a row hole this way. Reads like a type: `() → {_} Int`
   is "a computation of an `Int`, performing whatever". Today's
   "expected an ability" becomes the accepted meaning.
2. **`{?e}` and `{e}`: a named row hole**, the same row at each place, as
   `?x` is the same term. Already accepted; it just has to work. Useful for
   "passes its callback's abilities through":
   `List ?a → (?a → {?e} ?b) → {?e} List ?b` finds `List.map`,
   `List.filterMap`-like functions and not ones that handle something.
3. **`{Parse _ | _}`: Parse and maybe more.** The language's own way to
   write "`Parse`, plus whatever else" is `{Parse Char | e}` (guide chapter
   8: "`{Log | e}` is '`Log`, plus whatever `e` stands for'"), so the
   pattern uses the same `|` with `_` as the tail. `{Parse _ | ?e}` names
   the rest.
4. **`{Parse _, _}`** for the same thing. Shorter, but it puts a "rest of the
   row" in a list of abilities, which no type does; a reader would take `_`
   for one unknown ability. Refuse it with a pointer to `|`.
5. **No braces meaning any row** (Unison's reading). Makes `Text → Nat`
   find `Text → {Fail} Nat` without asking. But in Stitchwort `A -> B` *is*
   pure and total (docs/syntax.md, Abilities), a pasted goal or signature
   would mean something else in a pattern than in code, and a precise
   search for a pure function couldn't be written. Better: keep it pure,
   and fall back to the open reading when the pure one finds nothing
   (Ranking, below).
6. **A flag** (`--any-abilities`). Doesn't compose (which arrow?), isn't
   visible in the pattern, and the JSON's `elaborated` would need it
   explained. No.
7. **`_ Int`** (Haskell's and Koka's habit). In Stitchwort that's a hole
   applied to `Int`, a type constructor hole, which is a different feature
   (it would also match `List Int`). Refuse it with a pointer to `{_} Int`.

### Matching: what a row hole matches

- **Rows are sets.** Abilities are compared as a set, in any order; the
  language already keeps rows sorted by declaration (docs/core.md), so this
  is about partial rows, which plain unification can't reorder.
- **`{_}` matches every row: the empty one (a pure `() → Int`), any
  abilities, and `Partial`.** A row variable in a *program* never stands for
  `Partial` (core.md), but a search hole isn't a program's row variable: it
  stands for "I don't know", and a partial function is one of the things
  you didn't know. Matt's question asks for every `() → {…} Int`.
- **`{Parse _ | _}` matches a row with at least `Parse`** (its argument
  unified with the candidate's), the rest of the row anything, `Partial`
  included. `{Parse _}` without a tail stays exact: `Parse` and nothing else,
  as a type says (today's behaviour).
- **A candidate with its own row variable** (`bindIn`'s `{row} a`,
  `List.filterMap`'s `{e} List b`): `{_}` meets it as a variable meets a
  variable. Against `{Parse _ | _}`, the candidate's variable would have to
  *become* a row with `Parse`: a match, but one where the candidate's
  variable absorbed the pattern, so it ranks with the other "absorbing"
  matches, last (search.md's rule for a conclusion `{row} a`). Today a pure
  pattern already matches an effect-polymorphic candidate at the empty row
  (`List ?a → (?a → Option ?b) → List ?b` finds `List.filterMap` first);
  that stays.
- **The filter** stops counting the row plumbing (`CompIn`, `CompD`,
  `rowOp`, `rowRes`, `Comp`, `Plus`, `NoOp`) as names the pattern requires,
  and counts the abilities a pattern writes (`Parse` in `{Parse _ | _}`)
  instead. That is the fix for the `{e}` miss.

### Ranking

Results are ranked by relation, absorption, place, then how much the
candidate took (search.md). Add one key after place: **how many abilities
the row holes took**, fewest first, with `Partial` counting as one. So for
`() → {_} Int` a pure `() → Int` comes first, then `{Parse Char}`, then
`{Parse Char, Fail}`; and `{Parse _ | _}` lists `{Parse Char}` before
`{Fail, Parse Char}`. This is Hoogle's cost per dropped context, and
Unison's "more tokens rank lower", in Stitchwort's ranking terms. An
anonymous `{_}` taking a row doesn't lower the relation (a written `_` never
does); a named `{?e}` that took abilities is a generalisation, as a named
hole that took structure is today.

**The fallback for a pure pattern.** When a pattern with no braces finds
nothing in the filtered pass, the search tries it again with `{_}` on each
arrow's result before going to the relaxed pass, and says so:

Illustrative (not run; the result list is a guess):

```
$ stitchwort search '() → Int'
 1. Std.Parse.int  definition · instance · whole
    () → {Parse Char} Int
    …
1 result, with abilities: nothing pure matched, so the results' abilities were left open, as `() → {_} Int` does
```

That keeps `Text → Nat` meaning what it says, and still answers the
question when the user didn't think of abilities. It runs only when the
filtered pass found nothing, so it costs nothing otherwise (about 2 s more
on std when it does run, like the relaxed pass).

In this fallback and in the relaxed pass, a premise or subterm of a function
type that matches only because a variable of the candidate took part of the
pattern is dropped (SW-4977): `() → {Parse t} a` is a premise of dozens of
parser lemmas and meets `() → Nat` by `a := Nat`, so it says nothing about
`Nat`. Whole and `reordered` matches stay; a query left with nothing shows
no results.

### Error messages for the spellings that fail today

| Written | Now | Proposed |
|---|---|---|
| `{_} Int` | `E-ABILITY` expected an ability | accepted: any row |
| `{Parse _ \| _} Int` | `E-PARSE` expected a row variable, but found `_` | accepted: `Parse` and maybe more |
| `{Parse _, _} Int` | `E-ABILITY` expected an ability | `E-SEARCH-PATTERN` "`_` can't be one of a row's abilities" — note: "for `Parse` and any others, write the rest after a `\|`: `{Parse _ \| _}`" |
| `_ Int` | `E-NOT-A-TYPE` this has type `_ Int` | `E-NOT-A-TYPE` as now, plus a note: "a computation's abilities go in braces before its type: `{_} Int` is an `Int` with any abilities" |
| `{_}` in a program's signature | `E-ABILITY` expected an ability | `E-ABILITY` "`{_}` (any abilities) is only for search patterns" — note: "in a signature, a row variable says 'whatever else': `{e}`, or `{Fail \| e}`" |
| `{A \| _}` in a program | `E-PARSE` | the same `E-ABILITY` message, at the `_` |

Koka allows `_e` as an inferred row in a signature; giving Stitchwort
signatures that is a separate question, not proposed here.

## Recommendation

- `{_}` is any row, empty and `Partial` included; `{?e}` and `{e}` are the
  same, named; `{Parse _ | _}` (and `| ?e`) is "at least `Parse`"; a closed
  row such as `{Parse _}` is exact. Patterns read like types, with `_` where
  a type would have a row variable.
- Rows are compared as sets; the filter ignores the row plumbing and
  requires the written abilities.
- Results rank by fewest abilities taken by the holes, after place.
- A pattern without braces stays pure, with the fallback to `{_}` on the
  results' rows when the filtered pass finds nothing.
- The refused spellings get the messages above.

## Decisions for Matt

- **A. `{_}` means any abilities in a search pattern, including none and
  `Partial`, and `{e}`/`{?e}` the same row each place.** Rec: yes.
- **B. "Parse and maybe more" is written `{Parse _ | _}`, as a type writes
  `{Parse Char | e}`; `{Parse _, _}` is refused with a pointer to it; a
  closed `{Parse _}` stays exact.** Rec: yes.
- **C. A pattern without braces stays pure (as `A → B` is in code), and when
  it finds nothing, the search retries with the results' abilities left
  open and says so, before the relaxed pass.** Rec: yes. (The alternative,
  Unison's "no braces means any", makes a pure search unwritable.)

Ranking (fewest abilities first) and the error wording are implementation
calls, recorded here for review.

## Implementation sketch

1. **Syntax** (`crates/syntax/src/ast.rs` `Row`, `parser.rs` near the "a row
   variable" error): a row's tail may be `_` (`tail: Option<RowTail>`, a
   name or a hole). `{_}` already parses (as an ability expression `_`).
   The Rust formatter prints `{A | _}` as written. The formatter-sync rule
   applies: the lane checks whether the self-hosted formatter's slices reach
   rows (not checked here) and, outside them, that it refuses the source.
2. **Elaboration** (`crates/elab/src/effects.rs`, the row elaborator around
   `ability_label`; `search.rs` `search_pattern`): in search-pattern mode (a
   flag `search_pattern` sets on the elaborator), a row `{_}`, `{e}` or
   `{A, … | _}` becomes `CompIn ?r t` with `?r` a fresh row unknown,
   recorded on the `Pattern` as a row hole with its required labels
   (`A`'s ability and argument terms) and whether it is named. Outside
   search mode, `_` in a row is the new `E-ABILITY` message. `{Parse _, _}`
   and `_ Int` get their messages here.
3. **Filter** (`search.rs`, `Pattern::constants`/`data`, `passes`,
   `overlaps`): leave the `Effect` row builtins out of a pattern's required
   names; add each required ability's operation data type to `data`.
4. **Matching** (`search.rs` `search_one`; `unify.rs` `row_rule` and
   `divergence_rule`): a search-only switch on the unifier (as
   `frozen_metas` is) lets a row hole meet a `Delay` (solving `?r` from its
   operations, noting `Partial`) and a `CompD` (the candidate's own index
   set to `Total` for the match). After a unification succeeds, each hole's
   solution is taken apart into labels (an `Ev`-level version of
   `comp_parts`/`decode`); each required label must unify with one of them,
   in any order, and the labels left over are counted. Elaboration is
   unchanged: the switch is off outside search.
5. **Ranking** (`search.rs` `Key`, `rank`): the count of abilities taken,
   after place; a candidate's own row variable that had to take a required
   ability sets `absorbs`. JSON gains `abilitiesTaken` per result.
6. **Fallback** (`crates/driver/src/search.rs`, the pass order beside the
   relaxed pass): a brace-free pattern that found nothing filtered is
   re-elaborated with `{_}` on each arrow's result and searched filtered,
   with `"searchTier": "openAbilities"` and the line above.
7. **Docs and tests:** docs/syntax.md's "Lemma search" (the `{_}`,
   `{?e}` and `{A | _}` holes, the ranking key, the fallback);
   a paragraph in guide chapter 8 ("finding a function when you don't know
   its abilities"); tests in `crates/driver/tests/library/search_match.rs`
   for each row of the error table and for `() → {_} Int` finding
   `Parse.int`, `Text → {_} Nat` finding `Text.toNatOrFail`,
   `{Parse _ | _}` finding `{Fail, Parse Char}` candidates, the ranking
   order, and the fallback.

Estimate: one Opus lane (it touches the unifier and the row elaborator),
about 90 min of agent time (estimated, not looked up from past lanes'
actuals), plus an Opus review of the unifier switch.
