# SW-2822 review: the assumptions follow-ups (F3-F6, F8, docs)

**Reviewed:** commit `4cde24659` ("Kernel: assumptions' follow-ups from the
Fable review (SW-2822)"), against the findings of
[SW-2804-assumptions-review.md](SW-2804-assumptions-review.md).
**Reviewer:** Fable, 11 November 2026 (D3473). **Method:** paper review
only. Nothing was built or run; the new tests were read, not executed. Line
numbers are `main`'s at `d5788f7f6`.

## Verdict

**Every fix closes its finding, and the change breaks nothing I can find.
No must-fix.** Four low notes follow the table: one more entry point closed
"by accident" that the doc's list leaves out (N1), and three wording points
in `docs/core.md` (N2-N4).

| Finding | Fix | Verdict |
|---|---|---|
| F3 | `assume` refuses a label an assumption already has | SOUND |
| F4 | `relied_on` follows `Nat`, `NumCase`, `Chars` | SOUND (untested, N5) |
| F5 | `add_validator` refuses an assumption | SOUND |
| F6 | `float::register_def` refuses an assumption | SOUND |
| F8 | `relied_on` takes data types as roots | SOUND |
| Docs | `docs/core.md` "Assumptions (open goals)" | Accurate; N1-N4 are small gaps |

## F3: one label, one assumption. SOUND

`check.rs:2424-2436`. I checked the three ways the check could leak:

- **A rewind can't bypass it.** The check keeps no table of its own: it
  scans `g.env.defs()`, and `Env::truncate` (`env.rs:139-143`) removes the
  definitions themselves on `forget_since` and `rewind`. So a label is held
  exactly while its assumption exists, and a rewound one is free again,
  which is right (the constant is gone, and its hash-cache entry with it,
  `globals.rs:827`).
- **Equality is the hashed identity.** `Assumption` is `owner` and `hole`
  only (`globals.rs:138-147`), compared by derived `PartialEq`; the span is
  on the `Def`, not in the label. The hasher writes the same two fields
  (`hash.rs:178-179`). So "same label" in the check is "same label" in the
  hash.
- **No side effect before it.** It runs before `admissible`, `check_type`
  and `push_def` (`check.rs:2437-2447`), and `push_def` is the only write.
  `assume` is the only place `Def::assumption` is set (`check.rs:2448`;
  `push_def` sets `None`, `check.rs:2377`), so no assumption can exist that
  the scan doesn't see.

Refusing the label whatever the type is stricter than the hash needs, and
is the right rule: it leaves nothing to the type's comparison.

The scan is linear in the kernel's definitions per `assume`. That is fine
for the handful of `?`s a file has; if stage 2 ever makes thousands in one
kernel, a set of labels kept by `Env` and truncated with it would do.

For stage 2: the refusal reaches the user as `E-MALFORMED`, so the
elaborator's owners must be distinct per kernel for every declaration that
can hold a `?`, including the ones without a name of their own (lifted
helpers, anonymous instances, `example`-like blocks, a declaration checked
again by the language server after a partial rewind).

## F4: the literal edges. SOUND

`assumption.rs:84-94` follows `Term::Nat` and `Term::NumCase` to
`builtins.nat`, and `Term::Chars` to `text.list` and `text.char`. That is
the hasher's list exactly: its only references are `def_ref` at
`hash.rs:708` and `data_ref` at `711`, `719`, `736` (Nat), `751-752`
(Chars), `786`, `809` (NumCase) and `831`. No other term form refers to a
declaration implicitly (`Eq`, `J`, `Refl` and `Quot` are built in; a float
or a char is an explicit `Ctor`; `Bool` is reached through the types of the
natives that return it).

Where a builtin isn't bound the walk skips the edge, where the hasher
panics. That is right: such a literal can't have been checked.

## F5: `add_validator`. SOUND

`check.rs:4339-4343`. The refusal comes after the `Final` check and before
anything is written; the only write is the push at `check.rs:4362-4364`.
`telescope` runs before it (`check.rs:4330`) and can fail first with
another message, but it writes nothing. `add_field_validator` is on data
types, so it has no assumption case.

## F6: `float::register_def`. SOUND

`float.rs:677-681`, before the `Float` and pin checks and before the insert
at `float.rs:693-696`. For a builtin outside `PINNED_DEFS` the function
returns `Ok(())` earlier (`float.rs:673-675`) without binding anything, so
an assumption passed with such a builtin isn't refused but nothing happens
to it either (N2).

## F8: data types as roots. SOUND

`relied_on` takes `&[Decl]` (`assumption.rs:43`), and a `Decl::Data` root
goes through the arm data types reached from terms already used
(`assumption.rs:65-74`). Nothing outside `crates/core/tests` calls
`relied_on`, so the signature change breaks no caller.

## `docs/core.md`

I checked each new sentence against the code; all hold. In particular: the
duplicate rule and its example; `retype_def` and both `define_primitive`s
take pending definitions only; the literal edges and why they're
unreachable (`native.rs:389-405` for `Nat`'s shape, the pins for `List`,
`Char` and natives); the capture's structural refusal
(`crates/elab/src/cache/mod.rs:1468-1470`) against the bookkeeping half
(`unfinished_count`, `cache/mod.rs:689-704`); the panic at an impossible
branch (`value.rs:2308-2313`); the runtimes' up-front refusal
(`crates/rt/src/lower.rs:123-131`). The `sealed` and `branch` comments in
`value.rs` and the paragraph in `erase.rs` match what the code does.

Small gaps:

- **N1. `nat_add::register` is missing from the list, and is closed by
  accident, as F6 was.** It takes a `DefId` (`nat_add.rs:237`) and switches
  on the rules for `+` if that definition and `Nat.addZero` are final
  theorems of the right types (`nat_add.rs:285-288`). An assumption with
  `Nat.addSucc`'s type is refused only because `assume` passes
  `theorem = false`. No harm either way: the module's own argument is that
  the rules are sound for the pinned `Nat.add` whoever proves the theorems
  (`nat_add.rs:57-62`), and it gives the assumption no body. But the doc's
  claim is a complete list, and this entry point isn't in it. Suggest the
  one-line explicit refusal and a mention in the doc. Related, and also
  harmless for the same reason: a `Nat.addSucc` that is a real theorem
  *relying on* an assumption passes, and the rules it switches on are an
  edge `relied_on` can't see.
- **N2.** "`register_native` and `float::register_def` refuse it" is true
  of `float::register_def` only for pinned builtins (F6 above). Not worth
  more than a clause, or move the check above the early return.
- **N3.** "each would be refused by its pinned hash and arity as well" fits
  the float path. `register_native`'s other check is the type
  (`register_shaped`, `native.rs:444-`), not the arity; only the pin
  refuses an assumption there.
- **N4.** In "Why it's sound", "So the term is well typed in the context
  extended by variables" now follows the new sentences about running
  programs, so its "So" reads as following from them. It follows from the
  rule-by-rule comparison before "The differences are two". Move the
  differences after it, or start a new paragraph.

## Tests

- **N5.** F4 has no test, because the edges are unreachable through the
  checked entry points. `Env::set_text_unchecked_for_tests` (`env.rs:117`)
  would let a test bind a `Char` whose field's type mentions an assumption
  and assert that a `Term::Chars` user relies on it. Optional.
- The others read right: `a_label_is_used_once` covers same type, another
  type, "nothing is added", and the two paired positives; the
  `add_validator` refusal is told apart from the shape refusal by its
  message; the validator, run-body, `unfolding` and data-root cases each
  assert the empty set before the edge exists.

## What I didn't check

- Nothing was run.
- Whether any caller of `assume` exists outside the tests: there is none
  on `main` (stage 2 isn't merged), so the new refusal can't fire today.
- The runtimes' behaviour under a false goal (the earlier review's F1) and
  the `Final` readers (F2): both are stage 2 and 3 work, untouched here,
  and the doc now states them.
