# SW-1747: stage 0b of bounded read-back, every unfolded read-back site

Stage 0b of [bounded-readback.md](../proposals/bounded-readback.md) (revision 3). Read only:
nothing was built or run. Method: grep of `crates/elab/src` for `quote(` and `quote_at_most(`
(the entry points that exist are `quote`, `quote_at_most`, `quote_folded`, `quote_shown`,
`quote_unfolded_shown`; there is no `nf` or `normalise`), then the code around each hit.
**288 hits**, each in the table below, grouped by file and function. `quote_folded` and
`quote_shown` sites are not unfolded and are not listed, except that three
`differ_only_*`/`with_alike_updates_note` sites read both.

The note's and stage 0a's own classifications are reused, tagged "(note 2.x)". Sites that
are not unfolded read-backs after all are kind `-` (27 of the 288).

**Kinds** are the note's: find, mentions, zonk, shown (an error note), decide, output (a term
the elaborator writes out), same (syntactic equality of two read-backs), other.
**Stage**: 1, 4, 5, 6a, 6b as in section 7; `STAY` = deliberately left unfolded (the note
keeps `equations.rs` out of stage 1); `GAP` = no stage in the plan covers it.
**Fails**: `P` the resource error propagates (`?`) and ends the declaration; `S` swallowed
(`.ok()`, `is_ok_and`, `if let Ok`), the site then answers "no" or prints nothing; `R`
recovered into a different elaboration (the stage-7 sites); `C` a cap that makes the site
answer "may"/"not found"/folded instead of failing.

## Totals

By stage:

| Stage | Sites | Of which |
|---|---|---|
| 1 | 126 | output 115, other 9, decide 1, zonk 1 |
| 4 | 41 | mentions 29, zonk 11, other 1 |
| 5 | 28 | shown 28 |
| 6a | 18 | find 13, mentions 2, same 2, zonk 1 |
| 6b | 20 | find 12, same 7, other 1 |
| STAY | 6 | output 6 (`equations.rs`) |
| GAP | 22 | same 22 (`omega.rs` 21, `ring.rs` 1) |
| not a read-back | 27 | omega's own `Quoter::quote` 16, goals.rs (already folded) 5, tests 3, the definition of `Ctx::quote` 1, `Chars` in `rename` 1, a test-planning key 1 |

By kind: output 121, mentions 31, same 31, shown 28, find 25, zonk 13, other 13, decide 1,
not a read-back 25 (the stage `-` count is 27 because two `other` sites need no stage).
By failure: P 224, S 30, R 5, C 4, and 25 not applicable.

Stage 7 (recovered `E-RESOURCE`s): the **5 R sites** are `rewrite.rs:739` (`rewrite_once`),
`matching.rs:779` (`blocker`), `matching.rs:933` and `:936` (`generalised_now`) and
`matching/as_written.rs:658` (`unfolded`). The **4 C sites** are not errors but caps that
change the answer: `interfaces.rs:1388` (`scanned`), `matching.rs:1428` (`normals`),
`unify.rs:177` and `:978` (`KNOWN_CAP`). So stage 7 and 0c have 9 sites to list, all in
stages 4, 6a and 6b; none in stages 1 or 5.

## What the classification found

1. **Gap: `omega.rs` and `ring.rs` (22 sites, kind `same`).** Atoms are identified, and
   lemma instances de-duplicated, by `matching::same` on two unfolded read-backs
   (`omega.rs:2142`, `:2176–2189`, `:2219`, `:2313–2331`, `:2349`, `:3085`, `:3090`, `:3224`,
   `:3419–3426`; `ring.rs:930`). No stage covers them; stages 4–6 take only `mentions`,
   `find`, `zonk`, `shown`, and `cases`/`matching`'s `same`. They propagate the resource
   error, so on a large term an `omega` or `ring` proof fails with `E-RESOURCE`. The
   unifier already has the tools for an exact answer without a read-back
   (`same_closure_solved`, `same_stuck_trees`, `conv`); a stage "atom identity by
   conversion" (est. 60 min, Sonnet) would close it. Trip-journal's failures did not come
   from here (stage 0a), so it need not come before SW-1667.
2. **Stage 1 is five times what the note sized.** The note's section 2.5 lists about 25 output
   sites; the grep finds about 90 more (115 output sites in all). `effects.rs` has 31, `derive_induct.rs` 30,
   `interfaces.rs` 10, then `auto.rs`, `defaults.rs`, `partial.rs` and others. They are all
   terms handed to the kernel (generated induction principles, effect builtins' row
   arguments, instance and super-projection terms), but they change the hashes of derived
   declarations and of every effectful std definition. Suggest splitting: **1** as the note
   says (accessors, record updates, `fromYes`, `decide`, the section 2.5 sites), and **1b**
   for derive, effects and the rest, with its own snapshot review. Only stage 1 is needed
   by trip-journal.
3. **Round trips need care in stage 1.** Ten sites do `eval(quote(v))` to "read again"
   after unknowns are solved (`effects.rs:1457`, `:1581`, `:3618`; `omega.rs:3992`,
   `:4019`; `ring.rs:1279`; `families.rs:702`; `rows.rs:250`; `rewrite.rs:588`, `:1605`).
   Folded, they would give glued values rather than normal forms. The
   row ones (`effects.rs`) feed `decode`, which may expect the unfolded shape. These are
   zonk-like (stage 4) or stage 1; each needs a check, not a bulk change.
4. **`interfaces.rs` (M5).** Of its 11 sites, 10 only build the terms the search returns
   (output, stage 1); the choice itself is made by unification on values, with no read-back.
   The one that can change a choice is `scanned` (`interfaces.rs:1388`): it reads back
   unfolded up to `SCAN_LIMIT` (100,000 nodes) and **above that silently reads folded**,
   so `refresh`, `unsolved_in`, `stuck_on_found` and `find_ready_dictionaries` (its
   callers; `check.rs:1066`, `queue.rs:858`, `queue.rs:1650` too, 8 uses in all) can answer
   differently from their small-term behaviour. It is a limit that chooses, the thing
   section 4.4 forbids, and it is not an `E-RESOURCE` so stage 7 as written would not list
   it. Stage 4 should replace it with `mentions`/`unfold_where` (not a cap), and 0c should
   count how often the fallback fires.
5. **Swallowed errors that matter** (S, 30 sites): 23 are message notes (fine). Three are not:
   `check.rs:3889` (`ignorable_arguments`: gives "nothing ignorable", SW-1743),
   `rewrite.rs:707` (an unknown in a premise: failure counts as "no unknown"),
   `lib.rs:4954` (a default's dependency: failure counts as "no dependency"). All are
   stage 4 and become exact there. `check.rs:1531` and `cases.rs:1157` swallow in the
   other direction (failure is "not equal" or "skip the equation").
6. **Error paths that can replace the intended error** (kind `shown`, but P): `effects.rs:4131`
   (`escapes` builds its type text with `?`), `induct_match.rs:429` (motive error),
   `rewrite.rs:1918–1919` (a hint for `E-REWRITE-NOTHING`), `lib.rs:880` (`#eval` printing,
   where that is the answer). Stage 5 should make the first three swallow like the others.
7. **A head-shape pattern.** `equations/induct.rs:974`, `:1453`, `:1811` and
   `defaults.rs:1239` read a forced type back in full only to match its head (`Term::Data` or
   a `Pi` telescope). The value is already forced, so they need no read-back; the
   arguments become output terms. `defaults.rs:1239` is the one that could regress: a head
   whose type is a `Pi` only after unfolding gives a short telescope and `internal()`.
8. **`equations.rs` (10 sites):** 6 stay unfolded (`:2532`'s right side, `:2787`, `:2827`,
   `:2833`, `:4445–4446`), as section 11 says; `:2674` and `:5899` are plain let types
   (stage 1); `:5064`, `:5072` are `mentions_computation` (stage 4, a constant, not a
   variable: the reader's `mentions` must take constants). `equations/induct.rs` is item 7.
9. **Sites that should move earlier than their stage:** none needs to move earlier for
   trip-journal beyond stage 0a's list. `ignorable_arguments` (13 events) and `both_forms`
   (9) are already stage 4. `effects.rs:4124–4131` and `:3688–3698` are mentions (4) and
   cheap to do with `check.rs:3889`. `rewrite.rs:1918–1919` (21 of the 0a events were
   `rewrite_once`, this is next to it) is a message hint, so it can go with stage 5, not 6a.
10. **Grep noise to tell the next lane:** `goals.rs:1088–1109` call a closure named `quote`
    that is `quote_folded`; omega's `Quoter::quote` is its own recursion over atoms (16
    hits); three hits are tests; `check.rs:649` is the definition.

## Sites

Line numbers are as of `lane/SW-1747` (cut from `main` at 3748cd291).

| Site (lines) | Function | Kind | Stage | Fails | Note |
|---|---|---|---|---|---|
| `auto.rs` 352 | `from_yes` | output | 1 | P | goal in `fromYes` (note 2.5) |
| `auto.rs` 520 | `conjuncts` | output | 1 | P | both conjuncts as term arguments of `AndLeft`/`AndRight` |
| `auto.rs` 649 | `membership_facts` | output | 1 | P | membership fact arguments |
| `auto.rs` 751 | `lex_less` | output | 1 | P | operands of the comparison, then evaluated |
| `auto.rs` 788 | `decide` | decide | 1 | P | D484 (note 2.6): unfolded read-back then evaluation with gluing off |
| `bind.rs` 95 | `bind_argument` | mentions | 4 | P | does the result type mention the bound variable; `None` (no binding) if so (note 2.2) |
| `bind.rs` 99 | `bind_argument` | mentions | 4 | P | same, for the whole type (note 2.2) |
| `bind.rs` 108 | `bind_argument` | output | 1 | P | binder type of the elaborated lambda (note 2.5) |
| `bind.rs` 437 | `operand` | output | 1 | P | binder type of an operand |
| `calc.rs` 107 | `elaborate` | output | 1 | P | type of the first step |
| `cases.rs` 875 | `is_proposition` | other | 4 | P | `is_proposition`: type read back so the kernel can infer its sort; sort only needs the head |
| `cases.rs` 953 | `take_apart` | output | 1 | P | `take_apart`: scrutinee term in a generated `J` |
| `cases.rs` 978 | `take_apart` | output | 1 | P | field type in the generated motive |
| `cases.rs` 992 | `take_apart` | output | 1 | P | fact's type in a generated `let` |
| `cases.rs` 1072 | `apply_guarded` | output | 1 | P | same, `apply_guarded` |
| `cases.rs` 1157 | `new` | same | 6b | S | `Finder::new`: known equations' left sides; read-back errors skip the equation (`if let Ok`) |
| `cases.rs` 1246, 1284, 1301 | `survey_chain` | same | 6b | P | keys for seen/known sets (note 2.1) |
| `cases.rs` 1330 | `split_field` | same | 6b | P | keys for seen/known sets (note 2.1) |
| `cases.rs` 1566 | `is_known` | same | 6b | P | `is_known` (note 2.1) |
| `cases.rs` 1582 | `has_meta` | mentions | 4 | P | `has_meta` (note 2.2) |
| `check.rs` 649 | `quote` | - | - | - | the definition of `Ctx::quote`, not a site |
| `check.rs` 754 | `show_unfolded` | shown | 5 | S | `show_unfolded` (note 2.4) |
| `check.rs` 772 | `with_opaque_notes` | shown | 5 | S | opaque notes |
| `check.rs` 798 | `with_unused_equation_notes` | shown | 5 | S | unused-equation notes: haystack |
| `check.rs` 816 | `with_unused_equation_notes` | shown | 5 | S | unused-equation notes: needle |
| `check.rs` 864 | `differ_only_in_hidden` | shown | 5 | S | `differ_only_in_hidden` (also reads `quote_shown`) |
| `check.rs` 880 | `differ_only_in_proofs` | shown | 5 | S | `differ_only_in_proofs` |
| `check.rs` 894 | `first_difference_note` | shown | 5 | S | `first_difference_note` |
| `check.rs` 921 | `with_alike_updates_note` | shown | 5 | S | `with_alike_updates_note` |
| `check.rs` 1170 | `unrefined_hint` | shown | 5 | S | `unrefined_hint` |
| `check.rs` 1322, 1323, 1336 | `along_match_equation_now` | find | 6b | P | `along_match_equation_now` (note 2.1) |
| `check.rs` 1531 | `refines_to` | same | 6b | S | `is_ok_and`; a failure is "not equal" |
| `check.rs` 2395 | `inferred_comp` | output | 1 | P | row argument of an inferred computation type |
| `check.rs` 3889 | `ignorable_arguments` | mentions | 4 | S | `ignorable_arguments`: `.ok()?` gives nothing ignorable (SW-1743), 13 events in 0a |
| `check.rs` 4980 | `proof_expected` | output | 1 | P | type handed to the kernel (note 2.5) |
| `check.rs` 6967 | `same_function` | shown | 5 | S | `same_function`: `.ok()?` |
| `check.rs` 6995 | `match_equation_note` | shown | 5 | S | `match_equation_note` |
| `check.rs` 7105 | `refl_error` | shown | 5 | S | `refl_error`'s branch notes |
| `counterexample/inputs.rs` 226 | `plan` | other | - | S | a type's pretty-printed text as a plan key; read-back error means no plan |
| `counterexample/inputs.rs` 354 | `map_plan` | output | 1 | S | argument of a built test input; error gives `None` |
| `counterexample/mod.rs` 126 | `statement_part` | shown | 5 | S | `statement_part`: already capped (`STATEMENT_NODES`); too large shows `…` |
| `counterexample/mod.rs` 285 | `with_opaque_counterexample_note` | shown | 5 | S | statement for an opaque-definition note |
| `counterexample/mod.rs` 854 | `show_closed` | shown | 5 | S | prints a closed value in full first |
| `counterexample/mod.rs` 869 | `shown_value` | shown | 5 | S | `shown_value` |
| `counterexample/mod.rs` 940 | `counterexample_text` | shown | 5 | S | `in_full` |
| `defaults.rs` 534 | `construct` | output | 1 | P | argument or binder type of a helper call for defaults |
| `defaults.rs` 598 | `call` | output | 1 | P | argument or binder type of a helper call for defaults |
| `defaults.rs` 1005 | `bind_needed` | output | 1 | P | argument or binder type of a helper call for defaults |
| `defaults.rs` 1239 | `local_defaults` | other | 1 | P | only the Pi telescope of the head's type is used; a head whose type is a Pi only after unfolding would, folded, give a short telescope and an internal error |
| `derive.rs` 330 | `members` | mentions | 4 | P | does a field type mention the data type being derived |
| `derive.rs` 486 | `field_plan_for` | mentions | 4 | P | does a field type mention the data type being derived |
| `derive.rs` 594 | `field_plan_for` | mentions | 4 | P | does a field type mention a parameter |
| `derive.rs` 700 | `derive_member_helpers` | output | 1 | P | member type as body of a generated definition |
| `derive.rs` 805 | `derive_field_in` | output | 1 | P | field type in a derived default's signature |
| `derive.rs` 810 | `derive_field_in` | output | 1 | P | same |
| `derive_induct.rs` 430 | `field_type` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_induct.rs` 630 | `pred_levels` | mentions | 4 | P | which binder levels a type uses (`subterms` walk) |
| `derive_induct.rs` 819 | `define_all` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_induct.rs` 935, 948, 957 | `pred_term` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_induct.rs` 1121 | `wrap_indices_pi` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_induct.rs` 1193, 1204 | `size_of` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_induct.rs` 1254 | `find_member` | other | 1 | P | moves a value to another depth by read-back and re-evaluation; needs substitution only |
| `derive_induct.rs` 1320, 1335, 1346 | `member_pi` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_induct.rs` 1493, 1523, 1533, 1536, 1543 | `define_member_size_mem` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_induct.rs` 1752 | `define_field_size_mem` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_induct.rs` 1778 | `define_field_size_mem` | other | 1 | P | same re-indexing, via eval then quote |
| `derive_induct.rs` 1787 | `define_field_size_mem` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_induct.rs` 2045 | `motive_type` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_induct.rs` 2125, 2149 | `case_type` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_induct.rs` 2188, 2196, 2202, 2212 | `mem_hypothesis` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_induct.rs` 2237 | `proof_of` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_induct.rs` 2474, 2485 | `case_adapter` | output | 1 | P | generated induction lemma type: a ctor field or index type read back under the data's own binders |
| `derive_show.rs` 241 | `show_plan` | mentions | 4 | P | does a field type mention a parameter |
| `effects.rs` 185 | `call` | output | 1 | P | row or type argument of an effect builtin (`LiftD`, `BindIn`, ...): kernel-checked, never compared syntactically |
| `effects.rs` 619 | `same_results` | mentions | 4 | P | any unknown in a row's value? (`Term::Meta` among subterms) |
| `effects.rs` 1124, 1138, 1177 | `lift` | output | 1 | P | row or type argument of an effect builtin (`LiftD`, `BindIn`, ...): kernel-checked, never compared syntactically |
| `effects.rs` 1298, 1325, 1360 | `lift_plain` | output | 1 | P | row or type argument of an effect builtin (`LiftD`, `BindIn`, ...): kernel-checked, never compared syntactically |
| `effects.rs` 1398 | `widen` | output | 1 | P | row or type argument of an effect builtin (`LiftD`, `BindIn`, ...): kernel-checked, never compared syntactically |
| `effects.rs` 1431, 1436 | `bind_term` | output | 1 | P | row or type argument of an effect builtin (`LiftD`, `BindIn`, ...): kernel-checked, never compared syntactically |
| `effects.rs` 1457 | `refresh` | other | 1 | P | `eval(quote(ops))` round trip so `decode` sees the row; a folded read-back leaves glued calls for `decode` (check it copes) |
| `effects.rs` 1581 | `settle_let_lambda` | other | 1 | P | `eval(quote(ty))` round trip after settling rows; same caution as 1457 |
| `effects.rs` 1834 | `effect_type` | output | 1 | P | row or type argument of an effect builtin (`LiftD`, `BindIn`, ...): kernel-checked, never compared syntactically |
| `effects.rs` 2584, 2593, 2607 | `done` | output | 1 | P | row or type argument of an effect builtin (`LiftD`, `BindIn`, ...): kernel-checked, never compared syntactically |
| `effects.rs` 3618 | `comp_app` | other | 1 | P | `eval(quote(ty))` round trip after settling rows; same caution |
| `effects.rs` 3688, 3698 | `row_in_result` | mentions | 4 | P | does a row's tail or the result mention an unknown (`row_in_result`) |
| `effects.rs` 3975 | `unsettled` | zonk | 4 | P | `unsettled`: read back, zonked, any unsolved unknown? |
| `effects.rs` 3999 | `written_outside` | mentions | 4 | P | does the value mention an inner binder (`written_outside`) |
| `effects.rs` 4124 | `escapes` | mentions | 4 | P | does the type mention one of the escaping handler variables |
| `effects.rs` 4131 | `escapes` | shown | 5 | P | type text for the escape error; read back with `?`, so a resource error replaces the intended error |
| `effects.rs` 4529, 4541, 4552 | `make_call` | output | 1 | P | row or type argument of an effect builtin (`LiftD`, `BindIn`, ...): kernel-checked, never compared syntactically |
| `effects.rs` 4591, 4597 | `op_value` | output | 1 | P | row or type argument of an effect builtin (`LiftD`, `BindIn`, ...): kernel-checked, never compared syntactically |
| `effects.rs` 4856, 4858, 4892, 4927, 4961, 4976, 4998, 5053, 5068 | `handle` | output | 1 | P | row or type argument of an effect builtin (`LiftD`, `BindIn`, ...): kernel-checked, never compared syntactically |
| `effects.rs` 5099 | `partial_mismatch` | mentions | 4 | P | does a found or expected type mention data type `req`: a constant, not a variable (reader's `mentions` must take constants) |
| `equations.rs` 2532 | `bool_equation` | output | STAY | P | right side of a Bool equation, deliberately unfolded (left is folded); `bool_test` then checks its shape |
| `equations.rs` 2674 | `probe_row_in` | output | 1 | P | let type for a special binder in a probe context |
| `equations.rs` 2787 | `probe_row_in` | output | STAY | P | left-hand argument of the probe's generated equation |
| `equations.rs` 2827 | `probe_row_in` | output | STAY | P | same, after the refl substitution |
| `equations.rs` 2833 | `probe_row_in` | output | STAY | P | binder types of the generated equation (note section 11): `rewrite f.eq_k` proofs may depend on them |
| `equations.rs` 4445, 4446 | `uniqueness` | output | STAY | P | sides of a Bool uniqueness lemma |
| `equations.rs` 5064, 5072 | `performs_abilities` | mentions | 4 | P | `mentions_computation`: does the unfolded type mention a `Computation` data type |
| `equations.rs` 5899 | `recompute_leaves` | output | 1 | P | same, in the recompute path |
| `equations/induct.rs` 974 | `induct_split` | other | 1 | P | head shape only (`Term::Data` match after `force`); the value already has the head |
| `equations/induct.rs` 1453 | `leaves` | other | 1 | P | head shape only, as above |
| `equations/induct.rs` 1811 | `refute` | other | 1 | P | head shape only, as above |
| `families.rs` 223 | `ctor_result` | output | 1 | P | index arguments of a family constructor's result, as terms |
| `families.rs` 702 | `enter` | zonk | 4 | P | `solved`: `eval(quote(v))` substitutes solved unknowns |
| `goals.rs` 1088, 1090, 1100, 1104, 1109 | `goal_snapshot_of` | - | - | - | already folded (`quote_folded` closure named `quote`): not an unfolded site |
| `goals.rs` 1180, 1184 | `enter_snapshot` | output | 1 | P | `enter_snapshot` defines the goal's variables: type and value |
| `induct_match.rs` 172 | `check_induct` | find | 6b | P | `call_normal`: the call's normal form looked for in the goal (a needle) |
| `induct_match.rs` 320, 322 | `check_induct` | find | 6b | P | the goal and every variable's type, searched for the call's normal form |
| `induct_match.rs` 429 | `check_induct` | shown | 5 | P | the current type for the motive error; read back with `?` |
| `interfaces.rs` 660 | `check_supers` | output | 1 | P | argument of a term the instance search builds |
| `interfaces.rs` 1051 | `attempt` | output | 1 | P | argument of a term the instance search builds |
| `interfaces.rs` 1291 | `locals` | output | 1 | P | argument of a term the instance search builds |
| `interfaces.rs` 1388 | `scanned` | mentions | 4 | C | `scanned`: unfolded up to SCAN_LIMIT (100,000) nodes, then silently read folded: the one limit in instance search that chooses (M5). Callers: check.rs:1066, interfaces.rs:1398, 1405, 1683, 1716, queue.rs:858, 1650 |
| `interfaces.rs` 1550 | `decide_eq` | output | 1 | P | argument of a term the instance search builds |
| `interfaces.rs` 1575, 1582 | `decide_eq_of` | output | 1 | P | argument of a term the instance search builds |
| `interfaces.rs` 1795, 1800 | `method_call` | output | 1 | P | argument of a term the instance search builds |
| `interfaces.rs` 1901 | `projected` | output | 1 | P | argument of a term the instance search builds |
| `interfaces.rs` 1935 | `relation_decider` | output | 1 | P | argument of a term the instance search builds |
| `lib.rs` 880 | `eval_expr` | shown | 5 | P | `eval_expr` prints the value and its type in full (`#eval`-style); a resource error is the result |
| `lib.rs` 956 | `check_proof_glued` | output | 1 | P | checked input's type (note 2.5) |
| `lib.rs` 1036 | `check_proof_at_glued` | output | 1 | P | checked input's type (note 2.5) |
| `lib.rs` 1080 | `infer_expr_glued` | output | 1 | P | checked input's type (note 2.5) |
| `lib.rs` 1375 | `test` | output | 1 | P | checked input's type (note 2.5) |
| `lib.rs` 4954 | `check_tree` | mentions | 4 | S | `is_ok_and`: failure means no dependency (`false`) |
| `matching.rs` 434 | `unit_parameter` | mentions | 4 | P | note 2.2 |
| `matching.rs` 512 | `lifted` | find | 6b | P | note 2.1 (normal forms of hypotheses) |
| `matching.rs` 521 | `lifted` | output | 1 | P | scrutinee type in the motive (note 2.5) |
| `matching.rs` 657 | `generalised_named` | output | 1 | P | note 2.5 |
| `matching.rs` 779 | `blocker` | find | 6b | R | `blocker`: on a recoverable `E-RESOURCE` reads folded and passes the error on in `too_large`; the match then fails later or goes as written (stage 7) |
| `matching.rs` 851 | `resume` | output | 1 | P | scrutinee type, re-read after generalisation (note 2.5); the line before reads it folded |
| `matching.rs` 933, 936 | `generalised_now` | find | 6b | R | `generalised_now`; a recoverable `E-RESOURCE` goes to `unconfirmed_now` (stage 7) |
| `matching.rs` 1428 | `normals` | find | 6b | C | `normals`: capped at the largest target (`quote_at_most`); `None` means not found there |
| `matching.rs` 1687 | `check_motive` | other | 6b | P | `check_motive`: motive read back for the lifted-type check |
| `matching.rs` 1778 | `unknown_left_for_lifting` | mentions | 4 | P | `unknown_left_for_lifting` = `first_meta` (note 2.2) |
| `matching/as_written.rs` 658 | `unfolded` | find | 6b | R | `unfolded`; recoverable error becomes `Unfolded::TooLarge` (as_written.rs:305) |
| `named.rs` 726, 727 | `bind_missing` | output | 1 | P | binder type of an elaborated lambda (note 2.5) |
| `named.rs` 895 | `dependencies` | mentions | 4 | P | `dependencies`: which earlier binders a type mentions |
| `numbers.rs` 1449 | `equation` | output | 1 | P | type of a generated equation |
| `omega.rs` 1965, 1991, 1998, 2002, 2011, 2034, 2035, 2045, 2058 | `quote` | - | - | - | not a read-back: omega's own `Quoter::quote` recursion over atoms |
| `omega.rs` 2084, 2128, 2129 | `quote_int` | - | - | - | not a read-back: `Quoter::quote` recursion |
| `omega.rs` 2138, 2139, 2142, 2143 | `quote_int` | same | GAP | P | `matching::same` on two unfolded terms: atom identity or a syntactic recheck |
| `omega.rs` 2176, 2177, 2189 | `sub_nat_nat` | same | GAP | P | `matching::same` on two unfolded terms: atom identity or a syntactic recheck |
| `omega.rs` 2219 | `division` | same | GAP | P | `matching::same` on two unfolded terms: atom identity or a syntactic recheck |
| `omega.rs` 2279, 2280, 2281 | `operation` | same | GAP | P | `matching::same` on two unfolded terms: atom identity or a syntactic recheck |
| `omega.rs` 2313, 2320, 2331 | `mul_left` | same | GAP | P | `matching::same` on two unfolded terms: atom identity or a syntactic recheck |
| `omega.rs` 2349 | `atom` | same | GAP | P | `matching::same` on two unfolded terms: atom identity or a syntactic recheck |
| `omega.rs` 2414, 2417 | `recomputed` | zonk | 4 | P | `recomputed`: read back and evaluated again, then `same` on the result; folded would be enough for the first, the second is a `same` test |
| `omega.rs` 2728, 2731 | `quote_fact` | - | - | - | not a read-back: `Quoter::quote` recursion |
| `omega.rs` 3085, 3090 | `nat_abs_dichotomies` | same | GAP | P | `matching::same` on two unfolded terms: atom identity or a syntactic recheck |
| `omega.rs` 3132, 3135 | `linear_once` | - | - | - | not a read-back: `Quoter::quote` recursion |
| `omega.rs` 3224, 3227 | `linear_once` | same | GAP | P | `matching::same` on two unfolded terms: atom identity or a syntactic recheck |
| `omega.rs` 3419, 3426 | `division_facts` | same | GAP | P | `matching::same` on two unfolded terms: atom identity or a syntactic recheck |
| `omega.rs` 3992 | `emit` | zonk | 4 | P | `eval(quote(prop))` fallback when `prop` is stuck on an unknown solved since |
| `omega.rs` 4019 | `emit` | zonk | 4 | P | same fallback for the goal |
| `partial.rs` 647, 656 | `split_signature` | output | 1 | P | type or row argument of a generated `Delay`/`Partial` term |
| `partial.rs` 783 | `shared_row` | output | 1 | P | shared row of a `Delay` |
| `pipe.rs` 125 | `lambda` | output | 1 | P | annotation |
| `queue.rs` 506 | `queue_item` | mentions | 4 | P | does the literal's type mention a context variable |
| `queue.rs` 1100 | `blockers` | mentions | 4 | P | `Comparison::blockers`: pending unknowns among a pair's sides (stage 0a: 1 event) |
| `queue.rs` 2365 | `a_filled_placeholder_zonks_to_the_items_term` | - | - | - | test code |
| `queue.rs` 2487 | `a_waiting_comparison_computes_its_sides_again` | - | - | - | test code |
| `records.rs` 1448, 1470 | `update` | output | 1 | P | record update annotation (note 2.5) |
| `records.rs` 1543 | `update_fields` | output | 1 | P | record update annotation (note 2.5) |
| `reify.rs` 85 | `return_display` | shown | 5 | S | `return_display`: unfolded computation shown beside the folded goal; `.ok()?` |
| `rewrite.rs` 588 | `discharge` | zonk | 4 | P | `discharge`: premise type read again so matching's solutions are in it |
| `rewrite.rs` 707 | `unproved_premise` | mentions | 4 | S | `is_ok_and`: failure counts as not unknown (note 2.2) |
| `rewrite.rs` 739 | `rewrite_once` | find | 6a | R | `rewrite_once` falls to `unconfirmed` on a recoverable error (stage 7) |
| `rewrite.rs` 756 | `rewrite_once` | find | 6a | P | re-read after `prove_now` |
| `rewrite.rs` 760 | `rewrite_once` | find | 6a | P | left side |
| `rewrite.rs` 805 | `rewrite_once` | find | 6a | P | goal after each step |
| `rewrite.rs` 986 | `replaced_by_match` | shown | 5 | S | `replaced_by_match`: `else return error`; compares with scrutinee needles for a hint |
| `rewrite.rs` 1095 | `replace_occurrences_as` | find | 6a | P | left side's key; folded flag chooses `quote_folded` |
| `rewrite.rs` 1191 | `replace_occurrences_as` | same | 6a | P | two read-backs compared with `same`, folded and unfolded |
| `rewrite.rs` 1225 | `replace_solving_instances` | mentions | 6a | P | `equation.open(&lhs)` |
| `rewrite.rs` 1435 | `decide` | find | 6a | P | as 1095 |
| `rewrite.rs` 1501 | `has_carrier` | mentions | 4 | P | `has_carrier`: carrier mentions an unknown |
| `rewrite.rs` 1605 | `check_motive` | zonk | 1 | P | `eval(quote(v))` for the kernel's inference (note 2.5) |
| `rewrite.rs` 1690 | `round_trip_awaiting_helpers` | mentions | 4 | P | `mentions_draft` (note 2.2) |
| `rewrite.rs` 1759 | `shown_computed` | shown | 5 | S | `shown_computed`: failure prints `…` |
| `rewrite.rs` 1918, 1919 | `other_direction_rewrites` | shown | 5 | P | `other_direction_rewrites`: only feeds a hint on the E-REWRITE-NOTHING path, yet propagates, so a resource error replaces the intended error (move to the swallowing form) |
| `rewrite.rs` 2101 | `nothing_found` | shown | 5 | S | opaque notes |
| `rewrite.rs` 2113 | `hypothesis_holding` | shown | 5 | S | `hypothesis_holding` |
| `rewrite.rs` 2127 | `hypothesis_holding` | shown | 5 | S | `hypothesis_holding`, every variable's type |
| `rewrite/as_written.rs` 288 | `search` | mentions | 6a | P | `equation.open(&lhs_term)`: does the left side still hold an unknown |
| `rewrite/as_written.rs` 351 | `search` | same | 6a | P | today's instance compared with the left side |
| `rewrite/as_written.rs` 415, 416 | `hidden_copy_in` | find | 6a | P | hidden_copy_in (note 2.1) |
| `rewrite/as_written.rs` 471 | `todays_instance` | find | 6a | P | todays_instance (note 2.1) |
| `rewrite/under.rs` 353 | `by_lemma` | zonk | 6a | P | arguments read as the call determined them; then checked for unknowns |
| `rewrite/under.rs` 546 | `rewrite_body` | find | 6a | P | left side's key |
| `rewrite/under.rs` 557, 558 | `rewrite_body` | find | 6a | P | type and body for the search under a binder |
| `rewrite/under.rs` 578 | `rewrite_body` | find | 6a | P | each step's result |
| `rewrite/under.rs` 650 | `rewrite_body` | output | 1 | P | the result term of the rewrite under a binder: handed on as the new goal |
| `ring.rs` 329 | `flipped` | output | 1 | P | argument of the flip lemma's proof |
| `ring.rs` 361 | `scaled` | output | 1 | P | arguments of the scaling lemma, also evaluated |
| `ring.rs` 930 | `atom` | same | GAP | P | atom identity |
| `ring.rs` 1279 | `emit` | zonk | 4 | P | `eval(quote(expected))` fallback, as omega.rs:3992 |
| `rows.rs` 250 | `refresh_at` | zonk | 4 | P | `refresh_at`: `eval(quote(v))`, the same round trip |
| `shared.rs` 246 | `accessors` | output | 1 | P | record accessor or update type (note 2.5) |
| `shared.rs` 600, 633 | `update_match` | output | 1 | P | record accessor or update type (note 2.5) |
| `shared.rs` 644 | `update_match` | output | 1 | P | annotation of a record update's field |
| `unify.rs` 177 | `on_pending` | mentions | 4 | C | `on_pending` (note 2.2): too large counts as may |
| `unify.rs` 978 | `mentions_unknown` | mentions | 4 | C | `mentions_unknown` (note 2.2): too large counts as may |
| `unify.rs` 2226 | `rename` | other | - | P | `rename` reads a `Chars` literal back: closed, small, no calls |
| `unify.rs` 2597 | `both_forms` | zonk | 4 | P | `both_forms` (note 2.3) |
| `unify.rs` 2779 | `zonk_changed` | zonk | 4 | P | `zonk_changed` whole-solution fallback (note 2.3) |
| `unify.rs` 3864 | `quoted` | - | - | - | test code |
