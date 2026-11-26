//! A static check for self-recursive functions with no stack guard:
//! docs/proposals/deep-input.md §6.2, SW-1966.
//!
//! It reads the source as text, not as a parser. A function's body is found by
//! brace matching, and a call is any occurrence of `name(` (also `.name(` or
//! `Self::name(`), so a same-named method or field is a false positive and
//! mutual recursion (`a` calling `b` calling `a`) is missed. Braces or calls
//! inside strings and comments do not count, while braces in a macro body are
//! read as ordinary braces; a guard anywhere in the body, even in a nested
//! function, counts for the outer one. A `// Depth:` comment in the function
//! or immediately above it (past attributes) states a bound instead of a guard.
//!
//! The allowlist below is to shrink: remove an entry when its function gains
//! a guard or a `// Depth:` reason.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

/// The crates SW-1966 scans: the proposal's findings are in these. Test
/// sources are not scanned.
const CRATES: &[&str] = &["syntax", "elab", "core", "driver"];

/// A guard is a call of one of these, or a `// Depth:` comment.
const GUARDS: &[&str] = &["nesting(", "deeper()", "exceeded()", "stack_exhausted()"];

/// This list only shrinks: remove an entry when its function gains a guard or a `// Depth:` reason.
const ALLOWED: &[&str] = &[
    "crates/core/src/backend.rs:defaults",
    "crates/core/src/backend.rs:js",
    "crates/core/src/check.rs:conv",
    "crates/core/src/check.rs:ctor",
    "crates/core/src/check.rs:error",
    "crates/core/src/check.rs:eval",
    "crates/core/src/check.rs:new",
    "crates/core/src/check.rs:prop_mark",
    "crates/core/src/check.rs:quote",
    "crates/core/src/check.rs:stored_only",
    "crates/core/src/check.rs:substitute",
    "crates/core/src/check.rs:why_not_nestable",
    "crates/core/src/env.rs:rewind",
    "crates/core/src/env.rs:truncate",
    "crates/core/src/ev.rs:data",
    "crates/core/src/ev.rs:def",
    "crates/core/src/float.rs:js_to_string",
    "crates/core/src/float.rs:name",
    "crates/core/src/globals.rs:data",
    "crates/core/src/globals.rs:def",
    "crates/core/src/globals.rs:mark",
    "crates/core/src/hash.rs:new",
    "crates/core/src/machine.rs:insert",
    "crates/core/src/machine.rs:is_empty",
    "crates/core/src/machine.rs:len",
    "crates/core/src/machine.rs:reset",
    "crates/core/src/nat_add.rs:contains",
    "crates/core/src/native.rs:name",
    "crates/core/src/partial.rs:term",
    "crates/core/src/pins.rs:hex",
    "crates/core/src/pretty.rs:defaulted",
    "crates/core/src/pretty.rs:go",
    "crates/core/src/pretty.rs:list_pieces",
    "crates/core/src/pretty.rs:map_tree_entries",
    "crates/core/src/pretty.rs:new",
    "crates/core/src/pretty.rs:placeholder",
    "crates/core/src/pretty.rs:size",
    "crates/core/src/pretty.rs:within",
    "crates/core/src/reference.rs:compact_or_lazy",
    "crates/core/src/reference.rs:conv_in",
    "crates/core/src/reference.rs:eval",
    "crates/core/src/reference.rs:eval_tree",
    "crates/core/src/reference.rs:expand_term",
    "crates/core/src/reference.rs:folds_mul",
    "crates/core/src/reference.rs:force",
    "crates/core/src/reference.rs:number_view",
    "crates/core/src/reference.rs:quote",
    "crates/core/src/reference.rs:same_trees",
    "crates/core/src/reference.rs:type_at",
    "crates/core/src/reference.rs:unfold",
    "crates/core/src/reference.rs:unfold_folded",
    "crates/core/src/reference.rs:validate_pi_marks",
    "crates/core/src/registry.rs:install_library",
    "crates/core/src/sct.rs:new",
    "crates/core/src/termination.rs:rebuilt",
    "crates/core/src/value.rs:bound_fields",
    "crates/core/src/value.rs:branch",
    "crates/core/src/value.rs:default",
    "crates/core/src/value.rs:drop",
    "crates/core/src/value.rs:field_type",
    "crates/core/src/value.rs:get",
    "crates/core/src/value.rs:hash",
    "crates/core/src/value.rs:into_iter",
    "crates/core/src/value.rs:into_vec",
    "crates/core/src/value.rs:matches_at_once",
    "crates/core/src/value.rs:new",
    "crates/core/src/value.rs:ptr_eq",
    "crates/core/src/value.rs:push",
    "crates/core/src/value.rs:quick",
    "crates/core/src/value.rs:resume",
    "crates/core/src/value.rs:stuck_on_variable",
    "crates/core/src/value.rs:take",
    "crates/core/src/value.rs:unfold_folded",
    "crates/core/src/value.rs:unfold_once",
    "crates/core/src/value.rs:visit",
    "crates/driver/src/axioms.rs:axioms",
    "crates/driver/src/axioms.rs:new",
    "crates/driver/src/check_cache.rs:abandon",
    "crates/driver/src/check_cache.rs:clear",
    "crates/driver/src/check_cache.rs:compiler",
    "crates/driver/src/check_cache.rs:default",
    "crates/driver/src/check_cache.rs:is_empty",
    "crates/driver/src/check_cache.rs:kernel",
    "crates/driver/src/check_cache.rs:len",
    "crates/driver/src/check_cache.rs:new",
    "crates/driver/src/check_cache.rs:read",
    "crates/driver/src/check_cache.rs:read_others",
    "crates/driver/src/check_cache.rs:remove",
    "crates/driver/src/check_cache.rs:salt",
    "crates/driver/src/check_cache.rs:write",
    "crates/driver/src/counterexample.rs:tree",
    "crates/driver/src/declhash.rs:is_empty",
    "crates/driver/src/doc.rs:new",
    "crates/driver/src/driver.rs:for_stack",
    "crates/driver/src/driver.rs:with_stack",
    "crates/driver/src/fingerprint.rs:collect",
    "crates/driver/src/live.rs:new",
    "crates/driver/src/live.rs:step",
    "crates/driver/src/live.rs:take",
    "crates/driver/src/live/trial.rs:is_empty",
    "crates/driver/src/palette.rs:set",
    "crates/driver/src/parallel.rs:abandon",
    "crates/driver/src/parallel.rs:compiler",
    "crates/driver/src/parallel.rs:kernel",
    "crates/driver/src/parallel.rs:new",
    "crates/driver/src/parallel.rs:read",
    "crates/driver/src/parallel.rs:read_others",
    "crates/driver/src/parallel.rs:salt",
    "crates/driver/src/parallel.rs:write",
    "crates/driver/src/project.rs:config",
    "crates/driver/src/project.rs:entries",
    "crates/driver/src/project.rs:include_files",
    "crates/driver/src/project.rs:is_file",
    "crates/driver/src/project.rs:new",
    "crates/driver/src/project.rs:read",
    "crates/driver/src/project.rs:read_all",
    "crates/driver/src/project.rs:walk",
    "crates/driver/src/reliance.rs:is_empty",
    "crates/driver/src/rewind.rs:cancel_flag",
    "crates/driver/src/rewind.rs:mark",
    "crates/driver/src/rewind.rs:mark_fresh",
    "crates/driver/src/rewind.rs:release",
    "crates/driver/src/rewind.rs:rewind",
    "crates/driver/src/rewind.rs:rewind_fresh",
    "crates/driver/src/search.rs:ambiguities",
    "crates/driver/src/search.rs:append_chain",
    "crates/driver/src/search.rs:default",
    "crates/driver/src/search.rs:numeric_group",
    "crates/driver/src/search.rs:search",
    "crates/driver/src/search_at.rs:compiler",
    "crates/driver/src/search_at.rs:config",
    "crates/driver/src/search_at.rs:entries",
    "crates/driver/src/search_at.rs:include_files",
    "crates/driver/src/search_at.rs:kernel",
    "crates/driver/src/search_at.rs:read",
    "crates/driver/src/search_at.rs:read_others",
    "crates/driver/src/search_at.rs:salt",
    "crates/driver/src/search_at.rs:write",
    "crates/elab/src/arm_display.rs:same",
    "crates/elab/src/arm_display.rs:set",
    "crates/elab/src/arm_display.rs:set_facts",
    "crates/elab/src/arm_display.rs:tally",
    "crates/elab/src/auto.rs:prove",
    "crates/elab/src/auto.rs:size",
    "crates/elab/src/auto.rs:take_apart",
    "crates/elab/src/autobind.rs:pattern_vars",
    "crates/elab/src/bind.rs:build",
    "crates/elab/src/bind.rs:shape",
    "crates/elab/src/build.rs:is_empty",
    "crates/elab/src/cache/dump.rs:dump",
    "crates/elab/src/cache/dump.rs:dump_probe",
    "crates/elab/src/cache/mod.rs:commit",
    "crates/elab/src/cache/mod.rs:count",
    "crates/elab/src/cache/mod.rs:data",
    "crates/elab/src/cache/mod.rs:def",
    "crates/elab/src/cache/mod.rs:holds_unproved_theorems",
    "crates/elab/src/cache/mod.rs:is_empty",
    "crates/elab/src/cache/mod.rs:probe",
    "crates/elab/src/cache/mod.rs:span",
    "crates/elab/src/cache/mod.rs:span_after",
    "crates/elab/src/cache/mod.rs:term",
    "crates/elab/src/cache/rows.rs:decode",
    "crates/elab/src/cache/rows.rs:encode",
    "crates/elab/src/carry.rs:new",
    "crates/elab/src/cases.rs:by_parts_at",
    "crates/elab/src/cases.rs:case_value",
    "crates/elab/src/cases.rs:ctor_vars",
    "crates/elab/src/cases.rs:find",
    "crates/elab/src/cases.rs:new",
    "crates/elab/src/cases.rs:walk",
    "crates/elab/src/chain.rs:check_type",
    "crates/elab/src/chain.rs:on_spine",
    "crates/elab/src/check.rs:alias_notes",
    "crates/elab/src/check.rs:check",
    "crates/elab/src/check.rs:error",
    "crates/elab/src/check.rs:eval",
    "crates/elab/src/check.rs:fill_placeholder",
    "crates/elab/src/check.rs:fresh_function_type_in",
    "crates/elab/src/check.rs:head_before_placeholder",
    "crates/elab/src/check.rs:if_h_condition",
    "crates/elab/src/check.rs:infer_inner",
    "crates/elab/src/check.rs:infer_value",
    "crates/elab/src/check.rs:is_true_test",
    "crates/elab/src/check.rs:mark_of_type",
    "crates/elab/src/check.rs:new",
    "crates/elab/src/check.rs:proof_search",
    "crates/elab/src/check.rs:quote_folded",
    "crates/elab/src/check.rs:quote_internal",
    "crates/elab/src/check.rs:quote_or_written",
    "crates/elab/src/check.rs:quote_unfolded",
    "crates/elab/src/check.rs:same_value",
    "crates/elab/src/check.rs:text",
    "crates/elab/src/check.rs:tuple_parts",
    "crates/elab/src/check.rs:unify",
    "crates/elab/src/closing.rs:fill_premises",
    "crates/elab/src/closing.rs:smaller_vars",
    "crates/elab/src/counterexample/inputs.rs:compositions",
    "crates/elab/src/counterexample/inputs.rs:decidable_value",
    "crates/elab/src/counterexample/inputs.rs:new",
    "crates/elab/src/counterexample/inputs.rs:proof",
    "crates/elab/src/counterexample/inputs.rs:random",
    "crates/elab/src/counterexample/inputs.rs:shown",
    "crates/elab/src/counterexample/inputs.rs:shrink",
    "crates/elab/src/counterexample/inputs.rs:size",
    "crates/elab/src/counterexample/inputs.rs:tier",
    "crates/elab/src/counterexample/mod.rs:now",
    "crates/elab/src/decreasing.rs:leaf_lambda",
    "crates/elab/src/decreasing.rs:mentions",
    "crates/elab/src/decreasing/plain.rs:mark_tree",
    "crates/elab/src/decreasing/plain.rs:rebuild",
    "crates/elab/src/derive_induct.rs:classify",
    "crates/elab/src/derive_induct.rs:inst",
    "crates/elab/src/derive_induct.rs:map_pred",
    "crates/elab/src/derive_induct.rs:pred_levels",
    "crates/elab/src/derive_induct.rs:pred_term",
    "crates/elab/src/derive_induct.rs:preds_eq",
    "crates/elab/src/derive_induct.rs:sum",
    "crates/elab/src/dot.rs:dot_on_reading",
    "crates/elab/src/dot.rs:dotted",
    "crates/elab/src/dot.rs:helper_owner",
    "crates/elab/src/dot.rs:note_left_out",
    "crates/elab/src/dot.rs:receiver_type",
    "crates/elab/src/effects.rs:done_value",
    "crates/elab/src/effects.rs:is_empty",
    "crates/elab/src/effects.rs:new",
    "crates/elab/src/effects.rs:position",
    "crates/elab/src/effects.rs:run_scrutinees",
    "crates/elab/src/equation_notes.rs:rule_equation",
    "crates/elab/src/equations.rs:branch_paths",
    "crates/elab/src/equations.rs:calls_itself",
    "crates/elab/src/equations.rs:expand_one",
    "crates/elab/src/equations.rs:guard_terms",
    "crates/elab/src/equations.rs:is_empty",
    "crates/elab/src/equations.rs:match_pattern",
    "crates/elab/src/equations.rs:match_pv",
    "crates/elab/src/equations.rs:new",
    "crates/elab/src/equations.rs:probe_body",
    "crates/elab/src/equations.rs:pv_in",
    "crates/elab/src/equations.rs:pv_of",
    "crates/elab/src/equations.rs:resolve",
    "crates/elab/src/equations.rs:same_but_proofs",
    "crates/elab/src/equations.rs:same_pv",
    "crates/elab/src/equations.rs:shift",
    "crates/elab/src/equations.rs:tail_split",
    "crates/elab/src/equations.rs:term",
    "crates/elab/src/equations.rs:test",
    "crates/elab/src/equations.rs:tuple",
    "crates/elab/src/equations.rs:tuple_ty",
    "crates/elab/src/equations.rs:unify",
    "crates/elab/src/equations/induct.rs:agrees",
    "crates/elab/src/equations/induct.rs:alt_descend",
    "crates/elab/src/equations/induct.rs:big_literal",
    "crates/elab/src/equations/induct.rs:bind",
    "crates/elab/src/equations/induct.rs:build",
    "crates/elab/src/equations/induct.rs:clash",
    "crates/elab/src/equations/induct.rs:find_places",
    "crates/elab/src/equations/induct.rs:get",
    "crates/elab/src/equations/induct.rs:helper_calls",
    "crates/elab/src/equations/induct.rs:induct_split",
    "crates/elab/src/equations/induct.rs:insert",
    "crates/elab/src/equations/induct.rs:len",
    "crates/elab/src/equations/induct.rs:node_proof",
    "crates/elab/src/equations/induct.rs:node_term",
    "crates/elab/src/equations/induct.rs:parse_pat",
    "crates/elab/src/equations/induct.rs:pat_at",
    "crates/elab/src/equations/induct.rs:resolve",
    "crates/elab/src/equations/induct.rs:term",
    "crates/elab/src/equations/induct.rs:values",
    "crates/elab/src/facts.rs:add",
    "crates/elab/src/facts.rs:apply",
    "crates/elab/src/facts.rs:define",
    "crates/elab/src/facts.rs:error",
    "crates/elab/src/facts.rs:fit",
    "crates/elab/src/facts.rs:is_fact",
    "crates/elab/src/facts.rs:split",
    "crates/elab/src/families.rs:is_empty",
    "crates/elab/src/families.rs:leaf_spans",
    "crates/elab/src/goals.rs:aliases",
    "crates/elab/src/goals.rs:eq_decision",
    "crates/elab/src/goals.rs:full_name",
    "crates/elab/src/goals.rs:loose_ctor",
    "crates/elab/src/goals.rs:names",
    "crates/elab/src/interfaces.rs:specialise_in",
    "crates/elab/src/kernel.rs:admit_trusted_data_decls",
    "crates/elab/src/kernel.rs:admit_trusted_data_group",
    "crates/elab/src/kernel.rs:admit_trusted_def",
    "crates/elab/src/kernel.rs:admit_trusted_group",
    "crates/elab/src/kernel.rs:admit_trusted_run_body",
    "crates/elab/src/kernel.rs:admit_trusted_stated",
    "crates/elab/src/kernel.rs:admit_trusted_unproved",
    "crates/elab/src/kernel.rs:declare_data_group",
    "crates/elab/src/kernel.rs:declare_def",
    "crates/elab/src/kernel.rs:declare_indexed_data_group",
    "crates/elab/src/kernel.rs:define_data_group",
    "crates/elab/src/kernel.rs:define_group",
    "crates/elab/src/kernel.rs:leave_stated",
    "crates/elab/src/kernel.rs:reread",
    "crates/elab/src/kernel.rs:reread_in",
    "crates/elab/src/kernel.rs:retype_def",
    "crates/elab/src/lib.rs:chosen_in",
    "crates/elab/src/lib.rs:error",
    "crates/elab/src/lib.rs:eval",
    "crates/elab/src/lib.rs:first_absurd",
    "crates/elab/src/lib.rs:guard_chain_missing",
    "crates/elab/src/lib.rs:is_empty",
    "crates/elab/src/lib.rs:is_flat",
    "crates/elab/src/lib.rs:is_unfinished",
    "crates/elab/src/lib.rs:mark_text_gaps",
    "crates/elab/src/lib.rs:moved",
    "crates/elab/src/lib.rs:note_meta_shown",
    "crates/elab/src/lib.rs:rest_of_text",
    "crates/elab/src/lib.rs:split_levels",
    "crates/elab/src/lib.rs:unfinished_use_of",
    "crates/elab/src/lib.rs:walk",
    "crates/elab/src/lib.rs:without_alternatives",
    "crates/elab/src/library.rs:install_library",
    "crates/elab/src/library/index_cache.rs:key",
    "crates/elab/src/library/index_cache.rs:write",
    "crates/elab/src/lift.rs:in_helper",
    "crates/elab/src/literal_facts.rs:differs",
    "crates/elab/src/literal_facts.rs:tree",
    "crates/elab/src/logic.rs:conjunction_lhs",
    "crates/elab/src/logic.rs:equation_side",
    "crates/elab/src/matching.rs:new",
    "crates/elab/src/matching.rs:same_in",
    "crates/elab/src/matching/as_written.rs:agree",
    "crates/elab/src/matching/as_written.rs:note_kept",
    "crates/elab/src/matching/untouched.rs:rigid",
    "crates/elab/src/matching/untouched.rs:value",
    "crates/elab/src/membership.rs:written_range",
    "crates/elab/src/missing.rs:annotate_in",
    "crates/elab/src/missing.rs:collect",
    "crates/elab/src/missing.rs:diagnostic",
    "crates/elab/src/missing.rs:numbers",
    "crates/elab/src/missing.rs:show_column",
    "crates/elab/src/module.rs:pattern_binders",
    "crates/elab/src/named.rs:any",
    "crates/elab/src/named.rs:bind_missing",
    "crates/elab/src/named.rs:map",
    "crates/elab/src/named.rs:unknown",
    "crates/elab/src/nav.rs:bytes",
    "crates/elab/src/nav.rs:distinct_keys",
    "crates/elab/src/nav.rs:entries",
    "crates/elab/src/nav.rs:pattern_binder_spans",
    "crates/elab/src/nav.rs:pattern_binders",
    "crates/elab/src/nav.rs:set_generation",
    "crates/elab/src/nav.rs:undo_to",
    "crates/elab/src/no_effect.rs:call_like",
    "crates/elab/src/no_effect.rs:named",
    "crates/elab/src/numbers.rs:attempt",
    "crates/elab/src/numbers.rs:map",
    "crates/elab/src/omega.rs:atoms",
    "crates/elab/src/omega.rs:cert_term",
    "crates/elab/src/omega.rs:ctor",
    "crates/elab/src/omega.rs:go",
    "crates/elab/src/omega.rs:lin",
    "crates/elab/src/omega.rs:linear_split",
    "crates/elab/src/omega.rs:new",
    "crates/elab/src/omega.rs:prove_goal",
    "crates/elab/src/omega.rs:prove_or",
    "crates/elab/src/omega.rs:quote",
    "crates/elab/src/omega.rs:quote_int",
    "crates/elab/src/omega.rs:read",
    "crates/elab/src/omega.rs:render",
    "crates/elab/src/omega.rs:render_int",
    "crates/elab/src/omega.rs:renumber",
    "crates/elab/src/omega.rs:term",
    "crates/elab/src/omega.rs:used_inputs",
    "crates/elab/src/omega_search.rs:emit",
    "crates/elab/src/omega_search.rs:go",
    "crates/elab/src/omega_search.rs:push",
    "crates/elab/src/omega_search.rs:refute",
    "crates/elab/src/omega_search.rs:write",
    "crates/elab/src/patlet.rs:bind",
    "crates/elab/src/patlet.rs:opens_exists",
    "crates/elab/src/patlet.rs:projectable",
    "crates/elab/src/patlet.rs:proposition",
    "crates/elab/src/patlet.rs:simple",
    "crates/elab/src/probe.rs:arm_bodies_in",
    "crates/elab/src/probe.rs:has_hole",
    "crates/elab/src/probe.rs:instrument",
    "crates/elab/src/probe.rs:is_match",
    "crates/elab/src/probe.rs:path_to",
    "crates/elab/src/probe.rs:probe",
    "crates/elab/src/probe.rs:tree",
    "crates/elab/src/probe.rs:walk",
    "crates/elab/src/proof_chain.rs:is_trans",
    "crates/elab/src/queue.rs:apply_default",
    "crates/elab/src/queue.rs:clear",
    "crates/elab/src/queue.rs:forget",
    "crates/elab/src/queue.rs:go",
    "crates/elab/src/queue.rs:lambda",
    "crates/elab/src/queue.rs:len",
    "crates/elab/src/queue.rs:stuck_error",
    "crates/elab/src/queue.rs:syntax",
    "crates/elab/src/reading.rs:last",
    "crates/elab/src/records.rs:brace_arguments",
    "crates/elab/src/redundant.rs:arm_spans",
    "crates/elab/src/redundant.rs:redundant_alternatives",
    "crates/elab/src/redundant.rs:subsumes",
    "crates/elab/src/rewind.rs:bytes",
    "crates/elab/src/rewind.rs:defs",
    "crates/elab/src/rewind.rs:distinct_keys",
    "crates/elab/src/rewind.rs:entries",
    "crates/elab/src/rewind.rs:mark",
    "crates/elab/src/rewind.rs:positions",
    "crates/elab/src/rewind.rs:release",
    "crates/elab/src/rewind.rs:rewind",
    "crates/elab/src/rewind.rs:rewind_fresh",
    "crates/elab/src/rewind.rs:set_generation",
    "crates/elab/src/rewind.rs:undo_to",
    "crates/elab/src/rewrite.rs:carried",
    "crates/elab/src/rewrite.rs:checks_against",
    "crates/elab/src/rewrite.rs:infers",
    "crates/elab/src/rewrite.rs:new",
    "crates/elab/src/rewrite.rs:unconfirmed",
    "crates/elab/src/rewrite/as_written.rs:opened",
    "crates/elab/src/rewrite/repeatedly.rs:close_parts",
    "crates/elab/src/rewrite/repeatedly.rs:depth",
    "crates/elab/src/rewrite/repeatedly.rs:get",
    "crates/elab/src/rewrite/repeatedly.rs:insert",
    "crates/elab/src/rewrite/repeatedly.rs:path",
    "crates/elab/src/rewrite/repeatedly.rs:render",
    "crates/elab/src/rewrite/repeatedly.rs:restore",
    "crates/elab/src/rewrite/under.rs:is_lambda",
    "crates/elab/src/ring.rs:ctor",
    "crates/elab/src/ring.rs:poly",
    "crates/elab/src/ring.rs:read_nat",
    "crates/elab/src/ring.rs:split_fact",
    "crates/elab/src/ring.rs:term",
    "crates/elab/src/saturate.rs:spine_args",
    "crates/elab/src/scope.rs:aliases",
    "crates/elab/src/scope.rs:bytes",
    "crates/elab/src/scope.rs:distinct_keys",
    "crates/elab/src/scope.rs:entries",
    "crates/elab/src/scope.rs:eq_decision",
    "crates/elab/src/scope.rs:get",
    "crates/elab/src/scope.rs:imported_namespaces",
    "crates/elab/src/scope.rs:insert",
    "crates/elab/src/scope.rs:keys",
    "crates/elab/src/scope.rs:positions",
    "crates/elab/src/scope.rs:remove",
    "crates/elab/src/scope.rs:set_generation",
    "crates/elab/src/scope.rs:undo_to",
    "crates/elab/src/search.rs:name",
    "crates/elab/src/search.rs:path",
    "crates/elab/src/search.rs:span",
    "crates/elab/src/search.rs:split_conjunction",
    "crates/elab/src/search.rs:ty",
    "crates/elab/src/shown.rs:walk",
    "crates/elab/src/state/attempt.rs:mark",
    "crates/elab/src/state/attempt.rs:restore",
    "crates/elab/src/state/caches.rs:clear",
    "crates/elab/src/state/journal.rs:contains_key",
    "crates/elab/src/state/journal.rs:default",
    "crates/elab/src/state/journal.rs:get",
    "crates/elab/src/state/journal.rs:get_key_value",
    "crates/elab/src/state/journal.rs:insert",
    "crates/elab/src/state/journal.rs:is_empty",
    "crates/elab/src/state/journal.rs:iter",
    "crates/elab/src/state/journal.rs:keys",
    "crates/elab/src/state/journal.rs:pop",
    "crates/elab/src/state/journal.rs:push",
    "crates/elab/src/state/journal.rs:retain",
    "crates/elab/src/state/journal.rs:values",
    "crates/elab/src/state/metas.rs:clear",
    "crates/elab/src/state/metas.rs:default",
    "crates/elab/src/state/metas.rs:keys",
    "crates/elab/src/state/owners.rs:truncate",
    "crates/elab/src/state/paths.rs:truncate",
    "crates/elab/src/state/presentation.rs:dump",
    "crates/elab/src/state/presentation.rs:mark",
    "crates/elab/src/state/presentation.rs:rewind",
    "crates/elab/src/state/session.rs:bytes",
    "crates/elab/src/state/session.rs:distinct_keys",
    "crates/elab/src/state/session.rs:entries",
    "crates/elab/src/state/session.rs:mark",
    "crates/elab/src/state/session.rs:rewind",
    "crates/elab/src/state/session.rs:set_generation",
    "crates/elab/src/state/session.rs:undo_to",
    "crates/elab/src/state/table.rs:decode",
    "crates/elab/src/state/table.rs:default",
    "crates/elab/src/state/table.rs:insert",
    "crates/elab/src/state/table.rs:push",
    "crates/elab/src/state/table.rs:remove",
    "crates/elab/src/state/tables.rs:bytes",
    "crates/elab/src/state/tables.rs:decode",
    "crates/elab/src/state/tables.rs:distinct_keys",
    "crates/elab/src/state/tables.rs:dump",
    "crates/elab/src/state/tables.rs:encode_since",
    "crates/elab/src/state/tables.rs:entries",
    "crates/elab/src/state/tables.rs:insert",
    "crates/elab/src/state/tables.rs:mark",
    "crates/elab/src/state/tables.rs:replay",
    "crates/elab/src/state/tables.rs:rewind",
    "crates/elab/src/state/tables.rs:set_generation",
    "crates/elab/src/state/tables.rs:undo_to",
    "crates/elab/src/state/tables.rs:update",
    "crates/elab/src/std_dir.rs:collect",
    "crates/elab/src/std_dir.rs:leak",
    "crates/elab/src/tailrec.rs:in_block",
    "crates/elab/src/tailrec.rs:is_field",
    "crates/elab/src/tailrec.rs:label",
    "crates/elab/src/timings.rs:report",
    "crates/elab/src/undo.rs:defaulted",
    "crates/elab/src/undo.rs:metas",
    "crates/elab/src/undo.rs:restore",
    "crates/elab/src/undo.rs:unify_abstracting",
    "crates/elab/src/undo.rs:unify_by_unknown_arguments",
    "crates/elab/src/unify.rs:blocked_within",
    "crates/elab/src/unify.rs:eta_contract",
    "crates/elab/src/unify.rs:is_proof",
    "crates/elab/src/unify.rs:rename_in",
    "crates/elab/src/unify.rs:rigidly_mentions",
    "crates/elab/src/unify.rs:stale_within",
    "crates/elab/src/unify.rs:type_fixed",
    "crates/elab/src/unify.rs:types_apart",
    "crates/elab/src/unify.rs:unannotate_let_heads",
    "crates/elab/src/unify.rs:zonk_changed",
    "crates/elab/src/walk/expand.rs:flatten",
    "crates/elab/src/walk/mod.rs:len",
    "crates/elab/src/walk/mod.rs:step",
    "crates/elab/src/walk/mod.rs:truncate",
    "crates/elab/src/walk/source.rs:code_lines",
    "crates/elab/src/walk/source.rs:performs",
    "crates/elab/src/walk/source.rs:statement_source",
    "crates/syntax/src/ast.rs:show_into",
    "crates/syntax/src/ast.rs:span",
    "crates/syntax/src/diagnostic.rs:new",
    "crates/syntax/src/lexer.rs:error",
    "crates/syntax/src/lower/binding.rs:exists_chain",
    "crates/syntax/src/lower/coverage.rs:bodies",
    "crates/syntax/src/lower/exprs.rs:binary",
    "crates/syntax/src/lower/exprs.rs:chain",
    "crates/syntax/src/lower/exprs.rs:go",
    "crates/syntax/src/lower/patterns.rs:bound_names",
    "crates/syntax/src/lower/sections.rs:method_section",
    "crates/syntax/src/lower/sections.rs:section_body",
    "crates/syntax/src/lower/sections.rs:section_dot",
    "crates/syntax/src/parser.rs:error",
    "crates/syntax/src/parser.rs:new",
    "crates/syntax/src/source.rs:is_empty",
    "crates/syntax/src/source.rs:len",
    "crates/syntax/src/source.rs:truncate",
    "crates/syntax/src/tree.rs:dump_node",
    "crates/syntax/src/tree.rs:for_each_leaf",
];

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

fn is_ident(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn is_space(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\n' | b'\r')
}

fn find(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.windows(needle.len()).position(|w| w == needle)
}

fn blank(out: &mut [u8], from: usize, to: usize) {
    for b in &mut out[from..to] {
        if *b != b'\n' {
            *b = b' ';
        }
    }
}

/// `text` with comments and the contents of strings and chars blanked out,
/// at the same byte offsets.
fn strip_code(text: &str) -> Vec<u8> {
    let b = text.as_bytes();
    let mut out = b.to_vec();
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'/' && b.get(i + 1) == Some(&b'/') {
            let end = b[i..]
                .iter()
                .position(|&c| c == b'\n')
                .map_or(b.len(), |n| i + n);
            blank(&mut out, i, end);
            i = end;
            continue;
        }
        if b[i] == b'/' && b.get(i + 1) == Some(&b'*') {
            let mut depth = 1;
            let mut j = i + 2;
            while j < b.len() && depth > 0 {
                if b[j] == b'/' && b.get(j + 1) == Some(&b'*') {
                    depth += 1;
                    j += 2;
                } else if b[j] == b'*' && b.get(j + 1) == Some(&b'/') {
                    depth -= 1;
                    j += 2;
                } else {
                    j += 1;
                }
            }
            blank(&mut out, i, j);
            i = j;
            continue;
        }
        if let Some((quote, hashes)) = raw_string_start(b, i) {
            let mut close = vec![b'"'];
            close.extend(std::iter::repeat_n(b'#', hashes));
            let end =
                find(&b[quote + 1..], &close).map_or(b.len(), |n| quote + 1 + n + close.len());
            blank(&mut out, i, end);
            i = end;
            continue;
        }
        if b[i] == b'"' {
            let mut j = i + 1;
            while j < b.len() {
                if b[j] == b'\\' {
                    j += 2;
                } else if b[j] == b'"' {
                    j += 1;
                    break;
                } else {
                    j += 1;
                }
            }
            blank(&mut out, i, j.min(b.len()));
            i = j;
            continue;
        }
        if b[i] == b'\'' {
            let end = if b.get(i + 1) == Some(&b'\\') {
                let mut j = i + 2;
                while j < b.len() && b[j] != b'\'' && b[j] != b'\n' {
                    if b[j] == b'\\' {
                        j += 1;
                    }
                    j += 1;
                }
                (j < b.len() && b[j] == b'\'').then_some(j + 1)
            } else if b.get(i + 2) == Some(&b'\'') {
                Some(i + 3)
            } else {
                None
            };
            if let Some(end) = end {
                blank(&mut out, i, end);
                i = end;
                continue;
            }
        }
        i += 1;
    }
    out
}

/// Where the string of a raw string starts, and its hash count, for `r"`,
/// `r#"`, `br##"` and the like at `i`.
fn raw_string_start(b: &[u8], i: usize) -> Option<(usize, usize)> {
    let mut j = i;
    if matches!(b.get(j), Some(b'b' | b'c')) {
        j += 1;
    }
    if b.get(j) != Some(&b'r') || (i > 0 && is_ident(b[i - 1])) {
        return None;
    }
    j += 1;
    let mut hashes = 0;
    while b.get(j) == Some(&b'#') {
        hashes += 1;
        j += 1;
    }
    (b.get(j) == Some(&b'"')).then_some((j, hashes))
}

fn matching_brace(code: &[u8], open: usize) -> Option<usize> {
    let mut depth = 0;
    for (i, &b) in code.iter().enumerate().skip(open) {
        match b {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// The `{` opening a function body, or `None` for a declaration ending in `;`.
fn body_open(code: &[u8], mut j: usize) -> Option<usize> {
    let (mut parens, mut brackets, mut angles) = (0usize, 0usize, 0usize);
    while let Some(&b) = code.get(j) {
        match b {
            b'(' => parens += 1,
            b')' => parens = parens.saturating_sub(1),
            b'[' => brackets += 1,
            b']' => brackets = brackets.saturating_sub(1),
            // The `>` of `->` is not the end of a generic list.
            b'<' if code.get(j.wrapping_sub(1)) != Some(&b'-') => angles += 1,
            b'>' if code.get(j.wrapping_sub(1)) != Some(&b'-') => {
                angles = angles.saturating_sub(1);
            }
            b'{' if parens == 0 && brackets == 0 && angles == 0 => return Some(j),
            b';' if parens == 0 && brackets == 0 && angles == 0 => return None,
            _ => {}
        }
        j += 1;
    }
    None
}

struct Function {
    name: String,
    start: usize,
    body: (usize, usize),
}

fn functions(code: &[u8]) -> Vec<Function> {
    let mut out = Vec::new();
    let mut i = 0;
    while i + 2 <= code.len() {
        let is_fn = &code[i..i + 2] == b"fn"
            && (i == 0 || !is_ident(code[i - 1]))
            && (i + 2 == code.len() || !is_ident(code[i + 2]));
        if is_fn {
            let mut j = i + 2;
            while code.get(j).is_some_and(|&b| is_space(b)) {
                j += 1;
            }
            if code.get(j).is_some_and(|&b| is_ident_start(b)) {
                let name_start = j;
                while code.get(j).is_some_and(|&b| is_ident(b)) {
                    j += 1;
                }
                let name = std::str::from_utf8(&code[name_start..j])
                    .expect("a function name")
                    .to_string();
                if let Some(open) = body_open(code, j)
                    && let Some(close) = matching_brace(code, open)
                {
                    out.push(Function {
                        name,
                        start: i,
                        body: (open, close + 1),
                    });
                    i = j;
                    continue;
                }
            }
        }
        i += 1;
    }
    out
}

/// The ranges of `#[cfg(test)] mod ... { ... }`, whose functions are tests.
fn test_ranges(code: &[u8]) -> Vec<(usize, usize)> {
    let needle = b"#[cfg(test)]";
    let mut ranges = Vec::new();
    let mut at = 0;
    while let Some(found) = find(&code[at..], needle) {
        let mut j = at + found + needle.len();
        loop {
            while code.get(j).is_some_and(|&b| is_space(b)) {
                j += 1;
            }
            if code.get(j) == Some(&b'#') && code.get(j + 1) == Some(&b'[') {
                let mut depth = 0;
                while j < code.len() {
                    match code[j] {
                        b'[' => depth += 1,
                        b']' => {
                            depth -= 1;
                            j += 1;
                            if depth == 0 {
                                break;
                            }
                            continue;
                        }
                        _ => {}
                    }
                    j += 1;
                }
                continue;
            }
            break;
        }
        if code.get(j..j + 3) == Some(b"mod") && code.get(j + 3).is_none_or(|&b| !is_ident(b)) {
            j += 3;
            while code.get(j).is_some_and(|&b| is_space(b)) {
                j += 1;
            }
            while code.get(j).is_some_and(|&b| is_ident(b)) {
                j += 1;
            }
            while code.get(j).is_some_and(|&b| b != b'{' && b != b';') {
                j += 1;
            }
            if code.get(j) == Some(&b'{')
                && let Some(close) = matching_brace(code, j)
            {
                ranges.push((at + found, close + 1));
                at = close + 1;
                continue;
            }
        }
        at = at + found + needle.len();
    }
    ranges
}

fn preceded_by_fn(code: &[u8], mut i: usize) -> bool {
    while i > 0 && is_space(code[i - 1]) {
        i -= 1;
    }
    i >= 2 && &code[i - 2..i] == b"fn" && (i == 2 || !is_ident(code[i - 3]))
}

fn calls_itself(code: &[u8], body: (usize, usize), name: &str) -> bool {
    let needle = name.as_bytes();
    let (start, end) = body;
    let mut i = start;
    while i + needle.len() <= end {
        if &code[i..i + needle.len()] == needle
            && (i == 0 || !is_ident(code[i - 1]))
            && (i + needle.len() == code.len() || !is_ident(code[i + needle.len()]))
        {
            let mut j = i + needle.len();
            while j < end && is_space(code[j]) {
                j += 1;
            }
            if code.get(j..j + 2) == Some(b"::") {
                j += 2;
                while j < end && is_space(code[j]) {
                    j += 1;
                }
                if code.get(j) == Some(&b'<') {
                    let mut angles = 0;
                    while j < end {
                        match code[j] {
                            b'<' => angles += 1,
                            b'>' => {
                                angles -= 1;
                                if angles == 0 {
                                    j += 1;
                                    break;
                                }
                            }
                            _ => {}
                        }
                        j += 1;
                    }
                    while j < end && is_space(code[j]) {
                        j += 1;
                    }
                }
            }
            if code.get(j) == Some(&b'(') && !preceded_by_fn(code, i) {
                return true;
            }
        }
        i += 1;
    }
    false
}

fn has_guard(code: &[u8], text: &str, body: (usize, usize), start: usize) -> bool {
    let body_code = &code[body.0..body.1];
    if GUARDS
        .iter()
        .any(|g| find(body_code, g.as_bytes()).is_some())
    {
        return true;
    }
    let body_text = &text[body.0..body.1];
    if body_text
        .lines()
        .any(|line| line.trim_start().starts_with("// Depth:"))
    {
        return true;
    }
    let line_start = text[..start].rfind('\n').map_or(0, |n| n + 1);
    for line in text[..line_start].lines().rev() {
        let line = line.trim_start();
        if line.starts_with("#[") || line.starts_with("#![") || line.starts_with("//") {
            if line.starts_with("// Depth:") {
                return true;
            }
        } else {
            break;
        }
    }
    false
}

fn source_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("a source folder")
        .map(|entry| entry.expect("an entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            source_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if name != "tests.rs" && !name.ends_with("_tests.rs") {
                out.push(path);
            }
        }
    }
}

fn offenders(root: &Path, found: &mut BTreeSet<String>) {
    for krate in CRATES {
        let mut files = Vec::new();
        source_files(&root.join("crates").join(krate).join("src"), &mut files);
        for path in files {
            let text = std::fs::read_to_string(&path).expect("a source file");
            let code = strip_code(&text);
            let tests = test_ranges(&code);
            for f in functions(&code) {
                if tests
                    .iter()
                    .any(|&(start, end)| start <= f.start && f.start < end)
                {
                    continue;
                }
                if !calls_itself(&code, f.body, &f.name) || has_guard(&code, &text, f.body, f.start)
                {
                    continue;
                }
                let rel = path.strip_prefix(root).expect("under the root");
                found.insert(format!("{}:{}", rel.display(), f.name));
            }
        }
    }
}

#[test]
fn self_recursion_is_guarded_or_stated() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut found = BTreeSet::new();
    offenders(&root, &mut found);
    let allowed: BTreeSet<String> = ALLOWED.iter().map(|s| s.to_string()).collect();
    let new: Vec<&String> = found.difference(&allowed).collect();
    let stale: Vec<&String> = allowed.difference(&found).collect();
    assert!(
        new.is_empty() && stale.is_empty(),
        "self-recursion without a guard or a `// Depth:` comment changed.\n\
         New (add a guard, a `// Depth:` reason, or an allowlist entry):\n{}\n\
         Stale (remove from ALLOWED):\n{}",
        new.iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n"),
        stale
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n")
    );
}
