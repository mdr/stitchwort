//! A static check for self-recursive functions with no stack guard:
//! docs/proposals/deep-input.md §6.2, SW-1966.
//!
//! It reads the source as text, not as a parser. A function's body is found by
//! brace matching. A call is `name(` for a free function, and `self.name(` or
//! `Self::name(` for a method; a call on another receiver is not counted. A
//! same-named local or method still gives a false positive, and mutual
//! recursion (`a` calling `b` calling `a`) is missed. Braces or calls inside
//! strings and comments do not count, while braces in a macro body are read as
//! ordinary braces; a guard anywhere in the body, even in a nested function,
//! counts for the outer one. A `// Depth:` comment in the function or
//! immediately above it (past attributes) states a bound instead of a guard.
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
    "crates/core/src/check.rs:conv",
    "crates/core/src/check.rs:eval",
    "crates/core/src/check.rs:prop_mark",
    "crates/core/src/check.rs:quote",
    "crates/core/src/check.rs:stored_only",
    "crates/core/src/check.rs:why_not_nestable",
    "crates/core/src/float.rs:js_to_string",
    "crates/core/src/pretty.rs:defaulted",
    "crates/core/src/pretty.rs:go",
    "crates/core/src/pretty.rs:list_pieces",
    "crates/core/src/pretty.rs:map_tree_entries",
    "crates/core/src/pretty.rs:size",
    "crates/core/src/pretty.rs:within",
    "crates/core/src/reference.rs:compact_or_lazy",
    "crates/core/src/reference.rs:conv_in",
    "crates/core/src/reference.rs:eval",
    "crates/core/src/reference.rs:eval_tree",
    "crates/core/src/reference.rs:expand_term",
    "crates/core/src/reference.rs:force",
    "crates/core/src/reference.rs:number_view",
    "crates/core/src/reference.rs:quote",
    "crates/core/src/reference.rs:same_trees",
    "crates/core/src/reference.rs:type_at",
    "crates/core/src/reference.rs:unfold",
    "crates/core/src/reference.rs:unfold_folded",
    "crates/core/src/reference.rs:validate_pi_marks",
    "crates/core/src/termination.rs:rebuilt",
    "crates/core/src/value.rs:bound_fields",
    "crates/core/src/value.rs:drop",
    "crates/core/src/value.rs:field_type",
    "crates/core/src/value.rs:matches_at_once",
    "crates/core/src/value.rs:quick",
    "crates/core/src/value.rs:stuck_on_variable",
    "crates/core/src/value.rs:unfold_once",
    "crates/core/src/value.rs:visit",
    "crates/driver/src/counterexample.rs:tree",
    "crates/driver/src/fingerprint.rs:collect",
    "crates/driver/src/project.rs:walk",
    "crates/driver/src/search.rs:ambiguities",
    "crates/driver/src/search.rs:append_chain",
    "crates/driver/src/search.rs:numeric_group",
    "crates/elab/src/arm_display.rs:set",
    "crates/elab/src/arm_display.rs:set_facts",
    "crates/elab/src/arm_display.rs:tally",
    "crates/elab/src/auto.rs:size",
    "crates/elab/src/auto.rs:take_apart",
    "crates/elab/src/autobind.rs:pattern_vars",
    "crates/elab/src/bind.rs:shape",
    "crates/elab/src/cache/dump.rs:dump_probe",
    "crates/elab/src/cache/mod.rs:probe",
    "crates/elab/src/cases.rs:by_parts_at",
    "crates/elab/src/cases.rs:case_value",
    "crates/elab/src/cases.rs:ctor_vars",
    "crates/elab/src/cases.rs:walk",
    "crates/elab/src/chain.rs:on_spine",
    "crates/elab/src/check.rs:alias_notes",
    "crates/elab/src/check.rs:check",
    "crates/elab/src/check.rs:eval",
    "crates/elab/src/check.rs:fill_placeholder",
    "crates/elab/src/check.rs:fresh_function_type_in",
    "crates/elab/src/check.rs:head_before_placeholder",
    "crates/elab/src/check.rs:if_h_condition",
    "crates/elab/src/check.rs:infer_inner",
    "crates/elab/src/check.rs:infer_value",
    "crates/elab/src/check.rs:is_true_test",
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
    "crates/elab/src/counterexample/inputs.rs:proof",
    "crates/elab/src/counterexample/inputs.rs:random",
    "crates/elab/src/counterexample/inputs.rs:shown",
    "crates/elab/src/counterexample/inputs.rs:shrink",
    "crates/elab/src/counterexample/inputs.rs:size",
    "crates/elab/src/counterexample/inputs.rs:tier",
    "crates/elab/src/decreasing.rs:leaf_lambda",
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
    "crates/elab/src/dot.rs:receiver_type",
    "crates/elab/src/effects.rs:done_value",
    "crates/elab/src/effects.rs:run_scrutinees",
    "crates/elab/src/equation_notes.rs:rule_equation",
    "crates/elab/src/equations.rs:branch_paths",
    "crates/elab/src/equations.rs:expand_one",
    "crates/elab/src/equations.rs:guard_terms",
    "crates/elab/src/equations.rs:match_pattern",
    "crates/elab/src/equations.rs:match_pv",
    "crates/elab/src/equations.rs:probe_body",
    "crates/elab/src/equations.rs:pv_in",
    "crates/elab/src/equations.rs:pv_of",
    "crates/elab/src/equations.rs:resolve",
    "crates/elab/src/equations.rs:same_but_proofs",
    "crates/elab/src/equations.rs:same_pv",
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
    "crates/elab/src/equations/induct.rs:helper_calls",
    "crates/elab/src/equations/induct.rs:induct_split",
    "crates/elab/src/equations/induct.rs:node_proof",
    "crates/elab/src/equations/induct.rs:node_term",
    "crates/elab/src/equations/induct.rs:parse_pat",
    "crates/elab/src/equations/induct.rs:pat_at",
    "crates/elab/src/equations/induct.rs:resolve",
    "crates/elab/src/equations/induct.rs:term",
    "crates/elab/src/equations/induct.rs:values",
    "crates/elab/src/facts.rs:add",
    "crates/elab/src/facts.rs:fit",
    "crates/elab/src/facts.rs:is_fact",
    "crates/elab/src/facts.rs:split",
    "crates/elab/src/families.rs:leaf_spans",
    "crates/elab/src/goals.rs:loose_ctor",
    "crates/elab/src/interfaces.rs:specialise_in",
    "crates/elab/src/lib.rs:chosen_in",
    "crates/elab/src/lib.rs:eval",
    "crates/elab/src/lib.rs:first_absurd",
    "crates/elab/src/lib.rs:guard_chain_missing",
    "crates/elab/src/lib.rs:is_flat",
    "crates/elab/src/lib.rs:mark_text_gaps",
    "crates/elab/src/lib.rs:rest_of_text",
    "crates/elab/src/lib.rs:unfinished_use_of",
    "crates/elab/src/lib.rs:walk",
    "crates/elab/src/lib.rs:without_alternatives",
    "crates/elab/src/library/index_cache.rs:key",
    "crates/elab/src/lift.rs:in_helper",
    "crates/elab/src/literal_facts.rs:differs",
    "crates/elab/src/literal_facts.rs:tree",
    "crates/elab/src/logic.rs:conjunction_lhs",
    "crates/elab/src/logic.rs:equation_side",
    "crates/elab/src/matching.rs:same_in",
    "crates/elab/src/matching/as_written.rs:agree",
    "crates/elab/src/matching/untouched.rs:rigid",
    "crates/elab/src/matching/untouched.rs:value",
    "crates/elab/src/membership.rs:written_range",
    "crates/elab/src/missing.rs:annotate_in",
    "crates/elab/src/missing.rs:collect",
    "crates/elab/src/missing.rs:diagnostic",
    "crates/elab/src/missing.rs:numbers",
    "crates/elab/src/missing.rs:show_column",
    "crates/elab/src/module.rs:pattern_binders",
    "crates/elab/src/named.rs:bind_missing",
    "crates/elab/src/nav.rs:pattern_binder_spans",
    "crates/elab/src/nav.rs:pattern_binders",
    "crates/elab/src/no_effect.rs:call_like",
    "crates/elab/src/no_effect.rs:named",
    "crates/elab/src/omega.rs:cert_term",
    "crates/elab/src/omega.rs:go",
    "crates/elab/src/omega.rs:linear_split",
    "crates/elab/src/omega.rs:prove_goal",
    "crates/elab/src/omega.rs:prove_or",
    "crates/elab/src/omega.rs:quote",
    "crates/elab/src/omega.rs:quote_int",
    "crates/elab/src/omega.rs:read",
    "crates/elab/src/omega.rs:render",
    "crates/elab/src/omega.rs:render_int",
    "crates/elab/src/omega.rs:used_inputs",
    "crates/elab/src/omega_search.rs:emit",
    "crates/elab/src/omega_search.rs:go",
    "crates/elab/src/omega_search.rs:write",
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
    "crates/elab/src/queue.rs:go",
    "crates/elab/src/queue.rs:lambda",
    "crates/elab/src/queue.rs:syntax",
    "crates/elab/src/records.rs:brace_arguments",
    "crates/elab/src/redundant.rs:arm_spans",
    "crates/elab/src/redundant.rs:redundant_alternatives",
    "crates/elab/src/redundant.rs:subsumes",
    "crates/elab/src/rewrite.rs:checks_against",
    "crates/elab/src/rewrite.rs:infers",
    "crates/elab/src/rewrite/repeatedly.rs:close_parts",
    "crates/elab/src/rewrite/repeatedly.rs:depth",
    "crates/elab/src/rewrite/repeatedly.rs:path",
    "crates/elab/src/rewrite/repeatedly.rs:render",
    "crates/elab/src/rewrite/under.rs:is_lambda",
    "crates/elab/src/ring.rs:read_nat",
    "crates/elab/src/ring.rs:split_fact",
    "crates/elab/src/saturate.rs:spine_args",
    "crates/elab/src/search.rs:split_conjunction",
    "crates/elab/src/shown.rs:walk",
    "crates/elab/src/std_dir.rs:collect",
    "crates/elab/src/unify.rs:blocked_within",
    "crates/elab/src/unify.rs:eta_contract",
    "crates/elab/src/unify.rs:rename_in",
    "crates/elab/src/unify.rs:rigidly_mentions",
    "crates/elab/src/unify.rs:stale_within",
    "crates/elab/src/unify.rs:type_fixed",
    "crates/elab/src/unify.rs:types_apart",
    "crates/elab/src/unify.rs:unannotate_let_heads",
    "crates/elab/src/unify.rs:zonk_changed",
    "crates/elab/src/walk/expand.rs:flatten",
    "crates/elab/src/walk/source.rs:code_lines",
    "crates/elab/src/walk/source.rs:performs",
    "crates/elab/src/walk/source.rs:statement_source",
    "crates/syntax/src/lower/binding.rs:exists_chain",
    "crates/syntax/src/lower/coverage.rs:bodies",
    "crates/syntax/src/lower/exprs.rs:binary",
    "crates/syntax/src/lower/exprs.rs:chain",
    "crates/syntax/src/lower/exprs.rs:go",
    "crates/syntax/src/lower/patterns.rs:bound_names",
    "crates/syntax/src/lower/sections.rs:method_section",
    "crates/syntax/src/lower/sections.rs:section_body",
    "crates/syntax/src/lower/sections.rs:section_dot",
    "crates/syntax/src/tree.rs:dump_node",
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

/// Whether `word` is the identifier just before `end`, past whitespace.
fn preceded_by_word(code: &[u8], mut end: usize, word: &[u8]) -> bool {
    while end > 0 && is_space(code[end - 1]) {
        end -= 1;
    }
    if end < word.len() || &code[end - word.len()..end] != word {
        return false;
    }
    let before = end - word.len();
    before == 0 || !is_ident(code[before - 1])
}

/// Whether the occurrence at `i` is `self.name`, with any whitespace.
fn preceded_by_self_dot(code: &[u8], i: usize) -> bool {
    let mut j = i;
    while j > 0 && is_space(code[j - 1]) {
        j -= 1;
    }
    j > 0 && code[j - 1] == b'.' && preceded_by_word(code, j - 1, b"self")
}

/// Whether the occurrence at `i` is `Self::name`, with any whitespace.
fn preceded_by_self_path(code: &[u8], i: usize) -> bool {
    let mut j = i;
    while j > 0 && is_space(code[j - 1]) {
        j -= 1;
    }
    j >= 2 && &code[j - 2..j] == b"::" && preceded_by_word(code, j - 2, b"Self")
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
            let mut before = i;
            while before > 0 && is_space(code[before - 1]) {
                before -= 1;
            }
            let free = !matches!(code.get(before.wrapping_sub(1)), Some(b'.' | b':'));
            let method = preceded_by_self_dot(code, i) || preceded_by_self_path(code, i);
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
            if (free || method) && code.get(j) == Some(&b'(') && !preceded_by_fn(code, i) {
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

/// A name in a string or a line comment is not a call.
#[test]
fn strings_and_comments_do_not_count() {
    let text = r#"
fn probe(n: usize) -> usize {
    let _ = "probe(n)";
    // probe(n)
    n
}
"#;
    let code = strip_code(text);
    let f = functions(&code)
        .into_iter()
        .find(|f| f.name == "probe")
        .expect("probe");
    assert!(!calls_itself(&code, f.body, &f.name));
}

/// A method call on another receiver is not self-recursion; `self.` and
/// `Self::` are.
#[test]
fn only_free_or_self_calls_count() {
    let text = r#"
fn free(n: usize) -> usize {
    free(n - 1)
}
impl T {
    fn only_other(&self, other: &T) {
        other.only_other();
    }
    fn self_call(&self) {
        self.self_call();
    }
    fn path_call(&self) {
        Self::path_call();
    }
}
"#;
    let code = strip_code(text);
    let found = functions(&code);
    let calls = |name: &str| {
        let f = found.iter().find(|f| f.name == name).expect("a function");
        calls_itself(&code, f.body, &f.name)
    };
    assert!(!calls("only_other"));
    assert!(calls("self_call"));
    assert!(calls("path_call"));
    assert!(calls("free"));
}
