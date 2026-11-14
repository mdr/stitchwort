//! The oracle: a file parsed both ways, the compiler's tree built directly
//! ([`crate::parse_module_recovering`]) and lowered from the lossless tree
//! ([`crate::parse_module_and_tree`] then [`Lower`]), and the two compared
//! exactly, declaration by declaration (docs/proposals/syntax-tree-lowering.md
//! §4). `stitchwort dev tree --lower` runs it over files.
//!
//! Trees are compared as their `{:#?}` text with spans: equal text means
//! equal trees, spans, hidden names and tags, with no `PartialEq` on the
//! compiler's tree. `Debug` recurses, so a caller comparing deeply nested
//! files runs this on a thread with a large stack.

use super::{Lower, LoweredDecl, Unsupported};
use crate::Span;
use crate::ast::{Decl, FailedName, Import, Module, NamespaceDecl};
use crate::source::FileId;
use crate::tree::{Element, Node, NodeKind};
use std::fmt::Debug;
use std::ops::RangeInclusive;

/// What comparing one file found.
#[derive(Debug, Default)]
pub struct Report {
    /// The root kind of each declaration that was lowered and compared.
    pub lowered: Vec<NodeKind>,
    /// Why each declaration that wasn't lowered wasn't.
    pub unsupported: Vec<Unsupported>,
    pub differences: Vec<Difference>,
    /// The single-line bodies parsed again as expressions on their own.
    pub expressions: Expressions,
}

/// The single-line bodies of declarations, each parsed as an expression
/// both ways (`parse_expression` and its tree, lowered).
#[derive(Debug, Default)]
pub struct Expressions {
    pub checked: usize,
    /// How many were lowered and compared (those that didn't parse are
    /// compared by their error alone).
    pub lowered: usize,
    pub unsupported: Vec<Unsupported>,
}

/// A difference between the two routes.
#[derive(Debug)]
pub struct Difference {
    /// Where: the byte offset of the declaration or expression, or 0 for
    /// the whole file.
    pub at: usize,
    /// What differs: "declaration", "diagnostics", "doc links", …
    pub what: &'static str,
    /// The first differing line of each side, with some lines around it.
    pub detail: String,
}

/// Parses `text` both ways and compares the results. With `expressions`,
/// also every declaration body that fits on one line, parsed on its own.
pub fn compare(file: FileId, text: &str, stack: usize, expressions: bool) -> Report {
    let mut report = Report::default();
    let (direct, direct_errors) = crate::parse_module_recovering(file, text, stack);
    let (_, errors, tree) = crate::parse_module_and_tree(file, text, stack);
    if direct_errors != errors {
        report.differ(0, "diagnostics", &direct_errors, &errors);
    }
    let lower = Lower::new(&tree, text, file, &errors);
    for root in tree.decls() {
        let range = match (root.raw_text_range(), root.span()) {
            (Some(raw), _) => raw.start..=raw.end,
            (None, Some(span)) => span.start as usize..=span.end as usize,
            (None, None) => continue,
        };
        match lower.decl(root) {
            Ok(lowered) => {
                report.lowered.push(root.kind());
                let want = Parts::of_module(&direct, &range);
                let got = Parts::of(lowered);
                report.differ(*range.start(), "declaration", &want, &got);
            }
            Err(what) => report.unsupported.push(what),
        }
    }
    let (module, unsupported) = lower.module();
    report.differ(0, "doc links", &direct.doc_links, &module.doc_links);
    if unsupported.is_empty() {
        report.differ(0, "module", &direct, &module);
    }
    if expressions {
        for root in tree.decls() {
            report.bodies(root, file, text, stack);
        }
    }
    report
}

/// What a declaration contributes to its module, in the order the module
/// lists them.
#[derive(Debug, Default)]
struct Parts {
    namespace: Option<NamespaceDecl>,
    imports: Vec<Import>,
    decls: Vec<Decl>,
    failed: Vec<FailedName>,
}

impl Parts {
    fn of(lowered: LoweredDecl) -> Parts {
        let mut parts = Parts::default();
        match lowered {
            LoweredDecl::Namespace(namespace) => parts.namespace = Some(namespace),
            LoweredDecl::Import(import) => parts.imports.push(import),
            LoweredDecl::Decls(decls) => parts.decls = decls,
            LoweredDecl::Failed(failed) => parts.failed = failed,
        }
        parts
    }

    /// The parts of `module` that start in `range`, a declaration's bytes.
    fn of_module(module: &Module, range: &RangeInclusive<usize>) -> Parts {
        let inside = |span: Span| range.contains(&(span.start as usize));
        Parts {
            namespace: module.namespace.clone().filter(|n| inside(n.span)),
            imports: module
                .imports
                .iter()
                .filter(|i| inside(i.span))
                .cloned()
                .collect(),
            decls: module
                .decls
                .iter()
                .filter(|d| inside(d.span()))
                .cloned()
                .collect(),
            failed: module
                .failed
                .iter()
                .filter(|f| inside(f.name.span))
                .cloned()
                .collect(),
        }
    }
}

impl Report {
    /// Records a difference if `want` and `got` print differently.
    fn differ<T: Debug + ?Sized>(&mut self, at: usize, what: &'static str, want: &T, got: &T) {
        let (want, got) = (format!("{want:#?}"), format!("{got:#?}"));
        if want != got {
            self.differences.push(Difference {
                at,
                what,
                detail: first_difference(&want, &got),
            });
        }
    }

    /// Every `Body` under `node` that fits on one line, parsed on its own
    /// both ways.
    fn bodies(&mut self, node: Node<'_>, file: FileId, text: &str, stack: usize) {
        for child in node.child_nodes() {
            self.bodies(child, file, text, stack);
        }
        if node.kind() != NodeKind::Body {
            return;
        }
        // Past the `:=` (or a synonym's `=`).
        let mut parts = node.children().skip(1).filter_map(|child| match child {
            Element::Node(node) => node.span(),
            Element::Leaf(leaf) => Some(leaf.span()),
        });
        let Some(first) = parts.next() else {
            return;
        };
        let last = parts.last().unwrap_or(first);
        let source = &text[first.start as usize..last.end as usize];
        if source.contains('\n') {
            return;
        }
        self.expression(first.start as usize, file, source, stack);
    }

    /// `source` parsed as an expression both ways, and compared.
    fn expression(&mut self, at: usize, file: FileId, source: &str, stack: usize) {
        self.expressions.checked += 1;
        let direct = crate::parse_expression_within(file, source, stack);
        let (parsed, tree) = crate::parse_expression_tree(file, source, stack);
        let (want, got) = match (direct, parsed) {
            (Ok(want), Ok(_)) => {
                let root = tree.decls().next().expect("an expression's root");
                match Lower::new(&tree, source, file, &[]).expression(root) {
                    Ok(got) => {
                        self.expressions.lowered += 1;
                        (format!("{want:#?}"), format!("{got:#?}"))
                    }
                    Err(what) => {
                        self.expressions.unsupported.push(what);
                        return;
                    }
                }
            }
            (want, got) => (format!("{want:#?}"), format!("{:#?}", got.map(|_| ()))),
        };
        if want != got {
            self.differences.push(Difference {
                at,
                what: "expression",
                detail: first_difference(&want, &got),
            });
        }
    }
}

/// The first line where `want` and `got` differ, with a few lines before
/// and after it on each side.
fn first_difference(want: &str, got: &str) -> String {
    let (want, got): (Vec<&str>, Vec<&str>) = (want.lines().collect(), got.lines().collect());
    let at = want
        .iter()
        .zip(&got)
        .position(|(a, b)| a != b)
        .unwrap_or(want.len().min(got.len()));
    let around = |lines: &[&str]| {
        let from = at.saturating_sub(6);
        let to = (at + 4).min(lines.len());
        lines[from..to]
            .iter()
            .map(|line| format!("    {line}"))
            .collect::<Vec<_>>()
            .join("\n")
    };
    format!(
        "  direct, line {}:\n{}\n  lowered:\n{}",
        at + 1,
        around(&want),
        around(&got)
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SourceMap;

    fn report(text: &str) -> Report {
        let file = SourceMap::new().next_id();
        compare(file, text, crate::DEFAULT_STACK, true)
    }

    fn differences(report: &Report) -> Vec<String> {
        report
            .differences
            .iter()
            .map(|d| format!("{} at {}:\n{}", d.what, d.at, d.detail))
            .collect()
    }

    /// Namespaces, imports, tests with leaf bodies and declarations that
    /// fail come out of the lowering as the parser builds them, spans
    /// included; the rest are counted as unsupported, not as differences,
    /// under the first kind the lowering can't lower yet (`def g`'s body).
    #[test]
    fn the_simplest_declarations_lower_as_parsed() {
        let text = "\
namespace Demo
--| See [`x`].
import List (map, filter as f)
import Option (..)

test \"one\" := 1
test \"name\" := x
test \"hole\" := _
test \"type\" := Type
test \"text\" := \"t\"
def g: Nat := f 1
type T = | A
";
        let report = report(text);
        assert_eq!(differences(&report), Vec::<String>::new());
        use NodeKind::*;
        assert_eq!(
            report.lowered,
            [
                Namespace, Import, Import, Test, Test, Test, Test, Test, DataType
            ]
        );
        assert_eq!(report.unsupported, [Unsupported::Kind(App)]);
        // The bodies, on their own; `def g`'s too, not lowered yet.
        assert_eq!(report.expressions.checked, 6);
        assert_eq!(report.expressions.lowered, 5);
    }

    /// A file the lowering lowers whole is compared as a whole module too,
    /// and a lowering that drifts is a difference.
    #[test]
    fn a_whole_module_is_compared_and_a_drift_is_found() {
        let text = "namespace Demo\n--| [`x`]\nimport List (map)\n\ntest \"t\" := x\n";
        let report = report(text);
        assert_eq!(differences(&report), Vec::<String>::new());
        assert!(report.unsupported.is_empty());
        let file = SourceMap::new().next_id();
        let (direct, _) = crate::parse_module_recovering(file, text, crate::DEFAULT_STACK);
        let (_, errors, tree) = crate::parse_module_and_tree(file, text, crate::DEFAULT_STACK);
        let (mut module, _) = Lower::new(&tree, text, file, &errors).module();
        assert_eq!(format!("{direct:#?}"), format!("{module:#?}"));
        assert_eq!(module.doc_links.len(), 1);
        module.imports[0].span = module.imports[0].path.span;
        let mut drifted = Report::default();
        drifted.differ(0, "module", &direct, &module);
        assert_eq!(drifted.differences.len(), 1);
    }

    /// Declarations that don't parse, or don't lex, lower to their names
    /// as failed, marked with their first error; a definition whose header
    /// parsed, to its signature.
    #[test]
    fn failed_declarations_lower_to_their_names() {
        let text = "\
type T = | A (
type U = | B | C \u{7}
test \"x\" :=
def f: Nat := (
";
        let report = report(text);
        assert_eq!(differences(&report), Vec::<String>::new());
        assert_eq!(report.lowered, [NodeKind::Error; 4]);
        assert!(report.unsupported.is_empty());
        // A file whose first declaration isn't at the start of a line is
        // one error and an empty module.
        let unsplit = super::tests::report("  test \"x\" := 1\n--| [`x`]\n");
        assert_eq!(differences(&unsplit), Vec::<String>::new());
        assert_eq!(unsplit.lowered, [NodeKind::Error]);
    }

    /// A single expression's tree has an `Expression` root holding it,
    /// even when one construct covers all of it.
    #[test]
    fn an_expression_has_a_tree() {
        let file = SourceMap::new().next_id();
        let (parsed, tree) = crate::parse_expression_tree(file, "f a", crate::DEFAULT_STACK);
        assert!(parsed.is_ok());
        assert_eq!(tree.dump("f a"), "Expression\n  App\n    f\n    a\n");
        let (parsed, tree) = crate::parse_expression_tree(file, "x", crate::DEFAULT_STACK);
        let root = tree.decls().next().unwrap();
        let lowered = Lower::new(&tree, "x", file, &[]).expression(root).unwrap();
        assert_eq!(format!("{lowered:?}"), format!("{:?}", parsed.unwrap()));
        let (parsed, tree) = crate::parse_expression_tree(file, "(", crate::DEFAULT_STACK);
        assert!(parsed.is_err());
        assert_eq!(tree.decls().next().unwrap().kind(), NodeKind::Error);
    }
}
