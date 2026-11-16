//! For the lowering's tests: what the lowering makes of a file, declaration
//! by declaration, and of each one-line body, type and default parsed on
//! its own. What the trees mean is held by the hash snapshots.

use super::{Lower, Unsupported};
use crate::source::FileId;
use crate::tree::{Element, Node, NodeKind};
use crate::{Diagnostic, SourceMap};

/// What lowering one file gave.
#[derive(Debug, Default)]
pub(crate) struct Report {
    /// The root kind of each declaration that was lowered (not those the
    /// lowering refused, whose errors are among `errors`).
    pub(crate) lowered: Vec<NodeKind>,
    /// Why each declaration that wasn't lowered wasn't.
    pub(crate) unsupported: Vec<Unsupported>,
    /// The file's diagnostics.
    pub(crate) errors: Vec<Diagnostic>,
    /// The single-line bodies, types and defaults parsed again as
    /// expressions on their own.
    pub(crate) expressions: Expressions,
}

/// The single-line bodies, result types and parameter defaults of
/// declarations, each parsed as an expression on its own.
#[derive(Debug, Default)]
pub(crate) struct Expressions {
    pub(crate) checked: usize,
    /// How many parsed and were lowered.
    pub(crate) lowered: usize,
    pub(crate) unsupported: Vec<Unsupported>,
    /// The diagnostics of those that didn't parse.
    pub(crate) errors: Vec<Diagnostic>,
}

/// Parses and lowers `text`, and every one-line body, result type and
/// default in it on its own.
pub(crate) fn report(text: &str) -> Report {
    report_within(text, crate::DEFAULT_STACK)
}

/// [`report`] with a stack of `stack` bytes.
pub(crate) fn report_within(text: &str, stack: usize) -> Report {
    let file = SourceMap::new().next_id();
    let (_, errors, tree) = crate::parse_module_and_tree(file, text, stack);
    let mut report = Report::default();
    let lower = Lower::new(&tree, text, file, &errors).with_stack(stack);
    for root in tree.decls() {
        match lower.decl(root) {
            Ok(_) => report.lowered.push(root.kind()),
            // An error in the program, among `errors`.
            Err(Unsupported::Invalid(_)) => {}
            Err(what) => report.unsupported.push(what),
        }
    }
    for root in tree.decls() {
        report.bodies(root, file, text, stack);
    }
    report.errors = errors;
    report
}

impl Report {
    /// Every `Body`, `ResultType` and `Default` under `node` that fits on
    /// one line, parsed on its own: the types are where most arrows and
    /// annotations are.
    fn bodies(&mut self, node: Node<'_>, file: FileId, text: &str, stack: usize) {
        for child in node.child_nodes() {
            self.bodies(child, file, text, stack);
        }
        if !matches!(
            node.kind(),
            NodeKind::Body | NodeKind::ResultType | NodeKind::Default
        ) {
            return;
        }
        // Past the `:=` (or a synonym's `=`, a type's `:`).
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
        self.expressions.checked += 1;
        let (parsed, tree) = crate::parse_expression_tree(file, source, stack);
        match parsed {
            Ok(_) => {
                let root = tree.decls().next().expect("an expression's root");
                match Lower::new(&tree, source, file, &[])
                    .with_stack(stack)
                    .expression(root)
                {
                    Ok(_) => self.expressions.lowered += 1,
                    Err(what) => self.expressions.unsupported.push(what),
                }
            }
            Err(error) => self.expressions.errors.push(error),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Namespaces, imports, tests, definitions and data types lower, and
    /// each one-line body and type parsed on its own does too.
    #[test]
    fn the_simplest_declarations_lower() {
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
def g: Nat -> Nat := x => x
type T = | A
";
        let report = report(text);
        assert_eq!(report.errors, []);
        use NodeKind::*;
        assert_eq!(
            report.lowered,
            [
                Namespace, Import, Import, Test, Test, Test, Test, Test, Def, DataType
            ]
        );
        assert_eq!(report.unsupported, []);
        // The bodies, on their own, and `def g`'s type.
        assert_eq!(report.expressions.checked, 7);
        assert_eq!(report.expressions.lowered, 7);
    }

    /// Declarations that don't parse, or don't lex, lower to their names
    /// as failed, marked with their first error; a definition whose body
    /// broke is recovered in, and lowers to its signature and an equation.
    #[test]
    fn failed_declarations_lower_to_their_names() {
        let text = "\
type T = | A (
type U = | B | C \u{7}
test \"x\" :=
def f: Nat := (
";
        let report = report(text);
        assert_eq!(report.errors.len(), 4, "{:#?}", report.errors);
        let error = NodeKind::Error;
        assert_eq!(report.lowered, [error, error, error, NodeKind::Def]);
        assert!(report.unsupported.is_empty());
        let file = SourceMap::new().next_id();
        let (module, _, _) = crate::parse_module_and_tree(file, text, crate::DEFAULT_STACK);
        let failed: Vec<_> = module.failed.iter().map(|f| f.name.text.as_str()).collect();
        assert_eq!(failed, ["T", "A", "U", "B", "C"]);
        assert_eq!(module.decls.len(), 2, "f's signature and equation");
        // A file whose first declaration isn't at the start of a line is
        // one error and an empty module.
        let unsplit = super::report("  test \"x\" := 1\n--| [`x`]\n");
        assert_eq!(unsplit.errors.len(), 1);
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
