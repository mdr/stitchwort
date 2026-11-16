//! The assembly of a module from its declarations.

use super::*;
use crate::SourceMap;
use crate::tree::Mark;

/// The module and errors of `text` with its first declaration's marks
/// changed by `tamper` first, as a parser bug might leave them.
fn lowered_with_marks(
    text: &str,
    tamper: impl FnOnce(&mut Vec<Mark>),
) -> (Module, Vec<Diagnostic>) {
    let file = SourceMap::new().next_id();
    let (lexed, failures) = lex_recovering_with_trivia(file, text);
    let (mut errors, mut groups) = parse_lexed(file, text, DEFAULT_STACK, &lexed.tokens, failures);
    tamper(&mut groups[0].marks);
    let tree = SyntaxFile::build_allowing_misnested(
        lexed.tokens,
        lexed.trivia,
        lexed.eof,
        lexed.bars,
        groups,
    );
    let module = lowered_module(&tree, text, file, DEFAULT_STACK, &mut errors);
    (module, errors)
}

/// A declaration whose marks cross fails with an internal error, rather
/// than being checked as a tree that reads as another statement
/// (SW-3243: `a ∧ b ∧ c → q` read as `a ∧ b ∧ c`).
#[test]
fn a_crossed_mark_fails_its_declaration() {
    let text = "theorem t (a q: Prop): a ∧ a → q := sorry\n\ndef ok: Nat := 1\n";
    let (module, errors) = lowered_with_marks(text, |marks| {
        // From the second `a`, so it crosses the `∧`'s node.
        let arrow = marks.iter_mut().find(|m| m.kind == NodeKind::Arrow);
        arrow.expect("an arrow").start += 2;
    });
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].code, "E-INTERNAL");
    assert!(errors[0].message.contains("cross"), "{}", errors[0].message);
    let failed: Vec<&str> = module.failed.iter().map(|f| f.name.text.as_str()).collect();
    assert_eq!(failed, ["t"]);
    assert_eq!(module.decls.len(), 2, "only `ok`: {:?}", module.decls);
}

/// A slot the lowering reads by its introducing token, with more after
/// it than the parser gives, fails as an internal error instead of
/// leaving the rest unread.
#[test]
fn a_result_type_with_parts_left_over_fails_its_declaration() {
    let text = "theorem t (a q: Prop): a ∧ a → q := sorry\n";
    let (module, errors) = lowered_with_marks(text, |marks| {
        let at = marks.iter().position(|m| m.kind == NodeKind::Arrow);
        marks.remove(at.expect("an arrow"));
    });
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].code, "E-INTERNAL");
    assert!(
        errors[0]
            .message
            .contains("ResultType with parts left unread"),
        "{}",
        errors[0].message
    );
    assert!(module.decls.is_empty(), "{:?}", module.decls);
}
