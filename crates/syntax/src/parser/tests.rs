//! The parser on its own.

use super::*;
use crate::SourceMap;
use crate::lexer::lex;

/// A parser over `text`'s tokens, recording marks.
fn with_parser<T>(text: &str, run: impl FnOnce(&mut Parser<'_>) -> T) -> T {
    let file = SourceMap::new().next_id();
    let tokens = lex(file, text).unwrap();
    let mut parser = Parser::new(
        &tokens,
        file,
        text.len(),
        StackLimit::from_here(DEFAULT_STACK),
    );
    run(&mut parser)
}

/// `recover_to` puts back every mode, and leaves the position and the
/// finished marks.
#[test]
fn recover_to_restores_the_modes() {
    with_parser("a + b * c", |parser| {
        parser.modes.limit = Some(2);
        let snapshot = parser.snapshot();
        parser.modes = Modes {
            in_list: true,
            limit: Some(4),
            allow: Some(1),
            calc_depth: 3,
            rewrite_rule: Some(1),
            guard_start: Some(2),
            rewrite_at: true,
            let_value: Some(0),
            recover: true,
            section_head: Some(1),
        };
        parser.pos = 3;
        parser.record(2, NodeKind::App);
        parser.recover_to(snapshot);
        assert_eq!(
            format!("{:?}", parser.modes),
            format!("{:?}", snapshot.modes)
        );
        assert_eq!(parser.modes.limit, Some(2));
        assert_eq!(parser.pos, 3);
        assert_eq!(parser.marks.len(), 1);
    });
}

/// An error recovered from fails the entry points that give one error
/// as if it had unwound, ahead of one that did.
#[test]
fn strict_fails_on_an_error_recovered_from() {
    with_parser("a b", |parser| {
        assert!(parser.strict(Ok(())).is_ok());
        parser.report(RecoveryPoint::Body, error(parser.here(), "first"));
        parser.report(RecoveryPoint::Body, error(parser.here(), "second"));
        let unwound: Result<()> = Err(Box::new(error(parser.here(), "unwound")));
        let failed = parser.strict(unwound).unwrap_err();
        assert_eq!(failed.message, "first");
        let failed = parser.strict(Ok(())).unwrap_err();
        assert_eq!(failed.message, "second");
        assert!(parser.strict(Ok(())).is_ok());
    });
}
