//! Which `-` is part of a negative argument or a negative numeral
//! (docs/proposals/negative-arguments.md §4.2). The tests are on tokens and
//! their spans alone, so the parser and the formatter share them and can't
//! disagree about where a `-` belongs.

use crate::lexer::{Tok, Token};

/// Whether a token ends an operand, so a `-` after it may be binary or an
/// argument minus. One list for the parser and the formatter.
pub fn closes_operand(tok: &Tok) -> bool {
    use Tok::*;
    matches!(
        tok,
        Lower(_)
            | Upper(_)
            | Num(_)
            | Float(_)
            | Str(_)
            | StrEnd(_)
            | Char(_)
            | RParen
            | RBracket
            | RBrace
            | Underscore
            | Question
            | TypeU
            | Prop
            | KwOmega
            | KwRing
            | KwCases
    )
}

/// Whether a token starts an atom, so a `-` right before it may negate it.
pub fn opens_atom(tok: &Tok) -> bool {
    use Tok::*;
    matches!(
        tok,
        Lower(_)
            | Upper(_)
            | Num(_)
            | Float(_)
            | Str(_)
            | StrStart(_)
            | Char(_)
            | LParen
            | LBracket
            | LBrace
            | Underscore
            | Question
    )
}

/// An argument minus: the `-` at `i` follows a closing token, has a space
/// (or a line break) before it and none after it, and is followed by an atom:
/// `f -2`, `f -x`. The token-level test only. The parser adds that the `-`
/// isn't at a statement stop, so a block line `-y` stays a new statement.
pub fn argument_minus(tokens: &[Token], i: usize) -> bool {
    let (Some(minus), Some(next)) = (tokens.get(i), tokens.get(i + 1)) else {
        return false;
    };
    let Some(before) = i.checked_sub(1).map(|j| &tokens[j]) else {
        return false;
    };
    minus.tok == Tok::Minus
        && closes_operand(&before.tok)
        && (minus.line_start || before.span.end != minus.span.start)
        && !next.line_start
        && minus.span.end == next.span.start
        && opens_atom(&next.tok)
}

/// A negative numeral (D1474): a `-` glued to a number, with no closing token
/// touching it on the left. `-1.abs` is `(-1).abs`; `x-1.abs` is not.
pub fn negative_numeral(tokens: &[Token], i: usize) -> bool {
    let (Some(minus), Some(next)) = (tokens.get(i), tokens.get(i + 1)) else {
        return false;
    };
    minus.tok == Tok::Minus
        && matches!(next.tok, Tok::Num(_) | Tok::Float(_))
        && minus.span.end == next.span.start
        && !next.line_start
        && !i
            .checked_sub(1)
            .map(|j| &tokens[j])
            .is_some_and(|b| closes_operand(&b.tok) && b.span.end == minus.span.start)
}
