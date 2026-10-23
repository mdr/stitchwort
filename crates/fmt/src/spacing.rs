//! Spacing between two tokens on one line: rules R3 to R6
//! (docs/proposals/formatter.md §3), and copying the source wherever
//! spacing can change meaning (§2.3).

use stitchwort_syntax::Tok;

/// What goes between two tokens written on one line.
pub(crate) enum Gap {
    /// A space or not, decided by a rule.
    Rule(bool),
    /// A space or not, copied from the source because it can change
    /// meaning.
    Kept(bool),
    /// A space or not, copied from the source because no rule covers the
    /// pair yet: the copy path that later stages remove.
    Copied(bool),
    /// The source text between them, exactly: the `${` and `}` of an
    /// interpolation, which belong to no token.
    Source,
}

/// The gap between `left` and `right`; `spaced` says whether the source had
/// any space between them.
pub(crate) fn gap(left: &Tok, right: &Tok, spaced: bool) -> Gap {
    use Tok::*;
    if matches!(left, StrStart(_) | StrMid(_)) || matches!(right, StrMid(_) | StrEnd(_)) {
        return Gap::Source;
    }
    // Spacing that changes meaning: `p.name` against `f .name` (a section),
    // `f()` against `f ()`, `<-` in `rewrite` against `< -`, `-x` against
    // `a - x` (until unary and binary minus are told apart from the tree),
    // and `@[`.
    let kept = matches!(left, Dot | At | Minus | Bang)
        || matches!(right, Dot | Minus | Bang)
        || (*left == LParen && *right == RParen)
        || (*left == LBrace && *right == RBrace);
    if kept {
        return Gap::Kept(spaced);
    }
    // R6: `a, b`.
    if *right == Comma {
        return Gap::Rule(false);
    }
    if *left == Comma {
        return Gap::Rule(true);
    }
    // R5: `(a)`, `[a]`. R5's `{ a }` is left as written for now: it is
    // right for records, but effect rows are written `{IO}` (see the
    // F1 report).
    if matches!(left, LParen | LBracket) || matches!(right, RParen | RBracket) {
        return Gap::Rule(false);
    }
    if *left == LBrace || *right == RBrace {
        return Gap::Copied(spaced);
    }
    // R3: `(x: Nat)`.
    if *right == Colon {
        return Gap::Rule(false);
    }
    if *left == Colon {
        return Gap::Rule(true);
    }
    // R4: one space around `:=`, `=>`, `->`, `=`, `|` and the binary
    // operators.
    if spaced_operator(left) || spaced_operator(right) {
        return Gap::Rule(true);
    }
    // R4: one space between application arguments, and wherever the source
    // had spaces. Where it had none (`f(x)`, and `f()`, which is a call with
    // no arguments where `f ()` applies `f` to the unit), none.
    if spaced {
        Gap::Rule(true)
    } else {
        Gap::Copied(false)
    }
}

fn spaced_operator(tok: &Tok) -> bool {
    use Tok::*;
    matches!(
        tok,
        ColonEq
            | FatArrow
            | Arrow
            | Equals
            | Pipe
            | OrOr
            | PipeGt
            | AndAnd
            | Plus
            | PlusPlus
            | Star
            | Slash
            | Percent
            | NotEq
            | EqEq
            | Lt
            | Le
            | Gt
            | Ge
    )
}
