//! Spacing between two tokens on one line: rules R3 to R6 and the decisions
//! D1037 and D1039 (docs/proposals/formatter.md §3, §8), copying the source
//! wherever spacing can change meaning (§2.3).

use stitchwort_syntax::Tok;

/// What a token is, where its spelling alone doesn't say. Worked out from
/// the position in the program (see `layout::roles`), the way the parser
/// reads it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub(crate) enum Role {
    #[default]
    Plain,
    /// A `{` or `}` of an effect row, `{IO}` (D1037): tight, unlike a
    /// record's `{ a = 1 }`.
    Row,
    /// A prefix `-`: `-x`.
    Unary,
    /// An infix `-`: `a - b`.
    Binary,
    /// The `-` of `<-` in `rewrite <- h in …`, which touches the `<`.
    RewriteArrow,
}

/// What goes between two tokens written on one line.
pub(crate) enum Gap {
    /// A space or not, decided by a rule.
    Rule(bool),
    /// A space or not, copied from the source because it can change
    /// meaning.
    Kept(bool),
    /// A space or not, copied from the source because no rule covers the
    /// pair: the copy path, counted in the stats.
    Copied(bool),
    /// The source text between them, exactly: the `${` and `}` of an
    /// interpolation, which belong to no token.
    Source,
}

/// The tokens around a gap.
pub(crate) struct Pair<'a> {
    pub left: &'a Tok,
    pub left_role: Role,
    pub right: &'a Tok,
    pub right_role: Role,
    /// The token after `right`, if any.
    pub after: Option<&'a Tok>,
    /// Whether the source had any space between `left` and `right`.
    pub spaced: bool,
}

/// The gap between two tokens.
pub(crate) fn gap(pair: &Pair) -> Gap {
    use Tok::*;
    let (left, right, spaced) = (pair.left, pair.right, pair.spaced);
    if matches!(left, StrStart(_) | StrMid(_)) || matches!(right, StrMid(_) | StrEnd(_)) {
        return Gap::Source;
    }
    // Spacing that changes meaning: `p.name` against `f .name` (a section),
    // `f()` against `f ()`, `<-` in `rewrite` against `< -`, and `@[`.
    let kept = matches!(left, Dot | At)
        || matches!(right, Dot)
        || (*left == LParen && *right == RParen)
        || (*left == LBrace && *right == RBrace)
        || pair.left_role == Role::RewriteArrow
        || pair.right_role == Role::RewriteArrow
        || (*left == RParen && *right == LParen);
    if kept {
        return Gap::Kept(spaced);
    }
    // Minus: `a - b`, `-x`, `a - -b`.
    if *right == Minus && pair.right_role == Role::Binary {
        return Gap::Rule(true);
    }
    if *left == Minus {
        return match pair.left_role {
            Role::Binary => Gap::Rule(true),
            // `- -x`, not the comment `--x`.
            _ => Gap::Rule(*right == Minus),
        };
    }
    // `!x`, `¬x`.
    if *left == Bang {
        return Gap::Rule(false);
    }
    // `exists (x: T) => P`, `∃ x => P`: the keyword stands apart.
    if *left == KwExists {
        return Gap::Rule(true);
    }
    // R6: `a, b`.
    if *right == Comma {
        return Gap::Rule(false);
    }
    if *left == Comma {
        return Gap::Rule(true);
    }
    // R5 and D1037: `{ a = 1 }` for records and `{IO}` for effect rows.
    if *left == LBrace {
        return Gap::Rule(pair.left_role != Role::Row);
    }
    if *right == RBrace {
        return Gap::Rule(pair.right_role != Role::Row);
    }
    // R5: `(a)`, `[a]`.
    if matches!(left, LParen | LBracket) || matches!(right, RParen | RBracket) {
        return Gap::Rule(false);
    }
    // `..base`: the spread touches its name.
    if *left == DotDot {
        return Gap::Kept(spaced);
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
    // D1039: `f(x)` is `f (x)`, which parses the same. `f()` is a call with
    // no arguments, where `f ()` applies `f` to the unit, so it stays.
    if *right == LParen && matches!(left, Lower(_) | Upper(_) | Underscore) {
        return if pair.after == Some(&RParen) {
            Gap::Kept(spaced)
        } else {
            Gap::Rule(true)
        };
    }
    // `Circle { id = "a", … }`: a constructor and the braces naming its
    // fields, in an expression or a pattern (docs/proposals/variant-fields.md
    // §4.5). Whitespace never changes what braces after a name mean.
    if matches!(left, Upper(_)) && *right == LBrace && pair.right_role == Role::Plain {
        return Gap::Rule(true);
    }
    // R4: one space between application arguments, and wherever the source
    // had spaces.
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
            | KwIn
            | NotIn
            | Iff
    )
}
