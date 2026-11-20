//! Spacing between two tokens on one line: rules R3 to R6 and the decisions
//! D1037 and D1039 (docs/proposals/formatter.md §3, §8; still in force), copying the source
//! wherever spacing can change meaning (§2.3).

use stitchwort_syntax::{
    Tok, Token, argument_minus, argument_prefix, closes_operand, opens_atom, record_braces,
};

/// What a token is, where its spelling alone doesn't say. Worked out from
/// the position in the program (see [`roles`]), the way the parser
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
    /// A prefix `-` before a numeral that heads an application: `- 2 n`.
    /// The gap after it is kept, since `-2 n` applies the negative numeral
    /// instead (SW-3716).
    UnaryAppliedNumeral,
    /// An infix `-`: `a - b`.
    Binary,
    /// An argument minus: `f -2`, a space before and none after it. The gap
    /// before it is kept, since `f-2` and `f - 2` are subtractions.
    ArgumentMinus,
    /// A `-` starting a statement, right after a line that ends an operand:
    /// its gap after is kept, since `-y` there could read as an argument.
    StatementMinus,
    /// The `-` of `<-` in `rewrite <- h then …`, which touches the `<`.
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
    /// The source text between them, exactly: inside an interpolated text,
    /// where the gaps are text or the writer's own spacing in `${ x }`.
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
    if matches!(left, StrStart(_) | StrMid(_) | InterpOpen | InterpClose)
        || matches!(right, StrMid(_) | StrEnd(_) | InterpOpen | InterpClose)
    {
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
        || pair.right_role == Role::ArgumentMinus
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
            Role::StatementMinus => Gap::Kept(spaced),
            // `- 2 n` negates the application; `-2 n` applies the negative
            // numeral instead, so keep the source's gap (SW-3716).
            Role::UnaryAppliedNumeral => Gap::Kept(spaced),
            // `- 1.abs` is not `-1.abs` (a negative numeral, D1474).
            _ if matches!(right, Num(_) | Float(_)) && pair.after == Some(&Dot) => {
                Gap::Kept(spaced)
            }
            // `- -x`, not the comment `--x`.
            _ => Gap::Rule(*right == Minus),
        };
    }
    // `!x`, `¬x`.
    if *left == Bang {
        return Gap::Rule(false);
    }
    // `exists (x: T) => P`, `∃ x => P`, `∀ x => P`: the keyword stands apart.
    if matches!(left, KwExists | KwForall) {
        return Gap::Rule(true);
    }
    // `(let x := e; body)`: the `;` touches the value, a space follows.
    if *right == Semi {
        return Gap::Rule(false);
    }
    if *left == Semi {
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
        // `[x, ..xs]`, in a pattern or an expression (list-spread.md).
        if matches!(right, Lower(_) | Upper(_) | LParen | LBracket) {
            return Gap::Rule(false);
        }
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
    // R4: adjacent call elements get a space, glued or not (`f[x]`, `]a`,
    // `2a`, `)[`): the lexer splits them and the tree is the same with a
    // space, so the formatters agree (SW-4459). `)(` is kept above.
    if (closes_operand(left) || *left == KwByWalking)
        && opens_atom(right)
        && !(*left == RParen && *right == LParen)
    {
        return Gap::Rule(true);
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
            | DotDotLt
            | DotDotEq
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

/// The role of each token (see [`Role`]).
pub(crate) fn roles(tokens: &[Token]) -> Vec<Role> {
    let mut roles = vec![Role::Plain; tokens.len()];
    let mut braces: Vec<bool> = Vec::new();
    // The column of the first token of the line before the current one.
    let (mut line_col, mut prev_line_col) = (0u32, 0u32);
    for (k, t) in tokens.iter().enumerate() {
        if t.line_start {
            prev_line_col = line_col;
            line_col = t.column;
        }
        match t.tok {
            Tok::LBrace => {
                // Only a function's result type has a row, and it follows
                // the `:` or `->` before it (`result_type` in the parser),
                // unless the braces are a record (a theorem's statement may
                // start with one, `{ p | x = 3 }.x = 3`).
                let row = k > 0
                    && matches!(tokens[k - 1].tok, Tok::Colon | Tok::Arrow)
                    && !record_braces(tokens, k);
                if row {
                    roles[k] = Role::Row;
                }
                braces.push(row);
            }
            Tok::RBrace => {
                if braces.pop().unwrap_or(false) {
                    roles[k] = Role::Row;
                }
            }
            Tok::Minus => {
                let before = k.checked_sub(1).map(|j| &tokens[j]);
                let role = if before.is_some_and(|b| {
                    b.tok == Tok::Lt && b.span.end == t.span.start && !t.line_start
                }) {
                    Role::RewriteArrow
                } else {
                    let operand = before.is_some_and(|b| closes_operand(&b.tok));
                    // A line starting with `-` at or left of the line above
                    // starts a statement, so the `-` is a prefix.
                    let continues = !t.line_start || t.column > prev_line_col;
                    if operand && continues && argument_minus(tokens, k) {
                        // `f -2`: the parser's own test, so the two agree.
                        Role::ArgumentMinus
                    } else if operand && continues {
                        Role::Binary
                    } else if operand {
                        // A statement `- y` after an operand: written
                        // `-y` it would read as an argument minus.
                        Role::StatementMinus
                    } else {
                        Role::Unary
                    }
                };
                roles[k] = if role == Role::Unary && numeral_application(tokens, k) {
                    Role::UnaryAppliedNumeral
                } else {
                    role
                };
            }
            _ => {}
        }
    }
    roles
}

/// Whether the numeral after the `-` at `k` is the head of an application:
/// `- 2 n` is `Neg (App 2 n)`, where `-2 n` applies the negative numeral `-2`
/// instead (SW-3716). The argument may sit on a later source line; the
/// printer may still put it on the numeral's line. It may also be an
/// argument prefix, as in `- 1 -2` (SW-3771): glued, the first `-` and `1`
/// become a negative numeral and the `-2` becomes its argument.
fn numeral_application(tokens: &[Token], k: usize) -> bool {
    let (Some(numeral), Some(after)) = (tokens.get(k + 1), tokens.get(k + 2)) else {
        return false;
    };
    matches!(numeral.tok, Tok::Num(_) | Tok::Float(_))
        && (opens_atom(&after.tok) || argument_prefix(tokens, k + 2))
}
