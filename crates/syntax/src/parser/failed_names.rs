//! The names a declaration that failed would have declared, read off its
//! tokens, so that the declarations after it that use them aren't reported
//! as using unknown names. The lowering asks for them too
//! (`lower/decls.rs`).

use super::{NO_PARTNER, match_brackets};
use crate::ast::{FailedName, Name};
use crate::lexer::{Tok, Token, lex};
use crate::{FileId, Span};

/// The names of the declaration in `text[range]`, which has a lexical error,
/// read from the part that lexes: the lines before the error's, or else the
/// text before the error itself.
pub(crate) fn failed_names_in(
    file: FileId,
    text: &str,
    range: &std::ops::Range<usize>,
    error_at: Option<Span>,
) -> Vec<FailedName> {
    let error_start = error_at.map_or(range.start, |span| span.start as usize);
    let error_line = text[..error_start].rfind('\n').map_or(0, |n| n + 1);
    let before_error_line = error_line.max(range.start);
    for end in [before_error_line, error_start] {
        if end <= range.start {
            continue;
        }
        let piece = &text[range.start..end];
        // The tokens' positions are in the piece, which starts the same place
        // as in the file only if it's padded.
        let padded = format!("{}{piece}", " ".repeat(range.start));
        if let Ok(tokens) = lex(file, &padded) {
            let names = failed_names_of(&tokens, error_at);
            if !names.is_empty() {
                return names;
            }
        }
    }
    Vec::new()
}

/// The names a declaration that didn't parse would have declared, read off
/// its tokens: after its keyword (`def`, `theorem`, `instance`, `type`,
/// `interface`, `ability`), and for the last three, each name after a `|`
/// outside brackets (a constructor or operation). Best effort: a
/// declaration that broke before its name declares nothing.
fn declared_names_of(group: &[Token]) -> Vec<Name> {
    // Past the attributes before the declaration.
    let matching = match_brackets(group);
    let mut i = 0;
    while group.get(i).map(|t| &t.tok) == Some(&Tok::At)
        && let Some(&close) = matching.get(i + 1)
        && close != NO_PARTNER
    {
        i = close as usize + 1;
    }
    let group = &group[i..];
    let mut i = 0;
    if group.first().map(|t| &t.tok) == Some(&Tok::KwExport) {
        i = 1;
    }
    if group.get(i).map(|t| &t.tok) == Some(&Tok::KwOpaque) {
        i += 1;
    }
    let Some(keyword) = group.get(i).map(|t| &t.tok) else {
        return Vec::new();
    };
    let has_members = match keyword {
        Tok::KwDef | Tok::KwTheorem | Tok::KwInstance => false,
        Tok::KwType | Tok::KwInterface | Tok::KwAbility => true,
        _ => return Vec::new(),
    };
    let name_at = |j: usize| match group.get(j) {
        Some(Token {
            tok: Tok::Lower(text) | Tok::Upper(text),
            span,
            ..
        }) => Some(Name {
            text: text.clone(),
            span: *span,
        }),
        _ => None,
    };
    let mut names: Vec<Name> = name_at(i + 1).into_iter().collect();
    if has_members {
        let matching = match_brackets(group);
        let mut depth = 0usize;
        for (j, token) in group.iter().enumerate() {
            match token.tok {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => depth = depth.saturating_sub(1),
                Tok::Pipe if depth == 0 => {
                    // Past a constructor's attributes, `| @[js.name "X"] C`.
                    let mut k = j + 1;
                    while group.get(k).map(|t| &t.tok) == Some(&Tok::At)
                        && let Some(&close) = matching.get(k + 1)
                        && close != NO_PARTNER
                    {
                        k = close as usize + 1;
                    }
                    names.extend(name_at(k));
                }
                _ => {}
            }
        }
    }
    names
}

/// The names `group` would declare, marked as failed at the first error of
/// the declaration (`error_at`).
pub(crate) fn failed_names_of(group: &[Token], error_at: Option<Span>) -> Vec<FailedName> {
    declared_names_of(group)
        .into_iter()
        .map(|name| FailedName { name, error_at })
        .collect()
}
