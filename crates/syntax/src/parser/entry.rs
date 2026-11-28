//! The public entry points: lex, parse, build the lossless tree, lower it.
//! Also the assembly of a file from its declarations (which come first, which
//! error is shown) and the rule for which error wins when the parser and the
//! lowering both found one in a declaration ([`lowered_module`]).

use crate::ast::{Expr, Module, NamespaceDecl};
use crate::lexer::{LexFailure, Tok, Token, Trivia, lex_recovering_with_trivia, lex_with_trivia};
use crate::lower::{Lower, LoweredDecl, Unsupported};
use crate::stack::StackLimit;
use crate::tree::{DeclMarks, NodeKind, SyntaxFile};
use crate::{Diagnostic, FileId, Span};

use super::declarations::misplaced_attributes;
use super::failed_names::failed_names_of;
use super::{Parsed, Parser, Result, error, nested_too_deeply, split_decls};
use crate::DEFAULT_STACK;

pub fn parse_module(file: FileId, text: &str) -> std::result::Result<Module, Vec<Diagnostic>> {
    parse_module_within(file, text, DEFAULT_STACK)
}

pub fn parse_expression(file: FileId, text: &str) -> Parsed<Expr> {
    parse_expression_within(file, text, DEFAULT_STACK)
}

/// Parses a module, using at most `stack` bytes of stack: a program nested
/// more deeply than that allows is an `E-RESOURCE` error, not a crash.
pub fn parse_module_within(
    file: FileId,
    text: &str,
    stack: usize,
) -> std::result::Result<Module, Vec<Diagnostic>> {
    match parse_module_recovering(file, text, stack) {
        (module, errors) if errors.is_empty() => Ok(module),
        (_, errors) => Err(errors),
    }
}

/// Like [`parse_module_within`], but keeps going after a syntax error
/// (docs/proposals/language-server.md, stage 0a). Parsing recovers at
/// declaration boundaries: a declaration that doesn't parse is left out of
/// the module, and its names (found by scanning its tokens) are in
/// `Module::failed`, so the declarations after it that use them aren't
/// reported as using unknown names. A `def` or `theorem` whose header
/// parsed and whose body didn't is kept instead, as its signature with
/// `syntax_error` set and no equations. Returns the declarations that did
/// parse and every error, in file order. A lexical error is recovered from
/// the same way: the declaration holding it (see [`crate::lexer::lex_recovering`]) is
/// left out, its names are in `failed`, and the rest of the file parses. A
/// first declaration not at the start of a line stops everything: the
/// module is empty.
pub fn parse_module_recovering(
    file: FileId,
    text: &str,
    stack: usize,
) -> (Module, Vec<Diagnostic>) {
    let (module, errors, _) = parse_module_and_tree(file, text, stack);
    (module, errors)
}

/// [`parse_tokens`] on what [`lex_recovering_with_trivia`] read, with the
/// declarations that didn't lex (`failures`) recovered from: their errors
/// among the others in file order, and each an `Error` root over its raw
/// text among the declarations' marks.
fn parse_lexed(
    file: FileId,
    text: &str,
    stack: usize,
    tokens: &[Token],
    failures: Vec<LexFailure>,
) -> (Vec<Diagnostic>, Vec<DeclMarks>) {
    let (mut errors, mut trees) = parse_tokens(file, text, stack, tokens);
    let raw_at = trees.len();
    for failure in failures {
        errors.push(failure.error);
        // At the first token after it, which the blanking left where it was.
        let next = tokens.partition_point(|t| (t.span.start as usize) < failure.range.start);
        trees.push(DeclMarks {
            tokens: next as u32..next as u32,
            root: NodeKind::Error,
            marks: Vec::new(),
            raw: Some(failure.range.start as u32..failure.range.end as u32),
            signature_kept: false,
            recovered: Vec::new(),
        });
    }
    errors.sort_by_key(|error| error.primary_span().map(|span| span.start));
    if trees.len() > raw_at {
        // Into file order: a declaration that didn't lex goes before the one
        // starting at the token after it. The sort is stable, so the raw
        // ones keep their order among themselves.
        trees.sort_by_key(|tree| (tree.tokens.start, tree.raw.is_none()));
    }
    (errors, trees)
}

/// The lossless tree of a file ([`crate::tree`]), from the same parse as
/// [`parse_module_recovering`]'s, using at most `stack` bytes of stack. A
/// declaration that doesn't parse is an `Error` node, holding the nodes of
/// what parsed before the error; one that doesn't lex is an `Error` node
/// holding its raw text ([`crate::tree::Node::raw_text_range`]).
pub fn parse_tree(file: FileId, text: &str, stack: usize) -> SyntaxFile {
    parse_with_tree(file, text, stack).1
}

/// [`parse_module_recovering`]'s module and errors, and the lossless tree,
/// from one parse: the module is the tree's lowering ([`crate::lower`]).
pub fn parse_module_and_tree(
    file: FileId,
    text: &str,
    stack: usize,
) -> (Module, Vec<Diagnostic>, SyntaxFile) {
    let (mut errors, tree) = parse_with_tree(file, text, stack);
    let module = lowered_module(&tree, text, file, stack, &mut errors);
    (module, errors, tree)
}

/// The module `tree` lowers to, with `errors` (the parse's) given the
/// lowering's own: a declaration the lowering refuses
/// ([`Unsupported::Invalid`], a check on what was written, such as a
/// repeated parameter) or can't lower is failed, like one that didn't parse,
/// with that error in place of any the parser found in it later.
fn lowered_module(
    tree: &SyntaxFile,
    text: &str,
    file: FileId,
    stack: usize,
    errors: &mut Vec<Diagnostic>,
) -> Module {
    let lower = Lower::new(tree, text, file, errors).with_stack(stack);
    let (mut module, unlowered) = lower.module();
    if unlowered.is_empty() {
        return module;
    }
    let roots: Vec<_> = tree.decls().collect();
    let kept: Vec<bool> = unlowered
        .iter()
        .map(|(i, what)| lower.signature_despite(roots[*i], what).is_some())
        .collect();
    for ((i, what), kept) in unlowered.into_iter().zip(kept) {
        let tokens = &tree.tokens()[roots[i].token_range()];
        let at = tokens.first().map_or(Span::NOWHERE, |token| token.span);
        let error = unlowered_error(what, at);
        // Without recovery a declaration reports its first error only.
        if let (Some(from), Some(range)) = (error.primary_span(), roots[i].span()) {
            errors.retain(|e| {
                e.primary_span()
                    .is_none_or(|s| s.start < from.start || s.start >= range.end)
            });
        }
        if !kept {
            module
                .failed
                .extend(failed_names_of(tokens, error.primary_span()));
        }
        errors.push(error);
    }
    module.failed.sort_by_key(|failed| failed.name.span.start);
    errors.sort_by_key(|error| error.primary_span().map(|span| span.start));
    module
}

/// The error for a declaration or expression starting at `at` that parsed
/// and that the lowering refused or couldn't lower.
fn unlowered_error(what: Unsupported, at: Span) -> Diagnostic {
    match what {
        Unsupported::TooDeep(span) => nested_too_deeply(span),
        Unsupported::Invalid(error) => *error,
        what => Diagnostic::error(
            "E-INTERNAL",
            format!("internal error: the parser couldn't build this ({what})"),
        )
        .with_label(at, "in this declaration")
        .with_note("this is a bug in the compiler's parser, not in your program"),
    }
}

/// The parse's errors and the lossless tree.
pub(crate) fn parse_with_tree(
    file: FileId,
    text: &str,
    stack: usize,
) -> (Vec<Diagnostic>, SyntaxFile) {
    let (lexed, failures) = lex_recovering_with_trivia(file, text);
    let (errors, groups) = parse_lexed(file, text, stack, &lexed.tokens, failures);
    let tree = SyntaxFile::build(lexed.tokens, lexed.trivia, lexed.eof, lexed.bars, groups);
    (errors, tree)
}

/// How much of the `stack` a parse may use the parser lets it use: half.
/// The lowering after it gets all of it, since for some shapes it takes
/// more stack per level than the parser, whose frames hold no trees
/// (`f (f (…))` and `(.f (.f …))` up to 1.55 times as much at the
/// parser's deepest in debug builds, 1.2 in release ones, SW-3213), so
/// what parses always lowers. Half still parses 18,000 nested brackets in
/// release builds.
fn parser_limit(stack: usize) -> StackLimit {
    StackLimit::from_here(stack / 2)
}

/// Parses a file's tokens, declaration by declaration, recovering as
/// [`parse_module_recovering`] says, into each declaration's marks for the
/// lossless tree.
fn parse_tokens(
    file: FileId,
    text: &str,
    stack: usize,
    tokens: &[Token],
) -> (Vec<Diagnostic>, Vec<DeclMarks>) {
    let limit = parser_limit(stack);
    // What came before: a namespace line, an import, a declaration that
    // parsed (or kept its signature).
    let (mut namespace, mut imports, mut decls) = (false, false, false);
    let mut errors: Vec<Diagnostic> = Vec::new();
    let mut trees = Vec::new();
    let all = 0..tokens.len() as u32;
    let groups = match split_decls(tokens) {
        Ok(groups) => groups,
        Err(d) => {
            trees.push(DeclMarks {
                tokens: all,
                root: NodeKind::Error,
                marks: Vec::new(),
                raw: None,
                signature_kept: false,
                recovered: Vec::new(),
            });
            return (vec![*d], trees);
        }
    };
    // The groups run to the end of `tokens`; any tokens before the first
    // start no declaration.
    let mut offset = (tokens.len() - groups.iter().map(|group| group.len()).sum::<usize>()) as u32;
    if offset > 0 {
        trees.push(DeclMarks {
            tokens: 0..offset,
            root: NodeKind::Error,
            marks: Vec::new(),
            raw: None,
            signature_kept: false,
            recovered: Vec::new(),
        });
    }
    for group in groups {
        let mut parser = Parser::new(group, file, text.len(), limit);
        // What the declaration turned out to be, once it has parsed.
        let mut root = NodeKind::Error;
        let mut signature_kept = false;
        'group: {
            // The attributes before the declaration, which belong to it.
            let first = match parser.attributes() {
                Ok(first) => first,
                Err(diagnostic) => {
                    errors.push(*diagnostic);
                    break 'group;
                }
            };
            if let Some(first) = first {
                let refused = match parser.peek() {
                    None => Some(
                        Diagnostic::error(
                            "E-PARSE",
                            "attributes must be followed by the declaration they apply to",
                        )
                        .with_label(first.span, "nothing follows these attributes"),
                    ),
                    Some(Tok::KwNamespace) => {
                        Some(misplaced_attributes(&first, "a namespace line"))
                    }
                    Some(Tok::KwImport) => Some(misplaced_attributes(&first, "an import")),
                    Some(Tok::KwTest) => Some(misplaced_attributes(&first, "a test")),
                    Some(Tok::KwAbility) => Some(misplaced_attributes(&first, "an ability")),
                    _ => None,
                };
                if let Some(diagnostic) = refused {
                    errors.push(diagnostic);
                    break 'group;
                }
            }
            if parser.peek() == Some(&Tok::KwNamespace) {
                if namespace {
                    errors.push(
                    error(group[0].span, "a file has only one namespace line").with_note(
                        "everything in a file goes in the namespace on its first line; to use another namespace, import from it or write its name in full",
                    ),
                );
                    break 'group;
                }
                if imports || decls {
                    let name = parser.namespace().ok();
                    let message =
                        "the namespace line must come first, before imports and declarations";
                    let mut diagnostic = Diagnostic::error("E-NAMESPACE-NOT-FIRST", message)
                        .with_label(group[0].span, message);
                    if let Some(name) = name {
                        diagnostic = diagnostic
                            .with_note(format!("move `namespace {name}` to the top of the file"));
                    }
                    errors.push(diagnostic);
                    break 'group;
                }
                let parsed = parser.namespace().and_then(|_| parser.finish());
                match parser.strict(parsed) {
                    Ok(()) => {
                        namespace = true;
                        root = NodeKind::Namespace;
                    }
                    Err(diagnostic) => errors.push(*diagnostic),
                }
                break 'group;
            }
            if parser.peek() == Some(&Tok::KwImport) {
                if decls {
                    errors.push(
                        error(group[0].span, "imports go at the top of the file")
                            .with_note("move it before the first declaration"),
                    );
                    break 'group;
                }
                let parsed = parser.import().and_then(|()| parser.finish());
                match parser.strict(parsed) {
                    Ok(()) => {
                        imports = true;
                        root = NodeKind::Import;
                    }
                    Err(diagnostic) => errors.push(*diagnostic),
                }
                break 'group;
            }
            // A `def` or `theorem` whose header parses is kept if its body
            // doesn't, so it can stand in for its statement
            // (docs/proposals/tests-with-errors.md §3.3): the lowering makes
            // its signature from the header's nodes.
            let keep = matches!(
                parser.peek(),
                Some(Tok::KwDef | Tok::KwTheorem | Tok::KwExport | Tok::KwOpaque)
            );
            parser.keep_header = keep;
            let parsed = match parser.decl() {
                Ok(kind) => match parser.finish() {
                    Ok(()) => Ok(kind),
                    // Something after a definition that parsed whole.
                    Err(diagnostic) => Err((
                        *diagnostic,
                        keep && matches!(kind, NodeKind::Def | NodeKind::Theorem),
                    )),
                },
                Err(diagnostic) => Err((*diagnostic, parser.header_kept)),
            };
            // A definition the parser recovered in is kept with its own
            // kind: its errors are in `parser.errors`, and its recoveries
            // make it failed (`Node::recoveries`).
            match parsed {
                Ok(kind) => {
                    root = kind;
                    decls = true;
                }
                Err((diagnostic, kept)) => {
                    errors.push(diagnostic);
                    if kept {
                        decls = true;
                        signature_kept = true;
                    }
                }
            }
        }
        errors.append(&mut parser.errors);
        let end = offset + group.len() as u32;
        trees.push(DeclMarks {
            tokens: offset..end,
            root,
            marks: std::mem::take(&mut parser.marks),
            raw: None,
            signature_kept,
            recovered: std::mem::take(&mut parser.recovered),
        });
        offset += group.len() as u32;
    }
    (errors, trees)
}

/// Reads only a file's namespace line: `Some` if the file's first
/// declaration group is one, `None` if it starts with anything else. For
/// finding a file's namespace when the rest of it doesn't parse or doesn't
/// lex (the declarations that don't lex are left out, as in
/// [`parse_module_recovering`]).
pub fn parse_namespace_line(
    file: FileId,
    text: &str,
    stack: usize,
) -> Parsed<Option<NamespaceDecl>> {
    namespace_line(file, text, stack).map_err(|d| *d)
}

fn namespace_line(file: FileId, text: &str, stack: usize) -> Result<Option<NamespaceDecl>> {
    let limit = StackLimit::from_here(stack);
    let (lexed, _) = lex_recovering_with_trivia(file, text);
    let groups = split_decls(&lexed.tokens)?;
    let Some(group) = groups.first() else {
        return Ok(None);
    };
    let mut parser = Parser::new(group, file, text.len(), limit);
    if parser.peek() != Some(&Tok::KwNamespace) {
        return Ok(None);
    }
    let parsed = parser.namespace().and_then(|_| parser.finish());
    parser.strict(parsed)?;
    // The groups run to the end of the tokens.
    let start = lexed.tokens.len() - groups.iter().map(|group| group.len()).sum::<usize>();
    let root = DeclMarks {
        tokens: start as u32..(start + group.len()) as u32,
        root: NodeKind::Namespace,
        marks: std::mem::take(&mut parser.marks),
        raw: None,
        signature_kept: false,
        recovered: Vec::new(),
    };
    let tree = SyntaxFile::build(
        lexed.tokens,
        lexed.trivia,
        lexed.eof,
        lexed.bars,
        vec![root],
    );
    let root = tree.decls().next().expect("the namespace line's root");
    match Lower::new(&tree, text, file, &[]).decl(root) {
        Ok(LoweredDecl::Namespace(decl)) => Ok(Some(decl)),
        Ok(_) => unreachable!("a namespace root lowers to a namespace"),
        Err(what) => {
            let at = tree.tokens()[root.token_range()]
                .first()
                .map_or(Span::NOWHERE, |token| token.span);
            Err(unlowered_error(what, at).into())
        }
    }
}

/// Parses an expression, using at most `stack` bytes of stack.
pub fn parse_expression_within(file: FileId, text: &str, stack: usize) -> Parsed<Expr> {
    parse_expression_tree(file, text, stack).0
}

/// [`parse_expression_within`]'s result, and the expression's lossless tree:
/// one root, an [`NodeKind::Expression`] holding the expression if it
/// parsed, an `Error` if it didn't, over its raw text if it didn't lex.
pub fn parse_expression_tree(file: FileId, text: &str, stack: usize) -> (Parsed<Expr>, SyntaxFile) {
    parse_expression_tree_as(file, text, stack, false)
}

/// Parses text read as a function's result type: [`parse_expression_within`]
/// except that a leading `{…}` is an ability row where it is not a record
/// literal or update (`{Parse _ | _} Nat`, `{_} Int`). Only search patterns
/// use it; program source is parsed as before.
pub fn parse_result_type_within(file: FileId, text: &str, stack: usize) -> Parsed<Expr> {
    parse_expression_tree_as(file, text, stack, true).0
}

fn parse_expression_tree_as(
    file: FileId,
    text: &str,
    stack: usize,
    result_type: bool,
) -> (Parsed<Expr>, SyntaxFile) {
    let limit = parser_limit(stack);
    let lexed = match lex_with_trivia(file, text) {
        Ok(lexed) => lexed,
        Err(error) => {
            let root = DeclMarks {
                tokens: 0..0,
                root: NodeKind::Error,
                marks: Vec::new(),
                raw: Some(0..text.len() as u32),
                signature_kept: false,
                recovered: Vec::new(),
            };
            let tree = SyntaxFile::build(
                Vec::new(),
                Vec::new(),
                Trivia::default(),
                Vec::new(),
                vec![root],
            );
            return (Err(error), tree);
        }
    };
    let mut parser = Parser::new(&lexed.tokens, file, text.len(), limit);
    parser.expression = true;
    let parsed = if result_type {
        parser.result_type()
    } else {
        parser.expr()
    }
    .and_then(|()| parser.finish());
    let parsed = parser.strict(parsed).map_err(|d| *d);
    let root = DeclMarks {
        tokens: 0..lexed.tokens.len() as u32,
        root: if parsed.is_ok() {
            NodeKind::Expression
        } else {
            NodeKind::Error
        },
        marks: std::mem::take(&mut parser.marks),
        raw: None,
        signature_kept: false,
        recovered: Vec::new(),
    };
    let tree = SyntaxFile::build(
        lexed.tokens,
        lexed.trivia,
        lexed.eof,
        lexed.bars,
        vec![root],
    );
    if let Err(error) = parsed {
        return (Err(error), tree);
    }
    let root = tree.decls().next().expect("an expression's root");
    let lowered = Lower::new(&tree, text, file, &[])
        .with_stack(stack)
        .expression(root)
        .map_err(|what| {
            let at = tree
                .tokens()
                .first()
                .map_or(Span::NOWHERE, |token| token.span);
            unlowered_error(what, at)
        });
    (lowered, tree)
}

#[cfg(test)]
mod tests;
