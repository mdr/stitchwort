//! Declarations (docs/proposals/declaration-syntax.md): `def` and
//! `theorem` headers with typed parameters, then a `:=` body or arms,
//! lowered to a signature and its equations (§2.3); `test "n" := e`;
//! `export def`; and handler clauses `| op x, k => body` (§2.11).
//!
//! Each function here is `#[inline(never)]` or only called from one that
//! is: the expression parser's recursive functions must keep small stack
//! frames, since the nesting limit is measured in stack.

use super::{Parser, Result, describe, error, has_absurd};
use crate::ast::{BinOp, Clause, Decl, Expr, Name, Pattern};
use crate::lexer::Tok;
use crate::{Diagnostic, Span};

/// A parameter written in a header, before the colon.
enum Param {
    /// `(x y : A)`; with `implicit`, `[x y : A]`; with `auto` too,
    /// `[auto h : P]`.
    Named {
        names: Vec<Name>,
        ty: Expr,
        implicit: bool,
        auto: bool,
        span: Span,
    },
    /// `()`: a parameter of type `()` that isn't used. It's matched by `_`
    /// (§2.3), not by the pattern `()`, which would make an arm absurd.
    Unit(Span),
}

impl Parser<'_> {
    /// A declaration: a definition (a signature and its equations), or one
    /// declaration of another kind.
    #[inline(never)]
    pub(super) fn decl(&mut self) -> Result<Vec<Decl>> {
        let start = self.here();
        match self.peek() {
            Some(Tok::KwType) => Ok(vec![self.data()?]),
            Some(Tok::KwAbility) => Ok(vec![self.ability()?]),
            Some(Tok::KwTest) => Ok(vec![self.test()?]),
            Some(Tok::KwExport) => {
                self.bump();
                if !matches!(self.peek(), Some(Tok::KwDef | Tok::KwTheorem)) {
                    return Err(self.unexpected("`def` or `theorem` after `export`"));
                }
                self.definition(start, true)
            }
            Some(Tok::KwDef | Tok::KwTheorem) => self.definition(start, false),
            Some(Tok::Lower(_) | Tok::Upper(_)) => Err(self.old_declaration()),
            _ => Err(self.unexpected("a declaration")),
        }
    }

    /// `test "name" := e`
    fn test(&mut self) -> Result<Decl> {
        let start = self.bump().span;
        let name = match self.peek() {
            Some(Tok::Str(text)) => {
                let text = text.clone();
                self.bump();
                text
            }
            _ => return Err(self.unexpected("the test's name, in quotes")),
        };
        if self.peek() == Some(&Tok::Equals) {
            return Err(self.def_equals());
        }
        self.expect(Tok::ColonEq, "`:=`")?;
        let expr = self.expr()?;
        Ok(Decl::Test {
            span: start.to(expr.span()),
            name,
            expr,
        })
    }

    /// `E-OLD-DECLARATION`: a declaration starting with a name, as the old
    /// syntax's signatures (`f : T`) and equations (`f x = e`) did.
    fn old_declaration(&self) -> Diagnostic {
        let name = match self.peek() {
            Some(Tok::Lower(text) | Tok::Upper(text)) => text.clone(),
            _ => "f".to_string(),
        };
        let note = if self.peek_at(1) == Some(&Tok::Colon) {
            format!(
                "write `def {name} : …` with a `:=` body or arms under it; a signature and \
                 equations are one definition now"
            )
        } else {
            format!(
                "write `def {name} (x : A) : B := …`, or arms `| p => …` under `def {name} : A -> B`"
            )
        };
        Diagnostic::error("E-OLD-DECLARATION", "definitions start with `def`")
            .with_label(
                self.here(),
                "expected `def`, `theorem`, `type`, `ability` or `test`",
            )
            .with_note(note)
    }

    /// `=` where `:=` gives something its value.
    pub(super) fn def_equals(&self) -> Diagnostic {
        Diagnostic::error(
            "E-DEF-EQUALS",
            "a definition's body follows `:=`; `=` is equality",
        )
        .with_label(self.here(), "write `:=` here")
    }

    /// `def name params : type`, then `:= body` or arms; or the same with
    /// `theorem`. With neither, a signature alone: only the prelude's
    /// primitives are declared that way, which the elaborator checks. At
    /// `def` or `theorem`; `start` is where the declaration starts (at
    /// `export`, if it's there). Once here, it's a header: the parser never
    /// goes back to read the tokens another way (§2.1).
    #[inline(never)]
    fn definition(&mut self, start: Span, export: bool) -> Result<Vec<Decl>> {
        let keyword = &self.tokens[self.pos];
        // D (§2.10) is the column of the declaration's first keyword:
        // `export`'s, when it's there.
        let column = if export {
            self.tokens[self.pos - 1].column
        } else {
            keyword.column
        };
        let theorem = keyword.tok == Tok::KwTheorem;
        self.bump();
        let name = self.def_name()?;
        let mut params = Vec::new();
        while self.peek() != Some(&Tok::Colon) {
            params.push(self.header_param()?);
        }
        self.bump();
        let result = self.result_type()?;
        check_duplicates(&name, &params, &result)?;
        let result_is_equation = matches!(result, Expr::Binary(BinOp::Eq, ..));
        let span = start.to(result.span());
        let (ty, header) = lower_header(params, result);
        let mut decls = vec![Decl::Signature {
            name: name.clone(),
            ty,
            theorem,
            export,
            span,
        }];
        match self.peek() {
            Some(Tok::ColonEq) => {
                self.bump();
                let rhs = self.expr()?;
                decls.push(Decl::Equation {
                    span: name.span.to(rhs.span()),
                    name,
                    patterns: header,
                    rhs: Some(rhs),
                    arm: None,
                });
                if self.peek() == Some(&Tok::Pipe) {
                    return Err(error(
                        self.here(),
                        "a definition has a `:=` body or arms, not both",
                    )
                    .with_note(
                        "named parameters can't be matched in arms: to take one apart, move it \
                         after the colon, or use `match`",
                    ));
                }
            }
            Some(Tok::Pipe) => self.arms(column, &name, &header, &mut decls)?,
            Some(Tok::Equals) => return Err(self.def_equals()),
            // `def f (x : Nat) : Nat = x`: the type swallowed the body as an
            // equation, and nothing follows.
            None if result_is_equation => {
                return Err(Diagnostic::error(
                    "E-DEF-EQUALS",
                    "a definition's body follows `:=`; `=` is equality",
                )
                .with_label(span, "this definition has no body")
                .with_note(
                    "its type is read as an equation; if that `=` was meant to start the \
                     body, write `:=`",
                ));
            }
            // A header without a body: a primitive, for the elaborator to
            // admit or refuse.
            None => {}
            _ => {
                return Err(self.unexpected(
                    "`:=` and the body, or arms starting with `|` on their own lines",
                ));
            }
        }
        if self.tokens.get(self.pos).map(|t| &t.tok) == Some(&Tok::KwWhere) {
            return Err(error(
                self.here(),
                "`where` after a definition isn't supported yet",
            )
            .with_note(
                "write the helper as a definition of its own (`where` is planned: \
                 docs/proposals/declaration-syntax.md §2.9)",
            ));
        }
        Ok(decls)
    }

    /// One parameter in a header: `(x y : A)`, `[x y : A]`, `[auto h : P]`
    /// or `()`.
    fn header_param(&mut self) -> Result<Param> {
        let start = self.here();
        let implicit = match self.peek() {
            Some(Tok::LParen) if self.peek_at(1) == Some(&Tok::RParen) => {
                self.bump();
                let end = self.bump().span;
                return Ok(Param::Unit(start.to(end)));
            }
            Some(Tok::LParen) => false,
            Some(Tok::LBracket) => true,
            _ => {
                return Err(self.unexpected(
                    "a parameter such as `(x : Nat)`, or `:` and the definition's type",
                ));
            }
        };
        self.bump();
        let mut names = vec![self.lower("a parameter's name")?];
        while let Some(Tok::Lower(_)) = self.peek() {
            names.push(self.lower("a parameter's name")?);
        }
        // `auto` is only special as the first word of a binder with names
        // after it, as in types.
        let auto = implicit && names.len() > 1 && names[0].text == "auto";
        if auto {
            names.remove(0);
        }
        let (open, close, closing) = if implicit {
            ("[", "]", Tok::RBracket)
        } else {
            ("(", ")", Tok::RParen)
        };
        let written = format!(
            "{open}{}{} : …",
            if auto { "auto " } else { "" },
            names
                .iter()
                .map(|n| n.text.as_str())
                .collect::<Vec<_>>()
                .join(" ")
        );
        if self.peek() != Some(&Tok::Colon) {
            return Err(error(self.here(), "a parameter needs a type")
                .with_note(format!("write `{written}{close}`")));
        }
        self.bump();
        let ty = self.expr()?;
        if self.peek() != Some(&closing) {
            return Err(self.unexpected(&format!("`{close}` to close the parameter `{written}`")));
        }
        let end = self.bump().span;
        Ok(Param::Named {
            names,
            ty,
            implicit,
            auto,
            span: start.to(end),
        })
    }

    /// The arms under a header, at `self.pos`'s `|`, onto `decls`. `d` is
    /// the column of the definition's keyword. Layout rules L4 to L6 (§2.10):
    /// every arm's `|` starts a line at one column, right of `d`, and a
    /// line at or left of that column ends an arm's body.
    #[inline(never)]
    fn arms(
        &mut self,
        d: u32,
        name: &Name,
        header: &[Pattern],
        decls: &mut Vec<Decl>,
    ) -> Result<()> {
        let first = &self.tokens[self.pos];
        if !first.line_start {
            return Err(
                error(first.span, "arms start on their own lines").with_note(
                    "put each `| … => …` on a line of its own, indented; a case analysis that fits \
                 on one line is a `:=` body with a `match`",
                ),
            );
        }
        if first.column <= d {
            return Err(error(
                first.span,
                "arms are indented further than the definition they belong to",
            ));
        }
        let (column, first_span) = (first.column, first.span);
        let saved = (self.limit, self.allow);
        self.limit = Some(column);
        let result = (|| {
            loop {
                self.allow = Some(self.pos);
                decls.push(self.arm(name, header)?);
                let Some(next) = self.tokens.get(self.pos) else {
                    return Ok(());
                };
                if !next.line_start {
                    return Err(self.unexpected("the end of the arm"));
                }
                match next.tok {
                    _ if next.column <= d => return Ok(()),
                    // Reported by `definition`.
                    Tok::KwWhere => return Ok(()),
                    Tok::Pipe if next.column == column => {}
                    Tok::Pipe => {
                        return Err(error(
                            next.span,
                            "this `|` doesn't line up with the definition's arms",
                        )
                        .with_label(first_span, "the arms start at this column")
                        .with_note(
                            "a `match` or `handle` inside an arm indents its `|`s further than \
                             the arms",
                        ));
                    }
                    _ => {
                        return Err(error(
                            next.span,
                            format!(
                                "expected `|` and another arm, or the end of the definition, \
                                 but found {}",
                                describe(&next.tok)
                            ),
                        )
                        .with_label(first_span, "the arms start at this column")
                        .with_note(
                            "an arm's body continues on lines indented further than its `|`",
                        ));
                    }
                }
            }
        })();
        (self.limit, self.allow) = saved;
        result
    }

    /// `| p, q => body`, or with an absurd pattern, `| p, ()`: an equation
    /// whose patterns are the header's, then the arm's.
    fn arm(&mut self, name: &Name, header: &[Pattern]) -> Result<Decl> {
        let bar = self.bump().span;
        let mut patterns = header.to_vec();
        patterns.push(self.alt_pattern()?);
        while self.eat(&Tok::Comma) {
            patterns.push(self.alt_pattern()?);
        }
        let absurd = patterns[header.len()..].iter().any(has_absurd);
        let rhs = if absurd && self.peek() != Some(&Tok::FatArrow) {
            None
        } else {
            self.expect(Tok::FatArrow, "`=>` and the arm's body")?;
            Some(self.expr()?)
        };
        let end = rhs.as_ref().map_or(self.prev_span(), Expr::span);
        Ok(Decl::Equation {
            name: name.clone(),
            patterns,
            rhs,
            arm: Some(header.len()),
            span: bar.to(end),
        })
    }

    /// A handler's clause in the new syntax, after its `|`:
    /// `return x => body`, or `op p, k => body`. The argument is one atomic
    /// pattern, so a comma inside its brackets belongs to it.
    #[inline(never)]
    pub(super) fn handler_clause(&mut self) -> Result<Clause> {
        if self.eat(&Tok::KwReturn) {
            let var = self.lower("a name for the result")?;
            self.expect(Tok::FatArrow, "`=>`")?;
            let body = self.expr()?;
            return Ok(Clause::Return { var, body });
        }
        let op = self.lower_q("an operation, or `return`")?;
        let arg = self.pattern()?;
        if self.peek() == Some(&Tok::FatArrow) {
            return Err(error(
                self.here(),
                format!("name the continuation: `| {} x, k => …`", op.text),
            ));
        }
        self.expect(Tok::Comma, "`,` and a name for the continuation")?;
        let k = self.lower("a name for the continuation")?;
        if self.peek() == Some(&Tok::Comma) {
            return Err(error(
                arg.span().to(self.here()),
                "an operation takes one argument; bracket a tuple: `(a, b)`",
            ));
        }
        self.expect(Tok::FatArrow, "`=>`")?;
        let body = self.expr()?;
        Ok(Clause::Op { op, arg, k, body })
    }
}

/// The signature's type, the header's parameters as arrows in front of the
/// result type, in the order written; and the patterns each equation starts
/// with, a variable for each explicit parameter and `_` for `()` (§2.3).
/// The elaborator auto-binds type variables once over this complete type,
/// as it does for an old-style signature: no parameter is elaborated on its
/// own.
fn lower_header(params: Vec<Param>, result: Expr) -> (Expr, Vec<Pattern>) {
    let mut patterns = Vec::new();
    for param in &params {
        match param {
            Param::Named {
                names,
                implicit: false,
                ..
            } => patterns.extend(names.iter().cloned().map(Pattern::Var)),
            Param::Named { .. } => {}
            Param::Unit(span) => patterns.push(Pattern::Wildcard(*span)),
        }
    }
    let ty = params
        .into_iter()
        .rev()
        .fold(result, |cod, param| match param {
            Param::Unit(span) => Expr::Arrow(Box::new(Expr::Unit(span)), Box::new(cod)),
            Param::Named {
                names,
                ty,
                implicit,
                auto,
                span,
            } => {
                let span = span.to(cod.span());
                Expr::Pi {
                    names,
                    implicit,
                    auto,
                    dom: Box::new(ty),
                    cod: Box::new(cod),
                    span,
                }
            }
        });
    (ty, patterns)
}

/// `E-DUPLICATE-PARAMETER`: the header's parameters, and the implicit and
/// auto parameters after the colon, all have different names (§2.5). The
/// elaborator binds the implicit ones before the header's explicit ones,
/// which are pattern variables, so a repeated name would refer to the
/// header's parameter where the reader expects the later one. Explicit
/// binders after the colon are local to the type, so they may repeat a
/// header's name.
fn check_duplicates(def: &Name, params: &[Param], result: &Expr) -> Result<()> {
    let mut seen: Vec<&Name> = Vec::new();
    let check = |seen: &[&Name], name: &Name| match seen.iter().find(|s| s.text == name.text) {
        Some(first) => Err(Diagnostic::error(
            "E-DUPLICATE-PARAMETER",
            format!("`{}` is already a parameter of `{}`", name.text, def.text),
        )
        .with_label(name.span, "named again here")
        .with_label(first.span, "first named here")
        .with_note(
            "the header's parameters and the implicit ones after the colon need different names",
        )),
        None => Ok(()),
    };
    for param in params {
        if let Param::Named { names, .. } = param {
            for name in names {
                check(&seen, name)?;
                seen.push(name);
            }
        }
    }
    // The implicit and auto binders on the type's spine, up to its result
    // (an ability row ends it, as it ends the arguments arms match).
    let mut ty = result;
    loop {
        match ty {
            Expr::Pi {
                names,
                implicit,
                cod,
                ..
            } => {
                if *implicit {
                    for name in names {
                        check(&seen, name)?;
                    }
                }
                ty = cod;
            }
            Expr::Arrow(_, cod) => ty = cod,
            _ => return Ok(()),
        }
    }
}
