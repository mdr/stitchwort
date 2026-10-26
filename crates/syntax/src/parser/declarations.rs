//! Declarations (docs/proposals/declaration-syntax.md): `def` and
//! `theorem` headers with typed parameters, then a `:=` body or arms,
//! lowered to a signature and its equations (§2.3); `test "n" := e`;
//! `export def`; and handler clauses `| op x, k => body` (§2.11).
//!
//! Each function here is `#[inline(never)]` or only called from one that
//! is: the expression parser's recursive functions must keep small stack
//! frames, since the nesting limit is measured in stack.

use super::{Parser, Result, describe, error, has_absurd};
use crate::ast::{Attribute, BinOp, Clause, Decl, Expr, NAMELESS, Name, Pattern};
use crate::lexer::Tok;
use crate::{Diagnostic, Span};

/// A parameter written in a header, before the colon.
pub(super) enum Param {
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

/// `E-ATTRIBUTE`: attributes written where none can apply, `first` being
/// the first of them. The parser knows no attribute's name, only where any
/// attribute may go (docs/syntax.md, Attributes); the elaborator decides
/// which may go on which data type, constructor, field or declaration.
pub(super) fn misplaced_attributes(first: &Attribute, what: &str) -> Diagnostic {
    Diagnostic::error("E-ATTRIBUTE", format!("attributes can't be used on {what}"))
        .with_label(first.span, format!("`{}` is on {what}", first.name.text))
        .with_note(ATTRIBUTE_PLACES)
}

/// Where attributes may be written, for messages.
pub(super) const ATTRIBUTE_PLACES: &str = "attributes go before a data type's `type`, after a \
     constructor's `|`, or before a field's name: `@[js.tag \"type\"]`, \
     `| @[js.name \"CIRCLE\"] Circle`, `(@[js.name \"center_x\"] centerX: Nat)`";

impl Parser<'_> {
    /// The attribute groups at `self.pos`, `@[a, b "x"] @[c]`, if any, in
    /// the order written. Only their shape is checked: a name of lowercase
    /// words joined by `.`, then at most one plain string.
    #[inline(never)]
    pub(super) fn attributes(&mut self) -> Result<Vec<Attribute>> {
        let mut attrs = Vec::new();
        while self.peek() == Some(&Tok::At) {
            self.bump();
            self.expect(Tok::LBracket, "`[`")?;
            let first = attrs.len();
            loop {
                if self.peek() == Some(&Tok::RBracket) && attrs.len() > first {
                    // A trailing comma.
                    break;
                }
                let start = self.lower_q("an attribute's name, such as `js.name`")?;
                let mut name = start.clone();
                while self.peek() == Some(&Tok::Dot) {
                    self.bump();
                    let part = self.lower_q("the rest of the attribute's name")?;
                    name.text.push('.');
                    name.text.push_str(&part.text);
                    name.span = name.span.to(part.span);
                }
                let arg = match self.peek() {
                    Some(Tok::Str(text)) => {
                        let text = text.clone();
                        Some((text, self.bump().span))
                    }
                    Some(Tok::StrStart(_)) => {
                        return Err(error(
                            self.here(),
                            "an attribute's argument is a plain string, without `${…}`",
                        ));
                    }
                    _ => None,
                };
                let span = arg.as_ref().map_or(name.span, |(_, s)| name.span.to(*s));
                attrs.push(Attribute { name, arg, span });
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(Tok::RBracket, "`,` or `]` after the attribute")?;
        }
        Ok(attrs)
    }

    /// `E-ATTRIBUTE` if attributes start at `self.pos`, which `what` can't
    /// have.
    pub(super) fn no_attributes(&mut self, what: &str) -> Result<()> {
        if self.peek() != Some(&Tok::At) {
            return Ok(());
        }
        let attrs = self.attributes()?;
        Err(misplaced_attributes(&attrs[0], what))
    }

    /// A declaration: a definition (a signature and its equations), or one
    /// declaration of another kind.
    #[inline(never)]
    pub(super) fn decl(&mut self) -> Result<Vec<Decl>> {
        let start = self.here();
        match self.peek() {
            Some(Tok::KwType | Tok::KwInterface) => self.data(),
            Some(Tok::KwInstance) => self.definition(start, false, false),
            Some(Tok::KwAbility) => Ok(vec![self.ability()?]),
            Some(Tok::KwTest) => Ok(vec![self.test()?]),
            Some(Tok::KwExport) => {
                self.bump();
                if self.peek() == Some(&Tok::KwOpaque) {
                    self.bump();
                    self.opaque_keyword()?;
                    return self.definition(start, true, true);
                }
                if !matches!(self.peek(), Some(Tok::KwDef | Tok::KwTheorem)) {
                    return Err(self.unexpected("`def`, `theorem` or `opaque` after `export`"));
                }
                self.definition(start, true, false)
            }
            Some(Tok::KwOpaque) => {
                self.bump();
                self.opaque_keyword()?;
                self.definition(start, false, true)
            }
            Some(Tok::KwDef | Tok::KwTheorem) => self.definition(start, false, false),
            Some(Tok::Lower(_) | Tok::Upper(_)) => Err(self.missing_keyword()),
            _ => Err(self.unexpected("a declaration")),
        }
    }

    /// After `opaque`, which only `def` may follow
    /// (docs/proposals/opaque-definitions.md §6.2): a theorem already stays
    /// folded, and an instance that can't be taken apart can't be used.
    fn opaque_keyword(&self) -> Result<()> {
        match self.peek() {
            Some(Tok::KwDef) => Ok(()),
            Some(Tok::KwTheorem) => Err(error(self.here(), "a theorem can't be `opaque`")
                .with_note("a theorem already stays folded where it's used")
                .with_note(
                    "to use an opaque definition's body in its proof, write `unfolding f` \
                     after its type",
                )),
            Some(Tok::KwInstance) => Err(error(self.here(), "an instance can't be `opaque`")
                .with_note("an instance is used by taking it apart, which needs its body")),
            Some(Tok::KwExport) => Err(error(self.here(), "`export` goes before `opaque`")
                .with_note("write `export opaque def`")),
            _ => Err(self.unexpected("`def` after `opaque`")),
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

    /// `E-PARSE`: a declaration starting with a name, as a definition
    /// written without `def` does.
    fn missing_keyword(&self) -> Diagnostic {
        Diagnostic::error(
            "E-PARSE",
            "expected a declaration: `def`, `theorem`, `type`, `ability`, `interface`, `instance` \
             or `test`",
        )
        .with_label(self.here(), "a declaration starts with a keyword")
        .with_note("a definition is written `def name (x: A): B := …`")
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
    /// `theorem` or `instance` (docs/proposals/interfaces.md §5.2). With neither, a signature alone: only the prelude's
    /// primitives are declared that way, which the elaborator checks. At
    /// `def` or `theorem`; `start` is where the declaration starts (at
    /// `export`, if it's there). Once here, it's a header: the parser never
    /// goes back to read the tokens another way (§2.1).
    #[inline(never)]
    pub(super) fn definition(
        &mut self,
        start: Span,
        export: bool,
        opaque: bool,
    ) -> Result<Vec<Decl>> {
        let keyword = &self.tokens[self.pos];
        // D (§2.10) is the column of the declaration's first keyword:
        // `export`'s or `opaque`'s, when one is there.
        let column = self.tokens[self.pos - usize::from(export) - usize::from(opaque)].column;
        let theorem = keyword.tok == Tok::KwTheorem;
        let instance = keyword.tok == Tok::KwInstance;
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
        // `decreasing e`, before `:=` or the arms (D474).
        let decreasing = if self.eat(&Tok::KwDecreasing) {
            if instance {
                return Err(error(
                    self.prev_span(),
                    "an instance can't have `decreasing`",
                ));
            }
            let measure = self.expr()?;
            // After it, `:=` may start a line of its own, at the
            // declaration's column (§6.1's layout).
            if self
                .tokens
                .get(self.pos)
                .is_some_and(|t| t.tok == Tok::ColonEq && t.line_start)
            {
                self.allow = Some(self.pos);
            }
            Some(Box::new(measure))
        } else {
            None
        };
        // `unfolding f, g`, after `decreasing e` if both are written
        // (docs/proposals/opaque-definitions.md §6.3).
        let mut unfolding = Vec::new();
        if self.eat(&Tok::KwUnfolding) {
            if instance {
                return Err(
                    error(self.prev_span(), "an instance can't have `unfolding`").with_note(
                        "an instance is never opaque, so it can't unfold opaque definitions",
                    ),
                );
            }
            loop {
                unfolding.push(match self.peek() {
                    Some(Tok::Upper(_)) => self.upper_q("the name of an opaque definition")?,
                    _ => self.lower_q("the name of an opaque definition")?,
                });
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            if self
                .tokens
                .get(self.pos)
                .is_some_and(|t| t.tok == Tok::ColonEq && t.line_start)
            {
                self.allow = Some(self.pos);
            }
        }
        if self.peek() == Some(&Tok::KwDecreasing) && !unfolding.is_empty() {
            return Err(error(self.here(), "`decreasing` goes before `unfolding`"));
        }
        let (ty, header) = lower_header(params, result);
        let mut decls = vec![Decl::Signature {
            name: name.clone(),
            ty,
            theorem,
            export,
            synonym: false,
            instance,
            decreasing,
            opaque,
            unfolding,
            attrs: Vec::new(),
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
        if instance && decls.len() == 1 {
            return Err(error(span, "an instance needs a body")
                .with_note("write `:=` and the instance's value after its type"));
        }
        if self.tokens.get(self.pos).map(|t| &t.tok) == Some(&Tok::KwWhere) {
            return Err(Diagnostic::error(
                "E-WHERE",
                "`where` isn't part of Stitchwort: declare helpers with a local `def`",
            )
            .with_label(self.here(), "no `where` here")
            .with_note(
                "write the helper as a `def` in the body's block, before the result, like \
                 `def f (n: Nat): Nat :=` then `  def go …` then `  go n`",
            ));
        }
        Ok(decls)
    }

    /// `type Grid = List (List Nat)`: a transparent name for a type, exactly
    /// `def Grid : Type := List (List Nat)`. After `=`, `{` starts a record's
    /// fields and `|` a sum's constructors; anything else is the type.
    #[inline(never)]
    pub(super) fn type_synonym(
        &mut self,
        start: Span,
        name: Name,
        params: Vec<crate::ast::Binder>,
        auto_params: Vec<bool>,
        sort: Option<Expr>,
    ) -> Result<Vec<Decl>> {
        let body = self.expr()?;
        let ambiguous = |what: &str| {
            error(
                body.span(),
                format!(
                    "`type {} = …` names a type, but this looks like {what}",
                    name.text
                ),
            )
            .with_note(
                "a sum type's constructors each start with `|`: `type T = | A | B`, and \
                 `type T = | Foo (x: Nat)` for one constructor; a record is `type T = { … }`",
            )
        };
        if self.peek() == Some(&Tok::Pipe) {
            return Err(ambiguous("a sum type without its leading `|`"));
        }
        let mut spine = &body;
        while let Expr::App(f, arg) = spine {
            if matches!(**arg, Expr::Ann(..)) {
                return Err(ambiguous(
                    "a constructor with named fields, without its leading `|`",
                ));
            }
            spine = f;
        }
        // An `auto` parameter, `[auto ord: Ord k]`, is one of the
        // definition's: `type Set (k: Type) [auto ord: Ord k] = …`
        // (docs/proposals/interfaces.md §7.5).
        let params: Vec<Param> = params
            .into_iter()
            .zip(auto_params)
            .map(|(b, auto)| Param::Named {
                span: b.names[0].span.to(b.ty.span()),
                names: b.names,
                ty: b.ty,
                implicit: auto,
                auto,
            })
            .collect();
        let result = sort.unwrap_or(Expr::Type(0, name.span));
        check_duplicates(&name, &params, &result)?;
        let (ty, header) = lower_header(params, result);
        Ok(vec![
            Decl::Signature {
                name: name.clone(),
                ty,
                theorem: false,
                export: false,
                synonym: true,
                instance: false,
                decreasing: None,
                opaque: false,
                unfolding: Vec::new(),
                attrs: Vec::new(),
                span: start.to(name.span),
            },
            Decl::Equation {
                span: name.span.to(body.span()),
                name,
                patterns: header,
                rhs: Some(body),
                arm: None,
            },
        ])
    }

    /// One parameter in a header: `(x y : A)`, `[x y : A]`, `[auto h : P]`
    /// or `()`.
    pub(super) fn header_param(&mut self) -> Result<Param> {
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
                    "a parameter such as `(x: Nat)`, or `:` and the definition's type",
                ));
            }
        };
        self.bump();
        self.no_attributes("a definition's parameter")?;
        let mut names = vec![self.param_name()?];
        while let Some(Tok::Lower(_)) = self.peek() {
            names.push(self.param_name()?);
        }
        // `auto` is only special as the first word of a binder with names
        // after it, as in types; or, without a name, `[auto Ord a]`
        // (docs/proposals/interfaces.md §5.3).
        if implicit
            && names.len() == 1
            && names[0].text == "auto"
            && !matches!(self.peek(), Some(Tok::Colon | Tok::RBracket) | None)
        {
            let ty = self.expr()?;
            if self.peek() != Some(&Tok::RBracket) {
                return Err(self.unexpected("`]` to close the parameter `[auto …]`"));
            }
            let end = self.bump().span;
            return Ok(Param::Named {
                names: vec![Name {
                    text: NAMELESS.to_string(),
                    span: names[0].span,
                }],
                ty,
                implicit,
                auto: true,
                span: start.to(end),
            });
        }
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
            "{open}{}{}: …",
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
        if self.peek() == Some(&Tok::ColonEq) {
            return Err(
                error(self.here(), "a parameter can't have a default value").with_note(
                    "only a record's or a constructor's fields can: take the options as a \
                     record, `{ step: Nat := 1, … }`, and leave out fields when calling",
                ),
            );
        }
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
        let k = if self.peek() == Some(&Tok::Underscore) {
            let span = self.bump().span;
            Name {
                text: "_".to_string(),
                span,
            }
        } else {
            self.lower("a name for the continuation")?
        };
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
            for name in names.iter().filter(|n| n.text != NAMELESS) {
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
                    for name in names.iter().filter(|n| n.text != NAMELESS) {
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
