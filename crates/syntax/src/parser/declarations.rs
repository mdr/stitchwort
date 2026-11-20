//! Declarations (docs/proposals/declaration-syntax.md): `def` and
//! `theorem` headers with typed parameters, then a `:=` body or arms
//! (§2.3); `test "n" := e`; `export def`; and handler clauses
//! `| op x, k => body` (§2.11).
//!
//! Each function here is `#[inline(never)]` or only called from one that
//! is: the expression parser's recursive functions must keep small stack
//! frames, since the nesting limit is measured in stack.

use super::{FirstAttribute, Lowered, Parser, Result, describe, error, name_text};
use crate::ast::{BinOp, Expr};
use crate::lexer::Tok;
use crate::tree::NodeKind;
use crate::{Diagnostic, Span};

/// `E-ATTRIBUTE`: attributes written where none can apply, `first` being
/// the first of them. The parser knows no attribute's name, only where any
/// attribute may go (docs/syntax.md, Attributes); the elaborator decides
/// which may go on which data type, constructor, field or declaration.
pub(super) fn misplaced_attributes(first: &FirstAttribute, what: &str) -> Diagnostic {
    Diagnostic::error("E-ATTRIBUTE", format!("attributes can't be used on {what}"))
        .with_label(first.span, format!("`{}` is on {what}", first.name))
        .with_generic_note(ATTRIBUTE_PLACES)
}

/// Where attributes may be written, for messages.
pub(super) const ATTRIBUTE_PLACES: &str = "attributes go before a data type's `type`, after a \
     constructor's `|`, or before a field's name: `@[js.tag \"type\"]`, \
     `| @[js.name \"CIRCLE\"] Circle`, `(@[js.name \"center_x\"] centerX: Nat)`";

/// `E-PARSE` for a default value where none may be written.
pub(super) const DEFAULT_PLACES: &str =
    "only a definition's parameter or a field can have a default value";

/// What the callers of [`Parser::definition`] need: the root kind, the
/// first name after `unfolding`, whether there is a body (or arms), and
/// the tokens of the result type.
pub(super) struct DefinitionRead {
    pub(super) kind: NodeKind,
    pub(super) unfolding: Option<Span>,
    pub(super) body: bool,
    pub(super) result: (u32, u32),
}

/// What the callers of [`Parser::header_param`] check: the tokens of its
/// default value, if it has one.
pub(super) struct ParamRead {
    pub(super) default: Option<(u32, u32)>,
}

impl Parser<'_> {
    /// The attribute groups at `self.pos`, `@[a, b "x"] @[c]`, if any, and
    /// the first attribute, for messages. Only their shape is checked: a
    /// name of lowercase words joined by `.`, then at most one plain string.
    #[inline(never)]
    pub(super) fn attributes(&mut self) -> Result<Option<FirstAttribute>> {
        let mut first: Option<FirstAttribute> = None;
        while self.peek() == Some(&Tok::At) {
            let group = self.mark();
            self.bump();
            self.expect(Tok::LBracket, "`[`")?;
            let mut attrs = 0;
            loop {
                if self.peek() == Some(&Tok::RBracket) && attrs > 0 {
                    // A trailing comma.
                    break;
                }
                let attribute = self.mark();
                let start = self.lower_q("an attribute's name, such as `js.name`")?;
                let mut name = name_text(start).to_string();
                if self.peek() == Some(&Tok::Dot) {
                    while self.peek() == Some(&Tok::Dot) {
                        self.bump();
                        let part = self.lower_q("the rest of the attribute's name")?;
                        name.push('.');
                        name.push_str(name_text(part));
                    }
                    self.node(attribute, NodeKind::AttributeName);
                }
                match self.peek() {
                    Some(Tok::Str(_)) => {
                        self.bump();
                    }
                    Some(Tok::StrStart(_)) => {
                        return Err(error(
                            self.here(),
                            "an attribute's argument is a plain string, without `${…}`",
                        )
                        .into());
                    }
                    _ => {}
                }
                if first.is_none() {
                    first = Some(FirstAttribute {
                        name,
                        span: start.span.to(self.prev_span()),
                    });
                }
                attrs += 1;
                self.node(attribute, NodeKind::Attribute);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(Tok::RBracket, "`,` or `]` after the attribute")?;
            self.node(group, NodeKind::Attributes);
        }
        Ok(first)
    }

    /// `E-ATTRIBUTE` if attributes start at `self.pos`, which `what` can't
    /// have.
    pub(super) fn no_attributes(&mut self, what: &str) -> Result<()> {
        if self.peek() != Some(&Tok::At) {
            return Ok(());
        }
        let first = self.attributes()?.expect("an attribute");
        Err(misplaced_attributes(&first, what).into())
    }

    /// A declaration: a definition, or a declaration of another kind. Its
    /// root kind.
    #[inline(never)]
    pub(super) fn decl(&mut self) -> Result<NodeKind> {
        let start = self.here();
        match self.peek() {
            Some(Tok::KwType | Tok::KwInterface) => self.data(),
            Some(Tok::KwInstance) => Ok(self.definition(start, false, false)?.kind),
            Some(Tok::KwAbility) => {
                self.ability()?;
                Ok(NodeKind::Ability)
            }
            Some(Tok::KwTest) => {
                self.test()?;
                Ok(NodeKind::Test)
            }
            Some(Tok::KwExport) => {
                self.bump();
                if self.peek() == Some(&Tok::KwOpaque) {
                    self.bump();
                    self.opaque_keyword()?;
                    return Ok(self.definition(start, true, true)?.kind);
                }
                if !matches!(self.peek(), Some(Tok::KwDef | Tok::KwTheorem)) {
                    return Err(self
                        .unexpected("`def`, `theorem` or `opaque` after `export`")
                        .into());
                }
                Ok(self.definition(start, true, false)?.kind)
            }
            Some(Tok::KwOpaque) => {
                self.bump();
                self.opaque_keyword()?;
                Ok(self.definition(start, false, true)?.kind)
            }
            Some(Tok::KwDef | Tok::KwTheorem) => Ok(self.definition(start, false, false)?.kind),
            Some(Tok::Lower(w))
                if w == "rules" && matches!(self.peek_at(1), Some(Tok::Lower(_))) =>
            {
                self.rule_set()?;
                Ok(NodeKind::Rules)
            }
            Some(Tok::Lower(_) | Tok::Upper(_)) => Err(self.missing_keyword().into()),
            Some(Tok::ColonEq) => Err(error(
                start,
                "a declaration can't start with `:=`",
            )
            .with_note(
                "a declaration starts with a keyword such as `def` or `theorem`; `:=` gives its body a value",
            )
            .into()),
            _ => Err(self.unexpected("a declaration").into()),
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
                )
                .into()),
            Some(Tok::KwInstance) => Err(error(self.here(), "an instance can't be `opaque`")
                .with_note("an instance is used by taking it apart, which needs its body")
                .into()),
            Some(Tok::KwExport) => Err(error(self.here(), "`export` goes before `opaque`")
                .with_note("write `export opaque def`")
                .into()),
            _ => Err(self.unexpected("`def` after `opaque`").into()),
        }
    }

    /// `test "name" := e`
    fn test(&mut self) -> Result<()> {
        self.bump();
        match self.peek() {
            Some(Tok::Str(_)) => {
                self.bump();
            }
            _ => return Err(self.unexpected("the test's name, in quotes").into()),
        }
        if self.peek() == Some(&Tok::Equals) {
            return Err(self.def_equals().into());
        }
        let body = self.mark();
        self.expect(Tok::ColonEq, "`:=`")?;
        self.expr()?;
        self.node(body, NodeKind::Body);
        Ok(())
    }

    /// `rules name := [r1, <- r2]`. `rules` is a word only at the start of
    /// a declaration, before a name, so a variable called `rules` still
    /// reads as one elsewhere.
    fn rule_set(&mut self) -> Result<()> {
        self.bump();
        self.def_name()?;
        if self.peek() == Some(&Tok::Equals) {
            return Err(self.def_equals().into());
        }
        let body = self.mark();
        self.expect(Tok::ColonEq, "`:=`")?;
        if self.peek() != Some(&Tok::LBracket) {
            return Err(self
                .unexpected("the set's rules, in brackets: `[r1, <- r2]`")
                .into());
        }
        self.repeated_rules()?;
        self.node(body, NodeKind::Body);
        Ok(())
    }

    /// `E-PARSE`: a declaration starting with a name, as a definition
    /// written without `def` does.
    fn missing_keyword(&self) -> Diagnostic {
        let diagnostic = Diagnostic::error(
            "E-PARSE",
            "expected a declaration: `def`, `theorem`, `type`, `ability`, `interface`, `instance` \
             or `test`",
        )
        .with_label(self.here(), "a declaration starts with a keyword")
        .with_note("a definition is written `def name (x: A): B := …`");
        // Lean and OCaml write a record with `record` or `structure` and
        // named fields, which Stitchwort writes as a `type` whose fields
        // are in braces.
        if self.text_at(self.pos as u32) == "record" {
            return diagnostic.with_note(
                "a record is a `type` with fields in braces: `type Point = { x: Nat, y: Nat }`",
            );
        }
        diagnostic
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
    ) -> Result<DefinitionRead> {
        let keyword = &self.tokens[self.pos];
        // D (§2.10) is the column of the declaration's first keyword:
        // `export`'s or `opaque`'s, when one is there.
        let column = self.tokens[self.pos - usize::from(export) - usize::from(opaque)].column;
        let theorem = keyword.tok == Tok::KwTheorem;
        let instance = keyword.tok == Tok::KwInstance;
        let kind = match keyword.tok {
            Tok::KwTheorem => NodeKind::Theorem,
            Tok::KwInstance => NodeKind::Instance,
            _ => NodeKind::Def,
        };
        // Taken here, before any local definition in the header can.
        let keep = std::mem::take(&mut self.keep_header) && !instance;
        self.bump();
        self.def_name()?;
        // A theorem's header may say `∀` before its parameters
        // (`theorem leTrans ∀ (a b c: Nat) (h: a ≤ b): …`, D3472). It is
        // cosmetic: the formatter writes it, and the term and hash are those
        // of the header without it.
        if self.peek() == Some(&Tok::KwForall) {
            if !theorem {
                return Err(error(
                    self.here(),
                    "`∀` before the parameters is only for theorems",
                )
                .with_note("a `def` or an instance lists its parameters directly after its name")
                .into());
            }
            self.bump();
            if !matches!(self.peek(), Some(Tok::LParen | Tok::LBracket)) {
                return Err(self
                    .unexpected("a parameter such as `(x: Nat)` after `∀`")
                    .into());
            }
        }
        while self.peek() != Some(&Tok::Colon) {
            self.header_param()?;
        }
        let colon = self.mark();
        self.bump();
        let result = self.mark();
        self.result_type()?;
        let result = (result, self.mark());
        self.node(colon, NodeKind::ResultType);
        // `decreasing e`, before `:=` or the arms (D474).
        let decreasing_start = self.mark();
        if self.eat(&Tok::KwDecreasing) {
            if instance {
                return Err(error(self.prev_span(), "an instance can't have `decreasing`").into());
            }
            self.expr()?;
            self.node(decreasing_start, NodeKind::Decreasing);
            // After it, `:=` may start a line of its own, at the
            // declaration's column (§6.1's layout).
            if self
                .tokens
                .get(self.pos)
                .is_some_and(|t| t.tok == Tok::ColonEq && t.line_start)
            {
                self.modes.allow = Some(self.pos);
            }
        }
        // `unfolding f, g`, after `decreasing e` if both are written
        // (docs/proposals/opaque-definitions.md §6.3).
        let mut unfolding = None;
        let unfolding_start = self.mark();
        if self.eat(&Tok::KwUnfolding) {
            if instance {
                return Err(
                    error(self.prev_span(), "an instance can't have `unfolding`")
                        .with_note(
                            "an instance is never opaque, so it can't unfold opaque definitions",
                        )
                        .into(),
                );
            }
            loop {
                let name = match self.peek() {
                    Some(Tok::Upper(_)) => self.upper_q("the name of an opaque definition")?,
                    _ => self.lower_q("the name of an opaque definition")?,
                };
                unfolding.get_or_insert(name.span);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.node(unfolding_start, NodeKind::Unfolding);
            if self
                .tokens
                .get(self.pos)
                .is_some_and(|t| t.tok == Tok::ColonEq && t.line_start)
            {
                self.modes.allow = Some(self.pos);
            }
        }
        if self.peek() == Some(&Tok::KwDecreasing) && unfolding.is_some() {
            return Err(error(self.here(), "`decreasing` goes before `unfolding`").into());
        }
        // From here a top-level definition recovers from a syntax error in
        // its body (R6), and keeps its signature.
        let body = if keep && matches!(self.peek(), Some(Tok::ColonEq | Tok::Pipe)) {
            self.header_kept = true;
            self.recovering_body(|p| p.definition_body(start, column, result, instance, false))?
        } else {
            self.definition_body(start, column, result, instance, true)?
        };
        Ok(DefinitionRead {
            kind,
            unfolding,
            body,
            result,
        })
    }

    /// A definition's body, after its header: `:= e` or arms, and none for
    /// a primitive; whether it has one. `column` is the definition's, and
    /// `result` its result type's tokens. With `mark_body` false, a `:=`
    /// body's `Body` node is left to the caller ([`Self::recovering_body`]).
    fn definition_body(
        &mut self,
        start: Span,
        column: u32,
        result: (u32, u32),
        instance: bool,
        mark_body: bool,
    ) -> Result<bool> {
        let body = match self.peek() {
            Some(Tok::ColonEq) => {
                let body = self.mark();
                self.bump();
                self.expr()?;
                if mark_body {
                    self.node(body, NodeKind::Body);
                }
                if self.peek() == Some(&Tok::Pipe) {
                    return Err(error(
                        self.here(),
                        "a definition has a `:=` body or arms, not both",
                    )
                    .with_note(
                        "named parameters can't be matched in arms: to take one apart, move it \
                         after the colon, or use `match`",
                    )
                    .into());
                }
                true
            }
            Some(Tok::Pipe) => {
                self.arms(column)?;
                true
            }
            Some(Tok::Equals) => return Err(self.def_equals().into()),
            // `def f (x : Nat) : Nat = x`: the type swallowed the body as an
            // equation, and nothing follows.
            None if self.is_equation(result) => {
                return Err(Diagnostic::error(
                    "E-DEF-EQUALS",
                    "a definition's body follows `:=`; `=` is equality",
                )
                .with_label(
                    start.to(self.lowered_span(result)),
                    "this definition has no body",
                )
                .with_note(
                    "its type is read as an equation; if that `=` was meant to start the \
                     body, write `:=`",
                )
                .into());
            }
            // A header without a body: a primitive, for the elaborator to
            // admit or refuse.
            None => false,
            _ => {
                return Err(self
                    .unexpected("`:=` and the body, or arms starting with `|` on their own lines")
                    .into());
            }
        };
        if instance && !body {
            return Err(error(
                start.to(self.lowered_span(result)),
                "an instance needs a body",
            )
            .with_note("write `:=` and the instance's value after its type")
            .into());
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
            )
            .into());
        }
        Ok(body)
    }

    /// Whether the type in tokens `range` is an equation, `a = b`: a
    /// definition's type that swallowed its body.
    #[inline(never)]
    fn is_equation(&self, range: (u32, u32)) -> bool {
        let tokens = &self.tokens[range.0 as usize..range.1 as usize];
        tokens.iter().any(|t| t.tok == Tok::Equals)
            && matches!(
                self.lowered(range, false),
                Some(Lowered::Expr(Expr::Binary(BinOp::Eq, ..)))
            )
    }

    /// `type Grid = List (List Nat)`: a transparent name for a type, exactly
    /// `def Grid : Type := List (List Nat)`, after its `=`. `name` is its
    /// name. After `=`, `{` starts a record's fields and `|` a sum's
    /// constructors; anything else is the type.
    #[inline(never)]
    pub(super) fn type_synonym(&mut self, name: &crate::lexer::Token) -> Result<()> {
        let equals = self.mark() - 1;
        let body = self.mark();
        self.expr()?;
        let body = (body, self.mark());
        self.node(equals, NodeKind::Body);
        let ambiguous = |parser: &Self, what: &str| {
            error(
                parser.lowered_span(body),
                format!(
                    "`type {} = …` names a type, but this looks like {what}",
                    name_text(name)
                ),
            )
            .with_note(
                "a sum type's constructors each start with `|`: `type T = | A | B`, and \
                 `type T = | Foo (x: Nat)` for one constructor; a record is `type T = { … }`",
            )
        };
        if self.peek() == Some(&Tok::Pipe) {
            return Err(ambiguous(self, "a sum type without its leading `|`").into());
        }
        // An argument with an annotation, `Foo (x: Nat)`: only written in
        // brackets, with a `:`.
        let tokens = &self.tokens[body.0 as usize..body.1 as usize];
        if tokens.iter().any(|t| t.tok == Tok::Colon)
            && let Some(Lowered::Expr(expr)) = self.lowered(body, false)
        {
            let mut spine = &expr;
            while let Expr::App(f, arg) = spine {
                if matches!(**arg, Expr::Ann(..)) {
                    return Err(ambiguous(
                        self,
                        "a constructor with named fields, without its leading `|`",
                    )
                    .into());
                }
                spine = f;
            }
        }
        Ok(())
    }

    /// One parameter in a header: `(x y : A)`, `[x y : A]`, `[auto h : P]`
    /// or `()`.
    pub(super) fn header_param(&mut self) -> Result<ParamRead> {
        let mark = self.mark();
        let param = self.header_param_parts()?;
        self.node(mark, NodeKind::Param);
        Ok(param)
    }

    /// [`Self::header_param`] without its `Param` node: a lambda's or
    /// `∀`'s parameter, which is a `LambdaParam`.
    pub(super) fn header_param_parts(&mut self) -> Result<ParamRead> {
        let implicit = match self.peek() {
            Some(Tok::LParen) if self.peek_at(1) == Some(&Tok::RParen) => {
                self.bump();
                self.bump();
                return Ok(ParamRead { default: None });
            }
            Some(Tok::LParen) => false,
            Some(Tok::LBracket) => true,
            _ => {
                return Err(self
                    .unexpected("a parameter such as `(x: Nat)`, or `:` and the definition's type")
                    .into());
            }
        };
        self.bump();
        self.no_attributes("a definition's parameter")?;
        let first = self.param_name()?;
        let mut names = vec![name_text(first)];
        while let Some(Tok::Lower(_)) = self.peek() {
            names.push(name_text(self.param_name()?));
        }
        // `auto` is only special as the first word of a binder with names
        // after it, as in types; or, without a name, `[auto Ord a]`
        // (docs/proposals/interfaces.md §5.3).
        if implicit
            && names.len() == 1
            && names[0] == "auto"
            && !matches!(self.peek(), Some(Tok::Colon | Tok::RBracket) | None)
        {
            self.expr()?;
            if self.peek() != Some(&Tok::RBracket) {
                return Err(self
                    .unexpected("`]` to close the parameter `[auto …]`")
                    .into());
            }
            self.bump();
            return Ok(ParamRead { default: None });
        }
        let auto = implicit && names.len() > 1 && names[0] == "auto";
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
            names.join(" ")
        );
        if self.peek() != Some(&Tok::Colon) {
            return Err(error(self.here(), "a parameter needs a type")
                .with_note(format!("write `{written}{close}`"))
                .into());
        }
        self.bump();
        self.binder_type()?;
        let default = if self.peek() == Some(&Tok::ColonEq) {
            if implicit {
                return Err(error(self.here(), DEFAULT_PLACES).with_note(
                    "an implicit or `auto` parameter is found by unification or by search; give \
                     one at a call with `[x := …]`",
                ).into());
            }
            let default = self.mark();
            self.bump();
            let value = self.mark();
            self.expr()?;
            self.node(default, NodeKind::Default);
            Some((value, self.mark()))
        } else {
            None
        };
        if self.peek() != Some(&closing) {
            return Err(self
                .unexpected(&format!("`{close}` to close the parameter `{written}`"))
                .into());
        }
        self.bump();
        Ok(ParamRead { default })
    }

    /// The arms under a header, at `self.pos`'s `|`. `d` is the column of
    /// the definition's keyword. Layout rules L4 to L6 (§2.10): every arm's
    /// `|` starts a line at one column, right of `d`, and a line at or left
    /// of that column ends an arm's body.
    #[inline(never)]
    fn arms(&mut self, d: u32) -> Result<()> {
        let first = &self.tokens[self.pos];
        if !first.line_start {
            return Err(error(first.span, "arms start on their own lines")
                .with_note(
                    "put each `| … => …` on a line of its own, indented; a case analysis that fits \
                 on one line is a `:=` body with a `match`",
                )
                .into());
        }
        if first.column <= d {
            return Err(error(
                first.span,
                "arms are indented further than the definition they belong to",
            )
            .into());
        }
        let (column, first_span) = (first.column, first.span);
        let arms = self.mark();
        let saved = (self.modes.limit, self.modes.allow);
        self.modes.limit = Some(column);
        let result = (|| -> Result<()> {
            loop {
                self.modes.allow = Some(self.pos);
                self.arm()?;
                let Some(next) = self.tokens.get(self.pos) else {
                    return Ok(());
                };
                if !next.line_start {
                    return Err(self.unexpected("the end of the arm").into());
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
                        )
                        .into());
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
                        .with_note("an arm's body continues on lines indented further than its `|`")
                        .into());
                    }
                }
            }
        })();
        (self.modes.limit, self.modes.allow) = saved;
        result?;
        self.node(arms, NodeKind::Arms);
        Ok(())
    }

    /// `| p, q => body`, or with an absurd pattern, `| p, ()`: an equation
    /// whose patterns are the header's, then the arm's.
    fn arm(&mut self) -> Result<()> {
        let mark = self.mark();
        self.bump();
        let patterns = self.mark();
        self.alt_pattern()?;
        while self.eat(&Tok::Comma) {
            self.alt_pattern()?;
        }
        let absurd = self.absurd_since(patterns);
        self.guard()?;
        self.arm_body(absurd, "`=>` and the arm's body")?;
        self.node(mark, NodeKind::Arm);
        Ok(())
    }

    /// A handler's clause in the new syntax, after its `|`:
    /// `return x => body`, or `op p, k => body`. The argument is one atomic
    /// pattern, so a comma inside its brackets belongs to it. A `return`
    /// clause may write `_` for the result when it doesn't use it.
    #[inline(never)]
    pub(super) fn handler_clause(&mut self) -> Result<()> {
        if self.eat(&Tok::KwReturn) {
            if self.peek() == Some(&Tok::Underscore) {
                self.bump();
            } else {
                self.lower("a name for the result")?;
            }
            self.expect(Tok::FatArrow, "`=>`")?;
            return self.expr();
        }
        let op = self.lower_q("an operation, or `return`")?;
        let arg = self.mark();
        self.pattern()?;
        let arg = (arg, self.mark());
        if self.peek() == Some(&Tok::FatArrow) {
            return Err(error(
                self.here(),
                format!("name the continuation: `| {} x, k => …`", name_text(op)),
            )
            .into());
        }
        self.expect(Tok::Comma, "`,` and a name for the continuation")?;
        if self.peek() == Some(&Tok::Underscore) {
            self.bump();
        } else {
            self.lower("a name for the continuation")?;
        }
        if self.peek() == Some(&Tok::Comma) {
            return Err(error(
                self.lowered_pattern_span(arg).to(self.here()),
                "an operation takes one argument; bracket a tuple: `(a, b)`",
            )
            .into());
        }
        self.expect(Tok::FatArrow, "`=>`")?;
        self.expr()
    }
}
