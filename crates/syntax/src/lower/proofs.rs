//! Proofs: `calc`, `rewrite`, `arithmetic`, `algebra` and `cases`.

use crate::Span;
use crate::ast::{BinOp, CalcStep, Decl, Expr, Facts, Name, RewriteRule, Walk};
use crate::lexer::Tok;
use crate::tree::{Element, Node, NodeKind};

use super::access::required;
use super::{Lower, Lowering, Unsupported};

impl<'f> Lower<'f> {
    /// `calc a` and its steps, `_ = b := proof`; with `>` or `>=` steps,
    /// read the other way round ([`reverse_calc`]). A chain mixing the two
    /// directions is the parser's error.
    #[inline(never)]
    pub(super) fn calc(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Calc;
        let first = required(node.after(&Tok::KwCalc), kind, "its first expression")?;
        let first = self.expr(first)?;
        let mut descending = false;
        let steps = node
            .child_nodes()
            .filter(|child| child.kind() == NodeKind::CalcStep)
            .map(|step| {
                let (step, down) = self.calc_step(step)?;
                descending |= down;
                Ok(step)
            })
            .collect::<Lowering<Vec<_>>>()?;
        if steps.is_empty() {
            return Err(Unsupported::Missing(kind, "a step"));
        }
        let span = whole(node)?;
        let (first, steps) = if descending {
            reverse_calc(first, steps)
        } else {
            (first, steps)
        };
        Ok(Expr::Calc {
            first: Box::new(first),
            steps,
            span,
        })
    }

    /// `_ R rhs := proof`, or without a proof; and whether `R` is `>` or
    /// `>=`, stored as `<` or `<=`.
    fn calc_step(&self, node: Node<'f>) -> Lowering<(CalcStep, bool)> {
        let kind = NodeKind::CalcStep;
        let rel = match node.after(&Tok::Underscore) {
            Some(Element::Leaf(leaf)) => match leaf.tok() {
                Tok::Equals => Some((BinOp::Eq, false, leaf)),
                Tok::Le => Some((BinOp::Le, false, leaf)),
                Tok::Lt => Some((BinOp::Lt, false, leaf)),
                Tok::Ge => Some((BinOp::Le, true, leaf)),
                Tok::Gt => Some((BinOp::Lt, true, leaf)),
                _ => None,
            },
            _ => None,
        };
        let (rel, descending, rel_leaf) = required(rel, kind, "its relation")?;
        let rhs = required(node.after(rel_leaf.tok()), kind, "its expression")?;
        let proof = match node.leaf(&Tok::ColonEq) {
            Some(_) => {
                let proof = required(node.after(&Tok::ColonEq), kind, "its proof")?;
                Some(self.expr(proof)?)
            }
            None => None,
        };
        let step = CalcStep {
            rel,
            rel_span: rel_leaf.span(),
            rhs: self.expr(rhs)?,
            proof,
            span: whole(node)?,
        };
        Ok((step, descending))
    }

    /// `rewrite p, <- q at h then t`: the rules, then the target after `at`
    /// and the body after `then`, each optional. It spans the keyword to the
    /// end of the body, the target or the last rule, whichever is last.
    #[inline(never)]
    pub(super) fn rewrite(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Rewrite;
        let keyword = required(node.first_leaf_is(&Tok::KwRewrite), kind, "`rewrite`")?.span();
        let repeated = node.child(NodeKind::RewriteRules);
        let repeatedly = match repeated {
            Some(_) => node
                .own_leaves()
                .find(|leaf| matches!(leaf.tok(), Tok::Lower(word) if word == "repeatedly"))
                .map(|leaf| leaf.span()),
            None => None,
        };
        let rules = repeated
            .unwrap_or(node)
            .child_nodes()
            .filter(|child| child.kind() == NodeKind::RewriteRule)
            .map(|rule| self.rewrite_rule(rule))
            .collect::<Lowering<Vec<_>>>()?;
        // Before the `then`: a body can be a name `at`, `rewrite h then at`.
        let at = node
            .own_leaves()
            .take_while(|leaf| *leaf.tok() != Tok::KwThen)
            .find(|leaf| matches!(leaf.tok(), Tok::Lower(word) if word == "at"));
        let target = match at {
            Some(at) => {
                let target = required(node.after(at.tok()), kind, "its target")?;
                Some(Box::new(self.expr(target)?))
            }
            None => None,
        };
        let then = node.leaf(&Tok::KwThen);
        let body = match then {
            Some(_) => {
                let body = required(node.after(&Tok::KwThen), kind, "its body")?;
                Some(Box::new(self.expr(body)?))
            }
            None => None,
        };
        let last_rule = required(rules.last(), kind, "a rule")?.span;
        let end = body
            .as_deref()
            .or(target.as_deref())
            .map_or(last_rule, Expr::span);
        Ok(Expr::Rewrite {
            rules,
            target,
            body,
            keyword,
            repeatedly,
            at: at.map(|at| at.span()),
            then: then.map(|then| then.span()),
            span: keyword.to(end),
        })
    }

    /// `rules name := [r1, <- r2]`.
    pub(crate) fn rule_set(&self, root: Node<'f>) -> Lowering<Decl> {
        let kind = NodeKind::Rules;
        let keyword = required(root.own_leaves().next(), kind, "`rules`")?;
        let name = required(
            root.own_leaves()
                .nth(1)
                .filter(|leaf| matches!(leaf.tok(), Tok::Lower(_))),
            kind,
            "its name",
        )?;
        let body = required(root.child(NodeKind::Body), kind, "its rules")?;
        let list = required(body.child(NodeKind::RewriteRules), kind, "its rules")?;
        let rules = list
            .child_nodes()
            .filter(|child| child.kind() == NodeKind::RewriteRule)
            .map(|rule| self.rewrite_rule(rule))
            .collect::<Lowering<Vec<_>>>()?;
        let close = required(list.own_leaves().last(), kind, "`]`")?;
        let start = keyword.span();
        Ok(Decl::Rules {
            name: Name {
                text: match name.tok() {
                    Tok::Lower(text) => text.to_string(),
                    _ => unreachable!("filtered"),
                },
                span: name.span(),
            },
            rules,
            span: start.to(close.span()),
        })
    }

    /// `p` or `<- p`, from the `<` (if any) to the end of the proof.
    fn rewrite_rule(&self, node: Node<'f>) -> Lowering<RewriteRule> {
        let kind = NodeKind::RewriteRule;
        let (reverse, proof) = match node.first_leaf_is(&Tok::Lt) {
            Some(_) => (true, node.after(&Tok::Minus)),
            None => (false, node.children().next()),
        };
        let proof = self.expr(required(proof, kind, "its proof")?)?;
        let first = self.tree.tokens().get(node.token_range().start);
        let start = required(first, kind, "tokens")?.span;
        Ok(RewriteRule {
            reverse,
            unfold: false,
            span: start.to(proof.span()),
            proof,
        })
    }

    /// `arithmetic [h1, h2]` or `algebra [h1, h2]`: the facts are a list's items,
    /// and it spans the keyword to the `]` (a list of facts with a `..`
    /// spread is the parser's error).
    #[inline(never)]
    pub(super) fn with_facts(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = node.kind();
        let keyword = match node.children().next() {
            Some(Element::Leaf(leaf)) => Some(leaf.span()),
            _ => None,
        };
        let keyword = required(keyword, kind, "its keyword")?;
        let list = required(node.child(NodeKind::List), kind, "its facts")?;
        let Expr::List(facts, list_span) = &mut self.list(list)? else {
            unreachable!("a list lowers to a list")
        };
        let (facts, list_span) = (std::mem::take(facts), *list_span);
        if facts.iter().any(|fact| matches!(fact, Expr::Spread(..))) {
            return Err(Unsupported::Missing(kind, "facts without a spread"));
        }
        let span = keyword.to(list_span);
        Ok(match kind {
            NodeKind::Ring => Expr::Ring { facts, span },
            _ => Expr::Omega { facts, span },
        })
    }

    /// `cases then t`, spanning the keyword to the end of `t`.
    #[inline(never)]
    pub(super) fn cases(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Cases;
        let keyword = required(node.first_leaf_is(&Tok::KwCases), kind, "`cases`")?.span();
        let body = required(node.after(&Tok::KwThen), kind, "its body")?;
        let body = self.expr(body)?;
        Ok(Expr::Cases {
            span: keyword.to(body.span()),
            body: Some(Box::new(body)),
        })
    }
}

impl<'f> Lower<'f> {
    /// `byWalking [items] then t`, spanning the word to the `]` or to the
    /// end of `t`.
    #[inline(never)]
    pub(super) fn walk(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Walk;
        let keyword = match node.children().next() {
            Some(Element::Leaf(leaf)) => Some(leaf.span()),
            _ => None,
        };
        let keyword = required(keyword, kind, "its word")?;
        let list = required(node.child(NodeKind::List), kind, "its lemmas")?;
        let Expr::List(items, list_span) = &mut self.list(list)? else {
            unreachable!("a list lowers to a list")
        };
        let (items, list_span) = (std::mem::take(items), *list_span);
        let body = match node.after(&Tok::KwThen) {
            Some(body) => Some(self.expr(body)?),
            None => None,
        };
        let end = body.as_ref().map_or(list_span, Expr::span);
        Ok(Expr::Walk(Box::new(Walk {
            items,
            body,
            keyword,
            span: keyword.to(end),
            resume: None,
        })))
    }
}

impl<'f> Lower<'f> {
    /// `byFacts [items] then t`, spanning the word to the `]` (or the word
    /// alone) or to the end of `t`.
    #[inline(never)]
    pub(super) fn facts(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Facts;
        let keyword = match node.children().next() {
            Some(Element::Leaf(leaf)) => Some(leaf.span()),
            _ => None,
        };
        let keyword = required(keyword, kind, "its word")?;
        let (items, list_end) = match node.child(NodeKind::List) {
            Some(list) => {
                let Expr::List(items, list_span) = &mut self.list(list)? else {
                    unreachable!("a list lowers to a list")
                };
                (std::mem::take(items), *list_span)
            }
            None => (Vec::new(), keyword),
        };
        let body = match node.after(&Tok::KwThen) {
            Some(body) => Some(self.expr(body)?),
            None => None,
        };
        let end = body.as_ref().map_or(list_end, Expr::span);
        Ok(Expr::Facts(Box::new(Facts {
            items,
            body,
            keyword,
            span: keyword.to(end),
        })))
    }
}

/// A chain `a > b >= c` (its steps stored as `<`/`<=`, the proofs being of
/// the flipped forms `b < a`, `c <= b`) read the other way round:
/// `c <= b < a`. A step `_ = x` flips its proof with `Eq.flipped`.
pub(crate) fn reverse_calc(first: Expr, steps: Vec<CalcStep>) -> (Expr, Vec<CalcStep>) {
    let mut elements = vec![first];
    elements.extend(steps.iter().map(|step| step.rhs.clone()));
    let mut reversed = Vec::new();
    for (i, mut step) in steps.into_iter().enumerate().rev() {
        step.rhs = elements[i].clone();
        if step.rel == BinOp::Eq
            && let Some(proof) = step.proof.take()
        {
            // Empty, at the proof, so the application spans just the proof.
            let at = proof.span();
            let sym = Expr::Var(Name {
                text: "Std.Eq.flipped".into(),
                span: Span::new(at.file, at.start, at.start),
            });
            step.proof = Some(Expr::App(Box::new(sym), Box::new(proof)));
        }
        reversed.push(step);
    }
    (elements.pop().expect("a last element"), reversed)
}

fn whole(node: Node<'_>) -> Lowering<Span> {
    required(node.span(), node.kind(), "tokens")
}
