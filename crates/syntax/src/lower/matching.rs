//! Matching: `match … with`, its `induct` and `reify` forms, and `handle`.

use crate::Span;
use crate::ast::{Alt, Clause, Expr, Guard, InductAlt, MatchKind, Name, Pattern, Scrutinee};
use crate::lexer::Tok;
use crate::tree::{Element, Leaf, Node, NodeKind};

use super::access::required;
use super::decls::name;
use super::{Lower, Lowering, Unsupported};

impl<'f> Lower<'f> {
    /// `match e, h: f with | p, q => body | …`
    #[inline(never)]
    pub(super) fn match_expr(&self, node: Node<'f>) -> Lowering<Expr> {
        let scrutinees = node
            .child_nodes()
            .filter(|child| child.kind() == NodeKind::Scrutinee)
            .map(|scrutinee| self.scrutinee(scrutinee))
            .collect::<Lowering<Vec<_>>>()?;
        let alts = node
            .child_nodes()
            .filter(|child| child.kind() == NodeKind::Arm)
            .map(|arm| self.alt(arm))
            .collect::<Lowering<Vec<_>>>()?;
        Ok(Expr::Match {
            scrutinees,
            alts,
            span: whole(node)?,
            kind: MatchKind::Match,
        })
    }

    /// `e`, or `h: e` naming its equation.
    fn scrutinee(&self, node: Node<'f>) -> Lowering<Scrutinee> {
        let kind = NodeKind::Scrutinee;
        if node.leaf(&Tok::Colon).is_some() {
            let label = node.own_leaves().next().and_then(name);
            let expr = required(node.after(&Tok::Colon), kind, "its expression")?;
            return Ok(Scrutinee {
                name: Some(required(label, kind, "its name")?),
                expr: self.expr(expr)?,
            });
        }
        let mut parts = node.children();
        match (parts.next(), parts.next()) {
            (Some(expr), None) => Ok(Scrutinee {
                name: None,
                expr: self.expr(expr)?,
            }),
            _ => Err(Unsupported::Missing(kind, "one expression")),
        }
    }

    /// An alternative of a `match`, spanning its `|` to its end.
    fn alt(&self, arm: Node<'f>) -> Lowering<Alt> {
        let (patterns, guard, body) = self.arm_parts(arm)?;
        Ok(Alt {
            patterns,
            guard,
            body,
            span: whole(arm)?,
        })
    }

    /// `| p, q if c => body`: its patterns, its condition, and its body,
    /// which an arm with an absurd pattern `()` may leave out.
    pub(crate) fn arm_parts(
        &self,
        arm: Node<'f>,
    ) -> Lowering<(Vec<Pattern>, Option<Guard>, Option<Expr>)> {
        let kind = NodeKind::Arm;
        let mut patterns = Vec::new();
        let (mut guard, mut body) = (None, None);
        let mut parts = arm.children();
        required(parts.next().filter(|bar| is(bar, &Tok::Pipe)), kind, "`|`")?;
        while let Some(part) = parts.next() {
            match part {
                Element::Leaf(leaf) if *leaf.tok() == Tok::Comma => {}
                Element::Leaf(leaf) if *leaf.tok() == Tok::FatArrow => {
                    let rhs = required(parts.next(), kind, "its body")?;
                    body = Some(self.expr(rhs)?);
                    break;
                }
                Element::Node(node) if node.kind() == NodeKind::Guard => {
                    guard = Some(self.guard(node)?);
                }
                pattern => patterns.push(self.pattern(pattern)?),
            }
        }
        Ok((patterns, guard, body))
    }

    /// `handle e with | return x => … | op p, k => …`
    #[inline(never)]
    pub(super) fn handle(&self, node: Node<'f>) -> Lowering<Expr> {
        let body = required(node.after(&Tok::KwHandle), NodeKind::Handle, "its body")?;
        Ok(Expr::Handle {
            body: Box::new(self.expr(body)?),
            clauses: self.clauses(node)?,
            span: whole(node)?,
        })
    }

    /// `match reify t with | return x => … | op p, k => …`
    #[inline(never)]
    pub(super) fn reify(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Reify;
        let thunk = required(after_word(node, "reify"), kind, "its computation")?;
        Ok(Expr::Reify {
            thunk: Box::new(self.expr(thunk)?),
            clauses: self.clauses(node)?,
            span: whole(node)?,
        })
    }

    /// The handler clauses of a `handle` or `match reify`.
    fn clauses(&self, node: Node<'f>) -> Lowering<Vec<Clause>> {
        node.child_nodes()
            .filter(|child| child.kind() == NodeKind::HandlerClause)
            .map(|clause| self.clause(clause))
            .collect()
    }

    /// `| return x => body` or `| op p, k => body`.
    fn clause(&self, node: Node<'f>) -> Lowering<Clause> {
        let kind = NodeKind::HandlerClause;
        let body = required(node.after(&Tok::FatArrow), kind, "its body")?;
        if node.leaf(&Tok::KwReturn).is_some() {
            let var = as_leaf(node.after(&Tok::KwReturn)).and_then(name);
            return Ok(Clause::Return {
                var: required(var, kind, "a name for the result")?,
                body: self.expr(body)?,
            });
        }
        let op = as_leaf(node.after(&Tok::Pipe));
        let op = required(op.and_then(name), kind, "its operation")?;
        let mut parts = node.children().skip(2);
        let arg = required(parts.next(), kind, "its argument")?;
        let k = as_leaf(node.after(&Tok::Comma)).and_then(binder_name);
        Ok(Clause::Op {
            op,
            arg: self.pattern(arg)?,
            k: required(k, kind, "its continuation")?,
            body: self.expr(body)?,
        })
    }

    /// `match induct (f args) with | eqK x y ih => … | …`
    #[inline(never)]
    pub(super) fn induct(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Induct;
        let call = required(after_word(node, "induct"), kind, "its call")?;
        let alts = node
            .child_nodes()
            .filter(|child| child.kind() == NodeKind::InductArm)
            .map(|arm| self.induct_alt(arm))
            .collect::<Lowering<Vec<_>>>()?;
        Ok(Expr::Induct {
            call: Box::new(self.expr(call)?),
            alts,
            span: whole(node)?,
        })
    }

    /// `| eqK x _ ih => body`
    fn induct_alt(&self, node: Node<'f>) -> Lowering<InductAlt> {
        let kind = NodeKind::InductArm;
        let mut leaves = node.own_leaves().skip(1);
        let case = required(leaves.next().and_then(name), kind, "its case")?;
        let binders = leaves
            .take_while(|leaf| leaf.tok() != &Tok::FatArrow)
            .map(|leaf| required(binder_name(leaf), kind, "a binder"))
            .collect::<Lowering<Vec<_>>>()?;
        let body = required(node.after(&Tok::FatArrow), kind, "its body")?;
        Ok(InductAlt {
            case,
            binders,
            body: self.expr(body)?,
            span: whole(node)?,
        })
    }
}

/// A name, or `_`.
fn binder_name(leaf: Leaf<'_>) -> Option<Name> {
    match leaf.tok() {
        Tok::Underscore => Some(Name {
            text: "_".to_string(),
            span: leaf.span(),
        }),
        _ => name(leaf),
    }
}

/// The part after a node's own name token `word` (`reify`, `induct`: names
/// anywhere but after `match`).
fn after_word<'f>(node: Node<'f>, word: &str) -> Option<Element<'f>> {
    let mut children = node.children();
    children.find(|child| {
        matches!(child, Element::Leaf(leaf) if matches!(leaf.tok(), Tok::Lower(w) if w == word))
    })?;
    children.next()
}

fn as_leaf(element: Option<Element<'_>>) -> Option<Leaf<'_>> {
    match element? {
        Element::Leaf(leaf) => Some(leaf),
        Element::Node(_) => None,
    }
}

fn is(element: &Element<'_>, tok: &Tok) -> bool {
    matches!(element, Element::Leaf(leaf) if leaf.tok() == tok)
}

fn whole(node: Node<'_>) -> Lowering<Span> {
    required(node.span(), node.kind(), "tokens")
}

#[cfg(test)]
mod tests {
    use crate::SourceMap;
    use crate::lower::oracle::{Report, compare};

    fn report(text: &str) -> Report {
        compare(SourceMap::new().next_id(), text, crate::DEFAULT_STACK, true)
    }

    fn differences(report: &Report) -> Vec<String> {
        let at =
            |d: &crate::lower::oracle::Difference| format!("{} at {}:\n{}", d.what, d.at, d.detail);
        report.differences.iter().map(at).collect()
    }

    /// Lane L4's kinds come out of the lowering as the parser builds them,
    /// spans and tags included: every pattern kind in the places whose
    /// spans differ (brackets round a constructor or a negative number,
    /// the cells of lists and tuples), `match` with named scrutinees,
    /// guards and absurd arms, `handle`, `match reify`, `match induct`,
    /// `calc` in both directions, `rewrite` with each optional part,
    /// `omega`, `ring` and `cases`.
    #[test]
    fn matching_and_proofs_lower_as_parsed() {
        let text = "\
def p (x: T): Nat := match x, h: y with
  | Some (Pair a b), _ => a
  | (Some x), ((Some y)) => 1
  | (-1), ((-2)) => 2
  | Some -1, (-3, a) => 3
  | [], [..r] => 4
  | [a, b,], [A | B, ..r] => 5
  | (a, b, c), (Some a, (b, c)) => 6
  | { x, y = Some z, .. }, C { x = p, y } => 7
  | (C { x }), D [n := (Succ m)] y => 8
  | A | B, 'c' if h: q => 9
  | Quot.mk, n if n => 10
  | Rock, ()
  | (A | B), (Some _ | None) => match x with
    | 0 => 1
def h: Nat := handle f () with
  | return x => x
  | State.get (), k => k 0
  | put _, _ => 1
theorem r: P := match reify t with
  | return x => x
  | Fail.stop msg, k => k
theorem i: P := match induct (f a b) with
  | eq1 x _ ih => ih
  | eq2 => rfl
theorem c: a = d := calc a
  _ = b := p
  _ <= c
  _ < (d) := q
theorem c2: a > d := calc a
  _ > b := p
  _ = (c) := (q)
  _ >= d
theorem w: P := rewrite h, <- (g x) at k in t
theorem w2: P := rewrite h at (k)
theorem w3: P := rewrite <- h
  in t
theorem o: P := omega [h, (0 ..< n)] && ring [(a)] && ring && omega
theorem s: P := cases in (t)
theorem s2: P := f cases
";
        let report = report(text);
        assert_eq!(differences(&report), Vec::<String>::new());
        assert!(report.unsupported.is_empty(), "{:?}", report.unsupported);
        assert_eq!(report.lowered.len(), 12);
        assert!(!report.lowered.contains(&crate::tree::NodeKind::Error));
        assert!(report.expressions.unsupported.is_empty());
    }
}
