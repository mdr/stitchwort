//! The rule for each construct: how a node of the lossless tree becomes a
//! layout [`Doc`] (docs/proposals/formatter-style.md §2, S1 to S40).
//!
//! Spacing between two tokens on one line is the current formatter's
//! ([`crate::spacing`]); these rules only say where a construct may break
//! and how far each piece is indented. A construct with no rule here is
//! printed as written, moved with its line ([`Rules::as_written`]); the
//! counts of those come from [`unruled`], not from here.

use std::collections::BTreeMap;

use super::token_text_range;
use stitchwort_syntax::tree::{Element, Leaf, Node, NodeKind, SyntaxFile};
use stitchwort_syntax::{Tok, Token};

use super::WIDTH;
use super::engine::{self, Doc};
use crate::spacing::{Gap, Pair, Role, gap};

/// The kinds printed as written for now, deliberately or for want of a
/// rule: only a node the parser couldn't make sense of.
pub(crate) fn has_rule(kind: NodeKind) -> bool {
    kind != NodeKind::Error
}

/// How many nodes of each kind in `root` have no rule. A node inside one
/// without a rule is counted too: it is printed as written as well.
pub(crate) fn unruled(root: Node<'_>, counts: &mut BTreeMap<NodeKind, usize>) {
    if !has_rule(root.kind()) {
        *counts.entry(root.kind()).or_default() += 1;
    }
    for child in root.children() {
        if let Element::Node(node) = child {
            unruled(node, counts);
        }
    }
}

pub(crate) struct Rules<'a> {
    file: &'a SyntaxFile,
    src: &'a str,
    tokens: &'a [Token],
    roles: Vec<Role>,
    /// Tokens before which an author's blank line is kept: the first token
    /// of an item of a vertical list (E4).
    keep_blank: Vec<bool>,
    /// Tokens whose own-line comments the file prints, not the declaration:
    /// each declaration's first.
    file_comments: Vec<bool>,
    /// Tokens whose own-line comments an element starting with them prints
    /// outside its groups, so they don't break them: set while the element
    /// is built.
    hoisted: Vec<bool>,
    /// Set while calls must not hug their last argument.
    no_hug: bool,
    /// How many alternatives (arms, clauses) the node being built is in.
    arm_depth: usize,
    /// Each call's hug (S23), by its first token, for a body after `:=`
    /// that opens on the line with it (S12).
    hugs: BTreeMap<usize, Doc>,
    /// A `match`'s doc with its head flat, by the match's first token, for a
    /// body that hugs the `:=` line.
    match_hugs: BTreeMap<usize, Doc>,
    next_id: u32,
}

/// Whether a token closes a bracket.
/// A run of a header's variables as a fill, except that the last line never
/// holds one variable alone when the line above could give it a companion
/// (SW-3193): that line's last variable moves down to it. `first` says the
/// run starts with the head, on the declaration's line; the other lines
/// start at the header's indentation, 4.
fn balanced_fill(items: Vec<Doc>, first: bool) -> Doc {
    let widths: Option<Vec<usize>> = items
        .iter()
        .map(|item| {
            let flat = engine::print(&Doc::flat(item.clone()), usize::MAX / 2);
            let simple =
                !item.forces_break() && flat.forced_comment_lines == 0 && !flat.text.contains('\n');
            simple.then(|| flat.text.chars().count())
        })
        .collect();
    let Some(widths) = widths else {
        return Doc::Fill(items);
    };
    // Where the greedy fill starts each line.
    let mut starts = vec![0];
    let mut column = if first { widths[0] } else { 4 + widths[0] };
    for (k, &width) in widths.iter().enumerate().skip(1) {
        if column + 1 + width > WIDTH {
            starts.push(k);
            column = 4 + width;
        } else {
            column += 1 + width;
        }
    }
    let [.., above, last] = starts[..] else {
        return Doc::Fill(items);
    };
    // The last line has one item; the line above, at least two, and the
    // moved item and the lone one must fit side by side.
    let lone = items.len() - 1;
    let moved = lone - 1;
    if last != lone || above + 1 >= last || 4 + widths[moved] + 1 + widths[lone] > WIDTH {
        return Doc::Fill(items);
    }
    let mut head = items;
    let tail = head.split_off(moved);
    Doc::concat([Doc::Fill(head), Doc::Line, Doc::Fill(tail)])
}

fn closer(tok: &Tok) -> bool {
    matches!(tok, Tok::RParen | Tok::RBracket | Tok::RBrace)
}

fn opener(tok: &Tok) -> bool {
    matches!(tok, Tok::LParen | Tok::LBracket | Tok::LBrace)
}

/// Operators that chain at one level (S27): a broken chain puts each of
/// them at the start of a line. `None` for a token that is no such
/// operator.
fn level(tok: &Tok) -> Option<u8> {
    use Tok::*;
    Some(match tok {
        Iff => 0,
        Arrow => 1,
        OrOr => 2,
        AndAnd => 3,
        Equals | EqEq | NotEq | Lt | Le | Gt | Ge => 4,
        PlusPlus => 5,
        Plus | Minus => 6,
        Star | Slash | Percent => 7,
        PipeGt => 8,
        _ => return None,
    })
}

impl<'a> Rules<'a> {
    pub(crate) fn new(file: &'a SyntaxFile, src: &'a str) -> Self {
        let tokens = file.tokens();
        let mut file_comments = vec![false; tokens.len()];
        for decl in file.decls() {
            if let Some(start) = Some(decl.token_range().start).filter(|&s| s < tokens.len()) {
                file_comments[start] = true;
            }
        }
        Rules {
            file,
            src,
            tokens,
            roles: crate::spacing::roles(tokens),
            keep_blank: vec![false; tokens.len()],
            file_comments,
            hoisted: vec![false; tokens.len()],
            no_hug: false,
            arm_depth: 0,
            hugs: BTreeMap::new(),
            match_hugs: BTreeMap::new(),
            next_id: 0,
        }
    }

    fn fresh_id(&mut self) -> u32 {
        self.next_id += 1;
        self.next_id
    }

    // ---- Elements, tokens and the spaces between them.

    fn first(el: Element<'_>) -> usize {
        match el {
            Element::Leaf(leaf) => leaf.index(),
            Element::Node(node) => node.token_range().start,
        }
    }

    fn last(el: Element<'_>) -> usize {
        match el {
            Element::Leaf(leaf) => leaf.index(),
            Element::Node(node) => node.token_range().end - 1,
        }
    }

    fn tok(&self, el: Element<'_>) -> Option<&'a Tok> {
        match el {
            Element::Leaf(leaf) => Some(&self.tokens[leaf.index()].tok),
            Element::Node(_) => None,
        }
    }

    fn is_tok(&self, el: Element<'_>, want: &Tok) -> bool {
        self.tok(el) == Some(want)
    }

    fn kind(el: Element<'_>) -> Option<NodeKind> {
        match el {
            Element::Node(node) => Some(node.kind()),
            Element::Leaf(_) => None,
        }
    }

    /// The indentation of the source line holding byte `at`.
    fn line_indent_at(&self, at: usize) -> usize {
        let start = self.src[..at].rfind('\n').map_or(0, |k| k + 1);
        let line = &self.src[start..];
        line.len() - line.trim_start_matches(' ').len()
    }

    /// What goes between tokens `l` and `r` on one line.
    fn space(&self, l: usize, r: usize) -> Doc {
        let (left, right) = (&self.tokens[l], &self.tokens[r]);
        let (left_end, right_start) = (token_text_range(left).end, token_text_range(right).start);
        let pair = Pair {
            left: &left.tok,
            left_role: self.roles[l],
            right: &right.tok,
            right_role: self.roles[r],
            after: self.tokens.get(r + 1).map(|t| &t.tok),
            spaced: left_end < right_start,
        };
        match gap(&pair) {
            Gap::Rule(true) | Gap::Kept(true) | Gap::Copied(true) => Doc::text(" "),
            Gap::Rule(false) | Gap::Kept(false) | Gap::Copied(false) => Doc::Nil,
            Gap::Source => {
                let between = &self.src[left_end.min(right_start)..right_start];
                if between.contains('\n') {
                    Doc::text(" ")
                } else {
                    Doc::text(between)
                }
            }
        }
    }

    /// The space between two elements.
    fn space_el(&self, l: Element<'_>, r: Element<'_>) -> Doc {
        self.space(Self::last(l), Self::first(r))
    }

    /// Own-line comments and kept blank lines before token `i`.
    fn leading(&self, i: usize) -> Vec<Doc> {
        let trivia = &self.file.trivia()[i];
        let keep = self.keep_blank[i];
        let mut parts = Vec::new();
        if self.hoisted[i] {
            return parts;
        }
        if !self.file_comments[i] && !trivia.leading.is_empty() {
            parts.push(Doc::BreakParent);
            parts.push(Doc::LineStart);
            for (k, comment) in trivia.leading.iter().enumerate() {
                if comment.blank_lines_before > 0 && (k > 0 || keep) {
                    parts.push(Doc::Blank);
                }
                parts.push(Doc::text(comment.text.trim_end_matches(' ')));
                parts.push(Doc::HardLine);
            }
            if trivia.blank_lines_before > 0 {
                parts.push(Doc::Blank);
            }
        } else if keep && trivia.blank_lines_before > 0 {
            parts.push(Doc::BreakParent);
            parts.push(Doc::Blank);
        }
        parts
    }

    /// The comment after token `i` on its line.
    fn trailing(&self, i: usize) -> Vec<Doc> {
        match &self.file.trivia()[i].trailing {
            Some(comment) => vec![Doc::LineSuffix(
                comment.text.trim_end_matches(' ').to_string(),
            )],
            None => Vec::new(),
        }
    }

    /// A token's text: a text block (S33) moves with its line.
    fn token_text(&self, i: usize) -> Doc {
        let range = token_text_range(&self.tokens[i]);
        let text = &self.src[range.clone()];
        if text.contains('\n') {
            Doc::TextBlock {
                text: text.to_string(),
                src_indent: self.line_indent_at(range.start),
            }
        } else {
            Doc::text(text)
        }
    }

    fn leaf(&self, leaf: Leaf<'_>) -> Doc {
        let i = leaf.index();
        let mut parts = self.leading(i);
        parts.push(self.token_text(i));
        parts.extend(self.trailing(i));
        Doc::concat(parts)
    }

    /// The comments of a comma that starts its line (D1012), as own-line
    /// comments for the item after it: the comma moves to the end of the
    /// previous item's line, and a comment on either side of it stays with
    /// the next token, as `comment_anchors` reads them.
    fn comma_first_comments(&mut self, i: usize) -> Vec<Doc> {
        let trivia = &self.file.trivia()[i];
        let has_leading = !trivia.leading.is_empty();
        let trailing = trivia.trailing.clone();
        let first_on_line = comma_first_on_line(self.src, token_text_range(&self.tokens[i]).start);
        let mut parts = Vec::new();
        if has_leading {
            self.keep_blank[i] = true;
            parts.extend(self.leading(i));
        }
        if let (true, Some(comment)) = (first_on_line, trailing) {
            parts.extend([
                Doc::BreakParent,
                Doc::LineStart,
                Doc::text(comment.text.trim_end_matches(' ')),
                Doc::HardLine,
            ]);
        }
        parts
    }

    /// A comma's text and its trailing comment, unless it starts its line
    /// (then `comma_first_comments` placed the comment).
    fn comma_end(&self, i: usize) -> Doc {
        let mut parts = vec![self.token_text(i)];
        if !comma_first_on_line(self.src, token_text_range(&self.tokens[i]).start) {
            parts.extend(self.trailing(i));
        }
        Doc::concat(parts)
    }

    /// A token's comments without its text: a comma the formatter drops.
    fn leaf_trivia_only(&self, i: usize) -> Doc {
        let mut parts = self.leading(i);
        parts.extend(self.trailing(i));
        Doc::concat(parts)
    }

    fn el(&mut self, el: Element<'_>) -> Doc {
        match el {
            Element::Leaf(leaf) => self.leaf(leaf),
            Element::Node(node) => {
                let first = node.token_range().start;
                let leading = self.leading(first);
                let saved = std::mem::replace(&mut self.hoisted[first], true);
                let doc = self.node(node);
                self.hoisted[first] = saved;
                Doc::concat([Doc::concat(leading), doc])
            }
        }
    }

    /// Whether own-line comments come before the element.
    fn has_leading(&self, el: Element<'_>) -> bool {
        !self.file.trivia()[Self::first(el)].leading.is_empty()
    }

    /// Elements on one line, with the usual spaces between them.
    fn join(&mut self, els: &[Element<'_>]) -> Doc {
        let mut parts = Vec::new();
        for (k, &el) in els.iter().enumerate() {
            // A block of two or more lines always starts a line of its own
            // (S12, S17): inside brackets, below them at 2.
            if k > 0 && Self::kind(el) == Some(NodeKind::Block) {
                let block = self.el(el);
                parts.push(Doc::nest(2, Doc::concat([Doc::HardLine, block])));
                continue;
            }
            if k > 0 {
                parts.push(self.space_el(els[k - 1], el));
            }
            parts.push(self.el(el));
        }
        Doc::concat(parts)
    }

    fn mark_item(&mut self, el: Element<'_>) {
        self.keep_blank[Self::first(el)] = true;
    }

    /// Whether the element holds a text block.
    fn holds_text_block(&self, el: Element<'_>) -> bool {
        let (a, b) = (Self::first(el), Self::last(el));
        (a..=b).any(|i| self.src[token_text_range(&self.tokens[i])].contains('\n'))
    }

    /// Whether a comment ends a line anywhere inside the node: a vertical
    /// list holding one stays broken (S39), so the comment keeps
    /// describing its item's line.
    fn holds_trailing_comment(&self, node: Node<'_>) -> bool {
        let range = node.token_range();
        self.file.trivia()[range.start..range.end - 1]
            .iter()
            .any(|t| t.trailing.is_some())
    }

    /// Whether a comment ends the line after the element's last token.
    fn trails_comment(&self, el: Element<'_>) -> bool {
        self.file.trivia()[Self::last(el)].trailing.is_some()
    }

    /// A construct with no rule yet: as written, moved with its line, its
    /// first token's comments and its last token's trailing comment placed
    /// as for any token.
    pub(crate) fn as_written(&self, node: Node<'_>) -> Doc {
        let range = node.token_range();
        let (first, last) = (range.start, range.end - 1);
        let start = token_text_range(&self.tokens[first]).start;
        let end = token_text_range(&self.tokens[last]).end;
        let mut parts = self.leading(first);
        parts.push(Doc::Verbatim {
            text: self.src[start..end].to_string(),
            src_indent: self.line_indent_at(start),
        });
        parts.extend(self.trailing(last));
        Doc::concat(parts)
    }

    // ---- Constructs.

    pub(crate) fn node(&mut self, node: Node<'_>) -> Doc {
        use NodeKind::*;
        match node.kind() {
            Def | Theorem | Instance | Test => self.decl(node),
            DataType => self.data_type(node),
            RecordType | Interface | TypeSynonym => self.type_decl(node),
            Ability => self.ability(node),
            Import => self.import(node),
            Block => self.block(node),
            Let => self.let_line(node),
            App => self.app(node),
            Binary | Chain | Iff | Arrow | Pipe | FunctionType => self.chain(node),
            Forall | Exists => self.quantifier(node),
            LetExpr | Seq => self.sequence(node),
            Interpolated => self.interpolated(node),
            Interpolation => self.interpolation(node),
            PatternCtor => self.app(node),
            Lambda => self.lambda(node),
            If => self.if_(node),
            Match | Handle | Reify | Induct | ClauseLambda => self.alternatives(node),
            Arm | HandlerClause | InductArm => self.arm(node),
            List | Tuple | Record | Fields | PatternList | PatternTuple | PatternRecord
            | Attributes => self.comma_bracket(node),
            Paren => self.paren(node),
            Calc => self.calc(node),
            CalcStep => self.calc_step(node),
            Rewrite => self.rewrite(node),
            Constructor => self.constructor(node),
            kind if has_rule(kind) => {
                let children: Vec<Element> = node.children().collect();
                self.join(&children)
            }
            _ => self.as_written(node),
        }
    }

    /// `( … )`. A bracketed `if` keeps its `else` lines under the `if`, not
    /// under the bracket (S19: the clauses start at the `if`'s column).
    fn paren(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let mut parts = Vec::new();
        for (k, &el) in children.iter().enumerate() {
            if k > 0 {
                parts.push(self.space_el(children[k - 1], el));
            }
            let doc = self.el(el);
            parts.push(if Self::kind(el) == Some(NodeKind::If) {
                Doc::align(doc)
            } else {
                doc
            });
        }
        Doc::concat(parts)
    }

    /// `def`, `theorem`, `instance` and `test` (S6 to S13), at top level or
    /// in a block.
    fn decl(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let mut parts = Vec::new();
        let mut k = 0;
        // S5: an attribute above a declaration has its own line.
        while let Some(&el) = children.get(k)
            && Self::kind(el) == Some(NodeKind::Attributes)
        {
            parts.push(self.el(el));
            parts.push(Doc::HardLine);
            k += 1;
        }
        let head_end = children[k..]
            .iter()
            .position(|&el| Self::kind(el).is_some())
            .map_or(children.len(), |p| k + p);
        let head: Vec<Element> = children[k..head_end].to_vec();
        let mut params = Vec::new();
        let mut result = None;
        let mut decreasing = None;
        let mut unfolding = None;
        let mut body = None;
        let mut arms = None;
        for &el in &children[head_end..] {
            match Self::kind(el) {
                Some(NodeKind::Param) => params.push(el),
                Some(NodeKind::ResultType) => result = Some(el),
                Some(NodeKind::Decreasing) => decreasing = Some(el),
                Some(NodeKind::Unfolding) => unfolding = Some(el),
                Some(NodeKind::Body) => body = Some(el),
                Some(NodeKind::Arms) => arms = Some(el),
                _ => return self.as_written(node),
            }
        }
        let id = self.fresh_id();
        // `unfolding` comes after `decreasing`, on a line of its own then.
        let (unfolding, unfolding_below) = match decreasing {
            Some(_) => (None, unfolding),
            None => (unfolding, None),
        };
        let header = self.header(&head, &params, result, unfolding);
        parts.push(Doc::IdGroup(
            id,
            Box::new(header.clone()),
            header.forces_break(),
        ));
        if let Some(decreasing) = decreasing {
            // S11: the measure on its own line at 4, `:=` alone below.
            let measure = self.el(decreasing);
            parts.push(Doc::nest(4, Doc::concat([Doc::HardLine, measure])));
            if let Some(unfolding) = unfolding_below {
                let unfolding = self.el(unfolding);
                parts.push(Doc::nest(4, Doc::concat([Doc::HardLine, unfolding])));
            }
            if let Some(Element::Node(body)) = body {
                let inner: Vec<Element> = body.children().collect();
                let assign = self.el(inner[0]);
                parts.push(Doc::HardLine);
                parts.push(assign);
                let value = self.join(&inner[1..]);
                parts.push(Doc::nest(2, Doc::concat([Doc::HardLine, value])));
            }
        } else if let Some(Element::Node(body)) = body {
            let inner: Vec<Element> = body.children().collect();
            let assign = self.el(inner[0]);
            parts.push(Doc::text(" "));
            parts.push(assign);
            let below_and_choice = self.body_after(&inner[1..]);
            let (below, choice) = below_and_choice;
            parts.push(Doc::IfBroken {
                id,
                broken: Box::new(below),
                flat: Box::new(choice),
            });
        }
        if let Some(Element::Node(arms)) = arms {
            let mut lines = Vec::new();
            self.arm_depth += 1;
            for arm in arms.children() {
                self.mark_item(arm);
                lines.push(Doc::HardLine);
                lines.push(self.el(arm));
            }
            self.arm_depth -= 1;
            parts.push(Doc::nest(2, Doc::concat(lines)));
        }
        Doc::concat(parts)
    }

    /// A header (S6 to S8): the head (`def name`, `theorem name ∀`), the
    /// parameters, and the result type or conclusion. On one line if it
    /// fits; otherwise the parameters fill lines at 4, each premise on a
    /// line of its own (D3564), and the conclusion on its own line at 4.
    fn header(
        &mut self,
        head: &[Element<'_>],
        params: &[Element<'_>],
        result: Option<Element<'_>>,
        unfolding: Option<Element<'_>>,
    ) -> Doc {
        let head_doc = self.join(head);
        let (colon, ty) = match result {
            Some(Element::Node(result)) => {
                let inner: Vec<Element> = result.children().collect();
                let colon = self.el(inner[0]);
                let ty = self.join(&inner[1..]);
                (Some(colon), Some(ty))
            }
            _ => (None, None),
        };
        let unfolding = unfolding.map(|el| self.el(el));
        if params.is_empty() {
            let mut parts = vec![head_doc];
            if let (Some(colon), Some(ty)) = (colon, ty) {
                parts.push(colon);
                parts.push(Doc::text(" "));
                parts.push(Doc::nest(4, ty));
            }
            if let Some(unfolding) = unfolding {
                parts.push(Doc::nest(4, Doc::concat([Doc::Line, unfolding])));
            }
            return Doc::concat(parts);
        }
        // Runs of variables, each run a fill; each premise alone (D3564).
        let premises = self.premises(params);
        let mut runs: Vec<Doc> = Vec::new();
        let mut run: Vec<Doc> = vec![head_doc];
        let mut first_run = true;
        let last = params.len() - 1;
        let mut previous = head.last().copied();
        for (k, &param) in params.iter().enumerate() {
            let mut doc = self.el(param);
            if k == last
                && let Some(colon) = &colon
            {
                doc = Doc::concat([doc, colon.clone()]);
            }
            // `def main()`: an empty `()` touching its name (or the one
            // before it) stays attached, as a call's does.
            let (first, end) = (Self::first(param), Self::last(param));
            let attached = end == first + 1
                && self.tokens[first].tok == Tok::LParen
                && previous.is_some_and(|prev| matches!(self.space_el(prev, param), Doc::Nil));
            previous = Some(param);
            if attached && !premises[k] && !run.is_empty() {
                let at = run.pop().expect("a run item");
                run.push(Doc::concat([at, doc]));
                continue;
            }
            if premises[k] {
                if !run.is_empty() {
                    runs.push(balanced_fill(std::mem::take(&mut run), first_run));
                    first_run = false;
                }
                runs.push(doc);
            } else if run.is_empty()
                && k > 0
                && premises[k - 1]
                && premises.get(k + 1).is_none_or(|&next| next)
                && let Some(premise) = runs.pop()
            {
                // A single variable between premises shares the line of
                // the premise before it, not a line of its own (D3571).
                runs.push(Doc::Fill(vec![premise, doc]));
            } else {
                run.push(doc);
            }
        }
        if !run.is_empty() {
            runs.push(balanced_fill(run, first_run));
        }
        let mut parts = Vec::new();
        for (k, run) in runs.into_iter().enumerate() {
            if k > 0 {
                parts.push(Doc::Line);
            }
            parts.push(run);
        }
        if let Some(ty) = ty {
            parts.push(Doc::Line);
            parts.push(ty);
        }
        if let Some(unfolding) = unfolding {
            parts.push(Doc::Line);
            parts.push(unfolding);
        }
        // The first run starts with the head, on the declaration's line.
        Doc::nest(4, Doc::concat(parts))
    }

    /// Which parameters are premises (D3564): the type has a relation or
    /// connective at its top, or at the end of its `→`/`∀` chain, or applies
    /// a capitalised name to an earlier parameter that is not a type.
    fn premises(&self, params: &[Element<'_>]) -> Vec<bool> {
        let mut earlier: Vec<&str> = Vec::new();
        let mut out = Vec::new();
        for &param in params {
            let Element::Node(param) = param else {
                out.push(false);
                continue;
            };
            let children: Vec<Element> = param.children().collect();
            let colon = children.iter().position(|&el| self.is_tok(el, &Tok::Colon));
            let names: Vec<&str> = children[..colon.unwrap_or(0)]
                .iter()
                .filter_map(|&el| match el {
                    Element::Leaf(leaf)
                        if matches!(self.tokens[leaf.index()].tok, Tok::Lower(_)) =>
                    {
                        Some(&self.src[leaf.text_range()])
                    }
                    _ => None,
                })
                .collect();
            let ty = colon.and_then(|c| children.get(c + 1).copied());
            let premise = ty.is_some_and(|ty| self.is_proposition(ty, &earlier));
            let is_type = ty.is_some_and(|ty| {
                matches!(self.tok(ty), Some(Tok::TypeU | Tok::Prop))
                    || Self::kind(ty) == Some(NodeKind::Universe)
            });
            if !is_type {
                earlier.extend(names);
            }
            out.push(premise);
        }
        out
    }

    fn is_proposition(&self, ty: Element<'_>, earlier: &[&str]) -> bool {
        let Element::Node(node) = ty else {
            return false;
        };
        let children: Vec<Element> = node.children().collect();
        match node.kind() {
            NodeKind::Binary => children
                .get(1)
                .and_then(|&op| self.tok(op))
                .is_some_and(|op| {
                    matches!(
                        op,
                        Tok::Equals
                            | Tok::NotEq
                            | Tok::Lt
                            | Tok::Le
                            | Tok::Gt
                            | Tok::Ge
                            | Tok::AndAnd
                            | Tok::OrOr
                            | Tok::EqEq
                    )
                }),
            NodeKind::Chain | NodeKind::Membership | NodeKind::Iff | NodeKind::Exists => true,
            NodeKind::Prefix => children
                .first()
                .is_some_and(|&el| self.is_tok(el, &Tok::Bang)),
            NodeKind::Arrow | NodeKind::FunctionType | NodeKind::Forall => children
                .last()
                .is_some_and(|&last| self.is_proposition(last, earlier)),
            NodeKind::Paren => children
                .get(1)
                .is_some_and(|&inner| self.is_proposition(inner, earlier)),
            NodeKind::App => {
                let capital = children.first().is_some_and(|&head| match head {
                    Element::Leaf(leaf) => {
                        let text = &self.src[leaf.text_range()];
                        let last = text.rsplit('.').next().unwrap_or(text);
                        last.starts_with(|c: char| c.is_ascii_uppercase())
                    }
                    Element::Node(_) => false,
                });
                capital
                    && children[1..].iter().any(|&arg| {
                        let mut found = false;
                        let (a, b) = (Self::first(arg), Self::last(arg));
                        for i in a..=b {
                            if let Tok::Lower(name) = &self.tokens[i].tok
                                && earlier.contains(&name.as_str())
                            {
                                found = true;
                            }
                        }
                        found
                    })
            }
            _ => false,
        }
    }

    /// What follows a `:=` (S12, S17): the doc for a header that broke (the
    /// value below at 2), and the choice for one that didn't: on the line if
    /// all of it fits; on the line if it is a `match`, `calc`, comma bracket,
    /// text block or hug whose first line fits; else below.
    fn body_after(&mut self, value: &[Element<'_>]) -> (Doc, Doc) {
        let doc = Doc::shared(self.join(value));
        let below = Doc::nest(2, Doc::concat([Doc::HardLine, doc.clone()]));
        if value
            .first()
            .is_some_and(|&el| self.has_leading(el) || Self::kind(el) == Some(NodeKind::Block))
        {
            return (below.clone(), below);
        }
        let mut options = vec![Doc::flat(Doc::concat([Doc::text(" "), doc.clone()]))];
        if let [el] = value {
            let el = *el;
            let match_hug = match el {
                Element::Node(node) if node.kind() == NodeKind::Match => {
                    self.match_hugs.get(&node.token_range().start).cloned()
                }
                _ => None,
            };
            let opens = match_hug.is_none()
                && matches!(
                    Self::kind(el),
                    Some(
                        NodeKind::Induct
                            | NodeKind::Reify
                            | NodeKind::ClauseLambda
                            | NodeKind::Calc
                            | NodeKind::List
                            | NodeKind::Record
                            | NodeKind::Tuple
                    )
                )
                || self.holds_text_block(el);
            // D3571: a record, list, tuple or hugging call goes below when
            // it fits on one line there; it hugs only when it can't.
            let hugs_after = matches!(
                Self::kind(el),
                Some(NodeKind::List | NodeKind::Record | NodeKind::Tuple)
            ) || matches!(el, Element::Node(node)
                if node.kind() == NodeKind::App
                    && self.hugs.contains_key(&node.token_range().start));
            if hugs_after {
                options.push(Doc::OneLineBelow(Box::new(doc.clone())));
            }
            if let Some(hug) = match_hug {
                // D3553, S12: a `match` joins the `:=` line only when its
                // whole `match … with` fits there; the scrutinee must not
                // wrap level with the arms.
                options.push(Doc::concat([Doc::text(" "), hug]));
            } else if opens {
                options.push(Doc::concat([Doc::text(" "), doc.clone()]));
            } else if let Element::Node(node) = el
                && node.kind() == NodeKind::Lambda
            {
                // D3568: a lambda stays on the `:=` line, its body below
                // at 2, as a last-argument lambda hugs.
                let (_, open) = self.lambda_both(node);
                options.push(Doc::concat([Doc::text(" "), open]));
            } else if let Element::Node(node) = el
                && node.kind() == NodeKind::App
                && let Some(hug) = self.hugs.get(&node.token_range().start).cloned()
            {
                options.push(Doc::concat([Doc::text(" "), hug]));
            }
        }
        options.push(below.clone());
        (below, Doc::Choice(options))
    }

    /// A data type (S14, D3566 (b)): its constructors on one line if the
    /// whole declaration fits, otherwise one a line at 2.
    fn data_type(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let split = children
            .iter()
            .position(|&el| Self::kind(el) == Some(NodeKind::Constructor))
            .unwrap_or(children.len());
        let (attrs, rest) = self.split_attributes(&children[..split]);
        let head = self.join(rest);
        let mut lines = Vec::new();
        for &ctor in &children[split..] {
            if Self::kind(ctor) != Some(NodeKind::Constructor) {
                return self.as_written(node);
            }
            self.mark_item(ctor);
            lines.push(Doc::Line);
            lines.push(self.el(ctor));
        }
        if self.holds_trailing_comment(node) {
            lines.push(Doc::BreakParent);
        }
        Doc::concat([
            attrs,
            Doc::group(Doc::concat([head, Doc::nest(2, Doc::concat(lines))])),
        ])
    }

    /// Attributes above a declaration, each on its own line (S5), and the
    /// rest.
    fn split_attributes<'e>(&mut self, els: &'e [Element<'e>]) -> (Doc, &'e [Element<'e>]) {
        let mut parts = Vec::new();
        let mut k = 0;
        while let Some(&el) = els.get(k)
            && Self::kind(el) == Some(NodeKind::Attributes)
        {
            parts.push(self.el(el));
            parts.push(Doc::HardLine);
            k += 1;
        }
        (Doc::concat(parts), &els[k..])
    }

    /// `| C fields`: the fields stay on its line (S14).
    fn constructor(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let mut parts = Vec::new();
        for (k, &el) in children.iter().enumerate() {
            if k > 0 {
                let space = self.space_el(children[k - 1], el);
                if Self::kind(el) == Some(NodeKind::Binder) {
                    parts.push(Doc::nest(4, Doc::concat([Doc::Line])));
                } else {
                    parts.push(space);
                }
            }
            parts.push(self.el(el));
        }
        Doc::group(Doc::concat(parts))
    }

    /// Record types, interfaces and type synonyms: a header, then `=` and
    /// a record's fields (S15) or a type (S6, S34).
    fn type_decl(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let (attrs, rest) = self.split_attributes(&children);
        let rest = rest.to_vec();
        if node.kind() == NodeKind::TypeSynonym
            && let Some((&Element::Node(body), head)) = rest.split_last()
            && body.kind() == NodeKind::Body
        {
            let head = self.join(head);
            let inner: Vec<Element> = body.children().collect();
            let equals = self.el(inner[0]);
            let (_, choice) = self.body_after(&inner[1..]);
            return Doc::concat([attrs, head, Doc::text(" "), equals, choice]);
        }
        let doc = self.join(&rest);
        Doc::concat([attrs, doc])
    }

    /// `ability A where` and one operation a line at 2 (S16).
    fn ability(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let (attrs, rest) = self.split_attributes(&children);
        let rest = rest.to_vec();
        let split = rest
            .iter()
            .position(|&el| Self::kind(el) == Some(NodeKind::AbilityOp))
            .unwrap_or(rest.len());
        let head = self.join(&rest[..split]);
        let mut lines = Vec::new();
        for &op in &rest[split..] {
            self.mark_item(op);
            lines.push(Doc::HardLine);
            lines.push(self.el(op));
        }
        Doc::concat([attrs, head, Doc::nest(2, Doc::concat(lines))])
    }

    /// `import M (a, b)`: the list is a comma bracket (S2).
    fn import(&mut self, node: Node<'_>) -> Doc {
        self.comma_bracket(node)
    }

    /// A comma bracket (S31, D1012): on one line if it fits, otherwise one
    /// item a line at 2 with the closer on its own line. Whatever comes
    /// before the opener (`import M`) stays in front of it; a record
    /// update's `{ r |` stays on the opening line.
    fn comma_bracket(&mut self, node: Node<'_>) -> Doc {
        Doc::group(self.comma_bracket_content(node))
    }

    /// A comma bracket's parts, not yet grouped.
    fn comma_bracket_content(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let Some(open) = children
            .iter()
            .position(|&el| self.tok(el).is_some_and(opener))
        else {
            return self.join(&children);
        };
        let close = children.len() - 1;
        if close <= open || !self.tok(children[close]).is_some_and(closer) {
            return self.join(&children);
        }
        let brace = self.is_tok(children[open], &Tok::LBrace);
        let edge = || if brace { Doc::Line } else { Doc::SoftLine };
        let mut prefix = self.join(&children[..=open]);
        let mut inside = &children[open + 1..close];
        if inside.is_empty() {
            return self.join(&children);
        }
        // `{ r | …`: the record being updated stays with the opener.
        if brace
            && let Some(bar) = inside.iter().position(|&el| self.is_tok(el, &Tok::Pipe))
            && !inside[..bar].iter().any(|&el| self.is_tok(el, &Tok::Comma))
        {
            let space = self.space_el(children[open], inside[0]);
            let base = self.join(&inside[..=bar]);
            prefix = Doc::concat([prefix, space, base]);
            inside = &inside[bar + 1..];
        }
        // Items between commas; a comma before the closer is dropped.
        let mut items: Vec<(Vec<Element>, Option<Element>)> = Vec::new();
        let mut current = Vec::new();
        for &el in inside {
            if self.is_tok(el, &Tok::Comma) {
                items.push((std::mem::take(&mut current), Some(el)));
            } else {
                current.push(el);
            }
        }
        let mut dropped = None;
        if current.is_empty() {
            if let Some((_, comma)) = items.last_mut() {
                dropped = comma.take();
            }
        } else {
            items.push((current, None));
        }
        // D3572: a list of only plain values fills its lines, the bracket
        // staying on the first.
        let plain = node.kind() == NodeKind::List
            && inside.len() == items.len() * 2 - usize::from(dropped.is_none())
            && !self.holds_trailing_comment(node)
            && items.iter().all(|(_, comma)| {
                comma.is_none_or(|c| self.file.trivia()[Self::first(c)].leading.is_empty())
            })
            && items.iter().all(|(item, _)| {
                matches!(item.as_slice(), [el @ Element::Leaf(_)]
                if !self.has_leading(*el)
                    && matches!(
                        self.tok(*el),
                        Some(
                            Tok::Num(_)
                                | Tok::Float(_)
                                | Tok::Char(_)
                                | Tok::Str(_)
                                | Tok::Lower(_)
                                | Tok::Upper(_)
                        )
                    ))
            });
        if plain {
            let mut cells = Vec::new();
            for (item, comma) in &items {
                self.mark_item(item[0]);
                let mut cell = vec![self.join(item)];
                if let Some(comma) = comma {
                    cell.push(self.el(*comma));
                }
                cells.push(Doc::concat(cell));
            }
            let closer_doc = self.el(children[close]);
            return Doc::concat([prefix, Doc::nest(2, Doc::Fill(cells)), closer_doc]);
        }
        let mut body = Vec::new();
        let mut pending = Vec::new();
        for (k, (item, comma)) in items.iter().enumerate() {
            if item.is_empty() {
                return self.as_written(node);
            }
            self.mark_item(item[0]);
            body.push(if k == 0 { edge() } else { Doc::Line });
            body.append(&mut pending);
            body.push(self.join(item));
            if let Some(comma) = comma {
                let i = Self::first(*comma);
                pending = self.comma_first_comments(i);
                body.push(self.comma_end(i));
            }
        }
        if let Some(comma) = dropped {
            body.push(self.leaf_trivia_only(Self::first(comma)));
        }
        let closer_doc = self.el(children[close]);
        let mut parts = vec![prefix, Doc::nest(2, Doc::concat(body)), edge(), closer_doc];
        if self.holds_trailing_comment(node) {
            parts.push(Doc::BreakParent);
        }
        Doc::concat(parts)
    }

    /// A block's lines, each at the block's column (S17).
    fn block(&mut self, node: Node<'_>) -> Doc {
        let mut parts = Vec::new();
        for (k, line) in node.children().enumerate() {
            if k > 0 {
                self.mark_item(line);
                parts.push(Doc::HardLine);
            }
            parts.push(self.el(line));
        }
        Doc::concat(parts)
    }

    /// `let p := value` (S17): the value as a body after `:=` (S12).
    fn let_line(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let Some(assign) = children
            .iter()
            .position(|&el| self.is_tok(el, &Tok::ColonEq))
        else {
            return self.join(&children);
        };
        // As a header (S6): a value after a `let` line that broke goes below.
        let head = self.join(&children[..=assign]);
        let id = self.fresh_id();
        let hard = head.forces_break();
        let (below, choice) = self.body_after(&children[assign + 1..]);
        Doc::concat([
            Doc::IdGroup(id, Box::new(head), hard),
            Doc::IfBroken {
                id,
                broken: Box::new(below),
                flat: Box::new(choice),
            },
        ])
    }

    /// Whether an argument stays on the function's line in a broken call
    /// (D3567 (c)): a name, a literal, `_`, `?`, a dotted name or `f()`.
    fn simple(&self, el: Element<'_>) -> bool {
        match el {
            Element::Leaf(_) => true,
            Element::Node(node) => {
                let children: Vec<Element> = node.children().collect();
                match node.kind() {
                    NodeKind::FieldAccess => children.iter().all(|&c| self.simple(c)),
                    NodeKind::App => {
                        children.len() == 2
                            && matches!(children[0], Element::Leaf(_))
                            && Self::kind(children[1]) == Some(NodeKind::Unit)
                    }
                    NodeKind::Unit => true,
                    // `[]`, `{}`: literals.
                    NodeKind::List | NodeKind::Record | NodeKind::Tuple => children.len() == 2,
                    NodeKind::Prefix | NodeKind::PatternNegative => {
                        children.iter().all(|&c| matches!(c, Element::Leaf(_)))
                    }
                    _ => false,
                }
            }
        }
    }

    /// Whether the last argument of a call can hug (S23): a lambda or clause
    /// lambda in brackets, a list, a record or a tuple.
    fn huggable(&self, el: Element<'_>) -> bool {
        match el {
            Element::Leaf(_) => false,
            Element::Node(node) => match node.kind() {
                NodeKind::List | NodeKind::Record | NodeKind::Tuple => true,
                NodeKind::Paren => node.children().any(|c| {
                    matches!(
                        Self::kind(c),
                        Some(NodeKind::Lambda | NodeKind::ClauseLambda | NodeKind::Block)
                    )
                }),
                _ => false,
            },
        }
    }

    /// The doc of a call's last argument, and its hug (S23): the same
    /// argument opening downwards. The parts are built once and shared.
    fn last_argument(&mut self, el: Element<'_>) -> (Doc, Option<Doc>) {
        let Element::Node(node) = el else {
            return (self.el(el), None);
        };
        if self.no_hug || !self.huggable(el) {
            return (self.el(el), None);
        }
        let first = node.token_range().start;
        let leading = Doc::concat(self.leading(first));
        let saved = std::mem::replace(&mut self.hoisted[first], true);
        let (normal, hug) = match node.kind() {
            NodeKind::Paren => {
                let inner: Vec<Element> = node.children().collect();
                let (mut normal, mut hug) = (Vec::new(), Vec::new());
                for (k, &el) in inner.iter().enumerate() {
                    if k > 0 {
                        let space = self.space_el(inner[k - 1], el);
                        normal.push(space.clone());
                        hug.push(space);
                    }
                    match el {
                        Element::Node(lambda) if lambda.kind() == NodeKind::Lambda => {
                            let (flat, open) = self.lambda_both(lambda);
                            normal.push(flat);
                            hug.push(open);
                        }
                        // A block opens below the bracket at 2 (S17).
                        Element::Node(block) if block.kind() == NodeKind::Block => {
                            let doc = self.el(el);
                            normal.pop();
                            hug.pop();
                            let below =
                                Doc::shared(Doc::nest(2, Doc::concat([Doc::HardLine, doc])));
                            normal.push(below.clone());
                            hug.push(below);
                        }
                        _ => {
                            let doc = Doc::shared(self.el(el));
                            normal.push(doc.clone());
                            hug.push(doc);
                        }
                    }
                }
                (Doc::concat(normal), Doc::concat(hug))
            }
            _ => {
                let content = Doc::shared(self.comma_bracket_content(node));
                let hard = content.forces_break();
                (
                    Doc::Group(Box::new(content.clone()), hard),
                    Doc::Group(Box::new(content), true),
                )
            }
        };
        self.hoisted[first] = saved;
        (
            Doc::concat([leading.clone(), normal]),
            Some(Doc::concat([leading, hug])),
        )
    }

    /// Docs of elements, joined on one line.
    fn join_docs(&self, els: &[Element<'_>], docs: &[Doc]) -> Doc {
        let mut parts = Vec::new();
        for (k, doc) in docs.iter().enumerate() {
            if k > 0 {
                parts.push(self.space_el(els[k - 1], els[k]));
            }
            parts.push(doc.clone());
        }
        Doc::concat(parts)
    }

    /// Whether the element must not start a line: a method section, `.f a`,
    /// would read as a field of the line before (S26), and `_` as the next
    /// step of a `calc` around it.
    fn section(&self, el: Element<'_>) -> bool {
        Self::kind(el) == Some(NodeKind::Section) || self.is_tok(el, &Tok::Underscore)
    }

    /// A call (S23, D3567 (c)): on one line if it fits; else hugging its
    /// last argument if that can and the line up to it fits; else the
    /// function and its leading simple arguments on the line and each other
    /// argument on its own line at 2.
    fn app(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let n = children.len();
        let mut docs: Vec<Doc> = Vec::with_capacity(n);
        for &child in &children[..n - 1] {
            let doc = self.el(child);
            docs.push(Doc::shared(doc));
        }
        let (last, hug) = self.last_argument(children[n - 1]);
        docs.push(Doc::shared(last));
        let all = self.join_docs(&children, &docs);
        let mut keep = 1;
        while keep < n
            && (self.simple(children[keep]) || self.section(children[keep]))
            && !self.trails_comment(children[keep - 1])
        {
            keep += 1;
        }
        if keep == n {
            return self.fill_call(&children, &docs).unwrap_or(all);
        }
        let mut options = vec![Doc::flat(all)];
        if let Some(hug) = hug {
            let front = self.join_docs(&children[..n - 1], &docs[..n - 1]);
            let space = self.space_el(children[n - 2], children[n - 1]);
            let hug = Doc::shared(Doc::concat([Doc::flat(front), space, hug]));
            self.hugs.insert(node.token_range().start, hug.clone());
            options.push(hug);
        }
        // D3569 for the leading plain arguments: when they alone pass the
        // width they fill lines at 4, and the other arguments follow at 4
        // too, so they don't sit left of the continuation.
        let fill_front = keep > 2 && !self.comment_between(&children[..keep]);
        let front_id = self.fresh_id();
        let front = if fill_front {
            let items = self.fill_items(&children[..keep], &docs[..keep]);
            Doc::IdGroup(front_id, Box::new(Doc::nest(4, Doc::Fill(items))), false)
        } else {
            self.join_docs(&children[..keep], &docs[..keep])
        };
        let mut rest = Vec::new();
        for k in keep..n {
            if self.section(children[k]) && !self.trails_comment(children[k - 1]) {
                rest.push(self.space_el(children[k - 1], children[k]));
            } else {
                rest.push(Doc::HardLine);
            }
            rest.push(docs[k].clone());
        }
        let rest = Doc::concat(rest);
        let rest = if fill_front {
            Doc::IfBroken {
                id: front_id,
                broken: Box::new(Doc::nest(4, rest.clone())),
                flat: Box::new(Doc::nest(2, rest)),
            }
        } else {
            Doc::nest(2, rest)
        };
        options.push(Doc::concat([front, rest]));
        Doc::Choice(options)
    }

    /// A call of plain arguments only (D3569): on one line if it fits,
    /// otherwise the arguments fill lines at 4 from the call's line, as many
    /// as fit. `None` where a comment inside makes the line breaks matter.
    fn fill_call(&self, children: &[Element<'_>], docs: &[Doc]) -> Option<Doc> {
        if self.comment_between(children) {
            return None;
        }
        let items = self.fill_items(children, docs);
        Some(Doc::nest(4, Doc::Fill(items)))
    }

    /// The elements as the items of a fill. Pieces written with nothing
    /// between them (`f()`) are one item.
    fn fill_items(&self, children: &[Element<'_>], docs: &[Doc]) -> Vec<Doc> {
        let mut items = vec![docs[0].clone()];
        for k in 1..children.len() {
            let space = self.space_el(children[k - 1], children[k]);
            if matches!(space, Doc::Nil) {
                let last = items.pop().expect("an item");
                items.push(Doc::concat([last, docs[k].clone()]));
            } else {
                items.push(docs[k].clone());
            }
        }
        items
    }

    /// Whether a comment sits between the elements, so that their line
    /// breaks matter.
    fn comment_between(&self, children: &[Element<'_>]) -> bool {
        (1..children.len())
            .any(|k| self.has_leading(children[k]) || self.trails_comment(children[k - 1]))
    }

    /// The operands and operators of a chain at one level, flattened from
    /// the nesting the operators' grouping gives.
    fn chain_parts<'e>(&self, node: Node<'e>, lvl: Option<u8>, out: &mut Vec<Element<'e>>) {
        for child in node.children() {
            match child {
                Element::Node(inner)
                    if matches!(
                        inner.kind(),
                        NodeKind::Binary
                            | NodeKind::Pipe
                            | NodeKind::Arrow
                            | NodeKind::FunctionType
                    ) && self.level_of(inner) == lvl
                        && lvl.is_some() =>
                {
                    self.chain_parts(inner, lvl, out)
                }
                _ => out.push(child),
            }
        }
    }

    /// The level of a node's operator.
    fn level_of(&self, node: Node<'_>) -> Option<u8> {
        node.children().find_map(|el| self.tok(el).and_then(level))
    }

    /// An operator chain (S27, S29): on one line if it fits, otherwise
    /// each operator of its level starting a line at 2.
    fn chain(&mut self, node: Node<'_>) -> Doc {
        let lvl = match node.kind() {
            NodeKind::Chain | NodeKind::Iff => None,
            _ => self.level_of(node),
        };
        let mut parts = Vec::new();
        self.chain_parts(node, lvl, &mut parts);
        let Some((&first, rest)) = parts.split_first() else {
            return Doc::Nil;
        };
        let head = self.el(first);
        let mut tail = Vec::new();
        let mut k = 0;
        while k < rest.len() {
            let op = rest[k];
            let is_op = self
                .tok(op)
                .is_some_and(|t| level(t).is_some() || matches!(t, Tok::Iff));
            if !is_op || k + 1 >= rest.len() {
                // Not a binary operator shape: keep it on the line.
                let prev = if k == 0 { first } else { rest[k - 1] };
                tail.push(self.space_el(prev, op));
                tail.push(self.el(op));
                k += 1;
                continue;
            }
            let operand = rest[k + 1];
            tail.push(Doc::Line);
            let op_doc = self.el(op);
            tail.push(op_doc);
            let operand_doc = self.el(operand);
            if Self::kind(operand) == Some(NodeKind::Block) {
                // A block starts a line of its own, below its operator.
                tail.push(Doc::nest(2, Doc::concat([Doc::HardLine, operand_doc])));
            } else {
                tail.push(self.space_el(op, operand));
                tail.push(operand_doc);
            }
            k += 2;
        }
        // After alternatives, whose arms are at 2, the operators stay at the
        // chain's column, where they can't read as part of the last arm.
        let indent = match Self::kind(first) {
            Some(
                NodeKind::Match
                | NodeKind::Induct
                | NodeKind::Reify
                | NodeKind::Handle
                | NodeKind::ClauseLambda,
            ) => 0,
            _ => 2,
        };
        Doc::group(Doc::concat([head, Doc::nest(indent, Doc::concat(tail))]))
    }

    /// `∀ binders => body` (S28): the binders stay on the line, and the
    /// body follows `=>`, its own breaks at 2 from the quantifier's line;
    /// a body that doesn't start on that line (a `∃` chain too long for
    /// it) goes below at 2, where the next `∃` decides again for itself.
    fn quantifier(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let Some(arrow) = children
            .iter()
            .position(|&el| self.is_tok(el, &Tok::FatArrow))
            .filter(|&k| k + 2 == children.len())
        else {
            return self.join(&children);
        };
        // An `∃`'s binders never break, so a chain too long for its line
        // goes below `=>` rather than inside a binder; a `∀`'s may.
        let head = self.join(&children[..=arrow]);
        let head = Doc::shared(if node.kind() == NodeKind::Exists {
            Doc::flat(head)
        } else {
            head
        });
        let body = Doc::shared(self.el(children[arrow + 1]));
        let space = self.space_el(children[arrow], children[arrow + 1]);
        let below = Doc::concat([
            head.clone(),
            Doc::nest(2, Doc::concat([Doc::HardLine, body.clone()])),
        ]);
        if self.has_leading(children[arrow + 1]) {
            return below;
        }
        let inline = Doc::concat([head, space, body]);
        Doc::Choice(vec![Doc::flat(inline.clone()), inline, below])
    }

    /// `(let x := e; body)` and `a; b` (S18): on one line if they fit,
    /// otherwise a line break after each `;`, the parts lined up where the
    /// first starts, one column inside the bracket.
    fn sequence(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let mut parts = Vec::new();
        for (k, &el) in children.iter().enumerate() {
            if k > 0 {
                if self.is_tok(children[k - 1], &Tok::Semi) {
                    parts.push(Doc::Line);
                } else {
                    parts.push(self.space_el(children[k - 1], el));
                }
            }
            parts.push(self.el(el));
        }
        Doc::group(Doc::align(Doc::concat(parts)))
    }

    /// An interpolated text (S32): its pieces touch each other as written,
    /// each `${…}` on one line whatever its length.
    fn interpolated(&mut self, node: Node<'_>) -> Doc {
        let parts: Vec<Doc> = node.children().map(|el| self.el(el)).collect();
        Doc::concat(parts)
    }

    /// `${expr}`: printed flat, spaced as the usual rules say.
    fn interpolation(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        Doc::flat(self.join(&children))
    }

    /// `params => body` (S30): the body after `=>` if it fits, otherwise
    /// below at 2. `open` forces the break (a hugged last argument).
    fn lambda(&mut self, node: Node<'_>) -> Doc {
        self.lambda_both(node).0
    }

    /// A lambda's parameters and `=>`: on the line if they fit, otherwise
    /// filling lines at 4 like a header's parameters (S22), `=>` after the
    /// last.
    fn lambda_head(&mut self, children: &[Element<'_>]) -> Doc {
        if children.len() < 3 || self.comment_between(children) {
            return self.join(children);
        }
        let docs: Vec<Doc> = children
            .iter()
            .map(|&el| Doc::shared(self.el(el)))
            .collect();
        let items = self.fill_items(children, &docs);
        Doc::nest(4, Doc::Fill(items))
    }

    /// A lambda, and the same lambda opened downwards (a hug, S23).
    fn lambda_both(&mut self, node: Node<'_>) -> (Doc, Doc) {
        let children: Vec<Element> = node.children().collect();
        let Some(arrow) = children
            .iter()
            .position(|&el| self.is_tok(el, &Tok::FatArrow))
        else {
            let doc = self.join(&children);
            return (doc.clone(), doc);
        };
        let head = Doc::shared(self.join(&children[..=arrow]));
        // Only the lambda that may go below (not an opened one, whose line
        // up to the body must fit, or the choice would take it) breaks its
        // parameters.
        let filled = Doc::shared(self.lambda_head(&children[..=arrow]));
        let body = Doc::shared(self.join(&children[arrow + 1..]));
        let flat = Doc::group(Doc::concat([
            filled,
            Doc::nest(2, Doc::concat([Doc::Line, body.clone()])),
        ]));
        let open = Doc::concat([head, Doc::nest(2, Doc::concat([Doc::HardLine, body]))]);
        (flat, open)
    }

    /// `if` (S19): on one line if it fits, otherwise one clause a line at
    /// the `if`'s column, each branch after its keyword if it fits, else
    /// below at 2.
    fn if_(&mut self, node: Node<'_>) -> Doc {
        let mut clauses = Vec::new();
        let mut current = node;
        let mut else_prefix: Option<Element> = None;
        loop {
            let children: Vec<Element> = current.children().collect();
            let then = children
                .iter()
                .position(|&el| self.is_tok(el, &Tok::KwThen));
            let els = children
                .iter()
                .position(|&el| self.is_tok(el, &Tok::KwElse));
            let (Some(then), Some(els)) = (then, els) else {
                return self.as_written(node);
            };
            if els != children.len() - 2 || then + 1 >= els {
                return self.as_written(node);
            }
            let mut head = Vec::new();
            if let Some(prefix) = else_prefix.take() {
                head.push(self.el(prefix));
                head.push(Doc::text(" "));
            }
            head.push(self.join(&children[..=then]));
            let branch = self.join(&children[then + 1..els]);
            clauses.push(Doc::group(Doc::concat([
                Doc::concat(head),
                Doc::nest(2, Doc::concat([Doc::Line, branch])),
            ])));
            let other = children[els + 1];
            match other {
                Element::Node(next) if next.kind() == NodeKind::If => {
                    else_prefix = Some(children[els]);
                    current = next;
                }
                _ => {
                    let else_doc = self.el(children[els]);
                    let branch = self.el(other);
                    clauses.push(Doc::group(Doc::concat([
                        else_doc,
                        Doc::nest(2, Doc::concat([Doc::Line, branch])),
                    ])));
                    break;
                }
            }
        }
        let mut parts = Vec::new();
        for (k, clause) in clauses.into_iter().enumerate() {
            if k > 0 {
                parts.push(Doc::Line);
            }
            parts.push(clause);
        }
        Doc::group(Doc::concat(parts))
    }

    /// `match`, `handle`, `match induct`, `match reify` and clause lambdas
    /// (S20, D3566): two or more alternatives one a line at 2; one may
    /// share the line.
    fn alternatives(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let split = children
            .iter()
            .position(|&el| {
                matches!(
                    Self::kind(el),
                    Some(NodeKind::Arm | NodeKind::HandlerClause | NodeKind::InductArm)
                )
            })
            .unwrap_or(children.len());
        let head = self.join(&children[..split]);
        let arms = &children[split..];
        // One alternative may share the line (S20), but not inside another
        // construct's alternative: the arms after it would read as its own.
        let many = arms.len() >= 2 || self.arm_depth > 0;
        let mut lines = Vec::new();
        self.arm_depth += 1;
        for &arm in arms {
            self.mark_item(arm);
            lines.push(if many { Doc::HardLine } else { Doc::Line });
            lines.push(self.el(arm));
        }
        self.arm_depth -= 1;
        let arms = Doc::nest(2, Doc::concat(lines));
        if node.kind() == NodeKind::Match {
            // The form that hugs a `:=` line: its head can't wrap there.
            let hug = Doc::concat([Doc::flat(head.clone()), arms.clone()]);
            let hug = if many { hug } else { Doc::group(hug) };
            self.match_hugs.insert(node.token_range().start, hug);
        }
        let doc = Doc::concat([head, arms]);
        if many { doc } else { Doc::group(doc) }
    }

    /// `| patterns => body` (S21): the body after `=>` if it fits, else
    /// below at 2; a body that is a `match` always below, and one that opens
    /// downwards (a comma bracket, a hug) on the arm's line.
    fn arm(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let Some(arrow) = children
            .iter()
            .position(|&el| self.is_tok(el, &Tok::FatArrow))
        else {
            return self.join(&children);
        };
        // S22: a pattern too long for its line continues at +4 from the `|`,
        // as a header's parameters do, so it never lines up with the body.
        let head = Doc::nest(2, self.join(&children[..=arrow]));
        let value = &children[arrow + 1..];
        // Alternatives and `calc` steps need a column of their own.
        let below = value.len() == 1
            && matches!(
                Self::kind(value[0]),
                Some(
                    NodeKind::Match
                        | NodeKind::Induct
                        | NodeKind::Reify
                        | NodeKind::Handle
                        | NodeKind::ClauseLambda
                        | NodeKind::Calc
                )
            );
        if below {
            let body = self.join(value);
            return Doc::concat([head, Doc::nest(2, Doc::concat([Doc::HardLine, body]))]);
        }
        // Otherwise as a body after `:=`: a comma bracket's opener ends the
        // arm's line (S31), as does a hug's (S23).
        let (_, body) = self.body_after(value);
        Doc::concat([head, body])
    }

    /// `calc e0` and its steps, one a line at 2 (S35).
    fn calc(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let split = children
            .iter()
            .position(|&el| Self::kind(el) == Some(NodeKind::CalcStep))
            .unwrap_or(children.len());
        // The first expression doesn't hug: what it opens downwards would
        // share the steps' column.
        let saved = std::mem::replace(&mut self.no_hug, true);
        let head = self.join(&children[..split]);
        self.no_hug = saved;
        let mut lines = Vec::new();
        for &step in &children[split..] {
            self.mark_item(step);
            lines.push(Doc::HardLine);
            lines.push(self.el(step));
        }
        Doc::concat([head, Doc::nest(2, Doc::concat(lines))])
    }

    /// `_ R e := proof` (S35): on one line if it fits, otherwise the proof
    /// below at 2, but for S12's exceptions.
    fn calc_step(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let Some(assign) = children
            .iter()
            .position(|&el| self.is_tok(el, &Tok::ColonEq))
        else {
            return self.join(&children);
        };
        if assign == 0 {
            return self.join(&children);
        }
        // `_ R e` breaks at 4, as a header would, apart from the proof at 2.
        // The proof follows `:=` as a declaration's body does (S12), so a
        // hug opens on the step's line (D3567's sample).
        let relation = self.join(&children[..assign]);
        let space = self.space_el(children[assign - 1], children[assign]);
        let assign_doc = self.el(children[assign]);
        let (_, proof) = self.body_after(&children[assign + 1..]);
        if self.has_leading(children[assign]) {
            // A comment above the `:=` takes its own line, at 2 from the
            // step, and the `:=` follows it.
            let rest = Doc::concat([Doc::HardLine, assign_doc, proof]);
            return Doc::concat([Doc::nest(2, relation), Doc::nest(2, rest)]);
        }
        Doc::concat([Doc::nest(2, relation), space, assign_doc, proof])
    }

    /// `rewrite rules in body` (S36): on one line if it fits; otherwise the
    /// body below at 2, and if the rules don't fit on the `rewrite` line,
    /// one rule a line at 4 with `in` at the end of the last.
    fn rewrite(&mut self, node: Node<'_>) -> Doc {
        let children: Vec<Element> = node.children().collect();
        let Some(in_at) = children.iter().rposition(|&el| self.is_tok(el, &Tok::KwIn)) else {
            return self.join(&children);
        };
        if in_at < 2 {
            return self.join(&children);
        }
        let keyword = self.el(children[0]);
        let mut rules = Vec::new();
        let mut current: Vec<Element> = Vec::new();
        let mut items = Vec::new();
        for &el in &children[1..in_at] {
            if self.is_tok(el, &Tok::Comma) {
                items.push((std::mem::take(&mut current), Some(el)));
            } else {
                current.push(el);
            }
        }
        items.push((current, None));
        for (k, (item, comma)) in items.iter().enumerate() {
            if item.is_empty() {
                return self.as_written(node);
            }
            if k > 0 {
                rules.push(Doc::Line);
            }
            rules.push(self.join(item));
            if let Some(comma) = comma {
                rules.push(self.el(*comma));
            }
        }
        let in_doc = self.el(children[in_at]);
        let body = self.join(&children[in_at + 1..]);
        let first_space = self.space_el(children[0], children[1]);
        let rules = Doc::group(Doc::concat([
            keyword,
            first_space,
            Doc::nest(4, Doc::concat(rules)),
            Doc::text(" "),
            in_doc,
        ]));
        Doc::group(Doc::concat([
            rules,
            Doc::nest(2, Doc::concat([Doc::Line, body])),
        ]))
    }
}

/// Whether the comma at byte `start` is the first token on its line.
pub(crate) fn comma_first_on_line(src: &str, start: usize) -> bool {
    let line = src[..start].rfind('\n').map_or(0, |k| k + 1);
    src[line..start].trim().is_empty()
}
