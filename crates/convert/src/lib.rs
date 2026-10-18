//! The one-off converter from Haskell-style declarations (a signature line,
//! then equations) to the Lean/Scala style (`def f (x : A) : B := …`, or a
//! header followed by `| p, q => …` arms): docs/proposals/declaration-syntax.md
//! §5.2–§5.3. It's deleted once the migration is done.
//!
//! It reads a file with today's parser and **edits the text at token spans**
//! rather than printing the syntax tree, so comments, blank lines and hand
//! alignment survive. Every rewrite is located by the parsed tree (which
//! construct a token belongs to) and checked against the token stream (that
//! the token is what the rewrite expects); anything unexpected fails the
//! whole file with a reason, rather than guessing.
//!
//! The rewrites:
//!
//! - a signature and its equations become one `def` / `theorem` (with
//!   `export` on the same line): named header parameters for leading columns
//!   where every equation binds the same plain variable and nothing in the
//!   type could be captured (§5.3 rule 2), else arms after the colon; a `:=`
//!   body when one equation remains with every column named;
//! - arms get exactly one pattern per explicit argument after the colon
//!   (§5.3 rule 4): a lambda's leading plain parameters move into the arm's
//!   patterns, or fresh names are added and the body applied to them; absurd
//!   arms get `_`;
//! - `=` becomes `:=` after headers, in `let` and `test`; `->` becomes `=>` in
//!   lambdas, `match` alternatives and handler clauses, and a handler's
//!   `| op x => k -> body` becomes `| op x, k => body`.
//!
//! Names are never renamed: whenever a nicer header would need a judgement
//! about names, the converter writes the all-arms form.

use std::collections::{BTreeMap, HashMap, HashSet};

use stitchwort_syntax::ast::{Clause, Decl, Expr, MatchKind, Pattern};
use stitchwort_syntax::{Diagnostic, SourceMap, Tok, Token, lex};

use crate::old_parser::{parse_expression, parse_module};

/// The parser of the old declaration syntax, kept here (and only here) so
/// the converter can still read old sources after the switch: Markdown code
/// blocks and any other old text that is converted later.
#[doc(hidden)]
pub mod old_parser;

/// Explicit-argument counts by definition name, from the elaborator
/// ([`elaborated_arities`]).
pub type Arities = HashMap<String, usize>;

/// What converting one piece of text did.
#[derive(Clone, Debug, Default)]
pub struct Report {
    /// Definitions and theorems written with a `:=` body.
    pub assign_form: usize,
    /// Definitions and theorems written with arms.
    pub arm_form: usize,
    /// Of those, how many have at least one named header parameter.
    pub with_parameters: usize,
    pub tests: usize,
    /// Arms given extra patterns to reach the exact arity (§5.3 rule 4).
    pub completions: Vec<Completion>,
    /// Signatures without equations (line, name), written as a header with
    /// no body: the prelude's primitives, and reject examples.
    pub bodiless: Vec<(usize, String)>,
    /// Header `()`s written for a column whose equations bound an unused
    /// variable (definition, column): `()` lowers to `_`, so the tree has
    /// `_` where the old one had the variable.
    pub unit_wildcards: Vec<(String, usize)>,
}

impl Report {
    pub fn add(&mut self, other: &Report) {
        self.assign_form += other.assign_form;
        self.arm_form += other.arm_form;
        self.with_parameters += other.with_parameters;
        self.tests += other.tests;
        self.completions.extend(other.completions.iter().cloned());
        self.bodiless.extend(other.bodiless.iter().cloned());
        self.unit_wildcards
            .extend(other.unit_wildcards.iter().cloned());
    }

    pub fn declarations(&self) -> usize {
        self.assign_form + self.arm_form
    }
}

/// One arm completed for exact arity, for the tidy-up lane to review.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Completion {
    /// 1-based line of the arm in the original text.
    pub line: usize,
    /// The definition's name.
    pub name: String,
    pub how: How,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum How {
    /// A lambda's parameters became the arm's patterns.
    Moved(Vec<String>),
    /// Fresh names were added and the body applied to them.
    Applied(Vec<String>),
    /// Some moved, then fresh ones for the rest.
    MovedThenApplied(Vec<String>, Vec<String>),
    /// An absurd arm, given `_`s.
    Absurd(usize),
}

impl std::fmt::Display for How {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            How::Moved(names) => write!(f, "moved lambda parameter(s) {}", names.join(" ")),
            How::Applied(names) => write!(f, "applied the body to fresh {}", names.join(" ")),
            How::MovedThenApplied(moved, fresh) => write!(
                f,
                "moved lambda parameter(s) {}, then applied to fresh {}",
                moved.join(" "),
                fresh.join(" ")
            ),
            How::Absurd(n) => write!(f, "absurd arm, added {n} `_`"),
        }
    }
}

#[derive(Debug)]
pub struct Converted {
    pub text: String,
    pub report: Report,
}

/// Converts a whole file (module). `arities` gives each definition's number
/// of explicit arguments as the elaborator counts them (unfolding
/// definitions); without it, or for a name it lacks, the arrows written in
/// the signature are counted.
pub fn convert_module(text: &str, arities: Option<&Arities>) -> Result<Converted, String> {
    let mut sources = SourceMap::new();
    let file = sources.add("input.sw", text);
    let toks = lex(file, text).map_err(|d| describe(text, &d))?;
    let module = parse_module(file, text).map_err(|ds| {
        ds.iter()
            .map(|d| describe(text, d))
            .collect::<Vec<_>>()
            .join("; ")
    })?;
    let mut src = Src::new(text, toks);
    let groups: Vec<(usize, usize)> = src
        .groups()
        .into_iter()
        .filter(|&(start, _)| src.toks[start].tok != Tok::KwImport)
        .collect();
    if groups.len() != module.decls.len() {
        return Err(format!(
            "internal: {} declaration groups but {} declarations",
            groups.len(),
            module.decls.len()
        ));
    }
    for decl in &module.decls {
        src.decl_exprs(decl)?;
    }
    let mut report = Report::default();
    let mut i = 0;
    while i < module.decls.len() {
        match &module.decls[i] {
            Decl::Signature { name, .. } => {
                let mut equations = Vec::new();
                let mut j = i + 1;
                while let Some(Decl::Equation {
                    name: n,
                    patterns,
                    rhs,
                    ..
                }) = module.decls.get(j)
                    && n.text == name.text
                {
                    equations.push((groups[j], patterns.as_slice(), rhs.as_ref()));
                    j += 1;
                }
                let n = arities.and_then(|a| a.get(&name.text)).copied();
                src.definition(&module.decls[i], groups[i], &equations, n, &mut report)?;
                i = j;
            }
            Decl::Equation { name, .. } => {
                return Err(format!(
                    "line {}: equations for `{}` without a signature before them",
                    src.line(groups[i].0),
                    name.text
                ));
            }
            Decl::Test { .. } => {
                let (start, _) = groups[i];
                let eq = start + 2;
                if src.toks.get(eq).map(|t| &t.tok) != Some(&Tok::Equals) {
                    return Err(format!(
                        "line {}: expected `=` after the test's name",
                        src.line(start)
                    ));
                }
                src.replace_token(eq, ":=")?;
                report.tests += 1;
                i += 1;
            }
            Decl::Data { .. } | Decl::Ability { .. } => i += 1,
        }
    }
    let converted = lexes(src.finish(false)?)?;
    check_ast_equivalence(text, &src.finish(true)?, &report)?;
    Ok(Converted {
        text: converted,
        report,
    })
}

/// Converts an expression on its own (a snippet that isn't a module):
/// lambdas, `match`, `handle` and `let` only.
pub fn convert_expression(text: &str) -> Result<String, String> {
    let mut sources = SourceMap::new();
    let file = sources.add("input.sw", text);
    let toks = lex(file, text).map_err(|d| describe(text, &d))?;
    let expr = parse_expression(file, text).map_err(|d| describe(text, &d))?;
    let mut src = Src::new(text, toks);
    src.expr(&expr)?;
    lexes(src.finish(false)?)
}

/// A check on the output: it must still lex (the edits only add tokens the
/// lexer knows, `:=` and `=>`).
fn lexes(text: String) -> Result<String, String> {
    let mut sources = SourceMap::new();
    let file = sources.add("output.sw", text.as_str());
    match lex(file, &text) {
        Ok(_) => Ok(text),
        Err(d) => Err(format!(
            "internal: the output doesn't lex: {}",
            describe(&text, &d)
        )),
    }
}

/// Converts a snippet (from a Rust test's string or a Markdown code block):
/// as a module, with the elaborator's arities if it checks, else as an
/// expression.
pub fn convert_snippet(text: &str) -> Result<Converted, String> {
    let arities = elaborated_arities(text).ok();
    match convert_module(text, arities.as_ref()) {
        Ok(converted) => Ok(converted),
        Err(module_error) => match convert_expression(text) {
            Ok(text) => Ok(Converted {
                text,
                report: Report::default(),
            }),
            Err(_) => Err(module_error),
        },
    }
}

/// How much stack elaboration gets: generous, since this is a batch tool.
const STACK: usize = 256 * 1024 * 1024;

/// Elaborates `text` (after the prelude; or, if `text` is the prelude, the
/// prelude itself) and counts each definition's explicit arguments the way
/// the arity check does: explicit `Pi`s of its type, after unfolding, up to
/// the first thing that isn't a function type. Fails if the text doesn't
/// check.
pub fn elaborated_arities(text: &str) -> Result<Arities, String> {
    use stitchwort_core::value::force;
    use stitchwort_core::{DefId, Icit, Limits, Value};
    use stitchwort_driver::driver::{Session, with_stack};

    let text = text.to_string();
    with_stack(STACK, move || {
        let mut session = Session::for_stack(STACK);
        let first = if text == stitchwort_elab::PRELUDE {
            0
        } else {
            let first = session.elab.globals.defs.len();
            // Read with the old parser, then elaborated as `Session::load`
            // would (the tree is the same in both syntaxes).
            let first_error = |ds: &[Diagnostic]| {
                let d = ds
                    .iter()
                    .find(|d| d.severity == stitchwort_syntax::Severity::Error)
                    .or(ds.first());
                match d {
                    Some(d) => format!("{}: {}", d.code, d.message),
                    None => "doesn't check".to_string(),
                }
            };
            let file = session.sources.add("input.sw", text.as_str());
            let module = crate::old_parser::parse_module_within(file, &text, STACK)
                .map_err(|ds| first_error(&ds))?;
            let diagnostics = session.elab.elaborate_module(&module);
            if diagnostics
                .iter()
                .any(|d| d.severity == stitchwort_syntax::Severity::Error)
            {
                return Err(first_error(&diagnostics));
            }
            first
        };
        let g = &session.elab.globals;
        let _op = g.budget.operation(Limits::stack_only(STACK));
        let mut arities = Arities::new();
        for id in first..g.defs.len() {
            let def = g.def(DefId(id));
            let mut ty = def.ty_value.clone();
            let mut level = 0;
            let mut explicit = 0;
            while let Ok(Value::Pi(_, icit, _, cod)) = force(g, ty.clone()) {
                if icit == Icit::Explicit {
                    explicit += 1;
                }
                match cod.apply(g, Value::var(level)) {
                    Ok(next) => ty = next,
                    Err(_) => break,
                }
                level += 1;
            }
            arities.insert(def.name.to_string(), explicit);
        }
        Ok(arities)
    })
}

/// Converts the playground's examples in `web/index.html`: the contents of
/// each `<script type="text/plain" …>` block. Returns the new page, and for
/// each block its id, the line its text starts on, and the outcome.
pub fn convert_html(page: &str) -> (String, Vec<HtmlBlock>) {
    let open_tag = "<script type=\"text/plain\"";
    let mut out = String::new();
    let mut blocks = Vec::new();
    let mut rest = page;
    let mut offset = 0;
    while let Some(at) = rest.find(open_tag) {
        let Some(gt) = rest[at..].find('>') else {
            break;
        };
        let content_start = at + gt + 1;
        let Some(len) = rest[content_start..].find("</script>") else {
            break;
        };
        let tag = &rest[at..content_start];
        let id = tag
            .split("id=\"")
            .nth(1)
            .and_then(|s| s.split('"').next())
            .unwrap_or("?")
            .to_string();
        let content = &rest[content_start..content_start + len];
        let first_line = page[..offset + content_start].matches('\n').count() + 1;
        out.push_str(&rest[..content_start]);
        let arities = elaborated_arities(content).ok();
        let outcome = convert_module(content, arities.as_ref());
        match &outcome {
            Ok(converted) => out.push_str(&converted.text),
            Err(_) => out.push_str(content),
        }
        blocks.push(HtmlBlock {
            id,
            first_line,
            elaborated: arities.is_some(),
            outcome,
        });
        offset += content_start + len;
        rest = &rest[content_start + len..];
    }
    out.push_str(rest);
    (out, blocks)
}

pub struct HtmlBlock {
    pub id: String,
    /// The page's line on which the block's text starts.
    pub first_line: usize,
    pub elaborated: bool,
    pub outcome: Result<Converted, String>,
}

/// Whether `new` (in the new syntax) and `old` (in the old) parse to the
/// same tree, spans and arm markers aside
/// ([`stitchwort_syntax::equivalence::shape`]). The error says which failed
/// to parse, or where the trees first differ. For the parser's tests of the
/// new forms against the old.
pub fn compare(new: &str, old: &str) -> Result<(), String> {
    use stitchwort_syntax::equivalence::{parse_shape, shape};
    let new_shape = parse_shape(new).map_err(|e| format!("the new syntax doesn't parse:\n{e}"))?;
    let mut sources = SourceMap::new();
    let file = sources.add("equivalence.sw", old);
    let old_shape = match parse_module(file, old) {
        Ok(module) => shape(&module),
        Err(errors) => {
            let errors: Vec<String> = errors
                .iter()
                .map(|d| format!("{}: {}", d.code, d.message))
                .collect();
            return Err(format!(
                "the old syntax doesn't parse:\n{}",
                errors.join("\n")
            ));
        }
    };
    if new_shape == old_shape {
        return Ok(());
    }
    let (new_lines, old_lines): (Vec<&str>, Vec<&str>) =
        (new_shape.lines().collect(), old_shape.lines().collect());
    let at = new_lines
        .iter()
        .zip(&old_lines)
        .position(|(a, b)| a != b)
        .unwrap_or(new_lines.len().min(old_lines.len()));
    let from = at.saturating_sub(12);
    let excerpt = |lines: &[&str]| lines[from..(at + 3).min(lines.len())].join("\n");
    Err(format!(
        "the trees differ at line {} of their shapes\n--- new:\n{}\n--- old:\n{}",
        at + 1,
        excerpt(&new_lines),
        excerpt(&old_lines)
    ))
}

/// Panics, showing the difference, unless `new` and `old` parse to the same
/// tree.
#[track_caller]
pub fn assert_equivalent(new: &str, old: &str) {
    if let Err(difference) = compare(new, old) {
        panic!("{difference}\n--- new source:\n{new}\n--- old source:\n{old}");
    }
}

/// Checks a conversion (§5.4 layer 8): `new`, read by the new-syntax parser,
/// must lower to the tree the old parser reads from `old`, declaration by
/// declaration, spans and arm markers aside (lane A's
/// `stitchwort_syntax::equivalence`). The expected differences, from
/// `report`: definitions completed for exact arity, whose equations differ
/// on purpose (their signatures must still agree), and header `()`s for an
/// unused variable, which lower to `_`.
pub fn check_ast_equivalence(old: &str, new: &str, report: &Report) -> Result<(), String> {
    use crate::old_parser::Syntax;
    use stitchwort_syntax::ast::Module;
    use stitchwort_syntax::equivalence::shape;

    // The old text by the old parser; the new text by the language's parser.
    let parse = |syntax, text: &str| {
        let mut sources = SourceMap::new();
        let file = sources.add("input.sw", text);
        let parsed = match syntax {
            Syntax::Old => crate::old_parser::parse_module(file, text),
            Syntax::New => stitchwort_syntax::parse_module(file, text),
        };
        parsed.map_err(|ds| {
            ds.iter()
                .map(|d| describe(text, d))
                .collect::<Vec<_>>()
                .join("; ")
        })
    };
    let mut old_module = parse(Syntax::Old, old)?;
    // Headers without a body are left out of `new` (see `Src::finish`).
    old_module.decls.retain(|d| match d {
        Decl::Signature { name, .. } => !report.bodiless.iter().any(|(_, n)| *n == name.text),
        _ => true,
    });
    let new_module =
        parse(Syntax::New, new).map_err(|e| format!("the output doesn't parse: {e}"))?;
    let completed: HashSet<&str> = report.completions.iter().map(|c| c.name.as_str()).collect();
    let one = |decl: &Decl| {
        shape(&Module {
            imports: Vec::new(),
            decls: vec![decl.clone()],
        })
    };
    let imports = |m: &Module| {
        shape(&Module {
            imports: m.imports.clone(),
            decls: Vec::new(),
        })
    };
    if imports(&old_module) != imports(&new_module) {
        return Err("the imports differ".into());
    }
    if old_module.decls.len() != new_module.decls.len() {
        return Err(format!(
            "{} declarations before, {} after",
            old_module.decls.len(),
            new_module.decls.len()
        ));
    }
    for (old_decl, new_decl) in old_module.decls.iter().zip(&new_module.decls) {
        let mut old_decl = unname_spine(old_decl);
        let new_decl = &unname_spine(new_decl);
        if let Decl::Equation { name, patterns, .. } = &mut old_decl {
            if completed.contains(name.text.as_str()) {
                continue;
            }
            for (def, col) in &report.unit_wildcards {
                if *def == name.text
                    && let Some(p @ Pattern::Var(_)) = patterns.get_mut(*col)
                {
                    *p = Pattern::Wildcard(p.span());
                }
            }
        }
        let (a, b) = (one(&old_decl), one(new_decl));
        if a != b {
            let line = old[..old_decl.span().start as usize].matches('\n').count() + 1;
            let at = a
                .lines()
                .zip(b.lines())
                .position(|(x, y)| x != y)
                .unwrap_or(0);
            let excerpt = |s: &str| {
                s.lines()
                    .skip(at.saturating_sub(3))
                    .take(6)
                    .collect::<Vec<_>>()
                    .join("\n")
            };
            return Err(format!(
                "the declaration at line {line} parses differently after conversion\n--- old:\n{}\n--- new:\n{}",
                excerpt(&a),
                excerpt(&b)
            ));
        }
    }
    Ok(())
}

/// `decl` with its signature's explicit binders whose names aren't used in
/// the rest of the type written as plain arrows: a header parameter
/// `(x : A)` lowers to `(x : A) -> …` where the old signature said `A -> …`,
/// which means the same (binder names aren't hashed).
fn unname_spine(decl: &Decl) -> Decl {
    let mut decl = decl.clone();
    if let Decl::Signature { ty, .. } = &mut decl {
        *ty = unname(ty);
    }
    decl
}

fn unname(ty: &Expr) -> Expr {
    match ty {
        Expr::Pi {
            names,
            implicit,
            auto,
            dom,
            cod,
            span,
        } => {
            let rest = unname(cod);
            let shown = format!("{cod:?}");
            let used = names
                .iter()
                .any(|n| shown.contains(&format!("text: {:?}", n.text)));
            if *implicit || used {
                return Expr::Pi {
                    names: names.clone(),
                    implicit: *implicit,
                    auto: *auto,
                    dom: dom.clone(),
                    cod: Box::new(rest),
                    span: *span,
                };
            }
            names.iter().fold(rest, |acc, _| {
                Expr::Arrow(Box::new((**dom).clone()), Box::new(acc))
            })
        }
        Expr::Arrow(a, b) => Expr::Arrow(a.clone(), Box::new(unname(b))),
        other => other.clone(),
    }
}

fn describe(text: &str, d: &Diagnostic) -> String {
    match d.primary_span() {
        Some(span) => format!(
            "line {}: {}",
            text[..span.start as usize].matches('\n').count() + 1,
            d.message
        ),
        None => d.message.clone(),
    }
}

#[derive(Clone, Debug)]
struct Edit {
    start: usize,
    end: usize,
    text: String,
}

/// The source text, its tokens, and the edits collected so far. Edits are
/// "fine" (single tokens inside expressions, keyed by start) or "coarse"
/// (whole headers and arm heads, which render the fine edits inside them).
struct Src<'a> {
    text: &'a str,
    toks: Vec<Token>,
    at: HashMap<u32, usize>,
    /// Byte ranges of comments.
    comments: Vec<(usize, usize)>,
    fine: BTreeMap<usize, Edit>,
    coarse: Vec<Edit>,
    /// Indices in `coarse` of headers without a body.
    bodiless: Vec<usize>,
    /// Lambdas by start: the `\` token and the `->` token.
    lambdas: HashMap<u32, (usize, usize)>,
    /// Every lowercase name in the text, for choosing fresh ones.
    names: HashSet<String>,
}

struct Equation<'m> {
    /// Token range.
    group: (usize, usize),
    patterns: &'m [Pattern],
    rhs: Option<&'m Expr>,
    /// The `=` token.
    equals: Option<usize>,
}

/// One step of a signature's spine: a binder or an unnamed argument type,
/// and the arrow after it.
struct Elem<'m> {
    /// First token: `(` or `[` of a binder, or the argument type's first.
    start: usize,
    /// Last token before the arrow.
    close: usize,
    arrow: usize,
    explicit: bool,
    /// A binder's names; empty for an unnamed argument.
    names: Vec<String>,
    /// The argument type's tokens, `[from, to)`.
    dom: (usize, usize),
    dom_expr: &'m Expr,
}

type Group = (usize, usize);

impl<'a> Src<'a> {
    fn new(text: &'a str, toks: Vec<Token>) -> Self {
        let at = toks
            .iter()
            .enumerate()
            .map(|(i, t)| (t.span.start, i))
            .collect();
        let mut comments = Vec::new();
        let mut prev = 0;
        let gaps = toks
            .iter()
            .map(|t| t.span.start as usize)
            .chain([text.len()]);
        for (i, start) in gaps.enumerate() {
            let gap = &text[prev..start];
            let mut from = 0;
            while let Some(c) = gap[from..].find("--") {
                let begin = prev + from + c;
                let end = text[begin..].find('\n').map_or(text.len(), |n| begin + n);
                comments.push((begin, end));
                from = end - prev;
                if from >= gap.len() {
                    break;
                }
            }
            if let Some(t) = toks.get(i) {
                prev = t.span.end as usize;
            }
        }
        let names = toks
            .iter()
            .filter_map(|t| match &t.tok {
                Tok::Lower(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        Src {
            text,
            toks,
            at,
            comments,
            fine: BTreeMap::new(),
            coarse: Vec::new(),
            bodiless: Vec::new(),
            lambdas: HashMap::new(),
            names,
        }
    }

    /// Declarations: from a token at column 0 to the next, with a line
    /// holding only `export` joined to what follows (the parser's
    /// `split_decls`).
    fn groups(&self) -> Vec<Group> {
        let toks = &self.toks;
        let alone =
            |i: usize| toks[i].column == 0 && toks.get(i + 1).is_some_and(|next| next.column == 0);
        let mut starts: Vec<usize> = (0..toks.len()).filter(|&i| toks[i].column == 0).collect();
        starts.retain(|&i| i == 0 || !(toks[i - 1].tok == Tok::KwExport && alone(i - 1)));
        starts
            .iter()
            .enumerate()
            .map(|(n, &s)| (s, starts.get(n + 1).copied().unwrap_or(toks.len())))
            .collect()
    }

    fn start(&self, i: usize) -> usize {
        self.toks[i].span.start as usize
    }

    fn end(&self, i: usize) -> usize {
        self.toks[i].span.end as usize
    }

    fn line(&self, i: usize) -> usize {
        self.line_of(self.start(i))
    }

    fn line_of(&self, pos: usize) -> usize {
        self.text[..pos].matches('\n').count() + 1
    }

    fn tok_at(&self, pos: u32) -> Result<usize, String> {
        self.at
            .get(&pos)
            .copied()
            .ok_or_else(|| format!("internal: no token at line {}", self.line_of(pos as usize)))
    }

    fn text_of(&self, from: usize, to: usize) -> &'a str {
        &self.text[from..to]
    }

    /// The first token from `from` on, outside any brackets opened after
    /// `from`, that `want` accepts.
    fn scan(&self, from: usize, want: impl Fn(&Tok) -> bool) -> Option<usize> {
        let mut depth = 0i32;
        for i in from..self.toks.len() {
            let tok = &self.toks[i].tok;
            if depth == 0 && want(tok) {
                return Some(i);
            }
            match tok {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => {
                    depth -= 1;
                    if depth < 0 {
                        return None;
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// The bracket closing the one at `open`.
    fn close_of(&self, open: usize) -> Option<usize> {
        let mut depth = 0i32;
        for i in open..self.toks.len() {
            match self.toks[i].tok {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(i);
                    }
                }
                _ => {}
            }
        }
        None
    }

    fn comment_in(&self, from: usize, to: usize) -> bool {
        self.comments.iter().any(|&(s, _)| from <= s && s < to)
    }

    fn replace_token(&mut self, i: usize, text: &str) -> Result<(), String> {
        let (start, end) = (self.start(i), self.end(i));
        self.fine_edit(start, end, text)
    }

    fn fine_edit(&mut self, start: usize, end: usize, text: &str) -> Result<(), String> {
        if self.fine.contains_key(&start) {
            return Err(format!(
                "internal: two edits at line {}",
                self.line_of(start)
            ));
        }
        self.fine.insert(
            start,
            Edit {
                start,
                end,
                text: text.to_string(),
            },
        );
        Ok(())
    }

    /// The text from `from` to `to` with the fine edits inside it applied.
    fn render(&self, from: usize, to: usize) -> String {
        let mut out = String::new();
        let mut pos = from;
        for edit in self.fine.range(from..to).map(|(_, e)| e) {
            if edit.end > to {
                break;
            }
            out.push_str(&self.text[pos..edit.start]);
            out.push_str(&edit.text);
            pos = edit.end;
        }
        out.push_str(&self.text[pos..to]);
        out
    }

    /// The edited text. With `blank_bodiless`, headers without a body are
    /// left out, for the equivalence check (the new parser has no form for
    /// them yet).
    fn finish(&self, blank_bodiless: bool) -> Result<String, String> {
        let blanks: Vec<Edit> = self
            .bodiless
            .iter()
            .map(|&i| Edit {
                text: String::new(),
                ..self.coarse[i].clone()
            })
            .collect();
        let mut edits: Vec<&Edit> = self
            .coarse
            .iter()
            .enumerate()
            .filter(|(i, _)| !(blank_bodiless && self.bodiless.contains(i)))
            .map(|(_, e)| e)
            .collect();
        if blank_bodiless {
            edits.extend(&blanks);
        }
        for f in self.fine.values() {
            let covered = self
                .coarse
                .iter()
                .any(|c| c.start < c.end && c.start <= f.start && f.end <= c.end);
            if !covered {
                edits.push(f);
            }
        }
        edits.sort_by_key(|e| (e.start, e.end));
        let mut out = String::new();
        let mut pos = 0;
        for e in edits {
            if e.start < pos {
                return Err(format!(
                    "internal: overlapping edits at line {}",
                    self.line_of(e.start)
                ));
            }
            out.push_str(&self.text[pos..e.start]);
            out.push_str(&e.text);
            pos = e.end;
        }
        out.push_str(&self.text[pos..]);
        Ok(out)
    }

    // --- Expressions --------------------------------------------------

    fn decl_exprs(&mut self, decl: &Decl) -> Result<(), String> {
        match decl {
            Decl::Data {
                params,
                sort,
                ctors,
                ..
            } => {
                for b in params {
                    self.expr(&b.ty)?;
                }
                if let Some(sort) = sort {
                    self.expr(sort)?;
                }
                for c in ctors {
                    for b in &c.fields {
                        self.expr(&b.ty)?;
                    }
                }
            }
            Decl::Signature { ty, .. } => self.expr(ty)?,
            Decl::Test { expr, .. } => self.expr(expr)?,
            Decl::Ability { params, ops, .. } => {
                for b in params {
                    self.expr(&b.ty)?;
                }
                for (_, ty) in ops {
                    self.expr(ty)?;
                }
            }
            Decl::Equation { rhs, .. } => {
                if let Some(rhs) = rhs {
                    self.expr(rhs)?;
                }
            }
        }
        Ok(())
    }

    fn expect(&self, i: usize, tok: &Tok, what: &str) -> Result<(), String> {
        if &self.toks[i].tok == tok {
            Ok(())
        } else {
            Err(format!("line {}: expected {what}", self.line(i)))
        }
    }

    /// `let … =`: the `=` at the top level after the `let` at `start`.
    fn let_equals(&mut self, start: u32) -> Result<(), String> {
        let kw = self.tok_at(start)?;
        self.expect(kw, &Tok::KwLet, "`let`")?;
        let eq = self
            .scan(kw + 1, |t| *t == Tok::Equals)
            .ok_or_else(|| format!("line {}: no `=` after `let`", self.line(kw)))?;
        self.replace_token(eq, ":=")
    }

    fn expr(&mut self, e: &Expr) -> Result<(), String> {
        match e {
            Expr::Var(_)
            | Expr::Num(..)
            | Expr::Str(..)
            | Expr::Char(..)
            | Expr::Type(..)
            | Expr::Prop(_)
            | Expr::Hole(_)
            | Expr::Unit(_) => {}
            Expr::App(a, b) | Expr::Arrow(a, b) | Expr::Binary(_, a, b) | Expr::Seq(a, b) => {
                self.expr(a)?;
                self.expr(b)?;
            }
            Expr::Ann(a, b, _) | Expr::Tuple(a, b, _) => {
                self.expr(a)?;
                self.expr(b)?;
            }
            Expr::Lam(_, body, span) => {
                let bs = self.tok_at(span.start)?;
                self.expect(bs, &Tok::Backslash, "`\\`")?;
                let arrow = self.scan(bs + 1, |t| *t == Tok::Arrow).ok_or_else(|| {
                    format!(
                        "line {}: no `->` after a lambda's parameters",
                        self.line(bs)
                    )
                })?;
                self.replace_token(arrow, "=>")?;
                self.lambdas.insert(span.start, (bs, arrow));
                match &**body {
                    Expr::Match {
                        kind: MatchKind::Lambda,
                        alts,
                        ..
                    } => {
                        for alt in alts {
                            self.expr(&alt.body)?;
                        }
                    }
                    body => self.expr(body)?,
                }
            }
            Expr::Pi { dom, cod, .. } => {
                self.expr(dom)?;
                self.expr(cod)?;
            }
            Expr::NamedArg(_, e, _) | Expr::Neg(e, _) | Expr::Field(e, _) => self.expr(e)?,
            Expr::If {
                cond,
                then,
                otherwise,
                ..
            } => {
                self.expr(cond)?;
                self.expr(then)?;
                self.expr(otherwise)?;
            }
            Expr::List(items, _) => {
                for item in items {
                    self.expr(item)?;
                }
            }
            Expr::Effect(row, b) => {
                for a in &row.abilities {
                    self.expr(a)?;
                }
                self.expr(b)?;
            }
            Expr::Let {
                ty,
                value,
                body,
                span,
                ..
            } => {
                self.let_equals(span.start)?;
                if let Some(ty) = ty {
                    self.expr(ty)?;
                }
                self.expr(value)?;
                self.expr(body)?;
            }
            Expr::Handle { body, clauses, .. } => {
                self.expr(body)?;
                for clause in clauses {
                    match clause {
                        Clause::Return { var, body } => {
                            let i = self.tok_at(var.span.start)?;
                            self.expect(i + 1, &Tok::Arrow, "`->` after `return x`")?;
                            self.replace_token(i + 1, "=>")?;
                            self.expr(body)?;
                        }
                        Clause::Op { k, body, .. } => {
                            let i = self.tok_at(k.span.start)?;
                            self.expect(i - 1, &Tok::FatArrow, "`=>` before the continuation")?;
                            self.expect(i + 1, &Tok::Arrow, "`->` after the continuation")?;
                            let (from, to) = (self.end(i - 2), self.end(i + 1));
                            if self.comment_in(from, to) {
                                return Err(format!(
                                    "line {}: a comment inside a handler clause's `=> k ->`",
                                    self.line(i)
                                ));
                            }
                            // `=>` lands where `->` was when the clauses were lined
                            // up (spaces before the `->`); otherwise one space.
                            let head = format!(", {}", k.text);
                            let room = self.text[from..self.start(i + 1)].chars().count();
                            let lined_up = self.start(i + 1) - self.end(i) > 1;
                            let pad = if lined_up {
                                room.saturating_sub(head.chars().count()).max(1)
                            } else {
                                1
                            };
                            self.fine_edit(
                                from,
                                self.start(i + 1),
                                &format!("{head}{}", " ".repeat(pad)),
                            )?;
                            self.replace_token(i + 1, "=>")?;
                            self.expr(body)?;
                        }
                    }
                }
            }
            Expr::Match {
                scrutinees,
                alts,
                kind,
                span,
            } => {
                match kind {
                    MatchKind::Match => {
                        for alt in alts {
                            let bar = self.tok_at(alt.span.start)?;
                            self.expect(bar, &Tok::Pipe, "`|`")?;
                            let arrow =
                                self.scan(bar + 1, |t| *t == Tok::Arrow).ok_or_else(|| {
                                    format!(
                                        "line {}: no `->` in a `match` alternative",
                                        self.line(bar)
                                    )
                                })?;
                            self.replace_token(arrow, "=>")?;
                        }
                    }
                    MatchKind::Let => self.let_equals(span.start)?,
                    MatchKind::Lambda => {}
                }
                for s in scrutinees {
                    self.expr(&s.expr)?;
                }
                for alt in alts {
                    self.expr(&alt.body)?;
                }
            }
            Expr::Record { base, fields, .. } => {
                if let Some(base) = base {
                    self.expr(base)?;
                }
                for (_, value) in fields {
                    self.expr(value)?;
                }
            }
        }
        Ok(())
    }

    // --- Definitions --------------------------------------------------

    /// Whether `name` is a lowercase name token in `[from, to)` (token
    /// indices).
    fn occurs(&self, name: &str, from: usize, to: usize) -> bool {
        self.toks[from..to]
            .iter()
            .any(|t| matches!(&t.tok, Tok::Lower(s) if s == name))
    }

    /// Whether `name` is bound by a binder in `[from, to)`: written as one
    /// of the names before a binder's `:`.
    fn binds(&self, name: &str, from: usize, to: usize) -> bool {
        (from..to).any(|i| {
            if !matches!(&self.toks[i].tok, Tok::Lower(s) if s == name) {
                return false;
            }
            let mut j = i + 1;
            while j < to && matches!(self.toks[j].tok, Tok::Lower(_)) {
                j += 1;
            }
            j < to && self.toks[j].tok == Tok::Colon
        })
    }

    /// The signature's spine: binders and argument types with an arrow
    /// after them, as far as they can be read with confidence.
    fn spine<'m>(&self, ty: &'m Expr, type_start: usize, sig_end: usize) -> Vec<Elem<'m>> {
        let mut elems = Vec::new();
        let mut cur = ty;
        let mut i = type_start;
        while i < sig_end {
            match cur {
                Expr::Pi {
                    names,
                    implicit,
                    dom,
                    cod,
                    span,
                    ..
                } => {
                    if self.toks[i].span.start != span.start {
                        break;
                    }
                    let Some(close) = self.close_of(i) else { break };
                    if close + 1 >= sig_end || self.toks[close + 1].tok != Tok::Arrow {
                        break;
                    }
                    let Some(colon) = self.scan(i + 1, |t| *t == Tok::Colon) else {
                        break;
                    };
                    if colon >= close {
                        break;
                    }
                    elems.push(Elem {
                        start: i,
                        close,
                        arrow: close + 1,
                        explicit: !implicit,
                        names: names.iter().map(|n| n.text.clone()).collect(),
                        dom: (colon + 1, close),
                        dom_expr: dom,
                    });
                    i = close + 2;
                    cur = cod;
                }
                Expr::Arrow(lhs, rhs) => {
                    let Some(arrow) = self.scan(i, |t| *t == Tok::Arrow) else {
                        break;
                    };
                    if arrow >= sig_end
                        || arrow == i
                        || (self.toks[arrow].span.start) < lhs.span().end
                        || self.toks[arrow].span.end > rhs.span().start
                    {
                        break;
                    }
                    elems.push(Elem {
                        start: i,
                        close: arrow - 1,
                        arrow,
                        explicit: true,
                        names: Vec::new(),
                        dom: (i, arrow),
                        dom_expr: lhs,
                    });
                    i = arrow + 1;
                    cur = rhs;
                }
                _ => break,
            }
        }
        elems
    }

    /// The variable every equation has in column `col`, if they agree.
    fn same_var(eqs: &[Equation], col: usize) -> Option<String> {
        let mut name = None;
        for eq in eqs {
            match &eq.patterns[col] {
                Pattern::Var(v) if name.is_none() || name.as_ref() == Some(&v.text) => {
                    name = Some(v.text.clone());
                }
                _ => return None,
            }
        }
        name
    }

    fn all_wildcards(eqs: &[Equation], col: usize) -> bool {
        eqs.iter()
            .all(|eq| matches!(eq.patterns[col], Pattern::Wildcard(_)))
    }

    fn used_in_bodies(&self, name: &str, eqs: &[Equation]) -> bool {
        eqs.iter().any(|eq| match eq.equals {
            Some(e) => self.occurs(name, e + 1, eq.group.1),
            None => false,
        })
    }

    /// The header binder for `elem`, whose columns start at `col`, if
    /// rule 2 of §5.3 allows one. `ty` is the signature's type tokens.
    fn header_binder(
        &self,
        elem: &Elem,
        col: usize,
        eqs: &[Equation],
        ty: (usize, usize),
    ) -> Option<String> {
        let unit = matches!(elem.dom_expr, Expr::Unit(_));
        let cod = (elem.arrow + 1, ty.1);
        if elem.names.is_empty() {
            if unit
                && (Self::all_wildcards(eqs, col)
                    || Self::same_var(eqs, col).is_some_and(|u| !self.used_in_bodies(&u, eqs)))
            {
                return Some("()".to_string());
            }
            let v = Self::same_var(eqs, col)?;
            if self.occurs(&v, ty.0, ty.1) {
                return None;
            }
            return Some(format!("({v} : {})", self.dom_text(elem)));
        }
        if unit && elem.names.len() == 1 {
            let x = &elem.names[0];
            let unused = Self::all_wildcards(eqs, col)
                || Self::same_var(eqs, col).is_some_and(|u| !self.used_in_bodies(&u, eqs));
            if unused && !self.occurs(x, cod.0, cod.1) {
                return Some("()".to_string());
            }
        }
        let vars: Vec<String> = (0..elem.names.len())
            .map(|w| Self::same_var(eqs, col + w))
            .collect::<Option<_>>()?;
        let distinct: HashSet<&String> = vars.iter().collect();
        if distinct.len() != vars.len() {
            return None;
        }
        for (x, v) in elem.names.iter().zip(&vars) {
            if x == v {
                // Bound here; it may appear in the rest of the type, but not
                // before this binder, in its type, or as another binder.
                if self.occurs(v, ty.0, elem.start)
                    || self.occurs(v, elem.dom.0, elem.dom.1)
                    || self.binds(v, cod.0, cod.1)
                    || elem.names.iter().filter(|n| *n == v).count() > 1
                {
                    return None;
                }
            } else if self.occurs(v, ty.0, ty.1) || self.occurs(x, cod.0, cod.1) {
                return None;
            }
        }
        if vars == elem.names {
            return Some(self.render(self.start(elem.start), self.end(elem.close)));
        }
        let dom = self.render(self.start(elem.dom.0), self.end(elem.dom.1 - 1));
        Some(format!("({} : {dom})", vars.join(" ")))
    }

    /// An unnamed argument's type, for `(v : A)`: without the brackets
    /// around it, unless they belong to it (a tuple, `()`, an annotation)
    /// or it starts with an ability row.
    fn dom_text(&self, elem: &Elem) -> String {
        let (from, to) = elem.dom;
        let wrapped = self.toks[from].tok == Tok::LParen && self.close_of(from) == Some(to - 1);
        let keep = matches!(
            elem.dom_expr,
            Expr::Tuple(..) | Expr::Unit(_) | Expr::Ann(..) | Expr::Effect(..)
        );
        if wrapped && !keep && to - from > 2 {
            self.render(self.start(from + 1), self.end(to - 2))
        } else {
            self.render(self.start(from), self.end(to - 1))
        }
    }

    /// A pattern's text for an arm: a constructor with arguments loses its
    /// brackets (`| Cons x xs, ys`), as alternatives are written.
    fn pattern_text(&self, p: &Pattern) -> String {
        let span = p.span();
        let text = self.text_of(span.start as usize, span.end as usize);
        match p {
            Pattern::Ctor(_, args, _) if !args.is_empty() && text.starts_with('(') => {
                text[1..text.len() - 1].trim().to_string()
            }
            // `[]`'s span is its `]` only.
            Pattern::Nil(_) => "[]".to_string(),
            _ => text.to_string(),
        }
    }

    /// The column of token `i`, if it's the first on its line.
    fn starts_line(&self, i: usize) -> Option<usize> {
        let t = &self.toks[i];
        t.line_start.then_some(t.column as usize)
    }

    fn column(&self, pos: usize) -> usize {
        pos - self.text[..pos].rfind('\n').map_or(0, |n| n + 1)
    }

    fn fresh(&self, n: usize) -> Vec<String> {
        let mut names = Vec::new();
        let mut i = 1;
        while names.len() < n {
            let name = format!("a{i}");
            if !self.names.contains(&name) {
                names.push(name);
            }
            i += 1;
        }
        names
    }

    fn definition(
        &mut self,
        sig: &Decl,
        group: Group,
        equations: &[(Group, &[Pattern], Option<&Expr>)],
        arity: Option<usize>,
        report: &mut Report,
    ) -> Result<(), String> {
        let Decl::Signature {
            name,
            ty,
            theorem,
            export,
            ..
        } = sig
        else {
            unreachable!("called on signatures");
        };
        let line = self.line(group.0);
        let fail = |why: String| Err(format!("line {line}: `{}`: {why}", name.text));
        let name_tok = self.tok_at(name.span.start)?;
        let colon = name_tok + 1;
        self.expect(colon, &Tok::Colon, "`:` after the name")?;
        if self.comment_in(self.start(group.0), self.start(colon + 1)) {
            return fail("a comment inside the signature's start".into());
        }
        let type_start = colon + 1;
        let sig_last = group.1 - 1;

        let mut eqs = Vec::new();
        for &(g, patterns, rhs) in equations {
            let equals = match rhs {
                Some(_) => {
                    let e = self.scan(g.0 + 1, |t| *t == Tok::Equals);
                    match e {
                        Some(e) if e < g.1 => Some(e),
                        _ => {
                            return fail(format!(
                                "no `=` in the equation at line {}",
                                self.line(g.0)
                            ));
                        }
                    }
                }
                None => None,
            };
            eqs.push(Equation {
                group: g,
                patterns,
                rhs,
                equals,
            });
        }
        if eqs.is_empty() {
            // A primitive (the prelude's `Effect.Delay`), or a reject
            // example's missing definition: the header alone. The new syntax
            // has no form for it yet (lane A decides); it's listed.
            let mut header = String::new();
            if *export {
                header.push_str("export ");
            }
            header.push_str(if *theorem { "theorem " } else { "def " });
            header.push_str(&name.text);
            header.push_str(" :");
            header.push_str(&self.render(self.end(colon), self.end(sig_last)));
            self.coarse.push(Edit {
                start: self.start(group.0),
                end: self.end(sig_last),
                text: header,
            });
            self.bodiless.push(self.coarse.len() - 1);
            report.bodiless.push((line, name.text.clone()));
            return Ok(());
        }
        let k = eqs[0].patterns.len();
        if eqs.iter().any(|e| e.patterns.len() != k) {
            return fail("its equations have different numbers of patterns".into());
        }
        if eqs.len() > 1 && k == 0 {
            return fail("several equations without patterns".into());
        }

        let elems = self.spine(ty, type_start, group.1);
        let written: usize = elems
            .iter()
            .filter(|e| e.explicit)
            .map(|e| e.names.len().max(1))
            .sum();
        let n = arity.unwrap_or(written).max(k);
        let tyr = (type_start, group.1);

        // Rule 2: named header parameters.
        let max_named = if eqs.len() > 1 { k - 1 } else { k };
        let mut binders = Vec::new();
        let mut col = 0;
        let mut taken = 0; // elements consumed
        while let Some(j) = (taken..elems.len()).find(|&j| elems[j].explicit) {
            let elem = &elems[j];
            let width = elem.names.len().max(1);
            if col + width > max_named {
                break;
            }
            // From the end of what has moved so far (a comment between two
            // arrows sits before the next binder's first token).
            let from = if taken > 0 {
                self.end(elems[taken - 1].arrow)
            } else {
                self.start(type_start)
            };
            if self.comment_in(from, self.end(elem.arrow)) {
                break;
            }
            let Some(binder) = self.header_binder(elem, col, &eqs, tyr) else {
                break;
            };
            for implicit in &elems[taken..j] {
                binders.push((
                    self.render(self.start(implicit.start), self.end(implicit.close)),
                    self.starts_line(implicit.start),
                ));
            }
            if binder == "()" {
                report.unit_wildcards.push((name.text.clone(), col));
            }
            binders.push((binder, self.starts_line(elem.start)));
            col += width;
            taken = j + 1;
        }
        let named = col;
        let rest_start = if taken > 0 {
            elems[taken - 1].arrow + 1
        } else {
            type_start
        };

        // The header.
        let mut header = String::new();
        if *export {
            header.push_str("export ");
        }
        header.push_str(if *theorem { "theorem " } else { "def " });
        header.push_str(&name.text);
        // A binder whose type started a line in the signature starts one in
        // the header, at the same column.
        for (b, line) in &binders {
            match line {
                Some(column) => {
                    header.push('\n');
                    header.push_str(&" ".repeat(*column));
                }
                None => header.push(' '),
            }
            header.push_str(b);
        }
        header.push_str(" :");
        if taken > 0 {
            let gap = self.text_of(self.end(rest_start - 1), self.start(rest_start));
            header.push_str(if gap.contains('\n') { gap } else { " " });
        } else {
            header.push_str(self.text_of(self.end(colon), self.start(type_start)));
        }
        header.push_str(&self.render(self.start(rest_start), self.end(sig_last)));
        if !binders.is_empty() {
            report.with_parameters += 1;
        }

        // Rule 3: one equation, every column named: a `:=` body.
        if eqs.len() == 1 && named == k {
            let eq = &eqs[0];
            let Some(equals) = eq.equals else {
                return fail("an absurd equation without patterns".into());
            };
            if self.comment_in(self.start(eq.group.0), self.start(equals)) {
                return fail("a comment inside the equation's left-hand side".into());
            }
            // Comments between the signature and the equation go above.
            let between = self.text_of(self.end(sig_last), self.start(eq.group.0));
            let mut moved = String::new();
            for l in between.lines().map(str::trim).filter(|l| !l.is_empty()) {
                moved.push_str(l);
                moved.push('\n');
            }
            self.coarse.push(Edit {
                start: self.start(group.0),
                end: self.end(equals),
                text: format!("{moved}{header} :="),
            });
            report.assign_form += 1;
            return Ok(());
        }

        // Arms. A type continued on lines indented no further than the arms
        // (column 2) is indented two more, so the arms stand out.
        report.arm_form += 1;
        let continued = header.lines().skip(1).filter(|l| !l.trim().is_empty());
        if continued
            .clone()
            .any(|l| l.len() - l.trim_start().len() <= 2)
        {
            let mut lines = header.split('\n');
            let mut shifted = lines.next().unwrap_or_default().to_string();
            for l in lines {
                shifted.push('\n');
                if !l.trim().is_empty() {
                    shifted.push_str("  ");
                }
                shifted.push_str(l);
            }
            header = shifted;
        }
        self.coarse.push(Edit {
            start: self.start(group.0),
            end: self.end(sig_last),
            text: header,
        });
        let missing = n.saturating_sub(k);
        let fresh_names = self.fresh(missing);
        let mut pieces: Vec<Vec<String>> = Vec::new();
        let mut opens = Vec::new();
        for eq in &eqs {
            let head_end = eq.equals.unwrap_or(eq.group.1 - 1);
            if self.line(eq.group.0) != self.line(head_end) {
                return fail(format!(
                    "the equation at line {} has a left-hand side over several lines",
                    self.line(eq.group.0)
                ));
            }
            if self.comment_in(self.start(eq.group.0), self.end(head_end)) {
                return fail("a comment inside an equation's left-hand side".into());
            }
            let mut arm: Vec<String> = eq.patterns[named..]
                .iter()
                .map(|p| self.pattern_text(p))
                .collect();
            let (extra, open) = self.complete(eq, &name.text, missing, &fresh_names, report)?;
            arm.extend(extra);
            pieces.push(arm);
            opens.push(open);
        }

        // Line the columns up where the equations had them lined up.
        let aligned = |pos: &dyn Fn(&Equation) -> Option<usize>| {
            let cols: Vec<usize> = eqs.iter().filter_map(pos).collect();
            cols.len() > 1 && cols.iter().all(|&c| c == cols[0])
        };
        let equals_aligned = aligned(&|e: &Equation| e.equals.map(|q| self.column(self.start(q))));
        let width = pieces[0].len();
        let mut heads: Vec<String> = vec!["  | ".to_string(); eqs.len()];
        for p in 0..width {
            if p > 0 {
                let line_up = if named + p < k {
                    aligned(&|e: &Equation| {
                        Some(self.column(e.patterns[named + p].span().start as usize))
                    })
                } else {
                    equals_aligned
                };
                for h in &mut heads {
                    h.push(',');
                }
                if line_up {
                    let target = heads.iter().map(|h| h.chars().count()).max().unwrap_or(0) + 1;
                    for h in &mut heads {
                        let pad = target - h.chars().count();
                        h.push_str(&" ".repeat(pad));
                    }
                } else {
                    for h in &mut heads {
                        h.push(' ');
                    }
                }
            }
            for (h, arm) in heads.iter_mut().zip(&pieces) {
                h.push_str(&arm[p]);
            }
        }
        let target = heads
            .iter()
            .zip(&eqs)
            .filter(|(_, e)| e.equals.is_some())
            .map(|(h, _)| h.chars().count())
            .max()
            .unwrap_or(0)
            + 1;
        for ((h, eq), open) in heads.iter_mut().zip(&eqs).zip(&opens) {
            let Some(equals) = eq.equals else {
                self.coarse.push(Edit {
                    start: self.start(eq.group.0),
                    end: self.end(eq.group.1 - 1),
                    text: h.clone(),
                });
                continue;
            };
            let pad = if equals_aligned {
                target - h.chars().count()
            } else {
                1
            };
            h.push_str(&" ".repeat(pad));
            h.push_str("=>");
            if *open {
                h.push_str(" (");
            }
            self.coarse.push(Edit {
                start: self.start(eq.group.0),
                end: self.end(equals),
                text: h.clone(),
            });
        }

        // L5: an arm's later lines must be indented further than its `|`.
        let shift = eqs.iter().any(|eq| {
            (eq.group.0 + 1..eq.group.1)
                .any(|i| self.toks[i].line_start && self.toks[i].column <= 2)
        });
        if shift {
            for eq in &eqs {
                let (from, to) = (self.start(eq.group.0), self.end(eq.group.1 - 1));
                let mut pos = from;
                while let Some(nl) = self.text[pos..to].find('\n') {
                    let line_start = pos + nl + 1;
                    let blank = self.text[line_start..]
                        .chars()
                        .take_while(|&c| c != '\n')
                        .all(|c| c == ' ');
                    if !blank {
                        self.coarse.push(Edit {
                            start: line_start,
                            end: line_start,
                            text: "  ".to_string(),
                        });
                    }
                    pos = line_start;
                }
            }
        }
        Ok(())
    }

    /// Rule 4: the patterns to add to an arm short of `missing` patterns,
    /// with the edits to its body. Returns whether the head must end with
    /// `(` (the body, starting on a later line, is applied to fresh names).
    fn complete(
        &mut self,
        eq: &Equation,
        name: &str,
        missing: usize,
        fresh: &[String],
        report: &mut Report,
    ) -> Result<(Vec<String>, bool), String> {
        if missing == 0 {
            return Ok((Vec::new(), false));
        }
        let line = self.line(eq.group.0);
        let (Some(rhs), Some(equals)) = (eq.rhs, eq.equals) else {
            report.completions.push(Completion {
                line,
                name: name.to_string(),
                how: How::Absurd(missing),
            });
            return Ok((vec!["_".to_string(); missing], false));
        };
        // Names the arm binds already: a moved parameter mustn't clash.
        let mut bound = HashSet::new();
        for p in eq.patterns {
            pattern_vars(p, &mut bound);
        }
        let mut moved: Vec<String> = Vec::new();
        let mut cur = rhs;
        let mut cur_tok = equals + 1;
        // Deletion of whole lambda headers: from where, to the last `->`.
        let mut deleted_to = None;
        let mut partial = None;
        while moved.len() < missing {
            let Expr::Lam(names, body, span) = cur else {
                break;
            };
            let Some(&(bs, arrow)) = self.lambdas.get(&span.start) else {
                break;
            };
            if bs != cur_tok || names.iter().any(|n| n.text.starts_with('%')) {
                break;
            }
            let mut take = 0;
            for n in names.iter().take(missing - moved.len()) {
                if n.text != "_" && (bound.contains(&n.text) || moved.contains(&n.text)) {
                    break;
                }
                if self.comment_in(self.start(bs), self.end(arrow)) {
                    break;
                }
                moved.push(n.text.clone());
                take += 1;
            }
            if take == 0 {
                break;
            }
            if take < names.len() {
                partial = Some((
                    names[0].span.start as usize,
                    names[take].span.start as usize,
                ));
                break;
            }
            deleted_to = Some(arrow);
            cur = body;
            cur_tok = arrow + 1;
        }
        let mut open = false;
        if let Some(arrow) = deleted_to {
            let next = arrow + 1;
            let (from, to) = if next < eq.group.1 && !self.toks[next].line_start {
                (self.start(equals + 1), self.start(next))
            } else {
                (self.end(equals), self.end(arrow))
            };
            self.coarse.push(Edit {
                start: from,
                end: to,
                text: String::new(),
            });
        }
        if let Some((from, to)) = partial {
            self.coarse.push(Edit {
                start: from,
                end: to,
                text: String::new(),
            });
        }
        let still = missing - moved.len();
        let applied: Vec<String> = fresh[..still].to_vec();
        if still > 0 {
            let last = eq.group.1 - 1;
            // Already in brackets, `(\y -> …)`, it needs no more.
            let bracketed =
                self.toks[cur_tok].tok == Tok::LParen && self.close_of(cur_tok) == Some(last);
            let wrap = partial.is_some()
                || !(bracketed || matches!(cur, Expr::Var(_) | Expr::App(..) | Expr::Field(..)));
            let args = applied.join(" ");
            if wrap {
                if self.toks[cur_tok].line_start {
                    open = true;
                } else {
                    let at = self.start(cur_tok);
                    self.coarse.push(Edit {
                        start: at,
                        end: at,
                        text: "(".to_string(),
                    });
                }
                let at = self.end(last);
                self.coarse.push(Edit {
                    start: at,
                    end: at,
                    text: format!(") {args}"),
                });
            } else {
                let at = self.end(last);
                self.coarse.push(Edit {
                    start: at,
                    end: at,
                    text: format!(" {args}"),
                });
            }
        }
        let how = match (moved.is_empty(), applied.is_empty()) {
            (false, true) => How::Moved(moved.clone()),
            (true, false) => How::Applied(applied.clone()),
            _ => How::MovedThenApplied(moved.clone(), applied.clone()),
        };
        report.completions.push(Completion {
            line,
            name: name.to_string(),
            how,
        });
        let mut extra = moved;
        extra.extend(applied);
        Ok((extra, open))
    }
}

fn pattern_vars(p: &Pattern, out: &mut HashSet<String>) {
    match p {
        Pattern::Var(v) => {
            out.insert(v.text.clone());
        }
        Pattern::Ctor(_, args, _) => args.iter().for_each(|a| pattern_vars(a, out)),
        Pattern::Tuple(a, b, _) | Pattern::Cons(a, b, _) => {
            pattern_vars(a, out);
            pattern_vars(b, out);
        }
        Pattern::Record { fields, .. } => fields.iter().for_each(|(_, p)| pattern_vars(p, out)),
        Pattern::Wildcard(_)
        | Pattern::Absurd(_)
        | Pattern::Num(..)
        | Pattern::NegNum(..)
        | Pattern::Nil(_) => {}
    }
}
