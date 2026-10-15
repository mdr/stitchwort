//! Elaboration: turns surface syntax into complete core terms. It resolves
//! names, desugars (numbers, lists, `+`), fills in implicit arguments by
//! unification, and compiles pattern-matching equations into case trees.
//!
//! Every declaration it produces is then re-checked by the kernel
//! (`stitchwort-core`), so a bug here can cause a confusing error but can't
//! make the kernel accept something false.

mod auto;
mod autobind;
mod check;
mod unify;

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use stitchwort_core::check as kernel;
use stitchwort_core::native::{self, Native};
use stitchwort_core::term::Branch;
use stitchwort_core::value::{eval, force};
use stitchwort_core::{DataId, DefId, Globals, Icit, Name, Sort, Term, Value, pretty};
use stitchwort_syntax::ast::{Decl, Expr, Module, Pattern};
use stitchwort_syntax::{Diagnostic, Span, ast};

use check::{Ctx, check, check_type, infer};

pub const PRELUDE: &str = include_str!("prelude.sw");

type Result<T> = std::result::Result<T, Diagnostic>;

/// Names with built-in meanings, which can't be redefined.
const RESERVED: &[&str] = &["rfl", "J"];

#[derive(Clone, Copy)]
enum Global {
    Def(DefId),
    Data(DataId),
    Ctor(DataId, usize),
}

/// A `test "name" = expr` declaration, checked as a definition of type `Bool`.
pub struct TestDecl {
    pub name: String,
    pub def: DefId,
    pub span: Span,
}

#[derive(Default)]
pub struct Elaborator {
    pub globals: Globals,
    pub tests: Vec<TestDecl>,
    names: HashMap<String, (Global, Span)>,
    /// Auto arguments still to be proved in the current declaration.
    obligations: RefCell<Vec<auto::Obligation>>,
    /// While the prelude is loaded, its built-in types and natively
    /// implemented definitions are registered with the kernel by name.
    pub loading_prelude: bool,
}

/// A pattern that matches a constructor.
struct CtorPattern<'p> {
    data: DataId,
    ctor: usize,
    args: Vec<&'p Pattern>,
    span: Span,
}

/// One equation during pattern-match compilation: the patterns still to be
/// matched, and the pattern variables already bound (to de Bruijn levels).
struct Row<'a> {
    pats: Vec<&'a Pattern>,
    aliases: Vec<(&'a str, usize)>,
    /// `None` for an equation with an absurd pattern `()`.
    rhs: Option<&'a Expr>,
    span: Span,
}

/// A compiled pattern match, before its right-hand sides are checked.
enum Tree<'a> {
    Leaf {
        aliases: Vec<(&'a str, usize)>,
        rhs: Option<&'a Expr>,
        span: Span,
    },
    /// The variable at `level` has a type with no values.
    Absurd { level: usize, span: Span },
    Case {
        /// The level of the variable being matched.
        level: usize,
        data: DataId,
        branches: Vec<(Vec<Name>, Tree<'a>)>,
        span: Span,
    },
}

fn error(code: &'static str, span: Span, message: impl Into<String>) -> Diagnostic {
    let message = message.into();
    Diagnostic::error(code, message.clone()).with_label(span, message)
}

fn name(n: &ast::Name) -> Name {
    n.text.as_str().into()
}

impl Elaborator {
    pub fn new() -> Self {
        Self::default()
    }

    /// Elaborates and checks every declaration, continuing past errors.
    pub fn elaborate_module(&mut self, module: &Module) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let decls = &module.decls;
        let mut i = 0;
        while i < decls.len() {
            let equations_for = |name: &str, from: usize| {
                let mut j = from;
                while let Some(Decl::Equation { name: n, .. }) = decls.get(j)
                    && n.text == name
                {
                    j += 1;
                }
                j
            };
            match &decls[i] {
                decl @ Decl::Data { .. } => {
                    if let Err(d) = self.data(decl) {
                        diagnostics.push(d);
                    }
                    i += 1;
                }
                Decl::Test { name, expr, span } => {
                    if let Err(d) = self.test(name, expr, *span) {
                        diagnostics.push(d);
                    }
                    i += 1;
                }
                decl @ Decl::Signature { name, .. } => {
                    let end = equations_for(&name.text, i + 1);
                    if let Err(d) = self.definition(decl, &decls[i + 1..end]) {
                        diagnostics.push(d);
                    }
                    i = end;
                }
                Decl::Equation { name, .. } => {
                    diagnostics.push(error(
                        "E-MISSING-SIGNATURE",
                        name.span,
                        format!(
                            "`{}` needs a type signature before its equations",
                            name.text
                        ),
                    ));
                    i = equations_for(&name.text, i);
                }
            }
        }
        self.clear_metas();
        diagnostics
    }

    /// Elaborates a closed expression, and infers its type with the kernel.
    pub fn infer_expr(&self, expr: &Expr) -> Result<(Term, Value)> {
        self.clear_metas();
        let (term, ty) = {
            let mut cx = Ctx::new(self, expr.span());
            let (mut term, mut ty) = infer(&mut cx, expr)?;
            // A call gets its trailing implicit and auto arguments too (so
            // `div 7 2` gets its proof); a bare name like `length` keeps its
            // polymorphic type.
            if matches!(expr, Expr::App(..) | Expr::Binary(..)) {
                (term, ty) = check::insert(&mut cx, term, ty);
            }
            (term, cx.quote(&ty))
        };
        let term = self.finish(&term, 0)?;
        self.finish(&ty, 0)?;
        self.clear_metas();
        kernel::infer_closed(&self.globals, &term, expr.span())
    }

    pub fn eval(&self, term: &Term) -> Value {
        eval(&self.globals, &[], term)
    }

    pub fn show(&self, value: &Value) -> String {
        pretty::value(&self.globals, &[], value)
    }

    fn clear_metas(&self) {
        self.globals.metas.borrow_mut().clear();
        self.obligations.borrow_mut().clear();
    }

    /// Proves outstanding auto arguments, then substitutes metavariable
    /// solutions into `term`, failing if any are unsolved.
    fn finish(&self, term: &Term, level: usize) -> Result<Term> {
        self.solve_obligations()?;
        unify::zonk(&self.globals, level, term).map_err(|m| {
            let span = self.globals.metas.borrow()[m].span;
            Diagnostic::error("E-UNSOLVED", "can't work out an implicit argument")
                .with_label(span, "the compiler couldn't work out what goes here")
                .with_note("supply it explicitly with `f [x := …]`, or add a type annotation")
        })
    }

    fn test(&mut self, name: &str, expr: &Expr, span: Span) -> Result<()> {
        if let Some(earlier) = self.tests.iter().find(|t| t.name == name) {
            return Err(error(
                "E-DUPLICATE",
                span,
                format!("there's already a test called \"{name}\""),
            )
            .with_label(earlier.span, "first defined here"));
        }
        let Some((Global::Data(bool_data), _)) = self.names.get("Bool").copied() else {
            return Err(error(
                "E-UNKNOWN-NAME",
                span,
                "tests need the prelude's `Bool`",
            ));
        };
        self.clear_metas();
        let body = {
            let mut cx = Ctx::new(self, span);
            let term = check(&mut cx, expr, &Value::Data(bool_data, Vec::new()))?;
            self.finish(&term, 0)?
        };
        let ty = Term::Data(bool_data, Vec::new());
        let label: Name = format!("test \"{name}\"").into();
        let id = kernel::declare_def(&mut self.globals, &label, &ty, false, false, span)?;
        kernel::define_def(&mut self.globals, id, &body)?;
        self.tests.push(TestDecl {
            name: name.to_string(),
            def: id,
            span,
        });
        Ok(())
    }

    fn check_new_name(&self, n: &ast::Name) -> Result<()> {
        if RESERVED.contains(&n.text.as_str()) {
            return Err(error(
                "E-DUPLICATE",
                n.span,
                format!("`{}` is built in and can't be redefined", n.text),
            ));
        }
        if let Some((_, previous)) = self.names.get(&n.text) {
            return Err(error(
                "E-DUPLICATE",
                n.span,
                format!("`{}` is already defined", n.text),
            )
            .with_label(*previous, "first defined here"));
        }
        Ok(())
    }

    fn data(&mut self, decl: &Decl) -> Result<()> {
        let Decl::Data {
            name: data_name,
            params,
            sort,
            ctors,
            span,
        } = decl
        else {
            unreachable!()
        };
        self.check_new_name(data_name)?;
        self.clear_metas();

        let (params, sort) = {
            let mut cx = Ctx::new(self, *span);
            let mut checked = Vec::new();
            for binder in params {
                let (ty, _) = check_type(&mut cx, &binder.ty)?;
                for (k, n) in binder.names.iter().enumerate() {
                    let ty = self.finish(&ty.shift(k, 0), cx.level())?;
                    let value = cx.eval(&ty);
                    checked.push((name(n), ty));
                    cx.bind(&n.text, value);
                }
            }
            let sort = match sort {
                None => Sort::Type(0),
                Some(e) => {
                    let mut cx = Ctx::new(self, e.span());
                    match check_type(&mut cx, e)?.0.strip_loc() {
                        Term::Sort(s) => *s,
                        _ => {
                            return Err(error(
                                "E-NOT-A-SORT",
                                e.span(),
                                "expected `Type`, `Type n` or `Prop`",
                            ));
                        }
                    }
                }
            };
            (checked, sort)
        };
        let d = kernel::declare_data(&mut self.globals, name(data_name), params, sort, *span)?;
        self.names
            .insert(data_name.text.clone(), (Global::Data(d), data_name.span));

        let mut core_ctors = Vec::new();
        for (c, ctor) in ctors.iter().enumerate() {
            self.check_new_name(&ctor.name)?;
            if let Some(earlier) = ctors[..c].iter().find(|e| e.name.text == ctor.name.text) {
                return Err(error(
                    "E-DUPLICATE",
                    ctor.name.span,
                    format!("`{}` is already defined", ctor.name.text),
                )
                .with_label(earlier.name.span, "first defined here"));
            }
            self.clear_metas();
            let mut cx = Ctx::new(self, *span);
            for (x, ty) in &self.globals.data(d).params {
                let value = cx.eval(ty);
                cx.bind(x, value);
            }
            let mut fields = Vec::new();
            for binder in &ctor.fields {
                let (ty, _) = check_type(&mut cx, &binder.ty)?;
                for (k, n) in binder.names.iter().enumerate() {
                    let ty = self.finish(&ty.shift(k, 0), cx.level())?;
                    let value = cx.eval(&ty);
                    fields.push((name(n), ty, binder.ty.span()));
                    cx.bind(&n.text, value);
                }
            }
            core_ctors.push(kernel::CtorDecl {
                name: name(&ctor.name),
                fields,
            });
        }
        kernel::define_ctors(&mut self.globals, d, core_ctors)?;
        if self.loading_prelude {
            match data_name.text.as_str() {
                "Nat" => native::register_nat(&mut self.globals, d)?,
                "Bool" => native::register_bool(&mut self.globals, d)?,
                "Decidable" => native::register_decidable(&mut self.globals, d)?,
                _ => {}
            }
        }
        for (c, ctor) in ctors.iter().enumerate() {
            self.names
                .insert(ctor.name.text.clone(), (Global::Ctor(d, c), ctor.name.span));
        }
        Ok(())
    }

    fn definition(&mut self, signature: &Decl, equations: &[Decl]) -> Result<()> {
        let Decl::Signature {
            name: def_name,
            ty,
            theorem,
            export,
            span,
        } = signature
        else {
            unreachable!()
        };
        self.check_new_name(def_name)?;
        self.clear_metas();

        let ty = {
            let auto = autobind::auto_bound(self, ty);
            let mut cx = Ctx::new(self, *span);
            let mut domains = Vec::new();
            for n in &auto {
                // The type of an implicitly bound variable is worked out from
                // how it's used (usually `Type`).
                cx.span = n.span;
                let dom = cx.fresh_meta();
                let value = cx.eval(&dom);
                domains.push(dom);
                cx.bind(&n.text, value);
            }
            cx.span = *span;
            let (mut term, _) = check_type(&mut cx, ty)?;
            for (n, dom) in auto.iter().zip(domains).rev() {
                term = Term::Pi(name(n), Icit::Implicit, Rc::new(dom), Rc::new(term));
            }
            self.finish(&term, 0)?
        };
        let id = kernel::declare_def(
            &mut self.globals,
            &name(def_name),
            &ty,
            *theorem,
            *export,
            *span,
        )?;
        // Registered before the body is elaborated, so it can refer to itself.
        // If the body fails, the definition stays without one (opaque), so
        // later uses don't cascade into "unknown name" errors.
        self.names
            .insert(def_name.text.clone(), (Global::Def(id), def_name.span));
        self.clear_metas();
        let body = self.body(id, def_name, equations)?;
        kernel::define_def(&mut self.globals, id, &body)?;
        if self.loading_prelude {
            if let Some(op) = Native::ALL.into_iter().find(|n| n.name() == def_name.text) {
                native::register_native(&mut self.globals, id, op)?;
            } else if def_name.text == "natNeq" {
                native::register_nat_neq(&mut self.globals, id)?;
            }
        }
        if *export {
            self.add_validators(id)?;
        }
        Ok(())
    }

    /// For each proof parameter of an export, a decision procedure that the
    /// extracted JS runs on its inputs (DESIGN.md §12). A proof parameter with
    /// no decision procedure can't be checked at runtime, so the export is
    /// refused.
    fn add_validators(&mut self, id: DefId) -> Result<()> {
        let Some((Global::Data(decidable), _)) = self.names.get("Decidable").copied() else {
            return Ok(()); // no prelude
        };
        let def = self.globals.def(id);
        let (name, span) = (def.name.clone(), def.span);
        let tel = kernel::telescope(&self.globals, &def.ty_value, span);
        let mut found = Vec::new();
        for (i, (_, ty, erased)) in tel.params.iter().enumerate() {
            if !erased || kernel::is_type_former(&self.globals, i, ty) {
                continue; // runtime data, or a type parameter (refused when exporting)
            }
            self.clear_metas();
            let mut cx = Ctx::from_parts(
                self,
                (0..i).map(Value::var).collect(),
                tel.params[..i].iter().map(|(_, t, _)| t.clone()).collect(),
                tel.params[..i].iter().map(|(x, _, _)| x.clone()).collect(),
                span,
            );
            let shown = cx.show(ty);
            let decision = auto::decide(&mut cx, ty, 0).map_err(|_| {
                Diagnostic::error("E-EXPORT", format!("`{name}` can't be exported"))
                    .with_label(
                        span,
                        format!("its precondition `{shown}` can't be checked at runtime"),
                    )
                    .with_note("an exported function's proof arguments need a decision procedure (a function returning `Decidable …`)")
            })?;
            found.push((i, self.finish(&decision, i)?));
        }
        self.clear_metas();
        for (i, decision) in found {
            kernel::add_validator(&mut self.globals, id, i, decidable, &decision)?;
        }
        Ok(())
    }

    fn body(&self, id: DefId, def_name: &ast::Name, equations: &[Decl]) -> Result<Term> {
        let g = &self.globals;
        let equations: Vec<(&Vec<Pattern>, Option<&Expr>, Span)> = equations
            .iter()
            .map(|eq| match eq {
                Decl::Equation {
                    patterns,
                    rhs,
                    span,
                    ..
                } => (patterns, rhs.as_ref(), *span),
                _ => unreachable!(),
            })
            .collect();
        let Some(&(first_patterns, first_rhs, first_span)) = equations.first() else {
            return Err(error(
                "E-MISSING-DEFINITION",
                def_name.span,
                format!("`{}` has a type signature but no equations", def_name.text),
            ));
        };
        let arity = first_patterns.len();
        for &(patterns, _, span) in &equations {
            if patterns.len() != arity {
                return Err(error(
                    "E-ARITY",
                    span,
                    format!(
                        "this equation has {} patterns, but the first one has {arity}",
                        patterns.len()
                    ),
                ));
            }
        }
        let span = first_span.to(equations.last().expect("non-empty").2);

        // Bind the parameters: implicit ones by their names in the signature,
        // explicit ones to be matched by the patterns. Implicit parameters after
        // the last pattern are bound too, so they can be used by name.
        let mut cx = Ctx::new(self, span);
        let mut lams: Vec<(Name, Icit)> = Vec::new();
        let mut columns = Vec::new();
        let mut ty = g.def(id).ty_value.clone();
        loop {
            match force(g, ty.clone()) {
                // Implicit and auto parameters are in scope by name, wherever
                // they are in the signature.
                Value::Pi(x, icit, dom, cod) if icit.is_implicit() => {
                    let var = Value::var(cx.level());
                    cx.bind(&x, (*dom).clone());
                    lams.push((x, icit));
                    ty = cod.apply(g, var);
                }
                Value::Pi(x, Icit::Explicit, dom, cod) if columns.len() < arity => {
                    let param = match &first_patterns[columns.len()] {
                        Pattern::Var(v) => name(v),
                        _ => x,
                    };
                    let var = Value::var(cx.level());
                    columns.push(cx.level());
                    cx.bind_hidden(param.clone(), (*dom).clone());
                    lams.push((param, Icit::Explicit));
                    ty = cod.apply(g, var);
                }
                _ => break,
            }
        }
        if columns.len() < arity {
            return Err(error(
                "E-ARITY",
                first_span,
                format!(
                    "`{}` takes {} explicit argument(s), but this equation has {arity} patterns",
                    def_name.text,
                    columns.len()
                ),
            ));
        }

        let tree = if arity == 0 {
            if let Some(&(_, _, span)) = equations.get(1) {
                return Err(error(
                    "E-DUPLICATE",
                    span,
                    format!("`{}` is defined more than once", def_name.text),
                ));
            }
            Tree::Leaf {
                aliases: Vec::new(),
                rhs: first_rhs,
                span: first_span,
            }
        } else {
            let rows: Vec<Row> = equations
                .iter()
                .map(|&(patterns, rhs, span)| Row {
                    pats: patterns.iter().collect(),
                    aliases: Vec::new(),
                    rhs,
                    span,
                })
                .collect();
            self.compile(&rows, cx.level(), &columns, span)?
        };
        let mut term = check_tree(&mut cx, &tree, &ty)?;
        for (x, icit) in lams.into_iter().rev() {
            term = Term::Lam(x, icit, Rc::new(term));
        }
        self.finish(&term, 0)
    }

    /// Compiles equations into a case tree. `columns[j]` is the de Bruijn level
    /// of the value each row's `j`th pattern matches; `depth` is the number of
    /// variables in scope.
    fn compile<'a>(
        &self,
        rows: &[Row<'a>],
        depth: usize,
        columns: &[usize],
        span: Span,
    ) -> Result<Tree<'a>> {
        let first = &rows[0];
        if let Some(j) = first
            .pats
            .iter()
            .position(|p| matches!(p, Pattern::Absurd(_)))
        {
            return Ok(Tree::Absurd {
                level: columns[j],
                span: first.pats[j].span(),
            });
        }
        let mut split = None;
        for (j, pattern) in first.pats.iter().enumerate() {
            if let Some(ctor) = self.pattern_ctor(pattern)? {
                split = Some((j, ctor.data));
                break;
            }
        }
        let Some((j, d)) = split else {
            // The first row matches whatever is left: it's the result.
            let mut aliases = first.aliases.clone();
            for (pattern, level) in first.pats.iter().zip(columns) {
                if let Pattern::Var(x) = pattern {
                    aliases.push((&x.text, *level));
                }
            }
            return Ok(Tree::Leaf {
                aliases,
                rhs: first.rhs,
                span: first.span,
            });
        };

        let level = columns[j];
        let data = self.globals.data(d);
        let rest_columns: Vec<usize> = columns
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != j)
            .map(|(_, c)| *c)
            .collect();
        let mut branches = Vec::new();
        for (c, ctor) in data.ctors.iter().enumerate() {
            let k = ctor.fields.len();
            let mut names: Vec<Option<Name>> = vec![None; k];
            let mut branch_rows = Vec::new();
            for row in rows {
                let pattern = row.pats[j];
                let mut aliases = row.aliases.clone();
                match self.pattern_ctor(pattern)? {
                    Some(CtorPattern {
                        data: d2,
                        ctor: c2,
                        args,
                        span: pattern_span,
                    }) => {
                        if d2 != d {
                            return Err(error(
                                "E-TYPE-MISMATCH",
                                pattern_span,
                                format!(
                                    "this pattern is a `{}`, but other patterns here are `{}`",
                                    self.globals.data(d2).name,
                                    data.name
                                ),
                            ));
                        }
                        if c2 != c {
                            continue;
                        }
                        if args.len() != k {
                            return Err(error(
                                "E-ARITY",
                                pattern_span,
                                format!(
                                    "`{}` has {k} fields, but this pattern has {}",
                                    ctor.name,
                                    args.len()
                                ),
                            ));
                        }
                        for (f, arg) in args.iter().enumerate() {
                            match arg {
                                Pattern::Var(x) => {
                                    aliases.push((&x.text, depth + f));
                                    names[f].get_or_insert_with(|| name(x));
                                }
                                Pattern::Wildcard(_) => {}
                                other => {
                                    return Err(error(
                                        "E-NESTED-PATTERN",
                                        other.span(),
                                        "nested patterns aren't supported yet",
                                    )
                                    .with_note(
                                        "use a variable here, and match on it in a helper function",
                                    ));
                                }
                            }
                        }
                    }
                    None => {
                        if let Pattern::Var(x) = pattern {
                            aliases.push((&x.text, level));
                        }
                    }
                }
                branch_rows.push(Row {
                    pats: row
                        .pats
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != j)
                        .map(|(_, p)| *p)
                        .collect(),
                    aliases,
                    rhs: row.rhs,
                    span: row.span,
                });
            }
            if branch_rows.is_empty() {
                let example = std::iter::once(ctor.name.to_string())
                    .chain(std::iter::repeat_n("_".to_string(), k))
                    .collect::<Vec<_>>()
                    .join(" ");
                return Err(error(
                    "E-NONEXHAUSTIVE",
                    span,
                    format!("missing case: no equation matches `{example}`"),
                ));
            }
            let body = self.compile(&branch_rows, depth + k, &rest_columns, span)?;
            let names = names
                .into_iter()
                .zip(&ctor.fields)
                .map(|(n, (field, _))| n.unwrap_or_else(|| field.clone()))
                .collect();
            branches.push((names, body));
        }
        Ok(Tree::Case {
            level,
            data: d,
            branches,
            span,
        })
    }

    /// The constructor `pattern` matches, if any.
    fn pattern_ctor<'p>(&self, pattern: &'p Pattern) -> Result<Option<CtorPattern<'p>>> {
        match pattern {
            Pattern::Var(_) | Pattern::Wildcard(_) | Pattern::Absurd(_) => Ok(None),
            Pattern::Num(0, span) => {
                let (d, c) = self.ctor_named("Zero", *span)?;
                Ok(Some(CtorPattern {
                    data: d,
                    ctor: c,
                    args: Vec::new(),
                    span: *span,
                }))
            }
            Pattern::Num(_, span) => Err(error(
                "E-NESTED-PATTERN",
                *span,
                "only `0` can be used as a number pattern for now",
            )
            .with_note("write `Succ n` instead")),
            Pattern::Ctor(n, args, span) => {
                let (d, c) = self.ctor_named(&n.text, n.span)?;
                Ok(Some(CtorPattern {
                    data: d,
                    ctor: c,
                    args: args.iter().collect(),
                    span: *span,
                }))
            }
        }
    }

    fn ctor_named(&self, ctor: &str, span: Span) -> Result<(DataId, usize)> {
        match self.names.get(ctor) {
            Some((Global::Ctor(d, c), _)) => Ok((*d, *c)),
            Some(_) => Err(error(
                "E-NOT-A-CONSTRUCTOR",
                span,
                format!("`{ctor}` isn't a constructor"),
            )),
            None => Err(error(
                "E-UNKNOWN-NAME",
                span,
                format!("unknown name `{ctor}`"),
            )),
        }
    }
}

/// Checks a compiled pattern match against `goal`, refining the goal in each
/// branch (the kernel does the same when it re-checks the result).
fn check_tree(cx: &mut Ctx, tree: &Tree, goal: &Value) -> Result<Term> {
    match tree {
        Tree::Leaf { aliases, rhs, span } => {
            let Some(rhs) = rhs else {
                return Err(error(
                    "E-ARITY",
                    *span,
                    "this equation needs `= …`: only an equation with a `()` pattern can leave it out",
                ));
            };
            let mark = cx.mark();
            for (x, level) in aliases {
                cx.alias(x, *level);
            }
            let result = check(cx, rhs, goal);
            cx.reset(mark);
            result
        }
        Tree::Absurd { level, span } => match force(cx.g(), cx.types[*level].clone()) {
            Value::Data(d, _) if cx.g().data(d).ctors.is_empty() => Ok(Term::Loc(
                *span,
                Rc::new(Term::Case(cx.level() - 1 - level, d, Vec::new().into())),
            )),
            other => Err(error(
                "E-NOT-EMPTY",
                *span,
                format!(
                    "`{}` has values, so this argument can't be `()`",
                    cx.show(&other)
                ),
            )),
        },
        Tree::Case {
            level: x,
            data: d,
            branches,
            span,
        } => {
            let g = cx.g();
            let data = g.data(*d);
            let params = match force(g, cx.types[*x].clone()) {
                Value::Data(d2, params) if d2 == *d => params,
                other => {
                    return Err(error(
                        "E-TYPE-MISMATCH",
                        *span,
                        format!(
                            "these patterns match a `{}`, but the argument has type `{}`",
                            data.name,
                            cx.show(&other)
                        ),
                    ));
                }
            };
            let goal_term = cx.quote(goal);
            let mut out = Vec::new();
            for (c, ((names, subtree), ctor)) in branches.iter().zip(&data.ctors).enumerate() {
                let mark = cx.mark();
                let base = cx.level();
                let fields: Vec<Value> = (0..ctor.fields.len())
                    .map(|i| Value::var(base + i))
                    .collect();
                // Inside the branch, the matched variable *is* the constructor
                // value, so the goal and the types of later variables are
                // refined with it (as the kernel does).
                let mut env = cx.env.clone();
                env[*x] = Value::Ctor(*d, c, fields.clone());
                let branch_goal = eval(g, &env, &goal_term);
                let refined: Vec<Value> = cx
                    .types
                    .iter()
                    .enumerate()
                    .map(|(l, ty)| {
                        if l > *x {
                            eval(g, &env, &cx.quote(ty))
                        } else {
                            ty.clone()
                        }
                    })
                    .collect();
                let saved_env = std::mem::replace(&mut cx.env, env);
                let saved_types = std::mem::replace(&mut cx.types, refined);
                let mut field_env = params.clone();
                for ((_, field_ty), (name, field)) in
                    ctor.fields.iter().zip(names.iter().zip(&fields))
                {
                    let ty = eval(g, &field_env, field_ty);
                    field_env.push(field.clone());
                    cx.bind_hidden(name.clone(), ty);
                }
                let result = check_tree(cx, subtree, &branch_goal);
                cx.reset(mark);
                cx.env = saved_env;
                cx.types = saved_types;
                out.push(Branch {
                    names: names.clone(),
                    body: result?,
                });
            }
            Ok(Term::Loc(
                *span,
                Rc::new(Term::Case(cx.level() - 1 - x, *d, out.into())),
            ))
        }
    }
}
