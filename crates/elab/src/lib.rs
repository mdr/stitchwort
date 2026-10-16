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
mod effects;
mod module;
mod records;
mod unify;

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use num_bigint::BigUint;
use stitchwort_core::chars;
use stitchwort_core::check as kernel;
use stitchwort_core::native::{self, Native};
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::{eval, force};
use stitchwort_core::{DataId, DefId, Globals, Icit, Limits, Name, Sort, Term, Value, pretty};
use stitchwort_syntax::ast::{Decl, Expr, Pattern};
use stitchwort_syntax::{Diagnostic, Span, ast};

use check::{Ctx, check, check_type, infer};
use module::Phase;

pub const PRELUDE: &str = include_str!("prelude.sw");

type Result<T> = std::result::Result<T, Diagnostic>;

/// Names with built-in meanings, which can't be redefined.
const RESERVED: &[&str] = &["rfl", "J"];

#[derive(Clone, Copy)]
enum Global {
    Def(DefId),
    Data(DataId),
    Ctor(DataId, usize),
    /// An ability, by its index in `Elaborator::abilities`.
    Ability(usize),
    /// Operation `i` of an ability.
    Op(usize, usize),
    /// Declared by this item of the module being elaborated, which hasn't
    /// been checked yet (`module::ModuleState::items`).
    Unchecked(usize),
    /// Declared by a declaration that failed before it was checked.
    Failed,
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
    abilities: Vec<effects::AbilityInfo>,
    /// Resource limits for checking each declaration.
    pub limits: Limits,
    /// For tests only: compile number patterns the old way, as nested `Succ`
    /// patterns, even where a number case would do. Only usable with small
    /// numbers. Tests compare the two compilations.
    pub numbers_as_succ: bool,
    /// The module being elaborated, and what's being checked in it.
    module: module::ModuleState,
    /// Warnings found while elaborating the current declaration.
    warnings: Vec<Diagnostic>,
    /// How many modules have been elaborated (the prelude is the first).
    modules: usize,
    /// The record types declared so far (docs/proposals/records.md).
    records: HashMap<DataId, records::RecordInfo>,
}

/// A pattern that matches a constructor.
struct CtorPattern<'a> {
    data: DataId,
    ctor: usize,
    args: Vec<Pat<'a>>,
    span: Span,
}

/// A pattern during compilation: one from the source, or one made by the
/// compiler (a wildcard for a field, or `n - 1` inside a number pattern `n`).
type Pat<'a> = Cow<'a, Pattern>;

/// The variable a pattern binds, if it's a variable from the source.
fn pattern_var<'a>(pattern: &Pat<'a>) -> Option<&'a ast::Name> {
    match pattern {
        Cow::Borrowed(Pattern::Var(x)) => Some(x),
        _ => None,
    }
}

/// One equation during pattern-match compilation: the patterns still to be
/// matched, and the pattern variables already bound (to de Bruijn levels).
#[derive(Clone)]
struct Row<'a> {
    pats: Vec<Pat<'a>>,
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
    /// The variable at `level` is a `Nat`, compared with numbers in
    /// increasing order (docs/proposals/number-patterns.md).
    NumCase {
        level: usize,
        arms: Vec<(BigUint, Tree<'a>)>,
        default: Box<Tree<'a>>,
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

    /// Elaborates a closed expression, and infers its type with the kernel.
    /// One operation, with its own resource limits.
    pub fn infer_expr(&self, expr: &Expr) -> Result<(Term, Value)> {
        let _op = self.globals.budget.operation(self.limits);
        self.infer_expr_in_operation(expr)
            .map_err(|d| self.locate(d, expr.span()))
    }

    /// Elaborates and evaluates a closed expression: its value and its type,
    /// printed. One operation, with its own resource limits, including
    /// printing the value.
    pub fn eval_expr(&self, expr: &Expr) -> Result<(String, String)> {
        let _op = self.globals.budget.operation(self.limits);
        let run = || -> Result<(String, String)> {
            let (term, ty) = self.infer_expr_in_operation(expr)?;
            let value = eval(&self.globals, &[], &term)?;
            let g = &self.globals;
            let show = |v: &Value| -> std::result::Result<String, stitchwort_core::ResourceError> {
                pretty::term_in_full(g, &[], &stitchwort_core::value::quote(g, 0, v)?)
            };
            Ok((show(&value)?, show(&ty)?))
        };
        run().map_err(|d| self.locate(d, expr.span()))
    }

    /// A diagnostic without a location (running out of resources) is
    /// reported at `span`.
    fn locate(&self, d: Diagnostic, span: Span) -> Diagnostic {
        if d.labels.is_empty() {
            d.with_label(span, "while evaluating this")
        } else {
            d
        }
    }

    fn infer_expr_in_operation(&self, expr: &Expr) -> Result<(Term, Value)> {
        self.clear_metas();
        let (term, ty) = {
            let mut cx = Ctx::new(self, expr.span());
            let (mut term, mut ty) = infer(&mut cx, expr)?;
            // A call gets its trailing implicit and auto arguments too (so
            // `div 7 2` gets its proof); a bare name like `length` keeps its
            // polymorphic type.
            if matches!(expr, Expr::App(..) | Expr::Binary(..)) {
                (term, ty) = check::insert(&mut cx, term, ty)?;
            }
            (term, cx.quote(&ty)?)
        };
        let term = self.finish(&term, 0)?;
        self.finish(&ty, 0)?;
        self.clear_metas();
        kernel::infer_closed(&self.globals, &term, expr.span())
    }

    pub fn eval(&self, term: &Term) -> std::result::Result<Value, stitchwort_core::ResourceError> {
        eval(&self.globals, &[], term)
    }

    /// Prints a closed value, as one operation: a part too large or nested
    /// too deeply to print within its limits is shown as `…`.
    pub fn show(&self, value: &Value) -> String {
        let _op = self.globals.budget.operation(self.limits);
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
        unify::zonk(&self.globals, level, term).map_err(|e| match e {
            unify::ZonkError::Resource(e) => e.into(),
            unify::ZonkError::Unsolved(m) => {
                let span = self.globals.metas.borrow()[m].span;
                Diagnostic::error("E-UNSOLVED", "can't work out an implicit argument")
                    .with_label(span, "the compiler couldn't work out what goes here")
                    .with_note("supply it explicitly with `f [x := …]`, or add a type annotation")
            }
        })
    }

    fn test(&mut self, name: &str, expr: &Expr, span: Span) -> Result<()> {
        self.module.phase = Phase::Body;
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

    /// `ability A params where op : X -> {A params} Y …`, as three generated
    /// declarations (see `effects`): the data type of its operations
    /// (constructors `A.op`), `A.res` giving each operation's result type,
    /// and the eliminator `A.elim` that handlers use.
    fn ability(&mut self, decl: &Decl) -> Result<()> {
        use ast::{Binder, CtorDecl, Expr};
        let Decl::Ability {
            name: ability,
            params,
            ops,
            span,
        } = decl
        else {
            unreachable!()
        };
        self.check_new_name(ability)?;
        let n = |text: String| ast::Name { text, span: *span };
        let var = |text: &str| Expr::Var(n(text.to_string()));
        let apps = |head: Expr, args: Vec<Expr>| {
            args.into_iter()
                .fold(head, |f, a| Expr::App(Box::new(f), Box::new(a)))
        };
        let param_names: Vec<ast::Name> = params.iter().flat_map(|b| b.names.clone()).collect();
        let applied = apps(
            var(&ability.text),
            param_names.iter().map(|p| var(&p.text)).collect(),
        );

        // Each operation is `x : A -> {Ability params} B`.
        let mut sigs = Vec::new();
        for (op, ty) in ops {
            self.check_new_name(op)?;
            let bad = || {
                error(
                    "E-ABILITY",
                    ty.span(),
                    format!(
                        "an operation's type must be `A -> {{{} …}} B`",
                        ability.text
                    ),
                )
            };
            let (x, dom, row, cod) = match ty {
                Expr::Arrow(a, b) => match b.as_ref() {
                    Expr::Effect(row, cod) => (None, a.as_ref(), row, cod.as_ref()),
                    _ => return Err(bad()),
                },
                Expr::Pi {
                    names,
                    implicit: false,
                    dom,
                    cod,
                    ..
                } if names.len() == 1 => match cod.as_ref() {
                    Expr::Effect(row, cod) => {
                        (Some(names[0].clone()), dom.as_ref(), row, cod.as_ref())
                    }
                    _ => return Err(bad()),
                },
                _ => return Err(bad()),
            };
            let only_self = row.tail.is_none()
                && row.abilities.len() == 1
                && matches!(
                    {
                        let mut h = &row.abilities[0];
                        while let Expr::App(f, _) = h {
                            h = f;
                        }
                        h
                    },
                    Expr::Var(v) if v.text == ability.text
                );
            if !only_self {
                return Err(error(
                    "E-ABILITY",
                    row.span,
                    format!(
                        "an operation of `{}` performs just `{}`",
                        ability.text, ability.text
                    ),
                ));
            }
            // Its argument and result can't use the ability itself: that's
            // Landin's knot (`Cell` in DESIGN.md §8).
            for (part, what) in [(dom, "argument"), (cod, "result")] {
                if mentions_ability(part, &ability.text) {
                    return Err(error(
                        "E-ABILITY",
                        part.span(),
                        format!(
                            "an operation's {what} can't perform `{}` itself",
                            ability.text
                        ),
                    )
                    .with_note(
                        "storing or returning a computation that uses the same ability could \
                         loop forever (Landin's knot)",
                    ));
                }
            }
            sigs.push((op.clone(), x, dom.clone(), cod.clone()));
        }
        let ctor_name = |op: &ast::Name| n(format!("{}.{}", ability.text, op.text));
        let x_name = |x: &Option<ast::Name>| x.clone().unwrap_or_else(|| n("x".into()));

        // type A params : Type = | A.op (x : X) …
        let data_decl = Decl::Data {
            name: ability.clone(),
            params: params.clone(),
            sort: None,
            ctors: sigs
                .iter()
                .map(|(op, x, dom, _)| CtorDecl {
                    name: ctor_name(op),
                    fields: vec![Binder {
                        names: vec![x_name(x)],
                        ty: dom.clone(),
                    }],
                })
                .collect(),
            record: false,
            span: *span,
        };
        self.data(&data_decl)?;
        let Some((Global::Data(op_data), _)) = self.names.get(&ability.text).copied() else {
            unreachable!("just declared");
        };

        // A.res : (params) -> A params -> Type
        let res_name = n(format!("{}.res", ability.text));
        let mut res_ty = Expr::Arrow(Box::new(applied.clone()), Box::new(Expr::Type(0, *span)));
        for binder in params.iter().rev() {
            res_ty = Expr::Pi {
                names: binder.names.clone(),
                implicit: false,
                auto: false,
                dom: Box::new(binder.ty.clone()),
                cod: Box::new(res_ty),
                span: *span,
            };
        }
        let res_sig = Decl::Signature {
            name: res_name.clone(),
            ty: res_ty,
            theorem: false,
            export: false,
            span: *span,
        };
        let res_eqs: Vec<Decl> = sigs
            .iter()
            .map(|(op, x, _, cod)| {
                let mut patterns: Vec<Pattern> = param_names
                    .iter()
                    .map(|p| Pattern::Var(p.clone()))
                    .collect();
                patterns.push(Pattern::Ctor(
                    ctor_name(op),
                    vec![Pattern::Var(x_name(x))],
                    *span,
                ));
                Decl::Equation {
                    name: res_name.clone(),
                    patterns,
                    rhs: Some(cod.clone()),
                    span: *span,
                }
            })
            .collect();
        self.definition(&res_sig, &res_eqs)?;
        let Some((Global::Def(res), _)) = self.names.get(&res_name.text).copied() else {
            unreachable!("just defined");
        };

        // A.elim : [params] -> [r : Type] -> ((x : X) -> (Y -> r) -> r) -> … ->
        //   (o : A params) -> (A.res params o -> r) -> r
        let elim_name = n(format!("{}.elim", ability.text));
        let r = || var("%r");
        let clause = |i: usize| format!("%clause{i}");
        let res_of_o = apps(
            var(&res_name.text),
            param_names
                .iter()
                .map(|p| var(&p.text))
                .chain([var("%o")])
                .collect(),
        );
        let mut elim_ty = Expr::Pi {
            names: vec![n("%o".into())],
            implicit: false,
            auto: false,
            dom: Box::new(applied.clone()),
            cod: Box::new(Expr::Arrow(
                Box::new(Expr::Arrow(Box::new(res_of_o), Box::new(r()))),
                Box::new(r()),
            )),
            span: *span,
        };
        for (i, (_, x, dom, cod)) in sigs.iter().enumerate().rev() {
            let k_ty = Expr::Arrow(Box::new(cod.clone()), Box::new(r()));
            let clause_ty = Expr::Pi {
                names: vec![x_name(x)],
                implicit: false,
                auto: false,
                dom: Box::new(dom.clone()),
                cod: Box::new(Expr::Arrow(Box::new(k_ty), Box::new(r()))),
                span: *span,
            };
            elim_ty = Expr::Pi {
                names: vec![n(clause(i))],
                implicit: false,
                auto: false,
                dom: Box::new(clause_ty),
                cod: Box::new(elim_ty),
                span: *span,
            };
        }
        elim_ty = Expr::Pi {
            names: vec![n("%r".into())],
            implicit: true,
            auto: false,
            dom: Box::new(Expr::Type(0, *span)),
            cod: Box::new(elim_ty),
            span: *span,
        };
        for binder in params.iter().rev() {
            elim_ty = Expr::Pi {
                names: binder.names.clone(),
                implicit: true,
                auto: false,
                dom: Box::new(binder.ty.clone()),
                cod: Box::new(elim_ty),
                span: *span,
            };
        }
        let elim_sig = Decl::Signature {
            name: elim_name.clone(),
            ty: elim_ty,
            theorem: false,
            export: false,
            span: *span,
        };
        let elim_eqs: Vec<Decl> = sigs
            .iter()
            .enumerate()
            .map(|(i, (op, x, _, _))| {
                let mut patterns: Vec<Pattern> = (0..sigs.len())
                    .map(|j| Pattern::Var(n(clause(j))))
                    .collect();
                patterns.push(Pattern::Ctor(
                    ctor_name(op),
                    vec![Pattern::Var(x_name(x))],
                    *span,
                ));
                patterns.push(Pattern::Var(n("%k".into())));
                Decl::Equation {
                    name: elim_name.clone(),
                    patterns,
                    rhs: Some(apps(var(&clause(i)), vec![var(&x_name(x).text), var("%k")])),
                    span: *span,
                }
            })
            .collect();
        self.definition(&elim_sig, &elim_eqs)?;
        let Some((Global::Def(elim), _)) = self.names.get(&elim_name.text).copied() else {
            unreachable!("just defined");
        };

        let index = self.abilities.len();
        self.abilities.push(effects::AbilityInfo {
            name: ability.text.clone(),
            op_data,
            res,
            elim,
            ops: sigs.iter().map(|(op, ..)| op.text.clone()).collect(),
            order: (
                self.modules,
                self.module
                    .item
                    .map_or(0, |i| self.module.items[i].position),
            ),
        });
        self.names
            .insert(ability.text.clone(), (Global::Ability(index), ability.span));
        for (i, (op, ..)) in sigs.iter().enumerate() {
            self.names
                .insert(op.text.clone(), (Global::Op(index, i), op.span));
        }
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
        // Claimed for this declaration when the module's names were
        // collected.
        if let Some((Global::Unchecked(item), _)) = self.names.get(&n.text)
            && self.module.in_current(*item)
        {
            return Ok(());
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

    /// A data type on its own (one in a component of its own, or one an
    /// ability generates).
    fn data(&mut self, decl: &Decl) -> Result<()> {
        let item = self.module.item;
        match self.data_group(&[(item, decl)]).into_iter().next() {
            Some((_, d)) => Err(d),
            None => Ok(()),
        }
    }

    /// A group of data types whose constructors may mention each other (or
    /// one data type), each with the module item that declares it: every
    /// header, then every constructor, then the kernel admits them together,
    /// or none of them (docs/proposals/mutual-recursion.md §5.4). Members
    /// must have the same parameters and universe, which the kernel checks
    /// once, for the whole group. The diagnostics, each with the item it's
    /// about.
    fn data_group(
        &mut self,
        members: &[(Option<usize>, &Decl)],
    ) -> Vec<(Option<usize>, Diagnostic)> {
        let mut out = Vec::new();
        let mut headers = Vec::new();
        for &(item, decl) in members {
            if item.is_some() {
                self.module.item = item;
            }
            match self.data_header(decl) {
                Ok(header) => headers.push(header),
                Err(d) => out.push((item, d)),
            }
        }
        if !out.is_empty() {
            return out;
        }
        let ((params, sort), first) = (headers[0].clone(), members[0].1);
        for (&(item, decl), header) in members.iter().zip(&headers).skip(1) {
            if let Err(d) = self.same_header(first, &headers[0], decl, header) {
                out.push((item, d));
            }
        }
        if !out.is_empty() {
            return out;
        }
        let names: Vec<(Name, Span, bool)> = members
            .iter()
            .map(|(_, decl)| match decl {
                Decl::Data {
                    name: n,
                    span,
                    record,
                    ..
                } => (name(n), *span, *record),
                _ => unreachable!(),
            })
            .collect();
        let ids = match kernel::declare_data_group_as(&mut self.globals, params, sort, names) {
            Ok(ids) => ids,
            Err(d) => return vec![(members[0].0, d)],
        };
        // Every member can be mentioned in fields now, as a type. None has
        // constructors until the kernel admits them all.
        for (&(_, decl), d) in members.iter().zip(&ids) {
            if let Decl::Data { name: n, .. } = decl {
                self.names
                    .insert(n.text.clone(), (Global::Data(*d), n.span));
            }
        }
        let mut defined = Vec::new();
        for (&(item, decl), d) in members.iter().zip(&ids) {
            if item.is_some() {
                self.module.item = item;
            }
            match self.data_ctors(decl, *d) {
                Ok(ctors) => defined.push((*d, ctors)),
                Err(d) => out.push((item, d)),
            }
        }
        if !out.is_empty() {
            return out;
        }
        if members[0].0.is_some() {
            self.module.item = members[0].0;
        }
        if let Err(d) = kernel::define_data_group(&mut self.globals, defined) {
            return vec![(members[0].0, d)];
        }
        for (&(item, decl), d) in members.iter().zip(&ids) {
            if let Err(e) = self.after_data(decl, *d) {
                out.push((item, e));
            }
        }
        out
    }

    /// Elaborates a data type's parameters and universe.
    fn data_header(&mut self, decl: &Decl) -> Result<(Vec<(Name, Term)>, Sort)> {
        let Decl::Data {
            name: data_name,
            params,
            sort,
            span,
            ..
        } = decl
        else {
            unreachable!()
        };
        self.check_new_name(data_name)?;
        self.clear_metas();
        self.module.phase = Phase::Header;
        let mut cx = Ctx::new(self, *span);
        let mut checked = Vec::new();
        for binder in params {
            let (ty, _) = check_type(&mut cx, &binder.ty)?;
            for (k, n) in binder.names.iter().enumerate() {
                let ty = self.finish(&ty.shift(&self.globals, k, 0)?, cx.level())?;
                let value = cx.eval(&ty)?;
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
        Ok((checked, sort))
    }

    /// Whether data type `decl` has the same parameters (names and types) and
    /// universe as `first`, which it's defined together with. The kernel
    /// takes one telescope for the whole group, so this is only for a clear
    /// error.
    fn same_header(
        &self,
        first: &Decl,
        (first_params, first_sort): &(Vec<(Name, Term)>, Sort),
        decl: &Decl,
        (params, sort): &(Vec<(Name, Term)>, Sort),
    ) -> Result<()> {
        let (
            Decl::Data {
                name: first_name, ..
            },
            Decl::Data { name: n, .. },
        ) = (first, decl)
        else {
            unreachable!()
        };
        let g = &self.globals;
        let show_params = |params: &[(Name, Term)]| {
            if params.is_empty() {
                return "no parameters".to_string();
            }
            let mut names: Vec<Name> = Vec::new();
            let mut shown = Vec::new();
            for (x, ty) in params {
                shown.push(format!("({x} : {})", pretty::term(g, &names, ty)));
                names.push(x.clone());
            }
            shown.join(" ")
        };
        let mut same = params.len() == first_params.len();
        let mut env = Vec::new();
        for ((x, ty), (y, first_ty)) in params.iter().zip(first_params) {
            if !same {
                break;
            }
            let level = env.len();
            let (a, b) = (eval(g, &env, ty)?, eval(g, &env, first_ty)?);
            same = x == y && stitchwort_core::value::conv(g, level, &a, &b)?;
            env.push(Value::var(level));
        }
        if !same {
            return Err(Diagnostic::error(
                "E-MUTUAL-PARAMETERS",
                format!(
                    "`{}` and `{}` are defined together, so they must have the same parameters",
                    first_name.text, n.text
                ),
            )
            .with_label(n.span, format!("`{}` has {}", n.text, show_params(params)))
            .with_label(
                first_name.span,
                format!("`{}` has {}", first_name.text, show_params(first_params)),
            )
            .with_note(
                "data types that refer to each other share one list of parameters: write the \
                 same parameters, with the same names, for each",
            ));
        }
        if sort != first_sort {
            let show = |s: &Sort| pretty::term(g, &[], &Term::Sort(*s));
            return Err(Diagnostic::error(
                "E-MUTUAL-PARAMETERS",
                format!(
                    "`{}` and `{}` are defined together, so they must be in the same universe",
                    first_name.text, n.text
                ),
            )
            .with_label(n.span, format!("`{}` is in `{}`", n.text, show(sort)))
            .with_label(
                first_name.span,
                format!("`{}` is in `{}`", first_name.text, show(first_sort)),
            ));
        }
        Ok(())
    }

    /// Elaborates the constructors of data type `d`, declared from `decl`.
    fn data_ctors(&mut self, decl: &Decl, d: DataId) -> Result<Vec<kernel::CtorDecl>> {
        let Decl::Data { ctors, span, .. } = decl else {
            unreachable!()
        };
        self.module.phase = Phase::Fields;
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
                let value = cx.eval(ty)?;
                cx.bind(x, value);
            }
            let mut fields = Vec::new();
            for (k, binder) in ctor.fields.iter().enumerate() {
                if let Some(earlier) = ctor.fields[..k]
                    .iter()
                    .flat_map(|b| &b.names)
                    .find(|e| binder.names.iter().any(|n| n.text == e.text))
                {
                    return Err(error(
                        "E-DUPLICATE",
                        binder.names[0].span,
                        format!("there's already a field `{}`", earlier.text),
                    )
                    .with_label(earlier.span, "first declared here"));
                }
                let (ty, _) = check_type(&mut cx, &binder.ty)?;
                for (k, n) in binder.names.iter().enumerate() {
                    let ty = self.finish(&ty.shift(&self.globals, k, 0)?, cx.level())?;
                    let value = cx.eval(&ty)?;
                    fields.push((name(n), ty, binder.ty.span()));
                    cx.bind(&n.text, value);
                }
            }
            core_ctors.push(kernel::CtorDecl {
                name: name(&ctor.name),
                fields,
            });
        }
        Ok(core_ctors)
    }

    /// After a data type is admitted: registering builtins (in the prelude),
    /// and making its constructors' names refer to them.
    fn after_data(&mut self, decl: &Decl, d: DataId) -> Result<()> {
        let Decl::Data {
            name: data_name,
            ctors,
            ..
        } = decl
        else {
            unreachable!()
        };
        for (c, ctor) in ctors.iter().enumerate() {
            self.names
                .insert(ctor.name.text.clone(), (Global::Ctor(d, c), ctor.name.span));
        }
        if self.loading_prelude {
            match data_name.text.as_str() {
                "Nat" => native::register_nat(&mut self.globals, d)?,
                "Bool" => native::register_bool(&mut self.globals, d)?,
                "Decidable" => native::register_decidable(&mut self.globals, d)?,
                // `Char` comes after `List`. If either isn't the declaration
                // the compact representation of text was written for, text
                // literals are constructors instead (and a test fails).
                "Char" => {
                    if let Some((Global::Data(list), _)) = self.names.get("List").copied() {
                        chars::register(&mut self.globals, list, d);
                    }
                }
                _ => {}
            }
        }
        if self.globals.data(d).record {
            self.after_record(d)?;
        }
        Ok(())
    }

    /// A definition on its own (one an ability generates): its signature,
    /// then its body.
    fn definition(&mut self, signature: &Decl, equations: &[Decl]) -> Result<()> {
        let Decl::Signature { name: def_name, .. } = signature else {
            unreachable!()
        };
        let id = self.signature(signature)?;
        // Registered before the body is elaborated, so it can refer to itself.
        // If the body fails, the definition stays declared but failed, so
        // later uses don't cascade into "unknown name" errors.
        self.names
            .insert(def_name.text.clone(), (Global::Def(id), def_name.span));
        self.clear_metas();
        self.module.phase = Phase::Body;
        let body = self.body(id, def_name, equations)?;
        kernel::define_def(&mut self.globals, id, &body)?;
        self.after_definition(signature, id)
    }

    /// A group of definitions that may call each other (or one definition),
    /// given as module items: every signature, then every body, then the
    /// kernel admits them together, or none of them
    /// (docs/proposals/mutual-recursion.md §5.3). The diagnostics, each with
    /// the item it's about.
    fn group(&mut self, members: &[(usize, &Decl, &[Decl])]) -> Vec<(usize, Diagnostic)> {
        let mut out = Vec::new();
        let mut ids = Vec::new();
        for &(item, signature, _) in members {
            self.module.item = Some(item);
            let result = self.signature(signature);
            out.extend(self.warnings.drain(..).map(|w| (item, w)));
            match result {
                Ok(id) => ids.push(id),
                Err(d) => out.push((item, d)),
            }
        }
        if ids.len() < members.len() {
            return out;
        }
        // Every member can be referred to now, by its signature. None has a
        // body until the kernel admits them all, so none unfolds while the
        // others are checked.
        for (&(_, signature, _), id) in members.iter().zip(&ids) {
            if let Decl::Signature { name: n, .. } = signature {
                self.names
                    .insert(n.text.clone(), (Global::Def(*id), n.span));
            }
        }
        let mut bodies = Vec::new();
        for (&(item, signature, equations), id) in members.iter().zip(&ids) {
            let Decl::Signature { name: def_name, .. } = signature else {
                unreachable!()
            };
            self.module.item = Some(item);
            self.module.phase = Phase::Body;
            self.clear_metas();
            match self.body(*id, def_name, equations) {
                Ok(body) => bodies.push((*id, body)),
                Err(d) => out.push((item, d)),
            }
        }
        if bodies.len() < members.len() {
            return out;
        }
        self.module.item = Some(members[0].0);
        if let Err(d) = kernel::define_group(&mut self.globals, &bodies) {
            out.push((members[0].0, d));
            return out;
        }
        for (&(item, signature, _), id) in members.iter().zip(&ids) {
            self.module.item = Some(item);
            if let Err(d) = self.after_definition(signature, *id) {
                out.push((item, d));
            }
        }
        out
    }

    /// Elaborates a definition's signature and declares it to the kernel,
    /// without making its name refer to it.
    fn signature(&mut self, signature: &Decl) -> Result<DefId> {
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
        self.module.phase = Phase::Signature;

        let auto = autobind::auto_bound(self, ty)?;
        // A name that would have been a type variable, but is the name of
        // something in this module.
        let mut notes = Vec::new();
        for used in &auto.shadowing {
            let Some((_, defined)) = self.names.get(&used.text) else {
                continue;
            };
            let note = format!(
                "to make `{0}` a type variable instead, bind it explicitly: start the type with \
                 `[{0} : Type] ->`",
                used.text
            );
            self.warnings.push(
                Diagnostic::warning(
                    "W-MODULE-NAME",
                    format!(
                        "`{}` in this type is the declaration of that name in this module, not a \
                         type variable",
                        used.text
                    ),
                )
                .with_label(used.span, format!("this is the module's `{}`", used.text))
                .with_label(*defined, format!("`{}` is defined here", used.text))
                .with_note(note.clone()),
            );
            notes.push(note);
        }
        let with_notes = |d: Diagnostic| notes.iter().fold(d, |d, n| d.with_note(n.clone()));
        let ty = (|| {
            let mut cx = Ctx::new(self, *span);
            let mut domains = Vec::new();
            for n in &auto.names {
                // The type of an implicitly bound variable is worked out from
                // how it's used (usually `Type`).
                cx.span = n.span;
                let dom = cx.fresh_meta();
                let value = cx.eval(&dom)?;
                domains.push(dom);
                cx.bind(&n.text, value);
            }
            cx.span = *span;
            let (mut term, _) = check_type(&mut cx, ty)?;
            for (n, dom) in auto.names.iter().zip(domains).rev() {
                term = Term::Pi(name(n), Icit::Implicit, Rc::new(dom), Rc::new(term));
            }
            self.finish(&term, 0)
        })()
        .map_err(with_notes)?;
        let id = kernel::declare_def(
            &mut self.globals,
            &name(def_name),
            &ty,
            *theorem,
            *export,
            *span,
        )
        .map_err(with_notes)?;
        if let Some(item) = self.module.item {
            self.module.def_items.insert(id, item);
        }
        Ok(id)
    }

    /// After a definition is admitted: registering natives (in the prelude)
    /// and an export's validators.
    fn after_definition(&mut self, signature: &Decl, id: DefId) -> Result<()> {
        let Decl::Signature {
            name: def_name,
            export,
            ..
        } = signature
        else {
            unreachable!()
        };
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
        let tel = kernel::telescope(&self.globals, &def.ty_value, span)?;
        let mut found = Vec::new();
        for (i, (_, ty, erased)) in tel.params.iter().enumerate() {
            if !erased || kernel::is_type_former(&self.globals, i, ty)? {
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
        // Records crossing the boundary with proof fields need decision
        // procedures for those too (docs/proposals/records.md §11.3).
        let crossing: Vec<Value> = tel
            .params
            .iter()
            .filter(|(_, _, erased)| !erased)
            .map(|(_, ty, _)| ty.clone())
            .chain([tel.result.clone()])
            .collect();
        let mut seen = std::collections::HashSet::new();
        for ty in &crossing {
            self.record_validators(ty, &name, span, &mut seen)?;
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
        let mut column_types = Vec::new();
        let mut ty = g.def(id).ty_value.clone();
        loop {
            match force(g, ty.clone())? {
                // Implicit and auto parameters are in scope by name, wherever
                // they are in the signature.
                Value::Pi(x, icit, dom, cod) if icit.is_implicit() => {
                    let var = Value::var(cx.level());
                    cx.bind(&x, (*dom).clone());
                    lams.push((x, icit));
                    ty = cod.apply(g, var)?;
                }
                Value::Pi(x, Icit::Explicit, dom, cod) if columns.len() < arity => {
                    let param = match &first_patterns[columns.len()] {
                        Pattern::Var(v) => name(v),
                        _ => x,
                    };
                    let var = Value::var(cx.level());
                    columns.push(cx.level());
                    column_types.push(Some((*dom).clone()));
                    cx.bind_hidden(param.clone(), (*dom).clone());
                    lams.push((param, Icit::Explicit));
                    ty = cod.apply(g, var)?;
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
                    // `()` with a right-hand side is the unit pattern; without
                    // one, it's absurd.
                    pats: patterns
                        .iter()
                        .map(|p| match p {
                            Pattern::Absurd(span) if rhs.is_some() => Cow::Owned(Pattern::Ctor(
                                ast::Name {
                                    text: "UnitValue".into(),
                                    span: *span,
                                },
                                Vec::new(),
                                *span,
                            )),
                            p => Cow::Borrowed(p),
                        })
                        .collect(),
                    aliases: Vec::new(),
                    rhs,
                    span,
                })
                .collect();
            self.compile(&rows, cx.level(), &columns, &column_types, span)?
        };
        let mut term = check_tree(&mut cx, &tree, &ty)?;
        for (x, icit) in lams.into_iter().rev() {
            term = Term::Lam(x, icit, Rc::new(term));
        }
        self.finish(&term, 0)
    }

    /// Compiles equations into a case tree. `columns[j]` is the de Bruijn level
    /// of the value each row's `j`th pattern matches, and `types[j]` its type
    /// if known (a record pattern needs it); `depth` is the number of
    /// variables in scope.
    fn compile<'a>(
        &self,
        rows: &[Row<'a>],
        depth: usize,
        columns: &[usize],
        types: &[Option<Value>],
        span: Span,
    ) -> Result<Tree<'a>> {
        self.globals.budget.nesting(check::PASS)?;
        let first = &rows[0];
        if let Some(j) = first
            .pats
            .iter()
            .position(|p| matches!(**p, Pattern::Absurd(_)))
        {
            return Ok(Tree::Absurd {
                level: columns[j],
                span: first.pats[j].span(),
            });
        }
        let mut split = None;
        for (j, pattern) in first.pats.iter().enumerate() {
            // A column of numbers (with variables and `_`) is compared with
            // numbers. One with a `Zero` or `Succ` pattern is split into
            // those constructors, and numbers in it count down as it's split.
            if matches!(**pattern, Pattern::Num(..))
                && !self.numbers_as_succ
                && !rows.iter().any(|r| matches!(*r.pats[j], Pattern::Ctor(..)))
            {
                return self.compile_numbers(rows, depth, columns, types, j, span);
            }
            if let Some(ctor) = self.pattern_ctor(pattern, types[j].as_ref())? {
                split = Some((j, ctor.data));
                break;
            }
        }
        let Some((j, d)) = split else {
            // The first row matches whatever is left: it's the result.
            let mut aliases = first.aliases.clone();
            for (pattern, level) in first.pats.iter().zip(columns) {
                if let Some(x) = pattern_var(pattern) {
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
        let mut branches = Vec::new();
        for (c, ctor) in data.ctors.iter().enumerate() {
            let k = ctor.fields.len();
            // In this branch, column `j` is replaced by the constructor's
            // fields, which are bound at levels `depth..depth + k`.
            let branch_columns: Vec<usize> = columns[..j]
                .iter()
                .copied()
                .chain(depth..depth + k)
                .chain(columns[j + 1..].iter().copied())
                .collect();
            let branch_types: Vec<Option<Value>> = types[..j]
                .iter()
                .cloned()
                .chain(self.field_types(types[j].as_ref(), d, c, depth)?)
                .chain(types[j + 1..].iter().cloned())
                .collect();
            let mut names: Vec<Option<Name>> = vec![None; k];
            let mut branch_rows = Vec::new();
            for row in rows {
                let pattern = &row.pats[j];
                let mut aliases = row.aliases.clone();
                let fields: Vec<Pat> = match self.pattern_ctor(pattern, types[j].as_ref())? {
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
                            if let Some(x) = pattern_var(arg) {
                                names[f].get_or_insert_with(|| name(x));
                            }
                        }
                        args
                    }
                    None => {
                        if let Some(x) = pattern_var(pattern) {
                            aliases.push((&x.text, level));
                        }
                        let wildcard = Pattern::Wildcard(pattern.span());
                        vec![Cow::Owned(wildcard); k]
                    }
                };
                let pats = row.pats[..j]
                    .iter()
                    .cloned()
                    .chain(fields)
                    .chain(row.pats[j + 1..].iter().cloned())
                    .collect();
                branch_rows.push(Row {
                    pats,
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
            let body =
                self.compile(&branch_rows, depth + k, &branch_columns, &branch_types, span)?;
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

    /// Compiles a split on column `j`, which holds numbers, variables and
    /// `_` (and maybe `()`), into a number case: one arm per number, keeping the rows that have
    /// that number or a variable there, in order, and a default keeping the
    /// rows with a variable. The same number in several rows is one arm.
    #[allow(clippy::too_many_arguments)]
    fn compile_numbers<'a>(
        &self,
        rows: &[Row<'a>],
        depth: usize,
        columns: &[usize],
        types: &[Option<Value>],
        j: usize,
        span: Span,
    ) -> Result<Tree<'a>> {
        // The rows with each number there, and the rest, by index.
        let mut by_key: BTreeMap<&BigUint, Vec<usize>> = BTreeMap::new();
        let mut others = Vec::new();
        for (i, row) in rows.iter().enumerate() {
            match &*row.pats[j] {
                Pattern::Num(n, _) => by_key.entry(n).or_default().push(i),
                _ => others.push(i),
            }
        }
        if others.is_empty() {
            let mut shown: Vec<String> = by_key.keys().take(5).map(|k| k.to_string()).collect();
            let listed = match (by_key.len(), shown.pop()) {
                (n, Some(last)) if n <= 5 && !shown.is_empty() => {
                    format!("{} and {last}", shown.join(", "))
                }
                (n, Some(last)) if n <= 5 => last,
                (_, last) => format!("{}, {}, …", shown.join(", "), last.unwrap_or_default()),
            };
            return Err(error(
                "E-NONEXHAUSTIVE",
                span,
                format!("missing case: no equation matches numbers other than {listed}"),
            )
            .with_note("add an equation with a variable or `_` in that position"));
        }
        let mut arms = Vec::new();
        for (key, matching) in by_key {
            // In the order of the source.
            let mut indices: Vec<usize> =
                matching.into_iter().chain(others.iter().copied()).collect();
            indices.sort_unstable();
            let arm_rows: Vec<Row> = indices
                .into_iter()
                .map(|i| {
                    let mut row = rows[i].clone();
                    if let Pattern::Num(_, s) = &*row.pats[j] {
                        row.pats[j] = Cow::Owned(Pattern::Wildcard(*s));
                    }
                    row
                })
                .collect();
            let tree = self.compile(&arm_rows, depth, columns, types, span)?;
            arms.push((key.clone(), tree));
        }
        let default_rows: Vec<Row> = others.iter().map(|&i| rows[i].clone()).collect();
        let default = self.compile(&default_rows, depth, columns, types, span)?;
        Ok(Tree::NumCase {
            level: columns[j],
            arms,
            default: Box::new(default),
            span,
        })
    }

    /// The types of the fields of constructor `c` of `d`, bound at levels
    /// from `depth`, when the matched value's type `ty` is known.
    fn field_types(
        &self,
        ty: Option<&Value>,
        d: DataId,
        c: usize,
        depth: usize,
    ) -> Result<Vec<Option<Value>>> {
        let g = &self.globals;
        let fields = &g.data(d).ctors[c].fields;
        let params = match ty.map(|t| force(g, t.clone())).transpose()? {
            Some(Value::Data(d2, params)) if d2 == d => params,
            _ => return Ok(vec![None; fields.len()]),
        };
        let mut env = params;
        let mut out = Vec::new();
        for (f, (_, field_ty)) in fields.iter().enumerate() {
            out.push(Some(eval(g, &env, field_ty)?));
            env.push(Value::var(depth + f));
        }
        Ok(out)
    }

    /// The constructor `pattern` matches, if any, and its argument patterns.
    /// A number `n` is `Succ` of `n - 1`; a record pattern is resolved by
    /// `ty`, the type of what it matches.
    fn pattern_ctor<'a>(
        &self,
        pattern: &Pat<'a>,
        ty: Option<&Value>,
    ) -> Result<Option<CtorPattern<'a>>> {
        match &**pattern {
            Pattern::Var(_) | Pattern::Wildcard(_) | Pattern::Absurd(_) => Ok(None),
            Pattern::Record { fields, rest, span } => Ok(Some(match pattern {
                Cow::Borrowed(Pattern::Record { fields, .. }) => {
                    self.record_pattern(fields, *rest, *span, ty)?
                }
                _ => {
                    let found = self.record_pattern(fields, *rest, *span, ty)?;
                    CtorPattern {
                        args: found
                            .args
                            .into_iter()
                            .map(|a| Cow::Owned(a.into_owned()))
                            .collect(),
                        ..found
                    }
                }
            })),
            Pattern::Num(n, span) => {
                let (ctor, args) = if n.bits() == 0 {
                    ("Zero", Vec::new())
                } else {
                    let pred = Pattern::Num(n - 1u32, *span);
                    ("Succ", vec![Cow::Owned(pred)])
                };
                let (data, ctor) = self.ctor_named(ctor, *span)?;
                Ok(Some(CtorPattern {
                    data,
                    ctor,
                    args,
                    span: *span,
                }))
            }
            Pattern::Ctor(n, args, span) => {
                let (data, ctor) = self.ctor_named(&n.text, n.span)?;
                let args = match pattern {
                    Cow::Borrowed(Pattern::Ctor(_, args, _)) => {
                        args.iter().map(Cow::Borrowed).collect()
                    }
                    _ => args.iter().cloned().map(Cow::Owned).collect(),
                };
                Ok(Some(CtorPattern {
                    data,
                    ctor,
                    args,
                    span: *span,
                }))
            }
        }
    }

    fn ctor_named(&self, ctor: &str, span: Span) -> Result<(DataId, usize)> {
        let used = || ast::Name {
            text: ctor.to_string(),
            span,
        };
        match self.names.get(ctor) {
            Some((Global::Ctor(d, c), _)) => Ok((*d, *c)),
            Some((Global::Unchecked(item), _)) => Err(self.unchecked(&used(), *item)),
            Some((Global::Failed, _)) => Err(module::failed_name(&used())),
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
    cx.g().budget.nesting(check::PASS)?;
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
        Tree::Absurd { level, span } => match force(cx.g(), cx.types[*level].clone())? {
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
            let params = match force(g, cx.types[*x].clone())? {
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
            let goal_term = cx.quote(goal)?;
            let mut out = Vec::new();
            for (c, ((names, subtree), ctor)) in branches.iter().zip(&data.ctors).enumerate() {
                let mark = cx.mark();
                let base = cx.level();
                let fields: Vec<Value> = (0..ctor.fields.len())
                    .map(|i| Value::var(base + i))
                    .collect();
                // Inside the branch, the matched variable *is* the constructor
                // value, so it's substituted into the goal and the whole
                // context (as the kernel does).
                let value = Value::Ctor(*d, c, fields.clone().into());
                let level = cx.level();
                let mut env = kernel::substitute(g, level, *x, &value, &cx.env)?;
                env[*x] = value.clone();
                let refined = kernel::substitute(g, level, *x, &value, &cx.types)?;
                let branch_goal =
                    kernel::substitute(g, level, *x, &value, &[eval(g, &cx.env, &goal_term)?])?
                        .pop()
                        .expect("one value in, one out");
                let saved_env = std::mem::replace(&mut cx.env, env);
                let saved_types = std::mem::replace(&mut cx.types, refined);
                let mut field_env = params.clone();
                for ((_, field_ty), (name, field)) in
                    ctor.fields.iter().zip(names.iter().zip(&fields))
                {
                    let ty = eval(g, &field_env, field_ty)?;
                    field_env.push(field.clone());
                    cx.bind_hidden(name.clone(), ty);
                }
                let result = check_tree(cx, subtree, &branch_goal);
                cx.reset(mark);
                cx.env = saved_env;
                cx.types = saved_types;
                out.push(Branch {
                    names: names.clone(),
                    body: Rc::new(result?),
                });
            }
            Ok(Term::Loc(
                *span,
                Rc::new(Term::Case(cx.level() - 1 - x, *d, out.into())),
            ))
        }
        Tree::NumCase {
            level: x,
            arms,
            default,
            span,
        } => {
            let g = cx.g();
            let nat = g.builtins.nat;
            match force(g, cx.types[*x].clone())? {
                Value::Data(d, params) if Some(d) == nat && params.is_empty() => {}
                other => {
                    return Err(error(
                        "E-TYPE-MISMATCH",
                        *span,
                        format!(
                            "these patterns match a `Nat`, but the argument has type `{}`",
                            cx.show(&other)
                        ),
                    ));
                }
            }
            let goal_term = cx.quote(goal)?;
            let mut out = Vec::new();
            for (key, subtree) in arms {
                // In this arm, the matched variable *is* the number, so it's
                // substituted into the goal and the whole context (as the
                // kernel does).
                let value = Value::Nat(Rc::new(key.clone()));
                let level = cx.level();
                let mut env = kernel::substitute(g, level, *x, &value, &cx.env)?;
                env[*x] = value.clone();
                let refined = kernel::substitute(g, level, *x, &value, &cx.types)?;
                let arm_goal =
                    kernel::substitute(g, level, *x, &value, &[eval(g, &cx.env, &goal_term)?])?
                        .pop()
                        .expect("one value in, one out");
                let saved_env = std::mem::replace(&mut cx.env, env);
                let saved_types = std::mem::replace(&mut cx.types, refined);
                let result = check_tree(cx, subtree, &arm_goal);
                cx.env = saved_env;
                cx.types = saved_types;
                out.push(NumArm {
                    value: Rc::new(key.clone()),
                    body: Rc::new(result?),
                });
            }
            // The default knows nothing new about the variable. If its type
            // mentions it, the programmer may have expected otherwise.
            let default = check_tree(cx, default, goal).map_err(|d| {
                let ix = cx.level() - 1 - x;
                let mentioned = |v: &Value| cx.quote(v).is_ok_and(|t| t.mentions(ix));
                let depends = mentioned(goal) || cx.types[*x + 1..].iter().any(mentioned);
                if depends && ["E-TYPE-MISMATCH", "E-NOT-EMPTY", "E-REFL"].contains(&d.code) {
                    let n = cx.show(&Value::var(*x));
                    d.with_note(format!(
                        "number patterns only test values: an equation with a variable or `_` \
                         where the others have numbers knows nothing about `{n}`, not even that \
                         it's a different number. To use the shape of `{n}`, match on `Zero` and \
                         `Succ` instead"
                    ))
                } else {
                    d
                }
            })?;
            Ok(Term::Loc(
                *span,
                Rc::new(Term::NumCase(
                    cx.level() - 1 - x,
                    out.into(),
                    Rc::new(default),
                )),
            ))
        }
    }
}

/// Whether a row in `expr` mentions ability `name`. Uses a work list: the
/// expression can nest more deeply than recursion could follow.
fn mentions_ability(expr: &ast::Expr, name: &str) -> bool {
    use ast::Expr;
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr {
            Expr::Effect(row, ty) => {
                let mentioned = row.abilities.iter().any(|a| {
                    let mut h = a;
                    while let Expr::App(f, _) = h {
                        h = f;
                    }
                    matches!(h, Expr::Var(v) if v.text == name)
                });
                if mentioned {
                    return true;
                }
                pending.push(ty);
            }
            Expr::App(a, b) | Expr::Arrow(a, b) | Expr::Binary(_, a, b) | Expr::Seq(a, b) => {
                pending.extend([&**a, &**b]);
            }
            Expr::Pi { dom, cod, .. } => pending.extend([&**dom, &**cod]),
            Expr::Lam(_, b, _) | Expr::Ann(b, _, _) | Expr::NamedArg(_, b, _) => pending.push(b),
            Expr::List(items, _) => pending.extend(items),
            Expr::Record { base, fields, .. } => {
                pending.extend(base.as_deref());
                pending.extend(fields.iter().map(|(_, e)| e));
            }
            Expr::Field(e, _) => pending.push(e),
            _ => {}
        }
    }
    false
}
