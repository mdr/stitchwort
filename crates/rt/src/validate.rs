//! A check that a lowered program is well formed: every slot read is bound
//! in scope and inside its frame, captures and calls have the right number
//! of values, constructors and matches fit their types. Lowering should
//! never make one that isn't; tests run this on everything they lower.
//!
//! The copies that take a reuse token ([`crate::reuse`]) are checked too:
//! each is a function with one parameter more than its original, which lists
//! it; its token's slot, its last parameter, is never read or bound; and no
//! expression names a copy (it's called only by the bytecode, which passes
//! the token).

use crate::ir::{Body, Expr, GlobalId, GlobalKind, MatchKind, Program, Reuse};

impl Program {
    /// Whether the program is well formed, and if not, what's wrong first.
    pub fn validate(&self) -> Result<(), String> {
        for (g, global) in self.globals.iter().enumerate() {
            let check = |body: &Body, params: u32, token: bool| {
                let mut checker = Checker::new(self, body, params, None);
                if token {
                    checker.forbid(params - 1);
                }
                checker
                    .expr(&body.expr)
                    .map_err(|e| format!("{}: {e}", global.name))
            };
            self.check_reuse(g)
                .map_err(|e| format!("{}: {e}", global.name))?;
            let token = matches!(global.reuse, Reuse::Copy { .. });
            match &global.kind {
                GlobalKind::Function { params, body } => check(body, *params, token)?,
                GlobalKind::Constant { body } => check(body, 0, false)?,
                GlobalKind::Native(_) => {}
            }
        }
        for (i, lambda) in self.lambdas.iter().enumerate() {
            Checker::new(self, &lambda.body, lambda.params, Some(lambda.captures))
                .expr(&lambda.body.expr)
                .map_err(|e| format!("λ{i}: {e}"))?;
        }
        Checker::new(self, &self.entry, 0, None)
            .expr(&self.entry.expr)
            .map_err(|e| format!("entry: {e}"))
    }
}

impl Program {
    /// Global `g`'s copies, or what it's a copy of, agree with each other.
    fn check_reuse(&self, g: usize) -> Result<(), String> {
        let global = &self.globals[g];
        let me = GlobalId(u32::try_from(g).map_err(|_| "too many globals")?);
        let params = |id: GlobalId| match self.globals.get(id.0 as usize).map(|g| &g.kind) {
            Some(GlobalKind::Function { params, .. }) => Ok(*params),
            _ => Err(format!("global {} isn't a function", id.0)),
        };
        match &global.reuse {
            Reuse::None => Ok(()),
            Reuse::Copies(copies) => {
                let own = params(me)?;
                let mut last = 0;
                for &(size, copy) in copies {
                    if size <= last {
                        return Err("its copies aren't by increasing size".into());
                    }
                    last = size;
                    let ok = self
                        .globals
                        .get(copy.0 as usize)
                        .is_some_and(|c| c.reuse == Reuse::Copy { of: me, size });
                    if !ok || params(copy)? != own + 1 {
                        return Err(format!("global {} isn't its copy of size {size}", copy.0));
                    }
                }
                Ok(())
            }
            Reuse::Copy { of, size } => {
                let listed = self.globals.get(of.0 as usize).is_some_and(
                    |o| matches!(&o.reuse, Reuse::Copies(c) if c.contains(&(*size, me))),
                );
                if !listed || *size == 0 || params(me)? != params(*of)? + 1 {
                    return Err(format!("isn't a copy of global {} of size {size}", of.0));
                }
                Ok(())
            }
        }
    }
}

struct Checker<'p> {
    program: &'p Program,
    /// Which slots are bound now.
    bound: Vec<bool>,
    /// How many values the closure captured, in a lambda's body.
    captures: Option<u32>,
    /// A copy's reuse token: the slot the IR never reads or binds.
    token: Option<u32>,
}

impl<'p> Checker<'p> {
    fn new(program: &'p Program, body: &Body, params: u32, captures: Option<u32>) -> Self {
        let mut bound = vec![false; body.frame as usize];
        for slot in bound.iter_mut().take(params as usize) {
            *slot = true;
        }
        Checker {
            program,
            bound,
            captures,
            token: None,
        }
    }

    /// Makes `slot` the token's: neither read nor bound by the body.
    fn forbid(&mut self, slot: u32) {
        if let Some(b) = self.bound.get_mut(slot as usize) {
            *b = false;
        }
        self.token = Some(slot);
    }

    /// Global `g`, which no expression may name if it's a copy.
    fn global(&self, g: GlobalId) -> Result<&'p crate::ir::Global, String> {
        let global = self
            .program
            .globals
            .get(g.0 as usize)
            .ok_or_else(|| format!("no global {}", g.0))?;
        if let Reuse::Copy { .. } = global.reuse {
            return Err(format!("{} is named, which is a copy", global.name));
        }
        Ok(global)
    }

    /// Binds `slot`, which mustn't hold a variable that's still in scope.
    fn bind(&mut self, slot: u32) -> Result<bool, String> {
        if self.token == Some(slot) {
            return Err(format!("v{slot}, the reuse token's slot, is bound"));
        }
        let Some(b) = self.bound.get_mut(slot as usize) else {
            return Err(format!("v{slot} is outside the frame"));
        };
        if std::mem::replace(b, true) {
            return Err(format!("v{slot} is bound again while it's in scope"));
        }
        Ok(false)
    }

    fn exprs(&mut self, exprs: &[Expr]) -> Result<(), String> {
        exprs.iter().try_for_each(|e| self.expr(e))
    }

    fn expr(&mut self, expr: &Expr) -> Result<(), String> {
        match expr {
            Expr::Local(slot) => {
                if !self.bound.get(*slot as usize).copied().unwrap_or(false) {
                    return Err(format!("v{slot} is read where it isn't bound"));
                }
            }
            Expr::Captured(i) => match self.captures {
                Some(n) if *i < n => {}
                _ => return Err(format!("c{i} isn't captured")),
            },
            Expr::Global(g) => {
                self.global(*g)?;
            }
            Expr::Erased | Expr::Lit(_) | Expr::DoneK | Expr::Unreachable => {}
            Expr::Call(g, args) => {
                let global = self.global(*g)?;
                match &global.kind {
                    GlobalKind::Function { params, .. } if *params as usize == args.len() => {}
                    _ => {
                        return Err(format!(
                            "{} called with {} arguments",
                            global.name,
                            args.len()
                        ));
                    }
                }
                self.exprs(args)?;
            }
            Expr::Prim(op, args) => {
                if op.arity() as usize != args.len() {
                    return Err(format!("%{} given {} arguments", op.name(), args.len()));
                }
                self.exprs(args)?;
            }
            Expr::PartialApp(g, args) => {
                let global = self.global(*g)?;
                if args.is_empty() || args.len() >= global.kind.params() as usize {
                    return Err(format!(
                        "{} partially applied to {} arguments",
                        global.name,
                        args.len()
                    ));
                }
                self.exprs(args)?;
            }
            Expr::Apply(f, args) => {
                if args.is_empty() {
                    return Err("an application without arguments".into());
                }
                self.expr(f)?;
                self.exprs(args)?;
            }
            Expr::Closure(id, captures) => {
                let lambda = self
                    .program
                    .lambdas
                    .get(id.0 as usize)
                    .ok_or_else(|| format!("no λ{}", id.0))?;
                if lambda.captures as usize != captures.len() {
                    return Err(format!("λ{} given {} captures", id.0, captures.len()));
                }
                self.exprs(captures)?;
            }
            Expr::Ctor(t, c, fields) => {
                let info = &self.program.types[t.0 as usize];
                let ctor = info
                    .ctors
                    .get(*c as usize)
                    .ok_or_else(|| format!("{} has no constructor {c}", info.name))?;
                if ctor.fields.len() != fields.len() {
                    return Err(format!("{} given {} fields", ctor.name, fields.len()));
                }
                self.exprs(fields)?;
            }
            Expr::Let(slot, value, body) => {
                self.expr(value)?;
                let was = self.bind(*slot)?;
                self.expr(body)?;
                self.bound[*slot as usize] = was;
            }
            Expr::Match(scrutinee, kind, arms) => {
                self.expr(scrutinee)?;
                let fields: Vec<usize> = match kind {
                    MatchKind::Data(t) => self.program.types[t.0 as usize]
                        .ctors
                        .iter()
                        .map(|c| c.fields.len())
                        .collect(),
                    MatchKind::Nat => vec![0, 1],
                    MatchKind::Int => vec![1, 1],
                    MatchKind::Text => vec![1],
                };
                if arms.len() != fields.len() {
                    return Err(format!("a match with {} arms", arms.len()));
                }
                for (c, arm) in arms.iter().enumerate() {
                    if arm.ctor as usize != c {
                        return Err(format!("arm {c} is for constructor {}", arm.ctor));
                    }
                    let mut saved = Vec::new();
                    for (field, slot) in &arm.fields {
                        if *field as usize >= fields[c] {
                            return Err(format!("arm {c} binds field {field}"));
                        }
                        saved.push((*slot, self.bind(*slot)?));
                    }
                    self.expr(&arm.body)?;
                    for (slot, was) in saved.into_iter().rev() {
                        self.bound[slot as usize] = was;
                    }
                }
            }
            Expr::NumSwitch(scrutinee, arms, default) => {
                self.expr(scrutinee)?;
                for (_, body) in arms {
                    self.expr(body)?;
                }
                self.expr(default)?;
            }
            Expr::If(cond, then, otherwise) => {
                self.expr(cond)?;
                self.expr(then)?;
                self.expr(otherwise)?;
            }
        }
        Ok(())
    }
}
