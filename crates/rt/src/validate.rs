//! A check that a lowered program is well formed: every slot read is bound
//! in scope and inside its frame, captures and calls have the right number
//! of values, constructors and matches fit their types. Lowering should
//! never make one that isn't; tests run this on everything they lower.

use crate::ir::{Body, Expr, GlobalKind, MatchKind, Program};

impl Program {
    /// Whether the program is well formed, and if not, what's wrong first.
    pub fn validate(&self) -> Result<(), String> {
        for global in &self.globals {
            let check = |body: &Body, params: u32| {
                Checker::new(self, body, params, None)
                    .expr(&body.expr)
                    .map_err(|e| format!("{}: {e}", global.name))
            };
            match &global.kind {
                GlobalKind::Function { params, body } => check(body, *params)?,
                GlobalKind::Constant { body } => check(body, 0)?,
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

struct Checker<'p> {
    program: &'p Program,
    /// Which slots are bound now.
    bound: Vec<bool>,
    /// How many values the closure captured, in a lambda's body.
    captures: Option<u32>,
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
        }
    }

    /// Binds `slot`, which mustn't hold a variable that's still in scope.
    fn bind(&mut self, slot: u32) -> Result<bool, String> {
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
        let globals = &self.program.globals;
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
                globals
                    .get(g.0 as usize)
                    .ok_or_else(|| format!("no global {}", g.0))?;
            }
            Expr::Erased | Expr::Lit(_) | Expr::DoneK | Expr::Unreachable => {}
            Expr::Call(g, args) => {
                let global = globals
                    .get(g.0 as usize)
                    .ok_or_else(|| format!("no global {}", g.0))?;
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
                let global = globals
                    .get(g.0 as usize)
                    .ok_or_else(|| format!("no global {}", g.0))?;
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
