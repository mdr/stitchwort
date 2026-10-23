//! A readable listing of a lowered program, for tests and debugging.
//!
//! ```text
//! fn Std.List.map(v0, v1) {4 slots} =
//!   match v1: List {
//!     Nil => Nil
//!     Cons(head: v2, tail: v3) => Cons(apply v0(v2), Std.List.map(v0, v3))
//!   }
//! ```
//!
//! `vN` is slot `N` of the current frame and `cN` the `N`th captured value.
//! `Name(args)` is a saturated call, `pap Name(args)` a partial
//! application, `apply f(args)` a call of a function value and `%op(args)`
//! a native operation. A lambda is written where its closure is made:
//! `λ3[c0 = v1](v2) =>` captures `v1` as `c0` and takes `v2`.

use std::fmt::{self, Write};

use crate::ir::{Body, Expr, GlobalKind, Lit, MatchKind, Program};

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = String::new();
        for global in &self.globals {
            match &global.kind {
                GlobalKind::Function { params, body } => {
                    let params: Vec<String> = (0..*params).map(|i| format!("v{i}")).collect();
                    let _ = write!(
                        out,
                        "fn {}({}) {} =",
                        global.name,
                        params.join(", "),
                        slots(body)
                    );
                    self.body(&mut out, body);
                }
                GlobalKind::Constant { body } => {
                    let _ = write!(out, "const {} {} =", global.name, slots(body));
                    self.body(&mut out, body);
                }
                GlobalKind::Native(op) => {
                    let _ = write!(
                        out,
                        "native {} = %{}/{}",
                        global.name,
                        op.name(),
                        op.arity()
                    );
                }
            }
            out.push('\n');
        }
        let _ = write!(out, "entry {} =", slots(&self.entry));
        self.body(&mut out, &self.entry);
        out.push('\n');
        f.write_str(&out)
    }
}

thread_local! {
    /// The lambdas whose bodies are being written.
    static PRINTING: std::cell::RefCell<Vec<u32>> = const { std::cell::RefCell::new(Vec::new()) };
}

fn slots(body: &Body) -> String {
    format!("{{{} slots}}", body.frame)
}

fn pad(out: &mut String, indent: usize) {
    out.push('\n');
    for _ in 0..indent {
        out.push_str("  ");
    }
}

/// Whether an expression is written over several lines.
fn compound(expr: &Expr) -> bool {
    match expr {
        Expr::Let(..)
        | Expr::Match(..)
        | Expr::NumSwitch(..)
        | Expr::If(..)
        | Expr::Closure(..) => true,
        Expr::Call(_, args)
        | Expr::Prim(_, args)
        | Expr::PartialApp(_, args)
        | Expr::Ctor(_, _, args) => args.iter().any(compound),
        Expr::Apply(f, args) => compound(f) || args.iter().any(compound),
        Expr::Local(_)
        | Expr::Captured(_)
        | Expr::Global(_)
        | Expr::Erased
        | Expr::Lit(_)
        | Expr::DoneK
        | Expr::Unreachable => false,
    }
}

impl Program {
    /// A body after `=`: on the same line if it's short, otherwise
    /// indented on the next.
    fn body(&self, out: &mut String, body: &Body) {
        if compound(&body.expr) {
            pad(out, 1);
            self.expr(out, &body.expr, 1);
        } else {
            out.push(' ');
            self.expr(out, &body.expr, 1);
        }
    }

    /// Writes `expr`, whose first line starts where `out` is; later lines
    /// are indented `indent` levels.
    fn expr(&self, out: &mut String, expr: &Expr, indent: usize) {
        match expr {
            Expr::Local(slot) => {
                let _ = write!(out, "v{slot}");
            }
            Expr::Captured(i) => {
                let _ = write!(out, "c{i}");
            }
            Expr::Global(g) => out.push_str(&self.globals[g.0 as usize].name),
            Expr::Erased => out.push_str("erased"),
            Expr::DoneK => out.push_str("done-k"),
            Expr::Unreachable => out.push_str("unreachable"),
            Expr::Lit(lit) => match lit {
                Lit::Nat(n) => {
                    let _ = write!(out, "{n}");
                }
                Lit::Int(n) => {
                    let _ = write!(out, "int({n})");
                }
                Lit::Text(t) => {
                    let _ = write!(out, "{:?}", &**t);
                }
                Lit::Chars(t) => {
                    let _ = write!(out, "chars{:?}", &**t);
                }
                Lit::Float(bits) => {
                    out.push_str(&stitchwort_core::float::source(*bits));
                }
            },
            Expr::Call(g, args) => {
                out.push_str(&self.globals[g.0 as usize].name);
                self.args(out, args, indent);
            }
            Expr::Prim(op, args) => {
                let _ = write!(out, "%{}", op.name());
                self.args(out, args, indent);
            }
            Expr::PartialApp(g, args) => {
                let _ = write!(out, "pap {}", self.globals[g.0 as usize].name);
                self.args(out, args, indent);
            }
            Expr::Apply(f, args) => {
                out.push_str("apply ");
                self.operand(out, f, indent);
                self.args(out, args, indent);
            }
            Expr::Ctor(t, c, args) => {
                let info = &self.types[t.0 as usize];
                out.push_str(&info.ctors[*c as usize].name);
                if !args.is_empty() {
                    self.args(out, args, indent);
                }
            }
            Expr::Closure(id, captures) => {
                let lambda = &self.lambdas[id.0 as usize];
                let _ = write!(out, "λ{}", id.0);
                if !captures.is_empty() {
                    out.push('[');
                    for (i, c) in captures.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        let _ = write!(out, "c{i} = ");
                        self.operand(out, c, indent);
                    }
                    out.push(']');
                }
                // After inlining, a lambda can make a closure of itself:
                // its body is written once, where it's outermost.
                let inside = PRINTING.with(|p| p.borrow().contains(&id.0));
                if inside {
                    out.push_str(" (recursive)");
                    return;
                }
                let params: Vec<String> = (0..lambda.params).map(|i| format!("v{i}")).collect();
                let _ = write!(out, "({}) {} =>", params.join(", "), slots(&lambda.body));
                pad(out, indent + 1);
                PRINTING.with(|p| p.borrow_mut().push(id.0));
                self.expr(out, &lambda.body.expr, indent + 1);
                PRINTING.with(|p| p.borrow_mut().pop());
            }
            Expr::Let(slot, value, body) => {
                let _ = write!(out, "let v{slot} = ");
                self.operand(out, value, indent);
                pad(out, indent);
                self.expr(out, body, indent);
            }
            Expr::If(cond, then, otherwise) => {
                out.push_str("if ");
                self.operand(out, cond, indent);
                out.push_str(" then");
                pad(out, indent + 1);
                self.expr(out, then, indent + 1);
                pad(out, indent);
                out.push_str("else");
                pad(out, indent + 1);
                self.expr(out, otherwise, indent + 1);
            }
            Expr::Match(scrutinee, kind, arms) => {
                out.push_str("match ");
                self.operand(out, scrutinee, indent);
                let ctor_name = |c: u32| -> String {
                    match kind {
                        MatchKind::Data(t) => {
                            self.types[t.0 as usize].ctors[c as usize].name.to_string()
                        }
                        MatchKind::Nat => ["Zero", "Succ"][c as usize].into(),
                        MatchKind::Int => ["OfNat", "NegSucc"][c as usize].into(),
                        MatchKind::Text => "MkText".into(),
                    }
                };
                let field_name = |c: u32, i: u32| -> String {
                    match kind {
                        MatchKind::Data(t) => self.types[t.0 as usize].ctors[c as usize].fields
                            [i as usize]
                            .to_string(),
                        MatchKind::Nat => "pred".into(),
                        MatchKind::Int => "n".into(),
                        MatchKind::Text => "chars".into(),
                    }
                };
                match kind {
                    MatchKind::Data(t) => {
                        let info = &self.types[t.0 as usize];
                        let _ = write!(
                            out,
                            ": {}{} {{",
                            info.name,
                            if info.record { " (record)" } else { "" }
                        );
                    }
                    MatchKind::Nat => out.push_str(": Nat {"),
                    MatchKind::Int => out.push_str(": Int {"),
                    MatchKind::Text => out.push_str(": Text {"),
                }
                for arm in arms {
                    pad(out, indent + 1);
                    out.push_str(&ctor_name(arm.ctor));
                    if !arm.fields.is_empty() {
                        let fields: Vec<String> = arm
                            .fields
                            .iter()
                            .map(|(i, slot)| format!("{}: v{slot}", field_name(arm.ctor, *i)))
                            .collect();
                        let _ = write!(out, "({})", fields.join(", "));
                    }
                    self.arm(out, &arm.body, indent + 1);
                }
                pad(out, indent);
                out.push('}');
            }
            Expr::NumSwitch(scrutinee, arms, default) => {
                out.push_str("switch ");
                self.operand(out, scrutinee, indent);
                out.push_str(" {");
                for (value, body) in arms {
                    pad(out, indent + 1);
                    let _ = write!(out, "{value}");
                    self.arm(out, body, indent + 1);
                }
                pad(out, indent + 1);
                out.push('_');
                self.arm(out, default, indent + 1);
                pad(out, indent);
                out.push('}');
            }
        }
    }

    /// ` => body`: on the same line if it's short.
    fn arm(&self, out: &mut String, body: &Expr, indent: usize) {
        out.push_str(" =>");
        if compound(body) {
            pad(out, indent + 1);
            self.expr(out, body, indent + 1);
        } else {
            out.push(' ');
            self.expr(out, body, indent);
        }
    }

    /// An operand: in braces if it's a block (a closure's body is indented
    /// on the lines after it instead).
    fn operand(&self, out: &mut String, expr: &Expr, indent: usize) {
        if matches!(
            expr,
            Expr::Let(..) | Expr::Match(..) | Expr::NumSwitch(..) | Expr::If(..)
        ) {
            out.push('{');
            pad(out, indent + 1);
            self.expr(out, expr, indent + 1);
            pad(out, indent);
            out.push('}');
        } else {
            self.expr(out, expr, indent);
        }
    }

    fn args(&self, out: &mut String, args: &[Expr], indent: usize) {
        out.push('(');
        for (i, arg) in args.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            self.operand(out, arg, indent);
        }
        out.push(')');
    }
}
