//! Generated layout tests: random nested blocks, lambdas and handlers are
//! written out with the layout rules (docs/syntax.md), parsed back, and must
//! come back with the same structure.

use stitchwort_syntax::ast::{Clause, Decl, Expr};
use stitchwort_syntax::{SourceMap, parse_module};

/// What's generated, and what's compared.
enum Gen {
    Var(String),
    App(Box<Gen>, Box<Gen>),
    /// Lines of a block: `(Some(x), e)` is `let x = e`, `(None, e)` a line
    /// run for its effects. Then the result.
    Block(Vec<(Option<String>, Gen)>, Box<Gen>),
    Lam(String, Box<Gen>),
    Handle(Box<Gen>, Vec<(String, Gen)>),
    Match(Box<Gen>, Vec<Gen>),
}

struct Rng(u64);

impl Rng {
    fn below(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.0 >> 33) % n
    }
}

/// Like `generate`, but not a block: for a line of a block or an argument,
/// where a block can't start (it starts on a new line, after `=` or `->`).
fn generate_inline(rng: &mut Rng, depth: u32) -> Gen {
    loop {
        let g = generate(rng, depth);
        if !matches!(g, Gen::Block(..)) {
            return g;
        }
    }
}

fn generate(rng: &mut Rng, depth: u32) -> Gen {
    let name = |rng: &mut Rng| format!("v{}", rng.below(5));
    if depth == 0 {
        return Gen::Var(name(rng));
    }
    match rng.below(6) {
        0 => Gen::Var(name(rng)),
        1 => Gen::App(
            Box::new(Gen::Var(name(rng))),
            Box::new(generate_inline(rng, depth - 1)),
        ),
        2 => {
            let lines = (0..1 + rng.below(3))
                .map(|_| {
                    // A `let`'s value may be a block; a plain line may not.
                    let bound = (rng.below(2) == 0).then(|| name(rng));
                    let e = match bound {
                        Some(_) => generate(rng, depth - 1),
                        None => generate_inline(rng, depth - 1),
                    };
                    (bound, e)
                })
                .collect();
            Gen::Block(lines, Box::new(generate_inline(rng, depth - 1)))
        }
        3 => Gen::Lam(name(rng), Box::new(generate(rng, depth - 1))),
        4 => {
            let alts = (0..1 + rng.below(2))
                .map(|_| generate(rng, depth - 1))
                .collect();
            Gen::Match(Box::new(Gen::Var(name(rng))), alts)
        }
        _ => {
            let clauses = (0..1 + rng.below(2))
                .map(|i| (format!("op{i}"), generate(rng, depth - 1)))
                .collect();
            Gen::Handle(Box::new(Gen::Var(name(rng))), clauses)
        }
    }
}

/// Source text for `g`, as it continues the current line. `indent` is the
/// column of the line it's on: anything placed on new lines goes deeper.
fn render(g: &Gen, indent: usize) -> String {
    match g {
        Gen::Var(x) => x.clone(),
        Gen::App(f, a) => format!("{} ({})", render(f, indent), render(a, indent + 2)),
        Gen::Block(..) => block(g, indent + 2),
        Gen::Lam(x, body) => format!("\\{x} -> {}", render(body, indent)),
        Gen::Handle(body, clauses) => {
            let mut out = format!("handle {} with", render(body, indent));
            let col = indent + 2;
            for (op, body) in clauses {
                out.push_str(&format!(
                    "\n{}| {op} x => k -> {}",
                    " ".repeat(col),
                    render(body, col + 2)
                ));
            }
            out
        }
        Gen::Match(scrutinee, alts) => {
            let mut out = format!("match {} with", render(scrutinee, indent));
            let col = indent + 2;
            for body in alts {
                out.push_str(&format!(
                    "\n{}| Pat x _ -> {}",
                    " ".repeat(col),
                    render(body, col + 2)
                ));
            }
            out
        }
    }
}

/// A block whose lines start at `col`, on a new line.
fn block(g: &Gen, col: usize) -> String {
    let Gen::Block(lines, result) = g else {
        unreachable!()
    };
    let pad = " ".repeat(col);
    let mut out = String::new();
    for (bound, e) in lines {
        let text = render(e, col);
        match bound {
            Some(x) => out.push_str(&format!("\n{pad}let {x} = {text}")),
            None => out.push_str(&format!("\n{pad}{text}")),
        }
    }
    out.push_str(&format!("\n{pad}{}", render(result, col)));
    out
}

/// The structure of a generated term.
fn shape(g: &Gen) -> String {
    match g {
        Gen::Var(x) => x.clone(),
        Gen::App(f, a) => format!("({} {})", shape(f), shape(a)),
        Gen::Block(lines, result) => {
            let mut out = String::new();
            for (bound, e) in lines {
                match bound {
                    Some(x) => out.push_str(&format!("let {x} = {}; ", shape(e))),
                    None => out.push_str(&format!("{}; ", shape(e))),
                }
            }
            format!("{{{out}{}}}", shape(result))
        }
        Gen::Lam(x, body) => format!("(\\{x} {})", shape(body)),
        Gen::Handle(body, clauses) => {
            let cs: Vec<String> = clauses
                .iter()
                .map(|(op, b)| format!("{op} {}", shape(b)))
                .collect();
            format!("(handle {} [{}])", shape(body), cs.join(" | "))
        }
        Gen::Match(scrutinee, alts) => {
            let cs: Vec<String> = alts.iter().map(shape).collect();
            format!("(match {} [{}])", shape(scrutinee), cs.join(" | "))
        }
    }
}

/// The same for a parsed expression. A block parses as nested `let`s and
/// sequences, so they're gathered back into one.
fn parsed_shape(e: &Expr) -> String {
    match e {
        Expr::Var(x) => x.text.clone(),
        Expr::App(f, a) => format!("({} {})", parsed_shape(f), parsed_shape(a)),
        Expr::Let { .. } | Expr::Seq(..) => {
            let mut out = String::new();
            let mut e = e;
            loop {
                match e {
                    Expr::Let {
                        name, value, body, ..
                    } => {
                        out.push_str(&format!("let {} = {}; ", name.text, parsed_shape(value)));
                        e = body;
                    }
                    Expr::Seq(first, rest) => {
                        out.push_str(&format!("{}; ", parsed_shape(first)));
                        e = rest;
                    }
                    other => return format!("{{{out}{}}}", parsed_shape(other)),
                }
            }
        }
        Expr::Lam(names, body, _) => format!("(\\{} {})", names[0].text, parsed_shape(body)),
        Expr::Handle { body, clauses, .. } => {
            let cs: Vec<String> = clauses
                .iter()
                .map(|c| match c {
                    Clause::Op { op, body, .. } => format!("{} {}", op.text, parsed_shape(body)),
                    Clause::Return { body, .. } => format!("return {}", parsed_shape(body)),
                })
                .collect();
            format!("(handle {} [{}])", parsed_shape(body), cs.join(" | "))
        }
        Expr::Match {
            scrutinees, alts, ..
        } => {
            let cs: Vec<String> = alts.iter().map(|a| parsed_shape(&a.body)).collect();
            format!(
                "(match {} [{}])",
                parsed_shape(&scrutinees[0].expr),
                cs.join(" | ")
            )
        }
        other => format!("<{other:?}>"),
    }
}

#[test]
fn generated_layouts_parse_back_to_the_same_structure() {
    let mut rng = Rng(0x1a70_u64 << 32 | 0xbeef);
    for n in 0..3000 {
        let g = generate(&mut rng, 5);
        let body = match &g {
            Gen::Block(..) => block(&g, 2),
            other => format!(" {}", render(other, 0)),
        };
        let text = format!("f u ={body}\n");
        let mut sources = SourceMap::new();
        let file = sources.add("generated.sw", &text);
        let module = parse_module(file, &text)
            .unwrap_or_else(|e| panic!("program {n} doesn't parse: {e:?}\n\n{text}"));
        let Some(Decl::Equation { rhs: Some(rhs), .. }) = module.decls.first() else {
            panic!("program {n}: expected one equation\n\n{text}");
        };
        // A block of just a result is the result itself.
        let expected = shape(&g).replace("{}", "");
        assert_eq!(
            parsed_shape(rhs),
            expected,
            "program {n} parsed differently:\n\n{text}"
        );
    }
}
