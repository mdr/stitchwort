//! JavaScript extraction (DESIGN.md §12): erase types and proofs, generate an
//! ES module, and wrap each export in decode → compute → encode.
//!
//! First-milestone scope: exports take and return concrete first-order data
//! (`Nat`, `List`, and data types built from them) and have no proof
//! arguments.

use std::collections::HashSet;
use std::fmt::Write;

use stitchwort_core::check::telescope;
use stitchwort_core::term::Branch;
use stitchwort_core::value::eval;
use stitchwort_core::{DataId, DefId, Globals, Sort, Term, Value, pretty};
use stitchwort_syntax::Diagnostic;

/// How a type crosses the JS boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Boundary {
    /// `bigint`, non-negative.
    Nat,
    /// `readonly T[]`.
    List(Box<Boundary>),
    /// A tagged object union.
    Data(DataId),
}

pub struct ExportSig {
    pub id: DefId,
    pub name: String,
    pub params: Vec<(String, Boundary)>,
    pub result: Boundary,
}

/// The exportability check: an export must be pure, take and return concrete
/// data with a codec, and have no type or proof parameters.
pub fn exportable(g: &Globals, id: DefId) -> Result<ExportSig, Diagnostic> {
    let def = g.def(id);
    let refuse = |why: String| {
        Diagnostic::error("E-EXPORT", format!("`{}` can't be exported", def.name))
            .with_label(def.span, why)
    };
    if !is_js_identifier(&def.name) {
        return Err(refuse(
            "its name isn't a valid JavaScript identifier".into(),
        ));
    }
    let tel = telescope(g, &def.ty_value, def.span);
    if tel.result_erased {
        return Err(refuse(
            "it's a proof or a type, so it has no runtime value".into(),
        ));
    }
    // Prefer the names from the signature, then from the equations.
    let equation_names = lam_names(def.body.as_ref());
    let mut params = Vec::new();
    for (i, (x, ty, erased)) in tel.params.iter().enumerate() {
        if *erased {
            return Err(refuse(format!(
                "parameter `{x}` is a type or a proof; only concrete data can cross the JS boundary for now"
            ))
            .with_note(
                "for a type parameter, export a version specialised to a concrete type; \
                 proof parameters need decision procedures, which aren't implemented yet",
            ));
        }
        let boundary = boundary(g, ty, &mut HashSet::new())
            .map_err(|why| refuse(format!("parameter `{x}`: {why}")))?;
        let js_name = [Some(&**x), equation_names.get(i).map(|n| &**n)]
            .into_iter()
            .flatten()
            .find(|n| is_js_identifier(n) && *n != "_" && !n.starts_with("arg"))
            .map_or_else(|| format!("arg{i}"), str::to_string);
        params.push((js_name, boundary));
    }
    let result = boundary(g, &tel.result, &mut HashSet::new())
        .map_err(|why| refuse(format!("its result: {why}")))?;
    Ok(ExportSig {
        id,
        name: def.name.to_string(),
        params,
        result,
    })
}

fn boundary(g: &Globals, ty: &Value, visiting: &mut HashSet<DataId>) -> Result<Boundary, String> {
    let cannot = |ty: &Value| {
        format!(
            "`{}` can't cross the JS boundary yet",
            pretty::value(g, &[], ty)
        )
    };
    match ty {
        Value::Data(d, params) => {
            let data = g.data(*d);
            match (&*data.name, params.as_slice()) {
                ("Nat", []) => Ok(Boundary::Nat),
                ("List", [elem]) => Ok(Boundary::List(Box::new(boundary(g, elem, visiting)?))),
                (_, []) if data.sort != Sort::Prop => {
                    if !visiting.insert(*d) {
                        return Ok(Boundary::Data(*d));
                    }
                    for (ctor, fields) in data.ctors.iter().zip(data_fields(g, *d)) {
                        if ctor.field_erased.iter().any(|e| *e) {
                            return Err(format!(
                                "`{}` has a proof or type field, which can't be checked at the boundary yet",
                                data.name
                            ));
                        }
                        for (_, field_ty) in fields {
                            boundary(g, &field_ty, visiting)?;
                        }
                    }
                    Ok(Boundary::Data(*d))
                }
                _ => Err(cannot(ty)),
            }
        }
        Value::Pi(..) => Err("functions can't cross the JS boundary yet".into()),
        other => Err(cannot(other)),
    }
}

/// Field names and types of each constructor of a parameterless data type.
fn data_fields(g: &Globals, d: DataId) -> Vec<Vec<(String, Value)>> {
    g.data(d)
        .ctors
        .iter()
        .map(|ctor| {
            let mut env = Vec::new();
            ctor.fields
                .iter()
                .map(|(name, ty)| {
                    let value = eval(g, &env, ty);
                    env.push(Value::var(env.len()));
                    (name.to_string(), value)
                })
                .collect()
        })
        .collect()
}

pub struct Output {
    pub js: String,
    pub dts: String,
}

/// Generates the ES module and its TypeScript declarations for every export.
pub fn generate(g: &Globals) -> Result<Output, Diagnostic> {
    let exports = (0..g.defs.len())
        .map(DefId)
        .filter(|id| g.def(*id).export)
        .map(|id| exportable(g, id))
        .collect::<Result<Vec<_>, _>>()?;

    let mut boundary_datas = Vec::new();
    for sig in &exports {
        for b in sig.params.iter().map(|(_, b)| b).chain([&sig.result]) {
            collect_datas(g, b, &mut boundary_datas);
        }
    }

    let codegen = Gen::new(g);
    let mut js = String::from(RUNTIME);
    for &d in &boundary_datas {
        js.push_str(&codegen.codecs(d));
    }
    js.push('\n');
    for id in (0..g.defs.len()).map(DefId) {
        js.push_str(&codegen.def(id));
    }
    for sig in &exports {
        js.push_str(&codegen.wrapper(sig));
    }

    let mut dts = String::from(
        "// Generated by stitchwort. Do not edit.\n\nexport declare class StitchwortInputError extends Error {}\n",
    );
    for &d in &boundary_datas {
        dts.push_str(&codegen.ts_alias(d));
    }
    for sig in &exports {
        let params: Vec<String> = sig
            .params
            .iter()
            .map(|(x, b)| format!("{x}: {}", codegen.ts_type(b, true)))
            .collect();
        let _ = writeln!(
            dts,
            "export declare function {}({}): {};",
            sig.name,
            params.join(", "),
            codegen.ts_type(&sig.result, false)
        );
    }
    Ok(Output { js, dts })
}

fn collect_datas(g: &Globals, b: &Boundary, out: &mut Vec<DataId>) {
    match b {
        Boundary::Nat => {}
        Boundary::List(elem) => collect_datas(g, elem, out),
        Boundary::Data(d) => {
            if out.contains(d) {
                return;
            }
            out.push(*d);
            for fields in data_fields(g, *d) {
                for (_, ty) in fields {
                    let b = boundary(g, &ty, &mut HashSet::new()).expect("checked by exportable");
                    collect_datas(g, &b, out);
                }
            }
        }
    }
}

const RUNTIME: &str = r#"// Generated by stitchwort. Do not edit.

export class StitchwortInputError extends Error {
  constructor(message) {
    super(message);
    this.name = "StitchwortInputError";
  }
}

const dec_Nat = (x, path) => {
  if (typeof x !== "bigint" || x < 0n) {
    throw new StitchwortInputError(`${path}: expected a non-negative bigint`);
  }
  return x;
};
const enc_Nat = (v) => v;

// Decoding reads `length` and each element exactly once, into a fresh list.
const dec_List = (dec) => (x, path) => {
  if (!Array.isArray(x)) {
    throw new StitchwortInputError(`${path}: expected an array`);
  }
  const n = x.length;
  const items = new Array(n);
  for (let i = 0; i < n; i++) items[i] = dec(x[i], `${path}[${i}]`);
  let list = { tag: "Nil" };
  for (let i = n - 1; i >= 0; i--) list = { tag: "Cons", head: items[i], tail: list };
  return list;
};
const enc_List = (enc) => (v) => {
  const out = [];
  while (v.tag === "Cons") {
    out.push(enc(v.head));
    v = v.tail;
  }
  return out;
};
"#;

struct Gen<'g> {
    g: &'g Globals,
    nat: Option<DataId>,
    /// Per definition: whether it's erased, and which of its leading
    /// parameters (up to its arity) are erased.
    erased: Vec<(bool, Vec<bool>)>,
}

impl<'g> Gen<'g> {
    fn new(g: &'g Globals) -> Self {
        let erased = g
            .defs
            .iter()
            .map(|def| {
                let tel = telescope(g, &def.ty_value, def.span);
                let mask = tel
                    .params
                    .iter()
                    .take(def.arity)
                    .map(|(_, _, erased)| *erased)
                    .collect();
                (tel.result_erased, mask)
            })
            .collect();
        Gen {
            g,
            nat: g.find_data("Nat"),
            erased,
        }
    }

    fn def(&self, id: DefId) -> String {
        let def = self.g.def(id);
        let (erased, mask) = &self.erased[id.0];
        let Some(body) = &def.body else {
            return String::new();
        };
        if *erased {
            return String::new();
        }
        let mut env = mask.clone();
        let mut params = String::new();
        for (level, erased) in mask.iter().enumerate() {
            if !erased {
                let _ = write!(params, "({}) => ", var(level));
            }
        }
        let tree = body.peel_lams(def.arity);
        let rhs = if matches!(tree, Term::Case(..)) {
            let block = self.tree(tree, &mut env, 1);
            if params.is_empty() {
                format!("(() => {{\n{block}}})()")
            } else {
                format!("{{\n{block}}}")
            }
        } else {
            self.expr(tree, &mut env)
        };
        format!("const {} = {params}{rhs};\n", def_name(&def.name))
    }

    /// Statements for a case tree, ending in `return`. `env` says, for each
    /// variable level, whether it's erased.
    fn tree(&self, term: &Term, env: &mut Vec<bool>, depth: usize) -> String {
        let pad = "  ".repeat(depth);
        let Term::Case(ix, d, branches) = term.strip_loc() else {
            return format!("{pad}return {};\n", self.expr(term, env));
        };
        let data = self.g.data(*d);
        let scrutinee = var(env.len() - 1 - ix);
        let mut out = String::new();
        let predecessor = var(env.len());
        let mut branch = |out: &mut String, c: usize, b: &Branch, depth: usize| {
            let pad = "  ".repeat(depth);
            let level = env.len();
            for (f, ((field, _), erased)) in data.ctors[c]
                .fields
                .iter()
                .zip(&data.ctors[c].field_erased)
                .enumerate()
            {
                if !erased && Some(*d) != self.nat {
                    let _ = writeln!(
                        out,
                        "{pad}const {} = {scrutinee}.{};",
                        var(level + f),
                        js_field(field)
                    );
                }
                env.push(*erased);
            }
            out.push_str(&self.tree(&b.body, env, depth));
            env.truncate(level);
        };
        if data.sort == Sort::Prop {
            // The proof doesn't exist at runtime. Matching on it into data is
            // only allowed for at most one constructor with only proof fields.
            match branches.first() {
                Some(b) => branch(&mut out, 0, b, depth),
                None => {
                    let _ = writeln!(out, "{pad}throw new Error(\"unreachable\");");
                }
            }
        } else if Some(*d) == self.nat {
            let _ = writeln!(out, "{pad}if ({scrutinee} === 0n) {{");
            branch(&mut out, 0, &branches[0], depth + 1);
            let _ = writeln!(out, "{pad}}} else {{");
            let _ = writeln!(out, "{pad}  const {predecessor} = {scrutinee} - 1n;");
            branch(&mut out, 1, &branches[1], depth + 1);
            let _ = writeln!(out, "{pad}}}");
        } else {
            let _ = writeln!(out, "{pad}switch ({scrutinee}.tag) {{");
            for (c, b) in branches.iter().enumerate() {
                let _ = writeln!(out, "{pad}  case \"{}\": {{", data.ctors[c].name);
                branch(&mut out, c, b, depth + 2);
                let _ = writeln!(out, "{pad}  }}");
            }
            let _ = writeln!(out, "{pad}}}");
            let _ = writeln!(out, "{pad}throw new Error(\"unreachable\");");
        }
        out
    }

    fn expr(&self, term: &Term, env: &mut Vec<bool>) -> String {
        match term {
            Term::Loc(_, t) | Term::Ann(t, _) => self.expr(t, env),
            Term::Var(ix) => {
                let level = env.len() - 1 - ix;
                if env[level] {
                    "undefined".into()
                } else {
                    var(level)
                }
            }
            Term::Def(id) => self.def_ref(*id, &[], env),
            Term::App(..) => {
                let (head, args) = term.spine();
                if let Term::Def(id) = head {
                    return self.def_ref(*id, &args, env);
                }
                let mut out = format!("({})", self.expr(head, env));
                for arg in args {
                    let _ = write!(out, "({})", self.expr(arg, env));
                }
                out
            }
            Term::Lam(_, _, body) => {
                let level = env.len();
                env.push(false);
                let body = self.expr(body, env);
                env.pop();
                format!("(({}) => {body})", var(level))
            }
            Term::Ctor(d, c, args) => {
                let data = self.g.data(*d);
                if data.sort == Sort::Prop {
                    return "undefined".into();
                }
                if Some(*d) == self.nat {
                    return match c {
                        0 => "0n".into(),
                        _ => format!("({} + 1n)", self.expr(&args[0], env)),
                    };
                }
                let ctor = &data.ctors[*c];
                let mut fields = vec![format!("tag: \"{}\"", ctor.name)];
                for (((field, _), erased), arg) in
                    ctor.fields.iter().zip(&ctor.field_erased).zip(args)
                {
                    if !erased {
                        fields.push(format!("{}: {}", js_field(field), self.expr(arg, env)));
                    }
                }
                format!("{{ {} }}", fields.join(", "))
            }
            // Proofs are erased, and transport along an equality does nothing.
            Term::J(_, base, _) => self.expr(base, env),
            Term::Data(..) | Term::Sort(_) | Term::Pi(..) | Term::Eq(..) | Term::Refl => {
                "undefined".into()
            }
            Term::Case(..) => panic!("internal error: case outside a case tree"),
            Term::Meta(_) => {
                panic!("internal error: unsolved metavariable in a checked definition")
            }
        }
    }

    /// A call to a definition, leaving out its erased arguments.
    fn def_ref(&self, id: DefId, args: &[&Term], env: &mut Vec<bool>) -> String {
        let (erased, mask) = &self.erased[id.0];
        if *erased {
            return "undefined".into();
        }
        let mut out = def_name(&self.g.def(id).name);
        for (i, arg) in args.iter().enumerate() {
            if !mask.get(i).copied().unwrap_or(false) {
                let _ = write!(out, "({})", self.expr(arg, env));
            }
        }
        out
    }

    fn wrapper(&self, sig: &ExportSig) -> String {
        let params: Vec<&str> = sig.params.iter().map(|(x, _)| x.as_str()).collect();
        let mut out = format!("\nexport function {}({}) {{\n", sig.name, params.join(", "));
        let mut call = def_name(&self.g.def(sig.id).name);
        for (i, (x, b)) in sig.params.iter().enumerate() {
            let _ = writeln!(out, "  const a{i} = {}({x}, \"{x}\");", self.decoder(b));
            let _ = write!(call, "(a{i})");
        }
        let _ = writeln!(out, "  return {}({call});\n}}", self.encoder(&sig.result));
        out
    }

    fn decoder(&self, b: &Boundary) -> String {
        match b {
            Boundary::Nat => "dec_Nat".into(),
            Boundary::List(elem) => format!("dec_List({})", self.decoder(elem)),
            Boundary::Data(d) => format!("dec_{}", self.g.data(*d).name),
        }
    }

    fn encoder(&self, b: &Boundary) -> String {
        match b {
            Boundary::Nat => "enc_Nat".into(),
            Boundary::List(elem) => format!("enc_List({})", self.encoder(elem)),
            Boundary::Data(d) => format!("enc_{}", self.g.data(*d).name),
        }
    }

    fn field_boundaries(&self, d: DataId) -> Vec<Vec<(String, Boundary)>> {
        data_fields(self.g, d)
            .into_iter()
            .map(|fields| {
                fields
                    .into_iter()
                    .map(|(name, ty)| {
                        let b = boundary(self.g, &ty, &mut HashSet::new())
                            .expect("checked by exportable");
                        (name, b)
                    })
                    .collect()
            })
            .collect()
    }

    fn codecs(&self, d: DataId) -> String {
        let data = self.g.data(d);
        let name = &data.name;
        let mut dec = format!(
            "\nfunction dec_{name}(x, path) {{\n  if (typeof x !== \"object\" || x === null) {{\n    throw new StitchwortInputError(`${{path}}: expected a {name} object`);\n  }}\n  const tag = x.tag;\n  switch (tag) {{\n"
        );
        let mut enc = format!("function enc_{name}(v) {{\n  switch (v.tag) {{\n");
        for (ctor, fields) in data.ctors.iter().zip(self.field_boundaries(d)) {
            let _ = writeln!(dec, "    case \"{}\": {{", ctor.name);
            let mut built = vec![format!("tag: \"{}\"", ctor.name)];
            let mut encoded = built.clone();
            for (field, b) in &fields {
                let f = js_field(field);
                let _ = writeln!(
                    dec,
                    "      const {f} = {}(x.{f}, `${{path}}.{f}`);",
                    self.decoder(b)
                );
                built.push(f.clone());
                encoded.push(format!("{f}: {}(v.{f})", self.encoder(b)));
            }
            let _ = writeln!(dec, "      return {{ {} }};\n    }}", built.join(", "));
            let _ = writeln!(
                enc,
                "    case \"{}\": return {{ {} }};",
                ctor.name,
                encoded.join(", ")
            );
        }
        let _ = writeln!(
            dec,
            "    default:\n      throw new StitchwortInputError(`${{path}}: unknown tag ${{String(tag)}}`);\n  }}\n}}"
        );
        let _ = writeln!(enc, "  }}\n  throw new Error(\"unreachable\");\n}}");
        dec + &enc
    }

    /// Inputs are `readonly`; outputs are freshly built, so they're mutable.
    fn ts_type(&self, b: &Boundary, readonly: bool) -> String {
        match b {
            Boundary::Nat => "bigint".into(),
            Boundary::List(elem) if readonly => format!("readonly {}[]", self.ts_type(elem, true)),
            Boundary::List(elem) => format!("{}[]", self.ts_type(elem, false)),
            Boundary::Data(d) => self.g.data(*d).name.to_string(),
        }
    }

    fn ts_alias(&self, d: DataId) -> String {
        let data = self.g.data(d);
        let variants: Vec<String> = data
            .ctors
            .iter()
            .zip(self.field_boundaries(d))
            .map(|(ctor, fields)| {
                let mut parts = vec![format!("readonly tag: \"{}\"", ctor.name)];
                for (field, b) in &fields {
                    parts.push(format!(
                        "readonly {}: {}",
                        js_field(field),
                        self.ts_type(b, true)
                    ));
                }
                format!("{{ {} }}", parts.join("; "))
            })
            .collect();
        format!(
            "export type {} =\n  | {};\n",
            data.name,
            variants.join("\n  | ")
        )
    }
}

/// Parameter names of a definition's leading lambdas.
fn lam_names(body: Option<&Term>) -> Vec<stitchwort_core::Name> {
    let mut names = Vec::new();
    let mut term = body.map(Term::strip_loc);
    while let Some(Term::Lam(x, _, inner)) = term {
        names.push(x.clone());
        term = Some(inner.strip_loc());
    }
    names
}

fn var(level: usize) -> String {
    format!("v{level}")
}

fn def_name(name: &str) -> String {
    format!("${}", name.replace('\'', "$"))
}

fn js_field(name: &str) -> String {
    name.replace('\'', "$")
}

fn is_js_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_' || c == '$')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$')
}

/// A JS expression for `value`, encoded as it would cross the boundary. Used by
/// differential tests to compare the reference evaluator with generated JS.
pub fn boundary_literal(g: &Globals, b: &Boundary, value: &Value) -> Result<String, String> {
    let stuck = || format!("not a fully evaluated value: {value:?}");
    match (b, value) {
        (Boundary::Nat, _) => {
            let mut n: u64 = 0;
            let mut v = value;
            loop {
                match v {
                    Value::Ctor(_, 0, _) => return Ok(format!("{n}n")),
                    Value::Ctor(_, 1, fields) => {
                        n += 1;
                        v = &fields[0];
                    }
                    _ => return Err(stuck()),
                }
            }
        }
        (Boundary::List(elem), _) => {
            let mut items = Vec::new();
            let mut v = value;
            loop {
                match v {
                    Value::Ctor(_, 0, _) => return Ok(format!("[{}]", items.join(", "))),
                    Value::Ctor(_, 1, fields) => {
                        items.push(boundary_literal(g, elem, &fields[0])?);
                        v = &fields[1];
                    }
                    _ => return Err(stuck()),
                }
            }
        }
        (Boundary::Data(d), Value::Ctor(_, c, fields)) => {
            let ctor = &g.data(*d).ctors[*c];
            let boundaries = &Gen::new(g).field_boundaries(*d)[*c];
            let mut parts = vec![format!("tag: \"{}\"", ctor.name)];
            for ((name, b), field) in boundaries.iter().zip(fields) {
                parts.push(format!(
                    "{}: {}",
                    js_field(name),
                    boundary_literal(g, b, field)?
                ));
            }
            Ok(format!("{{ {} }}", parts.join(", ")))
        }
        _ => Err(stuck()),
    }
}
