//! JavaScript extraction (DESIGN.md §12): erase types and proofs, generate an
//! ES module, and wrap each export in decode → compute → encode.
//!
//! First-milestone scope: exports take and return concrete first-order data
//! (`Nat`, `List`, and data types built from them) and have no proof
//! arguments.

use std::collections::HashSet;
use std::fmt::Write;

use stitchwort_core::check::{is_type_former, telescope};
use stitchwort_core::native;
use stitchwort_core::term::Branch;
use stitchwort_core::value::eval;
use stitchwort_core::{DataId, DefId, Globals, Sort, Term, Value, pretty};
use stitchwort_syntax::Diagnostic;

/// How a type crosses the JS boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Boundary {
    /// `bigint`, non-negative.
    Nat,
    /// `boolean`.
    Bool,
    /// `readonly T[]`.
    List(Box<Boundary>),
    /// A tagged object union.
    Data(DataId),
}

pub struct ExportSig {
    pub id: DefId,
    pub name: String,
    /// The parameters JS passes: name and boundary type.
    pub params: Vec<(String, Boundary)>,
    /// For each of `params`, its position among all the function's parameters.
    pub param_positions: Vec<usize>,
    /// The proof parameters, which JS doesn't pass: they're checked at runtime.
    pub checks: Vec<Check>,
    pub result: Boundary,
}

/// A proof parameter of an export, checked at runtime by a decision procedure.
pub struct Check {
    /// Its position among all the function's parameters.
    pub position: usize,
    /// A `Decidable P` term, in the context of the parameters before it.
    pub decision: Term,
    /// `P`, for the error message.
    pub description: String,
}

/// The exportability check: an export must be pure, take and return concrete
/// data with a codec, and have no type parameters. Each proof parameter must
/// have a decision procedure (found by the elaborator), which becomes a
/// runtime check.
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
    let mut param_positions = Vec::new();
    let mut checks = Vec::new();
    for (i, (x, ty, erased)) in tel.params.iter().enumerate() {
        if *erased && is_type_former(g, i, ty) {
            return Err(refuse(format!(
                "parameter `{x}` is a type; only concrete data can cross the JS boundary for now"
            ))
            .with_note("export a version specialised to a concrete type"));
        }
        if *erased {
            let Some(validator) = def.validators.iter().find(|v| v.param == i) else {
                return Err(refuse(format!(
                    "proof parameter `{x}` has no runtime check"
                )));
            };
            // Describe the precondition as written in the signature.
            let names: Vec<_> = tel.params[..i].iter().map(|(n, _, _)| n.clone()).collect();
            let description = written_param_type(&def.ty, i).map_or_else(
                || pretty::value(g, &names, ty),
                |t| pretty::term(g, &names, t),
            );
            checks.push(Check {
                position: i,
                decision: validator.decision.clone(),
                description,
            });
            continue;
        }
        let boundary = boundary(g, ty, &mut HashSet::new())
            .map_err(|why| refuse(format!("parameter `{x}`: {why}")))?;
        let js_name = [Some(&**x), equation_names.get(i).map(|n| &**n)]
            .into_iter()
            .flatten()
            .find(|n| is_js_identifier(n) && *n != "_" && !n.starts_with("arg"))
            .map_or_else(|| format!("arg{i}"), str::to_string);
        params.push((js_name, boundary));
        param_positions.push(i);
    }
    let result = boundary(g, &tel.result, &mut HashSet::new())
        .map_err(|why| refuse(format!("its result: {why}")))?;
    Ok(ExportSig {
        id,
        name: def.name.to_string(),
        params,
        param_positions,
        checks,
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
                ("Bool", []) => Ok(Boundary::Bool),
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

/// For each constructor of a data type that crosses the boundary, its fields'
/// names and boundary types.
pub fn field_boundaries(g: &Globals, d: DataId) -> Vec<Vec<(String, Boundary)>> {
    data_fields(g, d)
        .into_iter()
        .map(|fields| {
            fields
                .into_iter()
                .map(|(name, ty)| {
                    let b = boundary(g, &ty, &mut HashSet::new()).expect("checked by exportable");
                    (name, b)
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
    // Only what the exports use, in declaration order (which is dependency order).
    let used = reachable(g, exports.iter().map(|sig| sig.id), |id| {
        codegen.erased[id.0].0 || g.builtins.native(id).is_some()
    });
    for id in (0..g.defs.len()).map(DefId).filter(|id| used[id.0]) {
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
        Boundary::Nat | Boundary::Bool => {}
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

const dec_Bool = (x, path) => {
  if (typeof x !== "boolean") {
    throw new StitchwortInputError(`${path}: expected a boolean`);
  }
  return x ? { tag: "True" } : { tag: "False" };
};
const enc_Bool = (v) => v.tag === "True";

// Decoders read each property exactly once, into fresh values. `inside` holds
// the objects currently being decoded, so an input that contains itself is
// refused instead of recursing forever. (Shared, acyclic parts are fine.)
const enter = (x, path, inside) => {
  if (inside.has(x)) {
    throw new StitchwortInputError(`${path}: the input contains itself`);
  }
  inside.add(x);
};

const dec_List = (dec) => (x, path, inside = new Set()) => {
  if (!Array.isArray(x)) {
    throw new StitchwortInputError(`${path}: expected an array`);
  }
  enter(x, path, inside);
  const n = x.length;
  const items = new Array(n);
  for (let i = 0; i < n; i++) items[i] = dec(x[i], `${path}[${i}]`, inside);
  inside.delete(x);
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
        if let Some(op) = self.g.builtins.native(id) {
            return format!("const {} = {};\n", def_name(&def.name), native_js(op));
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
                // No runtime parameters, but a case on an erased proof (like
                // `absurd`): a function, so it only runs when it's used.
                format!("() => {{\n{block}}}")
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
            Term::Nat(n) => format!("{n}n"),
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
                    // Count the `Succ`s: `Succ (Succ x)` is `x + 2n`, and a
                    // literal is just a number.
                    let mut count = 0u64;
                    let mut inner = term;
                    while let Term::Ctor(_, 1, succ) = inner.strip_loc() {
                        count += 1;
                        inner = &succ[0];
                    }
                    return match (inner.strip_loc(), count) {
                        (Term::Ctor(_, 0, _), n) => format!("{n}n"),
                        (Term::Nat(k), n) => format!("{}n", &**k + n),
                        (_, n) => format!("({} + {n}n)", self.expr(inner, env)),
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
        if self.is_thunk(id) {
            out.push_str("()");
        }
        for (i, arg) in args.iter().enumerate() {
            if !mask.get(i).copied().unwrap_or(false) {
                let _ = write!(out, "({})", self.expr(arg, env));
            }
        }
        out
    }

    /// A definition with a case tree but no runtime parameters is compiled to
    /// a function of no arguments (see [`Gen::def`]).
    fn is_thunk(&self, id: DefId) -> bool {
        let def = self.g.def(id);
        let (erased, mask) = &self.erased[id.0];
        !erased
            && mask.iter().all(|e| *e)
            && def
                .body
                .as_ref()
                .is_some_and(|b| matches!(b.peel_lams(def.arity), Term::Case(..)))
    }

    /// `export function f(…)`: decode the inputs, run the precondition checks,
    /// call the compiled definition, encode the result. Decoded parameter `i`
    /// (counting all parameters) is `v{i}`, which is what the compiled checks
    /// refer to.
    fn wrapper(&self, sig: &ExportSig) -> String {
        let params: Vec<&str> = sig.params.iter().map(|(x, _)| x.as_str()).collect();
        let mut out = format!("\nexport function {}({}) {{\n", sig.name, params.join(", "));
        let mut call = def_name(&self.g.def(sig.id).name);
        for ((x, b), position) in sig.params.iter().zip(&sig.param_positions) {
            let _ = writeln!(
                out,
                "  const {} = {}({x}, \"{x}\");",
                var(*position),
                self.decoder(b)
            );
            let _ = write!(call, "({})", var(*position));
        }
        let yes = self.decision_yes_tag();
        for check in &sig.checks {
            // Parameters before the check: proofs are erased, data is decoded.
            let mut env: Vec<bool> = (0..check.position)
                .map(|i| !sig.param_positions.contains(&i))
                .collect();
            let decision = self.expr(&check.decision, &mut env);
            let message = format!("precondition `{}` doesn't hold", check.description)
                .replace('\\', "\\\\")
                .replace('"', "\\\"");
            let _ = writeln!(
                out,
                "  if ({decision}.tag !== \"{yes}\") {{\n    throw new StitchwortInputError(\"{message}\");\n  }}"
            );
        }
        let _ = writeln!(out, "  return {}({call});\n}}", self.encoder(&sig.result));
        out
    }

    /// The tag of `Decidable`'s first constructor (`Yes`).
    fn decision_yes_tag(&self) -> String {
        self.g.find_data("Decidable").map_or_else(
            || "Yes".into(),
            |d| self.g.data(d).ctors[0].name.to_string(),
        )
    }

    fn decoder(&self, b: &Boundary) -> String {
        match b {
            Boundary::Nat => "dec_Nat".into(),
            Boundary::Bool => "dec_Bool".into(),
            Boundary::List(elem) => format!("dec_List({})", self.decoder(elem)),
            Boundary::Data(d) => format!("dec_{}", self.g.data(*d).name),
        }
    }

    fn encoder(&self, b: &Boundary) -> String {
        match b {
            Boundary::Nat => "enc_Nat".into(),
            Boundary::Bool => "enc_Bool".into(),
            Boundary::List(elem) => format!("enc_List({})", self.encoder(elem)),
            Boundary::Data(d) => format!("enc_{}", self.g.data(*d).name),
        }
    }

    fn field_boundaries(&self, d: DataId) -> Vec<Vec<(String, Boundary)>> {
        field_boundaries(self.g, d)
    }

    fn codecs(&self, d: DataId) -> String {
        let data = self.g.data(d);
        let name = &data.name;
        let mut dec = format!(
            "\nfunction dec_{name}(x, path, inside = new Set()) {{\n  if (typeof x !== \"object\" || x === null) {{\n    throw new StitchwortInputError(`${{path}}: expected a {name} object`);\n  }}\n  enter(x, path, inside);\n  const tag = x.tag;\n  switch (tag) {{\n"
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
                    "      const {f} = {}(x.{f}, `${{path}}.{f}`, inside);",
                    self.decoder(b)
                );
                built.push(f.clone());
                encoded.push(format!("{f}: {}(v.{f})", self.encoder(b)));
            }
            let _ = writeln!(
                dec,
                "      inside.delete(x);\n      return {{ {} }};\n    }}",
                built.join(", ")
            );
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
            Boundary::Bool => "boolean".into(),
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

/// The type of parameter `i` as written in a signature (before evaluation).
fn written_param_type(ty: &Term, i: usize) -> Option<&Term> {
    let mut ty = ty.strip_loc();
    for _ in 0..i {
        let Term::Pi(_, _, _, cod) = ty else {
            return None;
        };
        ty = cod.strip_loc();
    }
    match ty {
        Term::Pi(_, _, dom, _) => Some(dom),
        _ => None,
    }
}

/// Which definitions the given ones use, directly or indirectly. What an
/// `opaque` definition's body uses doesn't count: an erased one (a proof or a
/// type) or a natively implemented one.
fn reachable(
    g: &Globals,
    roots: impl IntoIterator<Item = DefId>,
    opaque: impl Fn(DefId) -> bool,
) -> Vec<bool> {
    fn visit(term: &Term, found: &mut Vec<DefId>) {
        match term {
            Term::Def(id) => found.push(*id),
            Term::Var(_) | Term::Nat(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => {}
            Term::Data(_, args) | Term::Ctor(_, _, args) => {
                args.iter().for_each(|a| visit(a, found))
            }
            Term::Pi(_, _, a, b) | Term::App(a, b, _) | Term::Ann(a, b) => {
                visit(a, found);
                visit(b, found);
            }
            Term::Lam(_, _, b) | Term::Loc(_, b) => visit(b, found),
            Term::Case(_, _, branches) => branches.iter().for_each(|b| visit(&b.body, found)),
            Term::Eq(t, a, b) => {
                t.iter().for_each(|t| visit(t, found));
                visit(a, found);
                visit(b, found);
            }
            Term::J(m, b, p) => {
                visit(m, found);
                visit(b, found);
                visit(p, found);
            }
        }
    }
    let mut used = vec![false; g.defs.len()];
    let mut stack: Vec<DefId> = roots.into_iter().collect();
    while let Some(id) = stack.pop() {
        if std::mem::replace(&mut used[id.0], true) {
            continue;
        }
        let def = g.def(id);
        if let Some(body) = &def.body
            && !opaque(id)
        {
            visit(body, &mut stack);
        }
        for validator in &def.validators {
            visit(&validator.decision, &mut stack);
        }
    }
    used
}

/// JS for a prelude definition with a native implementation (see
/// `stitchwort_core::native`). Like the evaluator's, these are trusted, and
/// tested against the definitions they replace.
fn native_js(op: native::Native) -> &'static str {
    use native::Native;
    match op {
        Native::Add => "(m) => (n) => m + n",
        Native::Sub => "(m) => (n) => (m >= n ? m - n : 0n)",
        Native::Mul => "(m) => (n) => m * n",
        Native::Leq => "(m) => (n) => ({ tag: m <= n ? \"True\" : \"False\" })",
        Native::EqNat => "(m) => (n) => ({ tag: m === n ? \"True\" : \"False\" })",
        Native::DivFuel => {
            "(fuel) => (n) => (d) => { if (d === 0n) return fuel; const q = n / d; return q < fuel ? q : fuel; }"
        }
        Native::DecEqNat => "(m) => (n) => ({ tag: m === n ? \"Yes\" : \"No\" })",
        // A proof, so it's erased and never emitted.
        Native::EqNatRefl => "undefined",
    }
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
        (Boundary::Bool, Value::Ctor(_, c, _)) => Ok((*c == 1).to_string()),
        (Boundary::Nat, _) => match native::as_nat(g, value) {
            Some(n) => Ok(format!("{n}n")),
            None => Err(stuck()),
        },
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
            let boundaries = &field_boundaries(g, *d)[*c];
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

#[cfg(test)]
mod tests {
    use super::is_js_identifier;

    #[test]
    fn recognises_javascript_identifiers() {
        for ok in ["f", "appendNats", "_private", "$x", "x1", "a_b$c"] {
            assert!(is_js_identifier(ok), "{ok}");
        }
        for bad in ["", "1x", "x'", "x-y", "x y", "é"] {
            assert!(!is_js_identifier(bad), "{bad}");
        }
    }
}
