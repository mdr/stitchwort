//! JavaScript extraction (DESIGN.md §12): erase types and proofs, generate an
//! ES module, and wrap each export in decode → compute → encode.
//!
//! First-milestone scope: exports take and return concrete first-order data
//! (`Nat`, `Bool`, `Text`, `Char`, `List`, and data types built from them,
//! such as `Maybe Text`), and their proof arguments are checked at runtime.

use std::cell::Cell;
use std::collections::HashSet;
use std::fmt::Write;

use stitchwort_core::check::{is_type_former, telescope};
use stitchwort_core::native;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{Head, eval};
use stitchwort_core::{DataId, DefId, Globals, Limits, ResourceError, Sort, Term, Value, pretty};
use stitchwort_syntax::Diagnostic;

/// Generating code recurses over a definition's body, so each level checks
/// there's stack left first (docs/proposals/stack-safe-evaluation.md).
type Fallible<T> = Result<T, ResourceError>;
const PASS: &str = "JavaScript generator";

/// How a type crosses the JS boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Boundary {
    /// `bigint`, non-negative.
    Nat,
    /// `boolean`.
    Bool,
    /// `string`, well-formed (no lone surrogates).
    Text,
    /// `string`, holding exactly one Unicode scalar value.
    Char,
    /// `readonly T[]`.
    List(Box<Boundary>),
    /// A tagged object union, with the type's arguments if it has parameters.
    Data(DataId, Vec<Boundary>),
    /// Parameter `i` of the data type whose codec this is: only inside a
    /// codec, which takes its parameters' codecs as arguments.
    Param(usize),
}

impl Boundary {
    /// Replaces each [`Boundary::Param`] with the corresponding argument.
    #[must_use]
    pub fn instantiate(&self, args: &[Boundary]) -> Boundary {
        match self {
            Boundary::Param(i) => args[*i].clone(),
            Boundary::List(elem) => Boundary::List(Box::new(elem.instantiate(args))),
            Boundary::Data(d, own) => {
                Boundary::Data(*d, own.iter().map(|b| b.instantiate(args)).collect())
            }
            other => other.clone(),
        }
    }
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
    let tel = telescope(g, &def.ty_value, def.span)?;
    if tel.result_erased {
        return Err(refuse(
            "it's a proof or a type, so it has no runtime value".into(),
        ));
    }
    // Prefer the names from the signature, then from the equations.
    let equation_names = lam_names(def.body.as_deref());
    let mut params = Vec::new();
    let mut param_positions = Vec::new();
    let mut checks = Vec::new();
    for (i, (x, ty, erased)) in tel.params.iter().enumerate() {
        if *erased && is_type_former(g, i, ty)? {
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
        let boundary = boundary(g, ty, 0, &mut HashSet::new())
            .map_err(|why| refuse(format!("parameter `{x}`: {why}")))?;
        let js_name = [Some(&**x), equation_names.get(i).map(|n| &**n)]
            .into_iter()
            .flatten()
            .find(|n| is_js_identifier(n) && *n != "_" && !n.starts_with("arg"))
            .map_or_else(|| format!("arg{i}"), str::to_string);
        params.push((js_name, boundary));
        param_positions.push(i);
    }
    let result = boundary(g, &tel.result, 0, &mut HashSet::new())
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

/// How `ty` crosses the boundary. Inside a data type's codec, its first
/// `params` variables are the type's parameters.
fn boundary(
    g: &Globals,
    ty: &Value,
    params: usize,
    visiting: &mut HashSet<DataId>,
) -> Result<Boundary, String> {
    let cannot = |ty: &Value| {
        format!(
            "`{}` can't cross the JS boundary yet",
            pretty::value(g, &[], ty)
        )
    };
    match ty {
        Value::Neutral(Head::Var(level), elims) if elims.is_empty() && *level < params => {
            Ok(Boundary::Param(*level))
        }
        Value::Data(d, args) => {
            let data = g.data(*d);
            match (&*data.name, args.as_slice()) {
                ("Nat", []) => Ok(Boundary::Nat),
                ("Bool", []) => Ok(Boundary::Bool),
                // Prelude names can't be redefined, so these are the prelude's.
                ("Text", []) => Ok(Boundary::Text),
                ("Char", []) => Ok(Boundary::Char),
                ("List", [elem]) => Ok(Boundary::List(Box::new(boundary(
                    g, elem, params, visiting,
                )?))),
                _ if data.sort != Sort::Prop => {
                    let args = args
                        .iter()
                        .map(|arg| boundary(g, arg, params, visiting))
                        .collect::<Result<Vec<_>, _>>()?;
                    check_codec(g, *d, visiting)?;
                    Ok(Boundary::Data(*d, args))
                }
                _ => Err(cannot(ty)),
            }
        }
        Value::Pi(..) => Err("functions can't cross the JS boundary yet".into()),
        other => Err(cannot(other)),
    }
}

/// Whether a data type can have a codec: its parameters are types, and its
/// fields all cross the boundary, whatever data the parameters stand for.
/// The codec of a type with parameters takes their codecs as arguments, as
/// `dec_List` does.
fn check_codec(g: &Globals, d: DataId, visiting: &mut HashSet<DataId>) -> Result<(), String> {
    if !visiting.insert(d) {
        return Ok(());
    }
    let data = g.data(d);
    let mut env = Vec::new();
    for (x, ty) in &data.params {
        if !matches!(
            eval(g, &env, ty).expect(OUTSIDE_LIMITS),
            Value::Sort(Sort::Type(_))
        ) {
            return Err(format!(
                "`{}`'s parameter `{x}` isn't a type, which can't cross the JS boundary yet",
                data.name
            ));
        }
        env.push(Value::var(env.len()));
    }
    for (ctor, fields) in data.ctors.iter().zip(data_fields(g, d)) {
        if ctor.field_erased.iter().any(|e| *e) {
            return Err(format!(
                "`{}` has a proof or type field, which can't be checked at the boundary yet",
                data.name
            ));
        }
        for (_, field_ty) in fields {
            boundary(g, &field_ty, data.params.len(), visiting)?;
        }
    }
    Ok(())
}

/// Field names and types of each constructor of a data type, with its
/// parameters as the first variables.
fn data_fields(g: &Globals, d: DataId) -> Vec<Vec<(String, Value)>> {
    let data = g.data(d);
    data.ctors
        .iter()
        .map(|ctor| {
            let mut env: Vec<Value> = (0..data.params.len()).map(Value::var).collect();
            ctor.fields
                .iter()
                .map(|(name, ty)| {
                    let value = eval(g, &env, ty).expect(OUTSIDE_LIMITS);
                    env.push(Value::var(env.len()));
                    (name.to_string(), value)
                })
                .collect()
        })
        .collect()
}

/// For each constructor of a data type that crosses the boundary, its fields'
/// names and boundary types, for the given arguments of its parameters.
pub fn field_boundaries(g: &Globals, d: DataId, args: &[Boundary]) -> Vec<Vec<(String, Boundary)>> {
    generic_field_boundaries(g, d)
        .into_iter()
        .map(|fields| {
            fields
                .into_iter()
                .map(|(name, b)| (name, b.instantiate(args)))
                .collect()
        })
        .collect()
}

/// [`field_boundaries`] with the parameters left as [`Boundary::Param`].
fn generic_field_boundaries(g: &Globals, d: DataId) -> Vec<Vec<(String, Boundary)>> {
    let params = g.data(d).params.len();
    data_fields(g, d)
        .into_iter()
        .map(|fields| {
            fields
                .into_iter()
                .map(|(name, ty)| {
                    let b = boundary(g, &ty, params, &mut HashSet::new())
                        .expect("checked by exportable");
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
/// It's one operation, using at most `limits.stack` bytes of stack: a
/// definition nested too deeply for that is an `E-RESOURCE` error.
pub fn generate(g: &Globals, limits: Limits) -> Result<Output, Diagnostic> {
    let _op = g.budget.operation(Limits::stack_only(limits.stack));
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

    let codegen = Gen::new(g)?;
    let mut js = String::from(RUNTIME);
    for &d in &boundary_datas {
        js.push_str(&codegen.codecs(d));
    }
    js.push('\n');
    // Only what the exports use, in declaration order (which is dependency order).
    let used = reachable(g, exports.iter().map(|sig| sig.id), |id| {
        codegen.erased[id.0].0 || g.builtins.native(id).is_some()
    });
    let while_generating = |id: DefId| {
        move |e: ResourceError| {
            Diagnostic::from(e).with_label(g.def(id).span, "while generating JavaScript for this")
        }
    };
    for id in (0..g.defs.len()).map(DefId).filter(|id| used[id.0]) {
        js.push_str(&codegen.def(id).map_err(while_generating(id))?);
    }
    for sig in &exports {
        js.push_str(&codegen.wrapper(sig).map_err(while_generating(sig.id))?);
    }

    let mut dts = String::from(
        "// Generated by stitchwort. Do not edit.\n\nexport declare class StitchwortInputError extends Error {}\nexport declare class StitchwortResourceError extends Error {}\n",
    );
    for &d in &boundary_datas {
        dts.push_str(&codegen.ts_alias(d));
    }
    for sig in &exports {
        let params: Vec<String> = sig
            .params
            .iter()
            .map(|(x, b)| format!("{x}: {}", codegen.ts_type(b, true, &[])))
            .collect();
        let _ = writeln!(
            dts,
            "export declare function {}({}): {};",
            sig.name,
            params.join(", "),
            codegen.ts_type(&sig.result, false, &[])
        );
    }
    Ok(Output { js, dts })
}

fn collect_datas(g: &Globals, b: &Boundary, out: &mut Vec<DataId>) {
    match b {
        Boundary::Nat | Boundary::Bool | Boundary::Text | Boundary::Char | Boundary::Param(_) => {}
        Boundary::List(elem) => collect_datas(g, elem, out),
        Boundary::Data(d, args) => {
            for arg in args {
                collect_datas(g, arg, out);
            }
            if out.contains(d) {
                return;
            }
            out.push(*d);
            for fields in generic_field_boundaries(g, *d) {
                for (_, b) in fields {
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

// Thrown when an export runs out of the JS engine's stack (recursion over a
// long text or list, or deeply nested data), or a number or string grows too
// large for it. The engine's own error is its `cause`.
export class StitchwortResourceError extends Error {
  constructor(message, options) {
    super(message, options);
    this.name = "StitchwortResourceError";
  }
}

// V8 and JavaScriptCore throw a `RangeError` when the stack overflows, and
// SpiderMonkey an `InternalError`. Nothing else in generated code throws
// either, but a too-large `BigInt` or string is a `RangeError` too.
const outOfResources = (name, e) =>
  e instanceof RangeError || (e instanceof Error && e.name === "InternalError")
    ? new StitchwortResourceError(
        `${name}: ran out of resources (${e.message}); the input may be too large`,
        { cause: e },
      )
    : e;

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

// `Text` is a string. Decoding takes its Unicode scalar values in order, and
// refuses a string with a lone surrogate (which JS allows) rather than
// repairing it, so encoding gives back exactly the string that was decoded.
const scalars = (x, path) => {
  if (typeof x !== "string") {
    throw new StitchwortInputError(`${path}: expected a string`);
  }
  const codes = [];
  for (let i = 0; i < x.length; i++) {
    const unit = x.charCodeAt(i);
    if (unit < 0xd800 || unit > 0xdfff) {
      codes.push(BigInt(unit));
      continue;
    }
    const low = i + 1 < x.length ? x.charCodeAt(i + 1) : 0;
    if (unit > 0xdbff || low < 0xdc00 || low > 0xdfff) {
      const hex = unit.toString(16).toUpperCase();
      throw new StitchwortInputError(
        `${path}: a lone surrogate (U+${hex}) at index ${i}; text must be a well-formed string`,
      );
    }
    codes.push(BigInt(0x10000 + ((unit - 0xd800) << 10) + (low - 0xdc00)));
    i++;
  }
  return codes;
};
const dec_Text = (x, path) => {
  const codes = scalars(x, path);
  let chars = { tag: "Nil" };
  for (let i = codes.length - 1; i >= 0; i--) {
    chars = { tag: "Cons", head: { tag: "MkChar", code: codes[i] }, tail: chars };
  }
  return { tag: "MkText", chars };
};
const enc_Text = (v) => {
  const parts = [];
  for (let l = v.chars; l.tag === "Cons"; l = l.tail) parts.push(enc_Char(l.head));
  return parts.join("");
};

// `Char` is a string holding exactly one scalar value: one or two UTF-16
// code units.
const dec_Char = (x, path) => {
  const codes = scalars(x, path);
  if (codes.length !== 1) {
    throw new StitchwortInputError(
      `${path}: expected exactly one character, but the string has ${codes.length}`,
    );
  }
  return { tag: "MkChar", code: codes[0] };
};
const enc_Char = (v) => String.fromCodePoint(Number(v.code));

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
    /// The prelude's `ifThenElse`, which `if` becomes.
    if_then_else: Option<DefId>,
}

/// The definition being generated, for turning calls to itself in tail
/// position into another turn of a loop. JS engines don't eliminate tail
/// calls, so otherwise each would use a stack frame.
struct SelfCall {
    id: DefId,
    /// Whether any call was turned into a loop.
    used: Cell<bool>,
}

impl<'g> Gen<'g> {
    fn new(g: &'g Globals) -> Result<Self, Diagnostic> {
        let erased = g
            .defs
            .iter()
            .map(|def| {
                let tel = telescope(g, &def.ty_value, def.span)?;
                let mask = tel
                    .params
                    .iter()
                    .take(def.arity)
                    .map(|(_, _, erased)| *erased)
                    .collect();
                Ok((tel.result_erased, mask))
            })
            .collect::<Result<_, Diagnostic>>()?;
        Ok(Gen {
            g,
            nat: g.find_data("Nat"),
            erased,
            if_then_else: g
                .defs
                .iter()
                .position(|def| &*def.name == "ifThenElse")
                .map(DefId),
        })
    }

    fn def(&self, id: DefId) -> Fallible<String> {
        let def = self.g.def(id);
        let (erased, mask) = &self.erased[id.0];
        let Some(body) = &def.body else {
            return Ok(String::new());
        };
        if *erased {
            return Ok(String::new());
        }
        if let Some(op) = self.g.builtins.native(id) {
            return Ok(format!(
                "const {} = {};\n",
                def_name(&def.name),
                native_js(op)
            ));
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
            if !params.is_empty()
                && let Some(block) = self.self_tail_loop(id, tree, &mut env)?
            {
                return Ok(format!(
                    "const {} = {params}{block};\n",
                    def_name(&def.name)
                ));
            }
            let block = self.tree(tree, &mut env, 1, None)?;
            if params.is_empty() {
                // No runtime parameters, but a case on an erased proof (like
                // `absurd`): a function, so it only runs when it's used.
                format!("() => {{\n{block}}}")
            } else {
                format!("{{\n{block}}}")
            }
        } else {
            let rhs = self.expr(tree, &mut env)?;
            // An object literal after `=>` needs parentheses.
            if !params.is_empty() && rhs.starts_with('{') {
                format!("({rhs})")
            } else {
                rhs
            }
        };
        Ok(format!("const {} = {params}{rhs};\n", def_name(&def.name)))
    }

    /// If the definition `id`, with case tree `tree`, calls itself in tail
    /// position, its body as a loop, where each such call is another turn:
    ///
    /// ```js
    /// {
    ///   let s0 = v0, s1 = v1;
    ///   for (;;) {
    ///     const v0 = s0, v1 = s1;
    ///     … s0 = next0; s1 = next1; continue; …
    ///   }
    /// }
    /// ```
    ///
    /// Each turn has its own `const`s, so a closure made in one turn keeps
    /// that turn's values, and the parameters themselves are never assigned,
    /// so a partial application can be called again.
    fn self_tail_loop(
        &self,
        id: DefId,
        tree: &Term,
        env: &mut Vec<bool>,
    ) -> Fallible<Option<String>> {
        let call = SelfCall {
            id,
            used: Cell::new(false),
        };
        let block = self.tree(tree, env, 2, Some(&call))?;
        if !call.used.get() {
            return Ok(None);
        }
        let slots: Vec<usize> = (0..env.len()).filter(|level| !env[*level]).collect();
        let copy = |from: fn(usize) -> String, to: fn(usize) -> String| {
            slots
                .iter()
                .map(|level| format!("{} = {}", to(*level), from(*level)))
                .collect::<Vec<_>>()
                .join(", ")
        };
        Ok(Some(format!(
            "{{\n  let {};\n  for (;;) {{\n    const {};\n{block}  }}\n}}",
            copy(var, slot),
            copy(slot, var)
        )))
    }

    /// Statements for a case tree, ending in `return` (or, for a call to
    /// `self_call` in tail position, `continue`). `env` says, for each
    /// variable level, whether it's erased.
    fn tree(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        depth: usize,
        self_call: Option<&SelfCall>,
    ) -> Fallible<String> {
        self.g.budget.nesting(PASS)?;
        let pad = "  ".repeat(depth);
        let Term::Case(ix, d, branches) = term.strip_loc() else {
            return match self_call {
                Some(call) => self.tail(term, env, depth, call),
                None => Ok(format!("{pad}return {};\n", self.expr(term, env)?)),
            };
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
            out.push_str(&self.tree(&b.body, env, depth, self_call)?);
            env.truncate(level);
            Ok(())
        };
        if data.sort == Sort::Prop {
            // The proof doesn't exist at runtime. Matching on it into data is
            // only allowed for at most one constructor with only proof fields.
            match branches.first() {
                Some(b) => branch(&mut out, 0, b, depth)?,
                None => {
                    let _ = writeln!(out, "{pad}throw new Error(\"unreachable\");");
                }
            }
        } else if Some(*d) == self.nat {
            let _ = writeln!(out, "{pad}if ({scrutinee} === 0n) {{");
            branch(&mut out, 0, &branches[0], depth + 1)?;
            let _ = writeln!(out, "{pad}}} else {{");
            let _ = writeln!(out, "{pad}  const {predecessor} = {scrutinee} - 1n;");
            branch(&mut out, 1, &branches[1], depth + 1)?;
            let _ = writeln!(out, "{pad}}}");
        } else {
            let _ = writeln!(out, "{pad}switch ({scrutinee}.tag) {{");
            for (c, b) in branches.iter().enumerate() {
                let _ = writeln!(out, "{pad}  case \"{}\": {{", data.ctors[c].name);
                branch(&mut out, c, b, depth + 2)?;
                let _ = writeln!(out, "{pad}  }}");
            }
            let _ = writeln!(out, "{pad}}}");
            let _ = writeln!(out, "{pad}throw new Error(\"unreachable\");");
        }
        Ok(out)
    }

    /// A leaf of the case tree of a definition that's being made a loop
    /// ([`Gen::self_tail_loop`]). A call to itself with all its arguments is
    /// another turn. `if` is written out as a JS `if`, so that calls in its
    /// branches are in tail position too.
    fn tail(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        depth: usize,
        call: &SelfCall,
    ) -> Fallible<String> {
        self.g.budget.nesting(PASS)?;
        let pad = "  ".repeat(depth);
        let (head, args) = term.spine();
        let Term::Def(id) = head else {
            return Ok(format!("{pad}return {};\n", self.expr(term, env)?));
        };
        if *id == call.id && args.len() == self.g.def(*id).arity {
            call.used.set(true);
            let mut out = String::new();
            for (level, arg) in args.iter().enumerate() {
                if !env[level] {
                    let _ = writeln!(out, "{pad}{} = {};", slot(level), self.expr(arg, env)?);
                }
            }
            let _ = writeln!(out, "{pad}continue;");
            return Ok(out);
        }
        if Some(*id) == self.if_then_else
            && let [_, cond, then, otherwise] = args.as_slice()
            && let (Term::Lam(_, _, then), Term::Lam(_, _, otherwise)) =
                (then.strip_loc(), otherwise.strip_loc())
        {
            let cond = self.expr(cond, env)?;
            // The branches' parameter is a proof of `Unit`, so it's erased.
            let mut branch = |body: &Term| -> Fallible<String> {
                env.push(true);
                let out = self.tail(body, env, depth + 1, call);
                env.pop();
                out
            };
            let then = branch(then)?;
            let otherwise = branch(otherwise)?;
            return Ok(format!(
                "{pad}if ({cond}.tag === \"True\") {{\n{then}{pad}}} else {{\n{otherwise}{pad}}}\n"
            ));
        }
        Ok(format!("{pad}return {};\n", self.expr(term, env)?))
    }

    fn expr(&self, term: &Term, env: &mut Vec<bool>) -> Fallible<String> {
        self.g.budget.nesting(PASS)?;
        Ok(match term {
            Term::Loc(_, t) | Term::Ann(t, _) => self.expr(t, env)?,
            Term::Var(ix) => {
                let level = env.len() - 1 - ix;
                if env[level] {
                    "undefined".into()
                } else {
                    var(level)
                }
            }
            Term::Def(id) => self.def_ref(*id, &[], env)?,
            Term::Nat(n) => format!("{n}n"),
            Term::App(..) => {
                let (head, args) = term.spine();
                if let Term::Def(id) = head {
                    return self.def_ref(*id, &args, env);
                }
                let mut out = format!("({})", self.expr(head, env)?);
                for arg in args {
                    let _ = write!(out, "({})", self.expr(arg, env)?);
                }
                out
            }
            Term::Lam(_, _, body) => {
                let level = env.len();
                env.push(false);
                let body = self.expr(body, env)?;
                env.pop();
                // An object literal as an arrow function's body needs
                // parentheses, or it's read as a block.
                if body.starts_with('{') {
                    format!("(({}) => ({body}))", var(level))
                } else {
                    format!("(({}) => {body})", var(level))
                }
            }
            Term::Ctor(d, c, args) => {
                let data = self.g.data(*d);
                if data.sort == Sort::Prop {
                    return Ok("undefined".into());
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
                    return Ok(match (inner.strip_loc(), count) {
                        (Term::Ctor(_, 0, _), n) => format!("{n}n"),
                        (Term::Nat(k), n) => format!("{}n", &**k + n),
                        (_, n) => format!("({} + {n}n)", self.expr(inner, env)?),
                    });
                }
                let ctor = &data.ctors[*c];
                let mut fields = vec![format!("tag: \"{}\"", ctor.name)];
                for (((field, _), erased), arg) in
                    ctor.fields.iter().zip(&ctor.field_erased).zip(args)
                {
                    if !erased {
                        fields.push(format!("{}: {}", js_field(field), self.expr(arg, env)?));
                    }
                }
                format!("{{ {} }}", fields.join(", "))
            }
            // Proofs are erased, and transport along an equality does nothing.
            Term::J(_, base, _) => self.expr(base, env)?,
            Term::Data(..) | Term::Sort(_) | Term::Pi(..) | Term::Eq(..) | Term::Refl => {
                "undefined".into()
            }
            Term::Case(..) => panic!("internal error: case outside a case tree"),
            Term::Meta(_) => {
                panic!("internal error: unsolved metavariable in a checked definition")
            }
        })
    }

    /// A call to a definition, leaving out its erased arguments.
    fn def_ref(&self, id: DefId, args: &[&Term], env: &mut Vec<bool>) -> Fallible<String> {
        let (erased, mask) = &self.erased[id.0];
        if *erased {
            return Ok("undefined".into());
        }
        let mut out = def_name(&self.g.def(id).name);
        if self.is_thunk(id) {
            out.push_str("()");
        }
        for (i, arg) in args.iter().enumerate() {
            if !mask.get(i).copied().unwrap_or(false) {
                let _ = write!(out, "({})", self.expr(arg, env)?);
            }
        }
        Ok(out)
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
    /// call the compiled definition, encode the result. Running out of stack
    /// on the way is a `StitchwortResourceError`. Decoded parameter `i`
    /// (counting all parameters) is `v{i}`, which is what the compiled checks
    /// refer to.
    fn wrapper(&self, sig: &ExportSig) -> Fallible<String> {
        let params: Vec<&str> = sig.params.iter().map(|(x, _)| x.as_str()).collect();
        let mut out = format!(
            "\nexport function {}({}) {{\n  try {{\n",
            sig.name,
            params.join(", ")
        );
        let mut call = def_name(&self.g.def(sig.id).name);
        for ((x, b), position) in sig.params.iter().zip(&sig.param_positions) {
            let _ = writeln!(
                out,
                "    const {} = {}({x}, \"{x}\");",
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
            let decision = self.expr(&check.decision, &mut env)?;
            let message = format!("precondition `{}` doesn't hold", check.description)
                .replace('\\', "\\\\")
                .replace('"', "\\\"");
            let _ = writeln!(
                out,
                "    if ({decision}.tag !== \"{yes}\") {{\n      throw new StitchwortInputError(\"{message}\");\n    }}"
            );
        }
        let _ = writeln!(
            out,
            "    return {}({call});\n  }} catch (e) {{\n    throw outOfResources(\"{}\", e);\n  }}\n}}",
            self.encoder(&sig.result),
            sig.name
        );
        Ok(out)
    }

    /// The tag of `Decidable`'s first constructor (`Yes`).
    fn decision_yes_tag(&self) -> String {
        self.g.find_data("Decidable").map_or_else(
            || "Yes".into(),
            |d| self.g.data(d).ctors[0].name.to_string(),
        )
    }

    fn decoder(&self, b: &Boundary) -> String {
        self.codec("dec", b)
    }

    fn encoder(&self, b: &Boundary) -> String {
        self.codec("enc", b)
    }

    /// The decoder (`dec`) or encoder (`enc`) for a boundary type. A codec
    /// for a type with arguments is applied to theirs.
    fn codec(&self, kind: &str, b: &Boundary) -> String {
        match b {
            Boundary::Nat => format!("{kind}_Nat"),
            Boundary::Bool => format!("{kind}_Bool"),
            Boundary::Text => format!("{kind}_Text"),
            Boundary::Char => format!("{kind}_Char"),
            Boundary::List(elem) => format!("{kind}_List({})", self.codec(kind, elem)),
            Boundary::Data(d, args) if args.is_empty() => {
                format!("{kind}_{}", self.g.data(*d).name)
            }
            Boundary::Data(d, args) => {
                let args: Vec<String> = args.iter().map(|a| self.codec(kind, a)).collect();
                format!("{kind}_{}({})", self.g.data(*d).name, args.join(", "))
            }
            Boundary::Param(i) => codec_param(*i),
        }
    }

    /// The decoder and encoder for a data type. With parameters, each takes
    /// the parameters' codecs and returns the codec.
    fn codecs(&self, d: DataId) -> String {
        let data = self.g.data(d);
        let name = &data.name;
        let (dec_head, enc_head, end) = if data.params.is_empty() {
            (
                format!("function dec_{name}(x, path, inside = new Set()) {{"),
                format!("function enc_{name}(v) {{"),
                "}",
            )
        } else {
            let ps: Vec<String> = (0..data.params.len()).map(codec_param).collect();
            let ps = ps.join(", ");
            (
                format!("const dec_{name} = ({ps}) => function (x, path, inside = new Set()) {{"),
                format!("const enc_{name} = ({ps}) => function (v) {{"),
                "};",
            )
        };
        let mut dec = format!(
            "\n{dec_head}\n  if (typeof x !== \"object\" || x === null) {{\n    throw new StitchwortInputError(`${{path}}: expected a {name} object`);\n  }}\n  enter(x, path, inside);\n  const tag = x.tag;\n  switch (tag) {{\n"
        );
        let mut enc = format!("{enc_head}\n  switch (v.tag) {{\n");
        for (ctor, fields) in data.ctors.iter().zip(generic_field_boundaries(self.g, d)) {
            let _ = writeln!(dec, "    case \"{}\": {{", ctor.name);
            let mut built = vec![format!("tag: \"{}\"", ctor.name)];
            let mut encoded = built.clone();
            for (field, b) in &fields {
                let f = js_field(field);
                // `$` keeps a field called `x` or `path` from hiding the
                // decoder's own variables. (Stitchwort names can't start
                // with `$`.)
                let _ = writeln!(
                    dec,
                    "      const ${f} = {}(x.{f}, `${{path}}.{f}`, inside);",
                    self.decoder(b)
                );
                built.push(format!("{f}: ${f}"));
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
            "    default:\n      throw new StitchwortInputError(`${{path}}: unknown tag ${{String(tag)}}`);\n  }}\n{end}"
        );
        let _ = writeln!(enc, "  }}\n  throw new Error(\"unreachable\");\n{end}");
        dec + &enc
    }

    /// Inputs are `readonly`; outputs are freshly built, so they're mutable.
    /// `params` names a data type's parameters, inside its alias.
    fn ts_type(&self, b: &Boundary, readonly: bool, params: &[String]) -> String {
        match b {
            Boundary::Nat => "bigint".into(),
            Boundary::Bool => "boolean".into(),
            Boundary::Text | Boundary::Char => "string".into(),
            Boundary::List(elem) if readonly => {
                format!("readonly {}[]", self.ts_type(elem, true, params))
            }
            Boundary::List(elem) => format!("{}[]", self.ts_type(elem, false, params)),
            Boundary::Data(d, args) if args.is_empty() => self.g.data(*d).name.to_string(),
            Boundary::Data(d, args) => {
                let args: Vec<String> = args
                    .iter()
                    .map(|a| self.ts_type(a, readonly, params))
                    .collect();
                format!("{}<{}>", self.g.data(*d).name, args.join(", "))
            }
            Boundary::Param(i) => params[*i].clone(),
        }
    }

    fn ts_alias(&self, d: DataId) -> String {
        let data = self.g.data(d);
        let params = self.ts_params(d);
        let variants: Vec<String> = data
            .ctors
            .iter()
            .zip(generic_field_boundaries(self.g, d))
            .map(|(ctor, fields)| {
                let mut parts = vec![format!("readonly tag: \"{}\"", ctor.name)];
                for (field, b) in &fields {
                    parts.push(format!(
                        "readonly {}: {}",
                        js_field(field),
                        self.ts_type(b, true, &params)
                    ));
                }
                format!("{{ {} }}", parts.join("; "))
            })
            .collect();
        let generics = if params.is_empty() {
            String::new()
        } else {
            format!("<{}>", params.join(", "))
        };
        format!(
            "export type {}{generics} =\n  | {};\n",
            data.name,
            variants.join("\n  | ")
        )
    }

    /// TypeScript names for a data type's parameters: their own names where
    /// those can't be mistaken for anything else, otherwise `$0`, `$1`, …
    /// (Stitchwort names can't start with `$`.)
    fn ts_params(&self, d: DataId) -> Vec<String> {
        const TS_TYPE_WORDS: &[&str] = &[
            "any",
            "bigint",
            "boolean",
            "never",
            "null",
            "number",
            "object",
            "string",
            "symbol",
            "undefined",
            "unknown",
            "void",
        ];
        let data = self.g.data(d);
        data.params
            .iter()
            .enumerate()
            .map(|(i, (x, _))| {
                let clear = is_js_identifier(x)
                    && !TS_TYPE_WORDS.contains(&&**x)
                    && self.g.find_data(x).is_none()
                    && data.params[..i].iter().all(|(y, _)| y != x);
                if clear {
                    x.to_string()
                } else {
                    format!("${i}")
                }
            })
            .collect()
    }
}

/// The name of a codec's argument: the codec for its type's parameter `i`.
fn codec_param(i: usize) -> String {
    format!("${i}")
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
        found.extend(term.subterms().filter_map(|(t, _)| match t {
            Term::Def(id) => Some(*id),
            _ => None,
        }));
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

/// Where a loop keeps parameter `level`'s value for its next turn.
fn slot(level: usize) -> String {
    format!("s{level}")
}

fn def_name(name: &str) -> String {
    // Primes become `$`; the dot in a generated name like `State.elim`
    // becomes `$$` (source names can't contain dots).
    format!("${}", name.replace('\'', "$").replace('.', "$$"))
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

/// Extraction runs on checked definitions, with no limit but the stack's
/// (see [`generate`]), so evaluating their types can't run out.
const OUTSIDE_LIMITS: &str = "internal error: evaluating a checked type ran out of resources";

/// A JS expression for `value`, encoded as it would cross the boundary. Used by
/// differential tests to compare the reference evaluator with generated JS.
pub fn boundary_literal(g: &Globals, b: &Boundary, value: &Value) -> Result<String, String> {
    let stuck = || format!("not a fully evaluated value: {value:?}");
    match (b, value) {
        (Boundary::Bool, Value::Ctor(_, c, _)) => Ok((*c == 1).to_string()),
        (Boundary::Nat, _) => match native::as_nat(g, value).map_err(|e| e.to_string())? {
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
        (Boundary::Char, _) => {
            let c = char_value(g, value)?.ok_or_else(stuck)?;
            Ok(js_string_literal(&c.to_string()))
        }
        (Boundary::Text, Value::Ctor(_, 0, fields)) => {
            let mut text = String::new();
            let mut v = &fields[0];
            loop {
                match v {
                    Value::Ctor(_, 0, _) => return Ok(js_string_literal(&text)),
                    Value::Ctor(_, 1, fields) => {
                        text.push(char_value(g, &fields[0])?.ok_or_else(stuck)?);
                        v = &fields[1];
                    }
                    _ => return Err(stuck()),
                }
            }
        }
        (Boundary::Data(d, args), Value::Ctor(_, c, fields)) => {
            let ctor = &g.data(*d).ctors[*c];
            let boundaries = &field_boundaries(g, *d, args)[*c];
            let mut parts = vec![format!("tag: \"{}\"", ctor.name)];
            for ((name, b), field) in boundaries.iter().zip(fields.iter()) {
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

/// The character a `Char` value stands for.
fn char_value(g: &Globals, value: &Value) -> Result<Option<char>, String> {
    let Value::Ctor(_, 0, fields) = value else {
        return Ok(None);
    };
    let code = native::as_nat(g, &fields[0]).map_err(|e| e.to_string())?;
    Ok(code
        .and_then(|n| u32::try_from(n).ok())
        .and_then(char::from_u32))
}

/// A JS string literal for `text`, with everything but printable ASCII
/// escaped, so it reads the same whatever the file's encoding.
pub fn js_string_literal(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '"' | '\\' => {
                out.push('\\');
                out.push(c);
            }
            ' '..='~' => out.push(c),
            _ => {
                let _ = write!(out, "\\u{{{:x}}}", u32::from(c));
            }
        }
    }
    out.push('"');
    out
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
