//! JavaScript extraction (DESIGN.md §12): erase types and proofs, generate an
//! ES module, and wrap each export in decode → compute → encode.
//!
//! First-milestone scope: exports take and return concrete first-order data
//! (`Nat`, `Bool`, `Text`, `Char`, `List`, and data types built from them,
//! such as `Maybe Text`), and their proof arguments are checked at runtime.

use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use stitchwort_core::check::{is_type_former, telescope};
use stitchwort_core::hash::def_hash;
use stitchwort_core::native;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{Head, eval, expand_step};
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
    /// Parameter `i` of the data type whose fields these are: only in the
    /// description of a data type's fields, where `close` (in the runtime)
    /// replaces it with the type's argument.
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
    if JS_RESERVED.contains(&&*def.name) {
        return Err(refuse("its name is reserved in JavaScript".into()));
    }
    if MODULE_NAMES.contains(&&*def.name) {
        return Err(refuse(
            "the generated module exports something else with that name".into(),
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
        let js_name = [Some(&**x), equation_names.get(i).map(|n| &**n)]
            .into_iter()
            .flatten()
            .find(|n| {
                is_js_identifier(n)
                    && !JS_RESERVED.contains(n)
                    && *n != "_"
                    && !n.starts_with("arg")
            })
            .map_or_else(|| format!("arg{i}"), str::to_string);
        let boundary = boundary(g, ty, 0, &mut HashSet::new())
            .map_err(|why| refuse(format!("parameter `{js_name}`: {why}")))?;
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

/// How `ty` crosses the boundary. In a data type's fields' types, its first
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
/// A type with parameters is described once, and its fields' types are
/// filled in with its arguments as a value is decoded or encoded.
fn check_codec(g: &Globals, d: DataId, visiting: &mut HashSet<DataId>) -> Result<(), String> {
    if !visiting.insert(d) {
        return Ok(());
    }
    let data = g.data(d);
    if MODULE_NAMES.contains(&&*data.name) {
        return Err(format!(
            "`{}` is the name of something else the generated module exports",
            data.name
        ));
    }
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
    for (c, (ctor, fields)) in data.ctors.iter().zip(data_fields(g, d)).enumerate() {
        for (i, (field, _)) in ctor.fields.iter().enumerate() {
            if !ctor.field_erased[i] {
                continue;
            }
            // A record's proof field is established by its decision procedure
            // (docs/proposals/records.md §11.3).
            let proof = ctor.field_sorts[i] == Sort::Prop;
            let checked =
                data.record && proof && data.validators.iter().any(|v| v.ctor == c && v.field == i);
            if !checked {
                return Err(if data.record && proof {
                    format!(
                        "`{}`'s proof field `{field}` has no runtime check",
                        data.name
                    )
                } else if data.record {
                    format!(
                        "`{}`'s field `{field}` is a type, which can't cross the JS boundary",
                        data.name
                    )
                } else {
                    format!(
                        "`{}` has a proof or type field, which can't be checked at the boundary yet",
                        data.name
                    )
                });
            }
        }
        for (field, field_ty) in fields {
            boundary(g, &field_ty, data.params.len(), visiting)
                .map_err(|why| format!("`{}`'s field `{field}`: {why}", data.name))?;
        }
    }
    Ok(())
}

/// Names and types of the runtime fields (those not erased) of each
/// constructor of a data type, with its parameters as the first variables.
fn data_fields(g: &Globals, d: DataId) -> Vec<Vec<(String, Value)>> {
    let data = g.data(d);
    data.ctors
        .iter()
        .map(|ctor| {
            let mut env: Vec<Value> = (0..data.params.len()).map(Value::var).collect();
            let mut out = Vec::new();
            for ((name, ty), erased) in ctor.fields.iter().zip(&ctor.field_erased) {
                let value = eval(g, &env, ty).expect(OUTSIDE_LIMITS);
                env.push(Value::var(env.len()));
                if !erased {
                    out.push((name.to_string(), value));
                }
            }
            out
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

/// How the generated code represents things.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Options {
    /// A `Text` is a JS string, and the prelude's text operations are native
    /// JS (docs/proposals/compact-text.md, option A). Off, a `Text` is
    /// `MkText` of a cons list and every operation is compiled from its
    /// definition, as before: that's for differential tests of the natives.
    pub native_text: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options { native_text: true }
    }
}

/// Generates the ES module and its TypeScript declarations for every export.
/// It's one operation, using at most `limits.stack` bytes of stack: a
/// definition nested too deeply for that is an `E-RESOURCE` error.
pub fn generate(g: &Globals, limits: Limits) -> Result<Output, Diagnostic> {
    generate_with(g, limits, Options::default())
}

/// [`generate`], with the given representation options.
pub fn generate_with(g: &Globals, limits: Limits, options: Options) -> Result<Output, Diagnostic> {
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

    let codegen = Gen::new(g, options)?;
    let mut js = String::from(RUNTIME);
    js.push('\n');
    if codegen.text.is_some() {
        js.push_str(TEXT_AS_STRING);
        js.push_str(CHARS_OF_TEXT);
        js.push_str(TEXT_OF_CHARS);
    } else {
        js.push_str(TEXT_AS_LIST);
        js.push_str(CHARS_OF_TEXT);
    }
    js.push_str(RUNTIME_CODECS);
    js.push('\n');
    // Every data type is declared before any is defined, so their fields'
    // types can refer to each other (and themselves).
    for &d in &boundary_datas {
        let name = &g.data(d).name;
        let _ = writeln!(
            js,
            "const {} = datatype({});",
            info_name(name),
            js_string_literal(name)
        );
    }
    for &d in &boundary_datas {
        js.push_str(&codegen.define(d).map_err(Diagnostic::from)?);
    }
    js.push('\n');
    // Only what the exports use, in declaration order. That's dependency
    // order: the kernel admits each group only once what it uses is final,
    // so a definition refers only to earlier ones and to members of its own
    // group. Those are thunks or functions, never values, so they look each
    // other up only when called, after all of them are defined.
    // What records' proof-field checks use, too.
    let checks = boundary_datas
        .iter()
        .flat_map(|d| &g.data(*d).validators)
        .flat_map(|v| v.decision.subterms())
        .filter_map(|(t, _)| match t {
            Term::Def(id) => Some(*id),
            _ => None,
        });
    let used = reachable(g, exports.iter().map(|sig| sig.id).chain(checks), |id| {
        codegen.erased[id.0].0
            || g.builtins.native(id).is_some()
            || codegen.text_natives.contains_key(&id)
    });
    let while_generating = |id: DefId| {
        move |e: ResourceError| {
            Diagnostic::from(e).with_label(g.def(id).span, "while generating JavaScript for this")
        }
    };
    for id in (0..g.defs.len()).map(DefId).filter(|id| used[id.0]) {
        // Only an admitted definition has a body. The driver doesn't extract
        // a module with errors, but if it were asked to, the JS would call a
        // function that isn't there.
        let def = g.def(id);
        if def.body.is_none() && !codegen.erased[id.0].0 {
            return Err(Diagnostic::error(
                "E-EXPORT",
                format!("can't generate JavaScript for `{}`", def.name),
            )
            .with_label(
                def.span,
                "it hasn't been checked successfully, so it has no definition to generate",
            ));
        }
        js.push_str(&codegen.def(id).map_err(while_generating(id))?);
    }
    for sig in &exports {
        js.push_str(&codegen.wrapper(sig).map_err(while_generating(sig.id))?);
    }
    // Exports aren't names in the module's scope, so they can't hide its
    // own names or the JS globals it uses (`Set`, `BigInt`, …).
    let exported: Vec<String> = exports
        .iter()
        .map(|sig| format!("{} as {}", wrapper_name(&sig.name), sig.name))
        .collect();
    if !exported.is_empty() {
        let _ = writeln!(js, "\nexport {{ {} }};", exported.join(", "));
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
  constructor(message, options) {
    super(message, options);
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

// Boundary types are described by data, and one loop decodes (or encodes) a
// value of any of them, keeping its own stack, so deeply nested input
// doesn't use up the JS stack:
// - a leaf (`NAT`, `BOOL`, `TEXT`, `CHAR`) is decoded and encoded in one step;
// - `list(t)` is an array;
// - `data(info, args)` is a data type applied to its arguments: a tagged
//   object, with the constructors and fields given by `define`, or for a
//   record, an object without a tag;
// - `param(i)`, in a field's type, is the data type's parameter `i`.
// `open` says whether a type mentions a parameter. Each type is made once
// (`list` and `data` give back the same object for the same arguments), so
// two types are the same exactly when they're the same object, and `decode`
// can remember what it has decoded at each. There are only so many: a data
// type's fields can only mention it, and the types defined together with it,
// applied to their own parameters (the positivity check), and otherwise only
// types declared before them, so a boundary type has finitely many types
// inside it.
const LEAF = 0, LIST = 1, DATA = 2, PARAM = 3;
let typeCount = 0;
const leaf = (dec, enc) => ({ kind: LEAF, open: false, id: typeCount++, dec, enc });
const list = (elem) => (elem.list ??= { kind: LIST, open: elem.open, id: typeCount++, elem });
const data = (info, args = []) => {
  const key = args.map((a) => a.id).join(" ");
  let t = info.instances.get(key);
  if (t === undefined) {
    t = { kind: DATA, open: args.some((a) => a.open), id: typeCount++, info, args };
    info.instances.set(key, t);
  }
  return t;
};
const paramTypes = [];
const param = (i) => (paramTypes[i] ??= { kind: PARAM, open: true, id: typeCount++, i });
const datatype = (name) => ({
  name, ctors: new Map(), flat: new Set(), tags: "", instances: new Map(), record: undefined, checks: [],
});
// Each constructor's tag, and its fields' keys and types, in order. A
// constructor is `flat` if all its fields are leaves. A record has one
// constructor, whose fields are `info.record`, and no tag; `checks` are its
// proof fields' runtime checks, each a message and a function of a decoded
// object saying whether the proof holds.
const define = (info, ctors, record = false, checks = []) => {
  if (record) info.record = ctors[0][1];
  info.checks = checks;
  for (const [tag, fields] of ctors) {
    info.ctors.set(tag, fields);
    if (fields.every(([, t]) => t.kind === LEAF)) info.flat.add(tag);
  }
  const tags = ctors.map(([tag]) => JSON.stringify(tag));
  info.tags =
    tags.length > 1 ? `${tags.slice(0, -1).join(", ")} or ${tags.at(-1)}`
    : tags.length === 1 ? tags[0]
    : `nothing: ${info.name} has no values`;
};
// A field's type `t`, with its data type's parameters replaced by `args`.
const close = (t, args) =>
  !t.open ? t
  : t.kind === PARAM ? args[t.i]
  : t.kind === LIST ? list(close(t.elem, args))
  : data(t.info, t.args.map((a) => close(a, args)));

// A leaf decoder refuses its input by throwing a `Refusal`, which `decode`
// turns into a `StitchwortInputError` saying where the input was wrong.
class Refusal {
  constructor(message, cause) {
    this.message = message;
    this.cause = cause;
  }
}
const refuse = (message, cause) => {
  throw new Refusal(message, cause);
};

const NAT = leaf(
  (x) => (typeof x === "bigint" && x >= 0n ? x : refuse("expected a non-negative bigint")),
  (v) => v,
);

const BOOL = leaf(
  (x) => (typeof x === "boolean" ? { tag: x ? "True" : "False" } : refuse("expected a boolean")),
  (v) => v.tag === "True",
);

// `Text` is a string. Decoding refuses a string with a lone surrogate (which
// JS allows) rather than repairing it, so encoding gives back exactly the
// string that was decoded.
const wellFormed = (x) => {
  if (typeof x !== "string") refuse("expected a string");
  for (let i = 0; i < x.length; i++) {
    const unit = x.charCodeAt(i);
    if (unit < 0xd800 || unit > 0xdfff) continue;
    const low = i + 1 < x.length ? x.charCodeAt(i + 1) : 0;
    if (unit > 0xdbff || low < 0xdc00 || low > 0xdfff) {
      const hex = unit.toString(16).toUpperCase();
      refuse(`a lone surrogate (U+${hex}) at index ${i}; text must be a well-formed string`);
    }
    i++;
  }
  return x;
};
// A well-formed string's Unicode scalar values, in order.
const scalars = (x) => {
  wellFormed(x);
  const codes = [];
  for (let i = 0; i < x.length; i++) {
    const code = x.codePointAt(i);
    codes.push(BigInt(code));
    if (code > 0xffff) i++;
  }
  return codes;
};
const encodeChar = (v) => String.fromCodePoint(Number(v.code));
"#;

/// The runtime's `Text` codec and helpers, with `Text` as a string inside
/// generated code too (docs/proposals/compact-text.md, option A). Both
/// bridges between a string and its `List Char` are loops.
const TEXT_AS_STRING: &str = r#"const TEXT = leaf(wellFormed, (v) => v);

// A list of the array's items.
const listOf = (items) => {
  let list = { tag: "Nil" };
  for (let i = items.length - 1; i >= 0; i--) list = { tag: "Cons", head: items[i], tail: list };
  return list;
};
"#;

/// The bridge from a string to its `List Char`, in a loop: `MkText`'s field
/// in [`TEXT_AS_STRING`], and a compact list of characters in a checked term
/// (`Term::Chars`) with either representation of `Text`.
const CHARS_OF_TEXT: &str = r#"// The scalar value whose last code unit is at index `i` of a well-formed
// string: one unit, or the two of a surrogate pair.
const scalarEndingAt = (t, i) => {
  const unit = t.charCodeAt(i);
  return unit >= 0xdc00 && unit <= 0xdfff
    ? 0x10000 + ((t.charCodeAt(i - 1) - 0xd800) << 10) + (unit - 0xdc00)
    : unit;
};
// `MkText`'s field: the text's characters, as a list.
const charsOfText = (t) => {
  let chars = { tag: "Nil" };
  for (let i = t.length - 1; i >= 0; i--) {
    const code = scalarEndingAt(t, i);
    if (code > 0xffff) i--;
    chars = { tag: "Cons", head: { tag: "MkChar", code: BigInt(code) }, tail: chars };
  }
  return chars;
};
"#;

/// The rest of [`TEXT_AS_STRING`].
const TEXT_OF_CHARS: &str = r#"// `MkText chars`: the string of a list of characters.
const textOfChars = (chars) => {
  const parts = [];
  for (let l = chars; l.tag === "Cons"; l = l.tail) parts.push(encodeChar(l.head));
  return parts.join("");
};
"#;

/// The runtime's `Text` codec when `Text` is `MkText` of a cons list inside
/// generated code, as it was before option A: for differential tests.
const TEXT_AS_LIST: &str = r#"const TEXT = leaf(
  (x) => {
    const codes = scalars(x);
    let chars = { tag: "Nil" };
    for (let i = codes.length - 1; i >= 0; i--) {
      chars = { tag: "Cons", head: { tag: "MkChar", code: codes[i] }, tail: chars };
    }
    return { tag: "MkText", chars };
  },
  (v) => {
    const parts = [];
    for (let l = v.chars; l.tag === "Cons"; l = l.tail) parts.push(encodeChar(l.head));
    return parts.join("");
  },
);
"#;

/// The rest of the runtime: `Char`, and decoding and encoding any boundary type.
const RUNTIME_CODECS: &str = r#"
// `Char` is a string holding exactly one scalar value: one or two UTF-16
// code units.
const CHAR = leaf(
  (x) => {
    const codes = scalars(x);
    if (codes.length !== 1) {
      refuse(`expected exactly one character, but the string has ${codes.length}`);
    }
    return { tag: "MkChar", code: codes[0] };
  },
  encodeChar,
);

// A short description of an unexpected tag.
const describe = (x) =>
  typeof x !== "string" ? (x === null ? "null" : typeof x)
  : x.length > 40 ? `${JSON.stringify(x.slice(0, 40))}…`
  : JSON.stringify(x);

// The path to a value, as in `arg0.left[2].tail`, from its steps: an array
// index or a field's key. A path into deeply nested input is summarised, so
// that the message stays short: a run of the same step is written once with
// a count, and the middle of a long path is left out.
const step = (s) => (typeof s === "number" ? `[${s}]` : `.${s}`);
const pathText = (root, path) => {
  if (path.length <= 12) return root + path.map(step).join("");
  const runs = [];
  for (let i = 0; i < path.length; ) {
    let j = i + 1;
    while (j < path.length && path[j] === path[i]) j++;
    const text = j - i > 3 ? `(${step(path[i])} ×${j - i})` : path.slice(i, j).map(step).join("");
    runs.push({ text, steps: j - i });
    i = j;
  }
  const text = (rs) => rs.map((r) => r.text).join("");
  if (runs.length <= 12) return root + text(runs);
  const hidden = runs.slice(6, -6).reduce((n, r) => n + r.steps, 0);
  return `${root}${text(runs.slice(0, 6))}…(${hidden} more steps)…${text(runs.slice(-6))}`;
};

const NONE = Symbol("none");

// Only an object's own properties count: an inherited one (from its
// prototype, or from `Object.prototype`, which any code can add to) is
// refused. `own` reads one, once, giving `MISSING` or `INHERITED` if it isn't
// the object's own. If reading it throws (a getter can), the input is refused,
// with that error as the `cause`.
const hasOwn = Object.hasOwn;
const MISSING = Symbol("missing"), INHERITED = Symbol("inherited");
const own = (x, key) => {
  try {
    return hasOwn(x, key) ? x[key] : key in x ? INHERITED : MISSING;
  } catch (e) {
    let what = "an error";
    try {
      what = e instanceof Error ? `${e.name}: ${e.message}` : String(e);
    } catch {}
    return refuse(`reading it threw ${what.length > 80 ? `${what.slice(0, 80)}…` : what}`, e);
  }
};

// Decodes `x` as a value of type `t` (which mentions no parameters), into
// fresh values. `root` names the argument, for error messages. Each array or
// object being decoded has a frame, and they're decoded depth first: elements
// and fields are read and decoded in order, each completely before the next
// is read.
//
// `seen` holds, for each type, the arrays and objects decoded at it so far,
// and those being decoded (as `INSIDE`). One reached again by another path
// (shared, but not a cycle) isn't decoded again, or read again: its value is
// shared. Values are never changed, so that's safe, and it means decoding
// takes time and memory in proportion to the number of distinct objects in
// the input, not the number of paths through it, which can be exponentially
// more (`a = { left: b, right: b }`, `b = { left: c, right: c }`, …). One reached again while it's being decoded at the same type contains
// itself, and is refused instead of looping forever. (A cycle comes back to
// the same type eventually, since there are only so many.) An object of a
// `flat` constructor, whose fields are all leaves, can't contain itself or
// share anything, and decoding it takes as long as decoding its fields, so
// it's decoded again each time it's reached, which is quicker than
// remembering it.
const INSIDE = Symbol("inside");
const decode = (t, x, root) => {
  const frames = [];
  const path = [];
  const seen = new Map();
  try {
    for (;;) {
      // Start on `x`: a leaf is done at once, as is an array or object
      // already decoded at this type; otherwise it gets a frame.
      let value = NONE;
      if (t.kind === LEAF) {
        value = t.dec(x);
      } else {
        if (t.kind === LIST) {
          if (!Array.isArray(x)) refuse("expected an array");
        } else if (typeof x !== "object" || x === null) {
          refuse(`expected a ${t.info.name} object`);
        } else if (Array.isArray(x)) {
          refuse(`expected a ${t.info.name} object, not an array`);
        }
        let done = seen.get(t);
        if (done === undefined) seen.set(t, (done = new Map()));
        const known = done.get(x);
        if (known === INSIDE) refuse("the input contains itself");
        if (known !== undefined) {
          value = known;
        } else if (t.kind === LIST) {
          done.set(x, INSIDE);
          frames.push({ t, x, done, fields: undefined, i: 0, n: x.length, out: [] });
        } else if (t.info.record !== undefined) {
          const fields = t.info.record;
          done.set(x, INSIDE);
          frames.push({ t, x, done, fields, i: 0, n: fields.length, out: {} });
        } else {
          const tag = own(x, "tag");
          if (tag === MISSING) refuse(`no tag; expected ${t.info.tags}`);
          if (tag === INHERITED) refuse("its tag is inherited, not its own property");
          const fields = t.info.ctors.get(tag);
          if (fields === undefined) refuse(`unknown tag ${describe(tag)}; expected ${t.info.tags}`);
          if (t.info.flat.has(tag)) done = undefined;
          else done.set(x, INSIDE);
          frames.push({ t, x, done, fields, i: 0, n: fields.length, out: { tag } });
        }
      }
      // Give `value` to the frame waiting for it, and finish frames, until
      // one has another element or field to decode, or the outermost is done.
      for (;;) {
        const f = frames[frames.length - 1];
        if (value !== NONE) {
          if (f === undefined) return value;
          if (f.fields === undefined) f.out.push(value);
          else f.out[f.fields[f.i][0]] = value;
          f.i++;
          path.pop();
        }
        if (f.i < f.n) {
          if (f.fields === undefined) {
            path.push(f.i);
            x = own(f.x, f.i);
            if (x === MISSING || x === INHERITED) refuse("a hole in the array");
            t = f.t.elem;
          } else {
            const [key, type] = f.fields[f.i];
            path.push(key);
            x = own(f.x, key);
            if (x === MISSING) refuse("missing");
            if (x === INHERITED) refuse("inherited, not the object's own property");
            t = close(type, f.t.args);
          }
          break;
        }
        frames.pop();
        if (f.fields === undefined) {
          value = { tag: "Nil" };
          for (let i = f.n - 1; i >= 0; i--) value = { tag: "Cons", head: f.out[i], tail: value };
        } else {
          value = f.out;
          for (const [message, holds] of f.t.info.checks) if (!holds(value)) refuse(message);
        }
        f.done?.set(f.x, value);
      }
    }
  } catch (e) {
    if (e instanceof Refusal) {
      throw new StitchwortInputError(
        `${pathText(root, path)}: ${e.message}`,
        e.cause === undefined ? undefined : { cause: e.cause },
      );
    }
    throw e;
  }
};

// Encodes `v`, a value of type `t`, as fresh JS values, the same way round.
// Values made by Stitchwort code are well-formed, so this can't fail.
const encode = (t, v) => {
  const frames = [];
  for (;;) {
    let value = NONE;
    if (t.kind === LEAF) {
      value = t.enc(v);
    } else if (t.kind === LIST) {
      frames.push({ t, v, fields: undefined, out: [] });
    } else {
      const record = t.info.record;
      frames.push(
        record !== undefined
          ? { t, v, fields: record, i: 0, out: {} }
          : { t, v, fields: t.info.ctors.get(v.tag), i: 0, out: { tag: v.tag } },
      );
    }
    for (;;) {
      const f = frames[frames.length - 1];
      if (value !== NONE) {
        if (f === undefined) return value;
        if (f.fields === undefined) f.out.push(value);
        else f.out[f.fields[f.i++][0]] = value;
      }
      if (f.fields === undefined) {
        // `f.v` is the rest of the list.
        if (f.v.tag === "Cons") {
          v = f.v.head;
          f.v = f.v.tail;
          t = f.t.elem;
          break;
        }
      } else if (f.i < f.fields.length) {
        const [key, type] = f.fields[f.i];
        v = f.v[key];
        t = close(type, f.t.args);
        break;
      }
      frames.pop();
      value = f.out;
    }
  }
};
"#;

struct Gen<'g> {
    g: &'g Globals,
    nat: Option<DataId>,
    /// The prelude's `Text`, if it's a JS string in generated code
    /// ([`Options::native_text`]).
    text: Option<DataId>,
    /// The prelude's text operations with native JS, and which.
    text_natives: HashMap<DefId, TextNative>,
    /// Per definition: whether it's erased, and which of its leading
    /// parameters (up to its arity) are erased.
    erased: Vec<(bool, Vec<bool>)>,
    /// Per definition: how it's compiled and called, decided once here and
    /// used at every site.
    conventions: Vec<Convention>,
    /// The prelude's `ifThenElse`, which `if` becomes.
    if_then_else: Option<DefId>,
}

/// How a definition is compiled, and so how every site uses it: its
/// declaration, references to it, applications, first-class uses and export
/// wrappers (docs/proposals/mutual-recursion.md §8.6).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Convention {
    /// A proof or a type: nothing is generated, and it's `undefined`.
    Erased,
    /// No runtime parameters, not a case tree and not in a group: `const f =
    /// …;`, computed when the module loads, used as `f`.
    Value,
    /// No runtime parameters, and either a case tree (like `absurd`, whose
    /// case is on an erased proof, so it mustn't run until it's used) or a
    /// member of a group of definitions that call each other (which mustn't
    /// call a sibling while the module loads, before the sibling is
    /// defined): `const f = () => …;`, used as `f()`.
    Thunk,
    /// Runtime parameters: `const f = (v0) => …;`, used as `f`, applied as
    /// `f(a)`.
    Function,
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
    fn new(g: &'g Globals, options: Options) -> Result<Self, Diagnostic> {
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
            .collect::<Result<Vec<(bool, Vec<bool>)>, Diagnostic>>()?;
        let conventions = g
            .defs
            .iter()
            .zip(&erased)
            .map(|(def, (erased, mask))| {
                if *erased {
                    return Convention::Erased;
                }
                if mask.iter().any(|e| !e) {
                    return Convention::Function;
                }
                let case_tree = def.body.as_ref().is_some_and(|b| {
                    matches!(b.peel_lams(def.arity), Term::Case(..) | Term::NumCase(..))
                });
                let in_group = def.group.as_ref().is_some_and(|m| m.len() > 1);
                if case_tree || in_group {
                    Convention::Thunk
                } else {
                    Convention::Value
                }
            })
            .collect();
        let text = g.find_data("Text").filter(|d| {
            let data = g.data(*d);
            options.native_text
                && data.params.is_empty()
                && data.ctors.len() == 1
                && data.ctors[0].fields.len() == 1
        });
        let text_natives = if text.is_some() {
            bind_text_natives(g)
                .map_err(Diagnostic::from)?
                .into_iter()
                .filter(|b| b.bound)
                .filter_map(|b| Some((b.id?, b.native)))
                .collect()
        } else {
            HashMap::new()
        };
        Ok(Gen {
            g,
            nat: g.find_data("Nat"),
            text,
            text_natives,
            erased,
            conventions,
            if_then_else: g
                .defs
                .iter()
                .position(|def| &*def.name == "ifThenElse")
                .map(DefId),
        })
    }

    fn def(&self, id: DefId) -> Fallible<String> {
        let def = self.g.def(id);
        let (_, mask) = &self.erased[id.0];
        let convention = self.conventions[id.0];
        if convention == Convention::Erased {
            return Ok(String::new());
        }
        let Some(body) = &def.body else {
            unreachable!("`generate_with` refuses a definition without a body");
        };
        if let Some(op) = self.text_natives.get(&id) {
            return Ok(format!(
                "const {} = {};\n",
                def_name(&def.name),
                text_native_js(*op)
            ));
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
        let rhs = if matches!(tree, Term::Case(..) | Term::NumCase(..)) {
            if !params.is_empty()
                && let Some(block) = self.self_tail_loop(id, tree, &mut env)?
            {
                return Ok(format!(
                    "const {} = {params}{block};\n",
                    def_name(&def.name)
                ));
            }
            let block = self.tree(tree, &mut env, 1, None)?;
            match convention {
                Convention::Thunk => format!("() => {{\n{block}}}"),
                _ => format!("{{\n{block}}}"),
            }
        } else {
            let rhs = self.expr(tree, &mut env)?;
            // An object literal after `=>` needs parentheses.
            let rhs = if convention != Convention::Value && rhs.starts_with('{') {
                format!("({rhs})")
            } else {
                rhs
            };
            match convention {
                Convention::Thunk => format!("() => {rhs}"),
                _ => rhs,
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
        if let Term::NumCase(ix, arms, default) = term.strip_loc() {
            // Each arm ends in `return` (or `continue`), so nothing falls
            // through, and after the `switch` comes the default.
            let scrutinee = var(env.len() - 1 - ix);
            let mut out = format!("{pad}switch ({scrutinee}) {{\n");
            for arm in arms.iter() {
                let _ = writeln!(out, "{pad}  case {}n: {{", arm.value);
                out.push_str(&self.tree(&arm.body, env, depth + 2, self_call)?);
                let _ = writeln!(out, "{pad}  }}");
            }
            let _ = writeln!(out, "{pad}}}");
            out.push_str(&self.tree(default, env, depth, self_call)?);
            return Ok(out);
        }
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
                        "{pad}const {} = {scrutinee}{};",
                        var(level + f),
                        member(&key(self.g, *d, field))
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
        } else if Some(*d) == self.text {
            // A `Text` is a string. Matching `MkText cs` makes the list of
            // its characters, in a loop, but only if `cs` is used.
            let level = env.len();
            env.push(false);
            let body = self.tree(&branches[0].body, env, depth, self_call)?;
            env.truncate(level);
            if mentions(&body, &var(level)) {
                let _ = writeln!(out, "{pad}const {} = charsOfText({scrutinee});", var(level));
            }
            out.push_str(&body);
        } else if data.record {
            // A record has one constructor and no tag.
            branch(&mut out, 0, &branches[0], depth)?;
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
            // A compact list of characters (a text literal's): the cons list
            // it stands for, built from a string in a loop.
            Term::Chars(chars) => {
                let text: String = chars.as_slice().iter().collect();
                format!("charsOfText({})", js_string_literal(&text))
            }
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
                if Some(*d) == self.text {
                    // A string: a literal if the characters are, otherwise
                    // made from the list in a loop.
                    return Ok(match text_literal(&args[0]) {
                        Some(text) => js_string_literal(&text),
                        None => format!("textOfChars({})", self.expr(&args[0], env)?),
                    });
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
                let mut fields = Vec::new();
                if !data.record {
                    fields.push(format!("tag: \"{}\"", ctor.name));
                }
                for (((field, _), erased), arg) in
                    ctor.fields.iter().zip(&ctor.field_erased).zip(args)
                {
                    if !erased {
                        let key = ts_key(&key(self.g, *d, field));
                        fields.push(format!("{key}: {}", self.expr(arg, env)?));
                    }
                }
                if fields.is_empty() {
                    "{}".into()
                } else {
                    format!("{{ {} }}", fields.join(", "))
                }
            }
            // Proofs are erased, and transport along an equality does nothing.
            Term::J(_, base, _) => self.expr(base, env)?,
            Term::Data(..) | Term::Sort(_) | Term::Pi(..) | Term::Eq(..) | Term::Refl => {
                "undefined".into()
            }
            Term::Case(..) | Term::NumCase(..) => {
                panic!("internal error: case outside a case tree")
            }
            Term::Meta(_) => {
                panic!("internal error: unsolved metavariable in a checked definition")
            }
        })
    }

    /// A call to a definition, leaving out its erased arguments.
    fn def_ref(&self, id: DefId, args: &[&Term], env: &mut Vec<bool>) -> Fallible<String> {
        let (_, mask) = &self.erased[id.0];
        let mut out = match self.conventions[id.0] {
            Convention::Erased => return Ok("undefined".into()),
            Convention::Thunk => format!("{}()", def_name(&self.g.def(id).name)),
            Convention::Value | Convention::Function => def_name(&self.g.def(id).name),
        };
        for (i, arg) in args.iter().enumerate() {
            if !mask.get(i).copied().unwrap_or(false) {
                let _ = write!(out, "({})", self.expr(arg, env)?);
            }
        }
        Ok(out)
    }

    /// `function $$f(…)`, exported as `f`: decode the inputs, run the
    /// precondition checks, call the compiled definition, encode the result.
    /// Running out of stack on the way is a `StitchwortResourceError`.
    /// Parameter `i` (counting all parameters) is `arg{i}`, decoded as
    /// `v{i}`, which is what the compiled checks refer to.
    fn wrapper(&self, sig: &ExportSig) -> Fallible<String> {
        let params: Vec<String> = sig.param_positions.iter().map(|p| arg(*p)).collect();
        let mut out = format!(
            "\nfunction {}({}) {{\n  try {{\n",
            wrapper_name(&sig.name),
            params.join(", ")
        );
        let mut call = def_name(&self.g.def(sig.id).name);
        if self.conventions[sig.id.0] == Convention::Thunk {
            call.push_str("()");
        }
        for ((x, b), position) in sig.params.iter().zip(&sig.param_positions) {
            let _ = writeln!(
                out,
                "    const {} = decode({}, {}, \"{x}\");",
                var(*position),
                self.type_expr(b),
                arg(*position)
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
            "    return encode({}, {call});\n  }} catch (e) {{\n    throw outOfResources(\"{}\", e);\n  }}\n}}",
            self.type_expr(&sig.result),
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

    /// A JS expression for a boundary type, as the runtime's `decode` and
    /// `encode` take it.
    fn type_expr(&self, b: &Boundary) -> String {
        match b {
            Boundary::Nat => "NAT".into(),
            Boundary::Bool => "BOOL".into(),
            Boundary::Text => "TEXT".into(),
            Boundary::Char => "CHAR".into(),
            Boundary::List(elem) => format!("list({})", self.type_expr(elem)),
            Boundary::Data(d, args) if args.is_empty() => {
                format!("data({})", info_name(&self.g.data(*d).name))
            }
            Boundary::Data(d, args) => {
                let args: Vec<String> = args.iter().map(|a| self.type_expr(a)).collect();
                format!(
                    "data({}, [{}])",
                    info_name(&self.g.data(*d).name),
                    args.join(", ")
                )
            }
            Boundary::Param(i) => format!("param({i})"),
        }
    }

    /// A data type's constructors, and the keys and types of their fields.
    /// Only names the runtime chose, and `info$`-prefixed ones, are used as
    /// JS names; tags and keys are strings.
    fn define(&self, d: DataId) -> Fallible<String> {
        let data = self.g.data(d);
        let mut out = format!("define({}, [\n", info_name(&data.name));
        for (ctor, fields) in data.ctors.iter().zip(generic_field_boundaries(self.g, d)) {
            let fields: Vec<String> = fields
                .iter()
                .map(|(field, b)| {
                    format!(
                        "[{}, {}]",
                        js_string_literal(&key(self.g, d, field)),
                        self.type_expr(b)
                    )
                })
                .collect();
            let _ = writeln!(
                out,
                "  [{}, [{}]],",
                js_string_literal(&ctor.name),
                fields.join(", ")
            );
        }
        out.push(']');
        if data.record {
            out.push_str(", true, [");
            for check in self.field_checks(d)? {
                let _ = write!(out, "\n  {check},");
            }
            out.push_str("\n]");
        }
        out.push_str(");\n");
        Ok(out)
    }

    /// For each proof field of record `d` with a decision procedure: the
    /// message for when it doesn't hold, and a function of the decoded
    /// object saying whether it does.
    fn field_checks(&self, d: DataId) -> Fallible<Vec<String>> {
        let data = self.g.data(d);
        let ctor = &data.ctors[0];
        let np = data.params.len();
        let yes = self.decision_yes_tag();
        let mut out = Vec::new();
        let mut validators: Vec<_> = data.validators.iter().filter(|v| v.ctor == 0).collect();
        validators.sort_by_key(|v| v.field);
        for v in validators {
            // The parameters are types, so erased; the earlier fields are read
            // from the object.
            let mut env: Vec<bool> = vec![true; np];
            let mut reads = String::new();
            for (j, ((field, _), erased)) in ctor.fields[..v.field]
                .iter()
                .zip(&ctor.field_erased)
                .enumerate()
            {
                if !erased {
                    let _ = write!(
                        reads,
                        "const {} = o{}; ",
                        var(np + j),
                        member(&key(self.g, d, field))
                    );
                }
                env.push(*erased);
            }
            let decision = self.expr(&v.decision, &mut env)?;
            let mut names: Vec<stitchwort_core::Name> =
                data.params.iter().map(|(x, _)| x.clone()).collect();
            names.extend(ctor.fields[..v.field].iter().map(|(x, _)| x.clone()));
            let field = &ctor.fields[v.field];
            let message = format!(
                "proof field `{}` (`{}`) doesn't hold",
                field.0,
                pretty::term(self.g, &names, &field.1)
            );
            out.push(format!(
                "[{}, (o) => {{ {reads}return {decision}.tag === \"{yes}\"; }}]",
                js_string_literal(&message)
            ));
        }
        Ok(out)
    }

    /// Inputs are `readonly`; outputs are freshly built, so they're mutable.
    /// `params` names a data type's parameters, inside its alias.
    fn ts_type(&self, b: &Boundary, readonly: bool, params: &[String]) -> String {
        match b {
            Boundary::Nat => "bigint".into(),
            Boundary::Bool => "boolean".into(),
            Boundary::Text | Boundary::Char => "string".into(),
            Boundary::List(elem) if readonly => {
                // `readonly readonly T[][]` isn't TypeScript.
                let elem = self.ts_type(elem, true, params);
                if elem.starts_with("readonly ") {
                    format!("readonly ({elem})[]")
                } else {
                    format!("readonly {elem}[]")
                }
            }
            Boundary::List(elem) => format!("{}[]", self.ts_type(elem, false, params)),
            Boundary::Data(d, args) if args.is_empty() => type_name(&self.g.data(*d).name),
            Boundary::Data(d, args) => {
                let args: Vec<String> = args
                    .iter()
                    .map(|a| self.ts_type(a, readonly, params))
                    .collect();
                format!("{}<{}>", type_name(&self.g.data(*d).name), args.join(", "))
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
                let mut parts = Vec::new();
                if !data.record {
                    parts.push(format!("readonly tag: \"{}\"", ctor.name));
                }
                for (field, b) in &fields {
                    parts.push(format!(
                        "readonly {}: {}",
                        ts_key(&key(self.g, d, field)),
                        self.ts_type(b, true, &params)
                    ));
                }
                if parts.is_empty() {
                    "{}".to_string()
                } else {
                    format!("{{ {} }}", parts.join("; "))
                }
            })
            .collect();
        let generics = if params.is_empty() {
            String::new()
        } else {
            format!("<{}>", params.join(", "))
        };
        if data.record {
            // Structural, like every TypeScript object type: another record
            // with the same fields is accepted too (docs/proposals/records.md
            // §11.1).
            return format!(
                "export type {}{generics} = {};\n",
                type_name(&data.name),
                variants[0]
            );
        }
        if variants.is_empty() {
            // A type without constructors has no values.
            return format!("export type {}{generics} = never;\n", type_name(&data.name));
        }
        format!(
            "export type {}{generics} =\n  | {};\n",
            type_name(&data.name),
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
        // Proofs, so they're erased and never emitted.
        Native::EqNatRefl | Native::EqNatSound => "undefined",
    }
}

/// A prelude text operation with a native JS implementation, in generated
/// code where a `Text` is a string ([`Options::native_text`]). Like the
/// number natives, these are trusted, and tested against the definitions
/// they replace (`crates/cli/tests/extract.rs`). Each works on Unicode scalar
/// values, never on UTF-16 code units, and none uses JS stack space
/// proportional to the length of a text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TextNative {
    TextToList,
    TextFromList,
    TextAppend,
    TextLength,
    TextIsEmpty,
    DecEqText,
    TextCompare,
    TextUncons,
    TextFold,
    TextTrim,
    TextSplit,
    TextJoin,
    NatToText,
    TextToNat,
}

/// Each text native, the prelude definition it replaces, and that
/// definition's content hash (DESIGN.md §11), which covers everything it
/// depends on. A native is only used for a definition with exactly that hash,
/// so if the prelude changes, the definition is compiled as written instead:
/// slower, but still right. A test fails until each native has been checked
/// against the changed definition and its hash updated here.
const TEXT_NATIVES: &[(&str, TextNative, &str)] = &[
    (
        "textToList",
        TextNative::TextToList,
        "549a42631552690743f06ace8493d5e2e85672173248cc72fa1842711b958066",
    ),
    (
        "textFromList",
        TextNative::TextFromList,
        "0d7126c14af1f18042bdb06fec7030139ab8bb7d57f7e2f5a5215c577479ad6d",
    ),
    (
        "textAppend",
        TextNative::TextAppend,
        "d04570fc5c40f95e7632ad9959589d5b2bdf54c75df57b765a1d72c6e29e4f11",
    ),
    (
        "textLength",
        TextNative::TextLength,
        "b49fbcc27f659077cf54460e8b8966f20999ef3d047d57fc11924628867399d5",
    ),
    (
        "textIsEmpty",
        TextNative::TextIsEmpty,
        "a90f3ce9f27a95267e8259192aa7bf7f45ce5c254983deb07be35c0d9eac7b67",
    ),
    (
        "decEqText",
        TextNative::DecEqText,
        "f69a059702df9f43714a8cee2ac83349859539cdf4d3385930f9dc2cfeb973b0",
    ),
    (
        "textCompare",
        TextNative::TextCompare,
        "99922cac2ece4c6fe119244f4e7ebfbe6a73c41c5d7d4bc33ad4cc68621990a1",
    ),
    (
        "textUncons",
        TextNative::TextUncons,
        "05907321fda3c2a8e740ec4a30518f8ab133d4bc43cf954877262bc5f3bb2aed",
    ),
    (
        "textFold",
        TextNative::TextFold,
        "5015ca6ea71ac66cf89ef1306af0a813ffa12c9bd93a06ab3e682c3fe802ff75",
    ),
    (
        "textTrim",
        TextNative::TextTrim,
        "e29b4385d236cc6c65a7f039a1a3cceb4f0a5b15956106c5938145cb49331dde",
    ),
    (
        "textSplit",
        TextNative::TextSplit,
        "c16121624ff5d1e29219e5550216bdfb0ec37238bbe86f7551b784b2b93d9bc3",
    ),
    (
        "textJoin",
        TextNative::TextJoin,
        "fc7855026fd1f585079f7687d5d47987f5696670d3e0ea3f69e466e745efb3ba",
    ),
    (
        "natToText",
        TextNative::NatToText,
        "fc4ff5aefcb7cc8800239627ebcbd718d6c86658a15c5b8827333c68cec6645a",
    ),
    (
        "textToNat",
        TextNative::TextToNat,
        "8e3282ab2c0d59e2aed04467ea456f529b3ee22ef869862412ea68df3ae05c60",
    ),
];

/// Whether a text native applies to the program's definition of that name.
pub struct TextBinding {
    pub name: &'static str,
    pub native: TextNative,
    /// The definition, if there is one.
    pub id: Option<DefId>,
    /// Its content hash, in hex.
    pub hash: Option<String>,
    /// Whether it's the definition the native was written for.
    pub bound: bool,
}

/// Matches each text native with the definition it replaces, by content hash.
pub fn bind_text_natives(g: &Globals) -> Result<Vec<TextBinding>, ResourceError> {
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    TEXT_NATIVES
        .iter()
        .map(|&(name, native, expected)| {
            // Prelude names can't be redefined, so this is the prelude's.
            let id = g.defs.iter().position(|def| &*def.name == name).map(DefId);
            let hash = match id {
                Some(id) => def_hash(g, id)?.map(|h| h.hex()),
                None => None,
            };
            Ok(TextBinding {
                name,
                native,
                id,
                bound: hash.as_deref() == Some(expected),
                hash,
            })
        })
        .collect()
}

/// JS for a text native. The runtime's helpers (`TEXT_AS_STRING`) are in
/// scope, and the prelude's types have the representation the runtime uses
/// (`MkChar`'s `code`, `Cons`'s `head` and `tail`, `Just`'s `value`,
/// `MkPair`'s `fst` and `snd`).
fn text_native_js(op: TextNative) -> &'static str {
    match op {
        TextNative::TextToList => "charsOfText",
        TextNative::TextFromList => "textOfChars",
        TextNative::TextAppend => "(a) => (b) => a + b",
        // A surrogate pair is one character.
        TextNative::TextLength => {
            r#"(t) => {
  let n = 0;
  for (let i = 0; i < t.length; i++, n++) {
    const unit = t.charCodeAt(i);
    if (unit >= 0xd800 && unit <= 0xdbff) i++;
  }
  return BigInt(n);
}"#
        }
        TextNative::TextIsEmpty => r#"(t) => ({ tag: t === "" ? "True" : "False" })"#,
        // Well-formed UTF-16 is one-to-one with sequences of scalar values.
        TextNative::DecEqText => r#"(a) => (b) => ({ tag: a === b ? "Yes" : "No" })"#,
        // By scalar value, not code unit. At the first code unit that
        // differs, `codePointAt` gives each side's whole scalar value, or, if
        // the high halves of two pairs were the same, their low halves, which
        // are in the same order. A string that runs out first is a prefix,
        // ending between scalar values.
        TextNative::TextCompare => {
            r#"(a) => (b) => {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i++) {
    if (a.charCodeAt(i) !== b.charCodeAt(i)) {
      return { tag: a.codePointAt(i) < b.codePointAt(i) ? "Less" : "Greater" };
    }
  }
  return { tag: a.length === b.length ? "Equal" : a.length < b.length ? "Less" : "Greater" };
}"#
        }
        TextNative::TextUncons => {
            r#"(t) => {
  if (t === "") return { tag: "Nothing" };
  const code = t.codePointAt(0);
  const c = { tag: "MkChar", code: BigInt(code) };
  return { tag: "Just", value: { tag: "MkPair", fst: c, snd: t.slice(code > 0xffff ? 2 : 1) } };
}"#
        }
        // A right fold, as the definition is: `f` gets the last character
        // first. (The definition is strict and pure, so only the result can
        // differ, and it doesn't.) `f` itself may still recurse.
        TextNative::TextFold => {
            r#"(f) => (z) => (t) => {
  let acc = z;
  for (let i = t.length - 1; i >= 0; i--) {
    const code = scalarEndingAt(t, i);
    if (code > 0xffff) i--;
    acc = f({ tag: "MkChar", code: BigInt(code) })(acc);
  }
  return acc;
}"#
        }
        // Exactly `isSpaceCode`'s six: space, tab, line feed, vertical tab,
        // form feed and carriage return. Not JS's `trim`, which also removes
        // U+00A0, U+2028, U+FEFF and others.
        TextNative::TextTrim => {
            r#"(t) => {
  const space = (unit) => unit === 32 || (unit >= 9 && unit <= 13);
  let start = 0;
  let end = t.length;
  while (start < end && space(t.charCodeAt(start))) start++;
  while (end > start && space(t.charCodeAt(end - 1))) end--;
  return t.slice(start, end);
}"#
        }
        // The separator is a whole scalar value, and in a well-formed string
        // a match can't start inside a pair. Empty fields are kept, and ""
        // splits into [""], as the definition says.
        TextNative::TextSplit => "(s) => (t) => listOf(t.split(encodeChar(s)))",
        TextNative::TextJoin => {
            r#"(s) => (ts) => {
  const parts = [];
  for (let l = ts; l.tag === "Cons"; l = l.tail) parts.push(l.head);
  return parts.join(encodeChar(s));
}"#
        }
        // Decimal, without leading zeros.
        TextNative::NatToText => "(n) => n.toString()",
        // One or more ASCII digits and nothing else; leading zeros are fine.
        // (`BigInt` alone would also accept "", " 12" and "0x10".)
        TextNative::TextToNat => {
            r#"(t) => {
  if (t === "") return { tag: "Nothing" };
  for (let i = 0; i < t.length; i++) {
    const unit = t.charCodeAt(i);
    if (unit < 48 || unit > 57) return { tag: "Nothing" };
  }
  return { tag: "Just", value: BigInt(t) };
}"#
        }
    }
}

/// The characters of a list of `Char`s written out in full (like a text
/// literal's), if it is one: cons cells of literal characters, ending in
/// `Nil` or a compact list. A loop, since a long literal nests deeply.
fn text_literal(chars: &Term) -> Option<String> {
    let mut text = String::new();
    let mut list = chars.strip_loc();
    loop {
        match list {
            Term::Chars(rest) => {
                text.extend(rest.as_slice());
                return Some(text);
            }
            Term::Ctor(_, 0, args) if args.is_empty() => return Some(text),
            Term::Ctor(_, 1, args) if args.len() == 2 => {
                let Term::Ctor(_, 0, fields) = args[0].strip_loc() else {
                    return None;
                };
                let Term::Nat(code) = fields.first()?.strip_loc() else {
                    return None;
                };
                text.push(u32::try_from(&**code).ok().and_then(char::from_u32)?);
                list = args[1].strip_loc();
            }
            _ => return None,
        }
    }
}

/// Whether generated JS mentions the name, as a whole identifier.
fn mentions(js: &str, name: &str) -> bool {
    let part = |c: char| c.is_ascii_alphanumeric() || c == '_' || c == '$';
    js.match_indices(name).any(|(i, _)| {
        !js[..i].chars().next_back().is_some_and(part)
            && !js[i + name.len()..].chars().next().is_some_and(part)
    })
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

/// The key of a constructor's field in a JS object, at the boundary and in
/// generated code: its name, with each prime as `$`. A name the
/// representation already uses (`tag` for the constructor, and `__proto__`,
/// which sets an object's prototype) gets a `$` in front: a field `tag` is
/// `$tag`. Stitchwort names can't contain `$` or start with a prime, so two
/// fields never get the same key, and no field's key is `tag`.
pub fn field_key(name: &str) -> String {
    let key = name.replace('\'', "$");
    if RESERVED_KEYS.contains(&name) {
        format!("${key}")
    } else {
        key
    }
}

const RESERVED_KEYS: &[&str] = &["tag", "__proto__"];

/// The key of a record's field: as [`field_key`], except that a field `tag`
/// keeps the key `tag`, since a record has no tag of its own
/// (docs/proposals/records.md §11.2). `__proto__` is still `$__proto__`.
pub fn record_key(name: &str) -> String {
    let key = name.replace('\'', "$");
    if name == "__proto__" {
        format!("${key}")
    } else {
        key
    }
}

/// The key of field `name` of data type `d`.
fn key(g: &Globals, d: DataId, name: &str) -> String {
    if g.data(d).record {
        record_key(name)
    } else {
        field_key(name)
    }
}

/// Reading property `key`: `.key`, or `["key"]` if it isn't an identifier.
fn member(key: &str) -> String {
    if is_js_identifier(key) {
        format!(".{key}")
    } else {
        format!("[{}]", js_string_literal(key))
    }
}

/// A property name in an object literal or a TypeScript object type: as it
/// is if it's an identifier, otherwise quoted.
fn ts_key(key: &str) -> String {
    if is_js_identifier(key) {
        key.to_string()
    } else {
        js_string_literal(key)
    }
}

/// A data type's name in the TypeScript declarations, with each prime as `$`.
fn type_name(name: &str) -> String {
    name.replace('\'', "$")
}

/// The JS name of the description of a data type (see `datatype` in
/// [`RUNTIME`]).
fn info_name(name: &str) -> String {
    format!("info${}", type_name(name))
}

/// The JS name of an export's wrapper, which is exported under the export's
/// own name. Definitions are `$name`, so they're never `$$name`.
fn wrapper_name(name: &str) -> String {
    format!("$${name}")
}

/// The JS name of an export's wrapper's parameter at `position`. (Its
/// Stitchwort name is used in the declarations and in error messages.)
fn arg(position: usize) -> String {
    format!("arg{position}")
}

fn is_js_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_' || c == '$')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$')
}

/// JavaScript's reserved words, in strict mode and in modules, and names
/// that can't be bound there (`eval`, `arguments`) or that TypeScript treats
/// specially. An export can't have one as its name (it couldn't be imported
/// by name), and the declarations don't use one as a parameter's name.
const JS_RESERVED: &[&str] = &[
    "arguments",
    "await",
    "break",
    "case",
    "catch",
    "class",
    "const",
    "continue",
    "debugger",
    "default",
    "delete",
    "do",
    "else",
    "enum",
    "eval",
    "export",
    "extends",
    "false",
    "finally",
    "for",
    "function",
    "if",
    "implements",
    "import",
    "in",
    "instanceof",
    "interface",
    "let",
    "new",
    "null",
    "package",
    "private",
    "protected",
    "public",
    "return",
    "static",
    "super",
    "switch",
    "this",
    "throw",
    "true",
    "try",
    "typeof",
    "undefined",
    "var",
    "void",
    "while",
    "with",
    "yield",
];

/// Names the generated module exports itself, which an export or a data
/// type at the boundary can't also have.
const MODULE_NAMES: &[&str] = &["StitchwortInputError", "StitchwortResourceError"];

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
        // A list, possibly ending in a compact one, walked one cell at a time
        // as matching would.
        (Boundary::List(elem), _) => {
            let mut items = Vec::new();
            let mut v = value.clone();
            loop {
                match expand_step(g, v) {
                    Value::Ctor(_, 0, _) => return Ok(format!("[{}]", items.join(", "))),
                    Value::Ctor(_, 1, fields) => {
                        items.push(boundary_literal(g, elem, &fields[0])?);
                        v = fields[1].clone();
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
            let mut v = fields[0].clone();
            loop {
                match expand_step(g, v) {
                    Value::Ctor(_, 0, _) => return Ok(js_string_literal(&text)),
                    Value::Ctor(_, 1, fields) => {
                        text.push(char_value(g, &fields[0])?.ok_or_else(stuck)?);
                        v = fields[1].clone();
                    }
                    _ => return Err(stuck()),
                }
            }
        }
        (Boundary::Data(d, args), Value::Ctor(_, c, fields)) => {
            let data = g.data(*d);
            let ctor = &data.ctors[*c];
            let boundaries = &field_boundaries(g, *d, args)[*c];
            let mut parts = Vec::new();
            if !data.record {
                parts.push(format!("tag: \"{}\"", ctor.name));
            }
            let runtime = fields
                .iter()
                .zip(&ctor.field_erased)
                .filter(|(_, erased)| !**erased)
                .map(|(field, _)| field);
            for ((name, b), field) in boundaries.iter().zip(runtime) {
                parts.push(format!(
                    "{}: {}",
                    ts_key(&key(g, *d, name)),
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
    use super::{is_js_identifier, mentions};

    #[test]
    fn finds_whole_identifiers() {
        assert!(mentions("return v1;", "v1"));
        assert!(mentions("f(v1)(v2)", "v2"));
        assert!(!mentions("return v10 + $v1 + v1_ + v1$;", "v1"));
        assert!(!mentions("", "v1"));
    }

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
