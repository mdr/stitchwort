//! JavaScript extraction (DESIGN.md §12): erase types and proofs, generate an
//! ES module, and wrap each export in decode → compute → encode.
//!
//! First-milestone scope: exports take and return concrete first-order data
//! (`Nat`, `Bool`, `Text`, `Char`, `List`, and data types built from them,
//! such as `Option Text`), and their proof arguments are checked at runtime.

use std::cell::{Cell, OnceCell};
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use stitchwort_core::check::{is_type_former, telescope};
use stitchwort_core::hash::{data_hash, def_hash};
use stitchwort_core::native;
use stitchwort_core::partial::Primitive;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{Head, eval, expand_step, force, quote};
use stitchwort_core::{
    BigUint, DataId, DefId, Globals, Limits, ResourceError, Sort, Term, Value, pretty,
};
use stitchwort_syntax::Diagnostic;

pub mod run;

/// Generating code recurses over a definition's body, so each level checks
/// there's stack left first (docs/proposals/stack-safe-evaluation.md).
type Fallible<T> = Result<T, ResourceError>;
const PASS: &str = "JavaScript generator";

/// How a type crosses the JS boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Boundary {
    /// `bigint`, non-negative: the prelude's `Nat`, when it's the data type
    /// the representation was written for ([`NAT_DATA_HASH`]).
    Nat,
    /// `bigint`, of either sign: the prelude's `Int`, when it's the data type
    /// the representation was written for ([`bind_int`]).
    Int,
    /// `boolean`.
    Bool,
    /// `string`, well-formed (no lone surrogates): the prelude's `Text`, when
    /// it's the data type the representation was written for
    /// ([`TEXT_DATA_HASH`]).
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

    /// Whether `leaf` is this type or inside it (not counting the fields of
    /// a data type).
    fn mentions(&self, leaf: &Boundary) -> bool {
        self == leaf
            || match self {
                Boundary::List(elem) => elem.mentions(leaf),
                Boundary::Data(_, args) => args.iter().any(|a| a.mentions(leaf)),
                _ => false,
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
    // A partial function, or one taking or returning one: generated code
    // has no way to run a `Delay` (docs/proposals/partial.md §7.6, §10.6).
    if let Some(delay) = g.builtins.primitive_id(Primitive::Delay)
        && quote(g, 0, &def.ty_value)?
            .subterms()
            .any(|(t, _)| matches!(t, Term::Def(d) if *d == delay))
    {
        return Err(Diagnostic::error(
            "E-JS-PARTIAL",
            format!("`{}` can't be exported", def.name),
        )
        .with_label(def.span, "its type mentions `Partial`")
        .with_note("partial functions can't be exported to JavaScript yet: only the runtime (`stitchwort run`, the playground) runs them")
        .with_note("export the total parts instead: the functions a partial loop calls"));
    }
    // An export is imported in JS by its short name: `Geometry.area` as
    // `area` (docs/proposals/namespaces.md §7.3).
    let export_name = short_name(&def.name);
    if !is_js_identifier(export_name) {
        return Err(refuse(
            "its name isn't a valid JavaScript identifier".into(),
        ));
    }
    if JS_RESERVED.contains(&export_name) {
        return Err(refuse("its name is reserved in JavaScript".into()));
    }
    if MODULE_NAMES.contains(&export_name) {
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
    let equation_names = lam_names(def.body().map(|b| &**b));
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
        name: export_name.to_string(),
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
            if args.is_empty() && int_data(g) == Some(*d) {
                return Ok(Boundary::Int);
            }
            if args.is_empty() && nat_data(g) == Some(*d) {
                return Ok(Boundary::Nat);
            }
            if args.is_empty() && text_data(g) == Some(*d) {
                return Ok(Boundary::Text);
            }
            // The prelude's other types have codecs of their own, chosen by
            // identity: a program's own `List` is encoded as the data type it
            // is.
            let builtin = [Builtin::Bool, Builtin::Char, Builtin::List]
                .into_iter()
                .find(|b| g.registry.is_data(*b, *d));
            match (builtin, args.as_slice()) {
                (Some(Builtin::Bool), []) => Ok(Boundary::Bool),
                (Some(Builtin::Char), []) => Ok(Boundary::Char),
                (Some(Builtin::List), [elem]) => Ok(Boundary::List(Box::new(boundary(
                    g, elem, params, visiting,
                )?))),
                // Decoding would have to check the indices (a `Vec a n`'s
                // length, a `Grid`'s rows): refused wherever it appears in the
                // serialized form (docs/proposals/indexed-families.md §6.8, D147).
                _ if !data.indices.is_empty() => Err(format!(
                    "`{}` is an indexed family, which can't cross the JS boundary yet: \
                     decoding would have to check its indices",
                    data.name
                )),
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
    if MODULE_NAMES.contains(&short_name(&data.name)) {
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
        // Each field has its own key at the boundary.
        for (i, (field, _)) in ctor.fields.iter().enumerate() {
            if ctor.fields[..i].iter().any(|(other, _)| other == field) {
                return Err(format!(
                    "`{}`'s constructor `{}` has two fields called `{field}`",
                    data.name, ctor.name
                ));
            }
        }
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
    /// This applies only to the prelude's `Text` as the representation was
    /// written for it ([`TEXT_DATA_HASH`]).
    pub native_text: bool,
    /// An `Int` is a `bigint` inside generated code too, and the prelude's
    /// integer operations are native JS (docs/proposals/integers.md, "The
    /// JavaScript boundary"). Off, an `Int` is `OfNat` or `NegSucc` inside
    /// generated code, with the same `bigint` boundary, and every operation
    /// is compiled from its definition: for differential tests of the
    /// natives. Either way, this applies only to the prelude's `Int` as the
    /// representation was written for it ([`bind_int`]).
    pub native_int: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            native_text: true,
            native_int: true,
        }
    }
}

/// Generates the ES module and its TypeScript declarations for every export.
/// It's one operation, using at most `limits.stack` bytes of stack: a
/// definition nested too deeply for that is an `E-RESOURCE` error.
/// Exports and boundary types are named by their short names
/// (docs/proposals/namespaces.md §7.3), so two with the same short name
/// can't both be exported. The same type reached twice is one type. The
/// data types at the boundary, in the order they're reached.
fn check_names(g: &Globals, exports: &[ExportSig]) -> Result<Vec<DataId>, Diagnostic> {
    let mut short_exports: HashMap<&str, DefId> = HashMap::new();
    for sig in exports {
        if let Some(other) = short_exports.insert(&sig.name, sig.id) {
            return Err(Diagnostic::error(
                "E-EXPORT",
                format!(
                    "`{}` and `{}` would both be exported as `{}`",
                    g.def(other).name,
                    g.def(sig.id).name,
                    sig.name
                ),
            )
            .with_label(g.def(sig.id).span, "exported here")
            .with_label(g.def(other).span, "and here")
            .with_note("export only one of them, or rename one"));
        }
    }
    let mut boundary_datas = Vec::new();
    for sig in exports {
        for b in sig.params.iter().map(|(_, b)| b).chain([&sig.result]) {
            collect_datas(g, b, &mut boundary_datas);
        }
    }
    let mut short_types: HashMap<String, DataId> = HashMap::new();
    for &d in &boundary_datas {
        if let Some(other) = short_types.insert(type_name(&g.data(d).name), d) {
            return Err(Diagnostic::error(
                "E-EXPORT",
                format!(
                    "`{}` and `{}` would both be called `{}` in the TypeScript declarations",
                    g.data(other).name,
                    g.data(d).name,
                    type_name(&g.data(d).name)
                ),
            )
            .with_label(g.data(d).span, "this type crosses the JS boundary")
            .with_label(g.data(other).span, "and so does this one")
            .with_note("rename one of them"));
        }
    }
    Ok(boundary_datas)
}

/// Checks that the exports loaded so far can be named in JS and TypeScript
/// together: [`exportable`] checks each on its own.
pub fn exports_fit_together(g: &Globals) -> Result<(), Diagnostic> {
    exports_fit_together_among(g, (0..g.defs.len()).map(DefId))
}

/// [`exports_fit_together`] for the exports among `ids` only: one
/// namespace's.
pub fn exports_fit_together_among(
    g: &Globals,
    ids: impl Iterator<Item = DefId>,
) -> Result<(), Diagnostic> {
    let exports = ids
        .filter(|id| g.def(*id).export)
        .map(|id| exportable(g, id))
        .collect::<Result<Vec<_>, _>>()?;
    check_names(g, &exports).map(|_| ())
}

pub fn generate(g: &Globals, limits: Limits) -> Result<Output, Diagnostic> {
    generate_with(g, limits, Options::default())
}

/// [`generate`], with the given representation options.
pub fn generate_with(g: &Globals, limits: Limits, options: Options) -> Result<Output, Diagnostic> {
    let ids: Vec<DefId> = (0..g.defs.len())
        .map(DefId)
        .filter(|id| g.def(*id).export)
        .collect();
    generate_exports(g, limits, options, &ids)
}

/// [`generate_with`] for the exports `ids` only: one namespace's.
pub fn generate_exports(
    g: &Globals,
    limits: Limits,
    options: Options,
    ids: &[DefId],
) -> Result<Output, Diagnostic> {
    let _op = g.budget.operation(Limits::stack_only(limits.stack));
    let exports = ids
        .iter()
        .map(|id| exportable(g, *id))
        .collect::<Result<Vec<_>, _>>()?;

    let boundary_datas = check_names(g, &exports)?;

    erasable(g)?;
    let codegen = Gen::new(g, options)?;
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
    let failure = std::cell::RefCell::new(None);
    let used = reachable(
        g,
        exports.iter().map(|sig| sig.id).chain(checks),
        |id| match codegen.try_info(id) {
            Ok(info) => {
                info.result_erased
                    || codegen.kernel_native(id).is_some()
                    || codegen.text_natives.contains_key(&id)
                    || codegen.int_natives.contains_key(&id)
                    || info.delay.is_some()
            }
            Err(e) => {
                failure.borrow_mut().get_or_insert(e);
                true
            }
        },
    );
    if let Some(e) = failure.into_inner() {
        return Err(e);
    }
    // `reachable` skips a definition without a body, so make sure of the rest.
    for id in (0..g.defs.len()).map(DefId).filter(|id| used[id.0]) {
        codegen.try_info(id)?;
    }
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
    // `INT` only where it's used.
    let at_boundary = |b: &Boundary| b.mentions(&Boundary::Int);
    let int_crosses = exports
        .iter()
        .flat_map(|sig| sig.params.iter().map(|(_, b)| b).chain([&sig.result]))
        .any(at_boundary)
        || boundary_datas.iter().any(|d| {
            generic_field_boundaries(g, *d)
                .iter()
                .flatten()
                .any(|(_, b)| at_boundary(b))
        });
    if let Some(int) = int_data(g).filter(|_| int_crosses) {
        js.push_str(&codegen.int_codec(int));
    }
    js.push_str(RUNTIME_CODECS);
    js.push('\n');
    // Every data type is declared before any is defined, so their fields'
    // types can refer to each other (and themselves).
    for &d in &boundary_datas {
        let data = g.data(d);
        let _ = writeln!(
            js,
            "const {} = datatype({});",
            info_name(&data.path),
            js_string_literal(&data.name)
        );
    }
    for &d in &boundary_datas {
        js.push_str(&codegen.define(d).map_err(Diagnostic::from)?);
    }
    js.push('\n');
    // Partial computations are one token (docs/proposals/partial.md §7.6).
    if (0..g.defs.len()).any(|i| used[i] && codegen.info(DefId(i)).delay.is_some()) {
        js.push_str("// A partial computation, which nothing here can run.\nconst delayed = Symbol(\"Delay\");\n\n");
    }
    let while_generating = |id: DefId| {
        move |e: ResourceError| {
            Diagnostic::from(e).with_label(g.def(id).span, "while generating JavaScript for this")
        }
    };
    for id in (0..g.defs.len())
        .map(DefId)
        .filter(|id| used[id.0] && codegen.info(*id).delay.is_none())
    {
        // Only an admitted definition has a body. The driver doesn't extract
        // a module with errors, but if it were asked to, the JS would call a
        // function that isn't there.
        let def = g.def(id);
        if def.body().is_none() && !codegen.info(id).result_erased {
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
        Boundary::Nat
        | Boundary::Int
        | Boundary::Bool
        | Boundary::Text
        | Boundary::Char
        | Boundary::Param(_) => {}
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
    /// The prelude's `Nat`, if the `bigint` representation applies
    /// ([`nat_data`]).
    nat: Option<DataId>,
    /// The prelude's `Text`, if it's a JS string in generated code
    /// ([`Options::native_text`], [`text_data`]).
    text: Option<DataId>,
    /// The prelude's text operations with native JS, and which.
    text_natives: HashMap<DefId, TextNative>,
    /// The prelude's `Int`, if it's a `bigint` in generated code
    /// ([`Options::native_int`], [`bind_int`]).
    int: Option<DataId>,
    /// The prelude's integer operations with native JS, and which.
    int_natives: HashMap<DefId, IntNative>,
    /// Per definition, computed on first use ([`Gen::try_info`]).
    infos: Vec<OnceCell<DefInfo>>,
    /// The prelude's `ifThenElse`, which `if` becomes.
    if_then_else: Option<DefId>,
    /// For `stitchwort run --js` ([`run`]): a `Delay` is a real value that
    /// the runner steps, rather than the erased token, so partial
    /// definitions are generated, and `Delay`'s constants build
    /// `StitchwortDelay` objects.
    run_delay: bool,
}

/// What the generator decides about a definition from its type.
struct DefInfo {
    /// Whether it's a proof or a type.
    result_erased: bool,
    /// Which of its leading parameters (up to its arity) are erased.
    mask: Vec<bool>,
    /// How it's compiled and called, decided once and used at every site.
    convention: Convention,
    /// For a definition whose result is a `Delay` (a partial function, or one
    /// of `Delay`'s constants): which of its parameters are erased. It's
    /// never generated: a call to it with all its arguments is the token
    /// `delayed`, and with fewer, a function returning the token.
    delay: Option<Vec<bool>>,
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
        let text = text_data(g).filter(|_| options.native_text);
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
        // The natives assume the `bigint` representation, so they're used
        // only with it, and it only for the `Int` it was written for.
        let int = int_data(g).filter(|_| options.native_int);
        let int_natives = if int.is_some() {
            bind_int(g)
                .map_err(Diagnostic::from)?
                .natives
                .into_iter()
                .filter(|b| b.bound && (text.is_some() || !b.native.uses_text()))
                .filter_map(|b| Some((b.id?, b.native)))
                .collect()
        } else {
            HashMap::new()
        };
        Ok(Gen {
            g,
            nat: nat_data(g),
            text,
            text_natives,
            int,
            int_natives,
            infos: g.defs.iter().map(|_| OnceCell::new()).collect(),
            if_then_else: g.registry.def(Builtin::IfThenElse),
            run_delay: false,
        })
    }

    /// Which kernel-native implementation applies to `id`, if any: the
    /// number natives assume the `bigint` representation, so they apply only
    /// with it ([`nat_data`]).
    fn kernel_native(&self, id: DefId) -> Option<native::Native> {
        self.nat.and(self.g.builtins.native(id))
    }

    /// What's decided about a definition, from its type: computed on first
    /// use, so a definition nothing extracted consults (a theorem, say) costs
    /// nothing.
    fn try_info(&self, id: DefId) -> Result<&DefInfo, Diagnostic> {
        let cell = &self.infos[id.0];
        if let Some(info) = cell.get() {
            return Ok(info);
        }
        let g = self.g;
        let def = g.def(id);
        let tel = telescope(g, &def.ty_value, def.span)?;
        let partial = match (
            force(g, tel.result)?,
            g.builtins.primitive_id(Primitive::Delay),
        ) {
            (Value::Neutral(Head::Def(d), spine), Some(delay)) => d == delay && spine.len() == 3,
            _ => false,
        };
        let delay =
            (partial && !self.run_delay).then(|| tel.params.iter().map(|(_, _, e)| *e).collect());
        // `Delay`'s constants have no body, so no arity: each takes all of
        // its parameters ([`run::primitive_js`]).
        let constant = self.run_delay && g.builtins.primitive(id).is_some();
        let mask: Vec<bool> = tel
            .params
            .iter()
            .take(if constant {
                tel.params.len()
            } else {
                def.arity
            })
            .map(|(_, _, erased)| *erased)
            .collect();
        let result_erased = tel.result_erased;
        let convention = if result_erased {
            Convention::Erased
        } else if mask.iter().any(|e| !e) {
            Convention::Function
        } else {
            let case_tree = def.body().is_some_and(|b| {
                matches!(b.peel_lams(def.arity), Term::Case(..) | Term::NumCase(..))
            });
            let in_group = def.group.as_ref().is_some_and(|m| m.len() > 1);
            if case_tree || in_group {
                Convention::Thunk
            } else {
                Convention::Value
            }
        };
        Ok(cell.get_or_init(|| DefInfo {
            result_erased,
            mask,
            convention,
            delay,
        }))
    }

    /// Whether `y => body` is `y => Done y`, the continuation the
    /// elaborator writes for an operation or a recursion request, which the
    /// runner recognises to run a tail request in constant space (as
    /// `stitchwort_core::step` does).
    fn is_done_continuation(&self, body: &Term) -> bool {
        let mut body = body;
        while let Term::Loc(_, t) | Term::Ann(t, _) = body {
            body = t;
        }
        matches!(body, Term::Ctor(d, 0, fields)
            if Some(*d) == self.g.registry.data(Builtin::Comp)
                && matches!(&fields[..], [field] if matches!(field.strip_loc(), Term::Var(0))))
    }

    /// `try_info` for a definition the generator has already consulted:
    /// `generate_with` computes it for every definition it reaches.
    fn info(&self, id: DefId) -> &DefInfo {
        self.infos[id.0]
            .get()
            .unwrap_or_else(|| panic!("no info for {}", self.g.def(id).name))
    }

    fn def(&self, id: DefId) -> Fallible<String> {
        let def = self.g.def(id);
        let DefInfo {
            mask, convention, ..
        } = self.info(id);
        let convention = *convention;
        if convention == Convention::Erased {
            return Ok(String::new());
        }
        if self.run_delay
            && let Some(prim) = self.g.builtins.primitive(id)
        {
            return Ok(format!(
                "const {} = {};\n",
                def_name(&def.path),
                run::primitive_js(prim)
            ));
        }
        let Some(body) = def.body() else {
            unreachable!("`generate_with` refuses a definition without a body");
        };
        if let Some(op) = self.text_natives.get(&id) {
            return Ok(format!(
                "const {} = {};\n",
                def_name(&def.path),
                text_native_js(*op)
            ));
        }
        if let Some(op) = self.int_natives.get(&id) {
            return Ok(format!(
                "const {} = {};\n",
                def_name(&def.path),
                int_native_js(*op)
            ));
        }
        if let Some(op) = self.kernel_native(id) {
            return Ok(format!(
                "const {} = {};\n",
                def_name(&def.path),
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
                    def_name(&def.path)
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
        Ok(format!("const {} = {params}{rhs};\n", def_name(&def.path)))
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
        if let Term::Let(_, _, value, body, erased) = term.strip_loc() {
            let mut out = self.let_statement(value, *erased, env, &pad)?;
            out.push_str(&self.tree(body, env, depth, self_call)?);
            env.pop();
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
            for (f, ((_, _), erased)) in data.ctors[c]
                .fields
                .iter()
                .zip(&data.ctors[c].field_erased)
                .enumerate()
            {
                if !erased && Some(*d) != self.nat && Some(*d) != self.int {
                    let _ = writeln!(
                        out,
                        "{pad}const {} = {scrutinee}{};",
                        var(level + f),
                        member(&field_key_at(self.g, *d, c, f))
                    );
                }
                env.push(*erased);
            }
            match &b.body {
                Some(body) => out.push_str(&self.tree(body, env, depth, self_call)?),
                // An impossible branch (docs/proposals/indexed-families.md
                // §6.8): never reached by a well-typed value.
                None => {
                    let _ = writeln!(out, "{pad}throw new Error(\"unreachable\");");
                }
            }
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
        } else if Some(*d) == self.int {
            // A `bigint`: `OfNat n` is `n` itself, and `NegSucc n` is
            // `-n - 1n`, so the sign tells them apart, and `-x - 1n` gives
            // `NegSucc`'s field back.
            let field = predecessor;
            let _ = writeln!(out, "{pad}if ({scrutinee} >= 0n) {{");
            let _ = writeln!(out, "{pad}  const {field} = {scrutinee};");
            branch(&mut out, 0, &branches[0], depth + 1)?;
            let _ = writeln!(out, "{pad}}} else {{");
            let _ = writeln!(out, "{pad}  const {field} = -{scrutinee} - 1n;");
            branch(&mut out, 1, &branches[1], depth + 1)?;
            let _ = writeln!(out, "{pad}}}");
        } else if Some(*d) == self.text {
            // A `Text` is a string. Matching `MkText cs` makes the list of
            // its characters, in a loop, but only if `cs` is used.
            let level = env.len();
            env.push(false);
            let body = match &branches[0].body {
                Some(body) => self.tree(body, env, depth, self_call)?,
                None => format!("{pad}throw new Error(\"unreachable\");\n"),
            };
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

    /// A `let` in statement position: `const v = value;`, or nothing for
    /// one the kernel marked skipped (a proof, a type, or unused;
    /// docs/proposals/let.md §6.1 rule 5). Adds its variable to `env`,
    /// which the caller removes after the body.
    fn let_statement(
        &self,
        value: &Term,
        erased: bool,
        env: &mut Vec<bool>,
        pad: &str,
    ) -> Fallible<String> {
        if erased {
            env.push(true);
            return Ok(String::new());
        }
        let line = format!(
            "{pad}const {} = {};\n",
            var(env.len()),
            self.expr(value, env)?
        );
        env.push(false);
        Ok(line)
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
        if let Term::Let(_, _, value, body, erased) = term.strip_loc() {
            let mut out = self.let_statement(value, *erased, env, &pad)?;
            out.push_str(&self.tail(body, env, depth, call)?);
            env.pop();
            return Ok(out);
        }
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
            Term::Nat(n) if self.nat.is_some() => format!("{n}n"),
            Term::Nat(n) => self.nat_from_number(n),
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
            Term::Lam(_, _, body) if self.run_delay && self.is_done_continuation(body) => {
                run::DONE_K.into()
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
            // A skipped `let` (a proof, a type, or unused) emits nothing: its
            // variable is `undefined`, as an erased parameter's is.
            Term::Let(_, _, _, body, true) => {
                env.push(true);
                let body = self.expr(body, env);
                env.pop();
                body?
            }
            // In an expression, computed once, before the body. (In a case
            // tree's leaf, it's a `const`: `Gen::let_statement`.)
            Term::Let(_, _, value, body, false) => {
                let value = self.expr(value, env)?;
                let level = env.len();
                env.push(false);
                let body = self.expr(body, env)?;
                env.pop();
                if body.starts_with('{') {
                    format!("(({}) => ({body}))({value})", var(level))
                } else {
                    format!("(({}) => {body})({value})", var(level))
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
                if Some(*d) == self.int {
                    // `OfNat n` is `n`, and `NegSucc n` is `-n - 1n`. A
                    // `Nat`'s JS is a literal, a name, a call or in brackets,
                    // so `-` applies to all of it.
                    return Ok(match (*c, self.nat_literal(&args[0])) {
                        (0, _) => self.expr(&args[0], env)?,
                        (_, Some(n)) => format!("-{}n", n + 1u32),
                        (_, None) => format!("(-{} - 1n)", self.expr(&args[0], env)?),
                    });
                }
                let ctor = &data.ctors[*c];
                let mut fields = Vec::new();
                if !data.record {
                    fields.push(format!("tag: \"{}\"", ctor.name));
                }
                for (f, (erased, arg)) in ctor.field_erased.iter().zip(args).enumerate() {
                    if !erased {
                        let key = ts_key(&field_key_at(self.g, *d, *c, f));
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
        // A partial computation is the token, whatever its arguments: they
        // only feed a `Delay`, which nothing can run, so they aren't
        // computed.
        if let Some(mask) = &self.info(id).delay {
            let mut out = "delayed".to_string();
            for erased in mask.iter().skip(args.len()).rev() {
                if !erased {
                    out = format!("((_) => {out})");
                }
            }
            return Ok(out);
        }
        let info = self.info(id);
        let mask = &info.mask;
        let mut out = match info.convention {
            Convention::Erased => return Ok("undefined".into()),
            Convention::Thunk => format!("{}()", def_name(&self.g.def(id).path)),
            Convention::Value | Convention::Function => def_name(&self.g.def(id).path),
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
        let mut call = def_name(&self.g.def(sig.id).path);
        if self.info(sig.id).convention == Convention::Thunk {
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

    /// A `Nat` written as a compact number, in the ordinary data-type
    /// representation (when [`nat_data`] doesn't apply): a loop building the
    /// type's constructors. The number representation would just be `{n}n`.
    fn nat_from_number(&self, n: &BigUint) -> String {
        let d = self
            .g
            .registry
            .data(Builtin::Nat)
            .expect("a checked `Nat` term has a declared `Nat`");
        let data = self.g.data(d);
        let zero = js_string_literal(&data.ctors[0].name);
        let succ = js_string_literal(&data.ctors[1].name);
        let key = ts_key(&field_key_at(self.g, d, 1, 0));
        format!(
            "((k) => {{ let v = {{ tag: {zero} }}; for (let i = 0n; i < k; i++) v = {{ tag: {succ}, {key}: v }}; return v; }})({n}n)"
        )
    }

    /// The number a `Nat` term is, if it's written out: `Succ`s around
    /// `Zero` or a compact number.
    fn nat_literal(&self, term: &Term) -> Option<BigUint> {
        let mut count = 0u64;
        let mut term = term.strip_loc();
        loop {
            match term {
                Term::Nat(k) => return Some(&**k + count),
                Term::Ctor(d, 0, _) if Some(*d) == self.nat => return Some(BigUint::from(count)),
                Term::Ctor(d, 1, succ) if Some(*d) == self.nat => {
                    count += 1;
                    term = succ[0].strip_loc();
                }
                _ => return None,
            }
        }
    }

    /// The runtime's `INT` codec, for the prelude's `Int` `d` (only when
    /// [`bind_int`] binds it). At the boundary, an `Int` is a `bigint` of
    /// either sign. Decoding refuses anything else, including a `number`
    /// and a numeric string; encoding can't fail.
    fn int_codec(&self, d: DataId) -> String {
        const DECODE: &str = "(x) => (typeof x === \"bigint\" ? x : refuse(\"expected a bigint\"))";
        if self.int.is_some() {
            return format!(
                "\n// `Int` is a `bigint` of either sign, inside generated code too.\nconst INT = leaf({DECODE}, (v) => v);\n"
            );
        }
        // Inside generated code, `OfNat n` and `NegSucc n` are objects, as
        // any data type's constructors are (`Options::native_int` off).
        let data = self.g.data(d);
        let tag = |c: usize| js_string_literal(&data.ctors[c].name);
        let field = |c: usize| key(self.g, d, &data.ctors[c].fields[0].0);
        format!(
            "\n// `Int` is a `bigint` of either sign at the boundary, and `{of_nat}` or\n\
             // `{neg_succ}` inside generated code.\n\
             const INT = leaf(\n  \
               (x) => {{\n    \
                 const n = ({DECODE})(x);\n    \
                 return n >= 0n ? {{ tag: {t0}, {k0}: n }} : {{ tag: {t1}, {k1}: -n - 1n }};\n  \
               }},\n  \
               (v) => (v.tag === {t0} ? v{m0} : -v{m1} - 1n),\n\
             );\n",
            of_nat = data.ctors[0].name,
            neg_succ = data.ctors[1].name,
            t0 = tag(0),
            t1 = tag(1),
            k0 = ts_key(&field(0)),
            k1 = ts_key(&field(1)),
            m0 = member(&field(0)),
            m1 = member(&field(1)),
        )
    }

    /// The tag of `Decidable`'s first constructor (`Yes`).
    fn decision_yes_tag(&self) -> String {
        self.g.registry.data(Builtin::Decidable).map_or_else(
            || "Yes".into(),
            |d| self.g.data(d).ctors[0].name.to_string(),
        )
    }

    /// A JS expression for a boundary type, as the runtime's `decode` and
    /// `encode` take it.
    fn type_expr(&self, b: &Boundary) -> String {
        match b {
            Boundary::Nat => "NAT".into(),
            Boundary::Int => "INT".into(),
            Boundary::Bool => "BOOL".into(),
            Boundary::Text => "TEXT".into(),
            Boundary::Char => "CHAR".into(),
            Boundary::List(elem) => format!("list({})", self.type_expr(elem)),
            Boundary::Data(d, args) if args.is_empty() => {
                format!("data({})", info_name(&self.g.data(*d).path))
            }
            Boundary::Data(d, args) => {
                let args: Vec<String> = args.iter().map(|a| self.type_expr(a)).collect();
                format!(
                    "data({}, [{}])",
                    info_name(&self.g.data(*d).path),
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
        let mut out = format!("define({}, [\n", info_name(&data.path));
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
            Boundary::Nat | Boundary::Int => "bigint".into(),
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
                    && !self.g.datas.iter().any(|d| type_name(&d.name) == **x)
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

/// Erasing `Delay` values to one token is correct only while no code can tell
/// two of them apart (docs/proposals/partial.md §7.6): `Delay` has no
/// eliminator and its constants no computation rules. A definition is how
/// the kernel would give one a rule, so a `Delay` constant with a body means
/// erasure must be replaced by a real representation.
fn erasable(g: &Globals) -> Result<(), Diagnostic> {
    for prim in Primitive::ALL {
        // Each of these builds a `Delay` (or is the type): none observes one.
        let builds = match prim {
            Primitive::Delay
            | Primitive::Now
            | Primitive::Lift
            | Primitive::BindD
            | Primitive::MapSig
            | Primitive::Pfix => true,
        };
        if let Some(id) = g.builtins.primitive_id(prim)
            && (!builds || g.def(id).body().is_some())
        {
            return Err(Diagnostic::error(
                "E-JS-PARTIAL",
                "partial computations can't be extracted to JavaScript",
            )
            .with_label(
                g.def(id).span,
                format!(
                    "`{}` computes, so `Delay` values can't all be erased to one token",
                    prim.name()
                ),
            ));
        }
    }
    Ok(())
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
        if let Some(body) = def.body()
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
const TEXT_NATIVES: &[(Builtin, TextNative, &str)] = &[
    (
        Builtin::TextToList,
        TextNative::TextToList,
        "5b7bb97178c88fb32f9dd52228e79092ba01b232b2baec6b3c2bbfc149b7ee25",
    ),
    (
        Builtin::TextFromList,
        TextNative::TextFromList,
        "ff6dfd79fb5d30f73789a90465220af1262921f825fc279131ec998d77aff52c",
    ),
    (
        Builtin::TextAppend,
        TextNative::TextAppend,
        "2932df6055a76217279c02f1029c686f49a3d3f14b07c0d9d2f8d3ad544d228d",
    ),
    (
        Builtin::TextLength,
        TextNative::TextLength,
        "7d849ba83d94eb1c9582a3aed83f96ee47293ad797eb3ab488312f2322338168",
    ),
    (
        Builtin::TextIsEmpty,
        TextNative::TextIsEmpty,
        "8cf3888e45e7b7f0ffdf72aad1d480c2f5a98de424c3b521f3e37d8ed8bc75ce",
    ),
    (
        Builtin::DecEqText,
        TextNative::DecEqText,
        "f8a116b6a32f76629d63dd09dae98c7d4e573b21a9beac53bf9384f00f23500b",
    ),
    (
        Builtin::TextCompare,
        TextNative::TextCompare,
        "760170c44c40d109e8575b4d40883f2667258596d31784411edb92856c49d2af",
    ),
    (
        Builtin::TextUncons,
        TextNative::TextUncons,
        "0ae0aa954e25c910ed2a640d244d6cea813d6ade7a4e8aaae3ab6fab52285daa",
    ),
    (
        Builtin::TextFold,
        TextNative::TextFold,
        "097f7308711e9d444266ff6d4cd122a61408939315f34a2f92f7d642ba8a10f7",
    ),
    (
        Builtin::TextTrim,
        TextNative::TextTrim,
        "7cd992f70a7af95942fdee8093070a0c73ce462379478388309a49a7f1d2c70a",
    ),
    (
        Builtin::TextSplit,
        TextNative::TextSplit,
        "2129a03514372b94ffa763784132d5fc371b9c9fbdeeca6eb577151284807990",
    ),
    (
        Builtin::TextJoin,
        TextNative::TextJoin,
        "e47161040f4bdf30256086842bada04d4577359e53f6a428f3adcdb7c87d1242",
    ),
    (
        Builtin::NatToText,
        TextNative::NatToText,
        "80418de4c24c264a31bef72b6173e2ab3ab8e19c2a8bea7c3355314191e2da0a",
    ),
    (
        Builtin::TextToNat,
        TextNative::TextToNat,
        "97b7fc76c4af2fff57b526a9281489da3096aa21b6374aabbb455b5b06e328aa",
    ),
];

/// Whether a native applies to the program's definition of that name.
pub struct NativeBinding<N> {
    pub name: &'static str,
    pub native: N,
    /// The definition, if there is one.
    pub id: Option<DefId>,
    /// Its content hash, in hex.
    pub hash: Option<String>,
    /// Whether it's the definition the native was written for.
    pub bound: bool,
}

pub type TextBinding = NativeBinding<TextNative>;

/// Matches each native in `table` with the definition it replaces, by
/// content hash.
fn bind_natives<N: Copy>(
    g: &Globals,
    table: &[(Builtin, N, &str)],
) -> Result<Vec<NativeBinding<N>>, ResourceError> {
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    table
        .iter()
        .map(|&(builtin, native, expected)| {
            let id = g.registry.def(builtin);
            let hash = match id {
                Some(id) => def_hash(g, id)?.map(|h| h.hex()),
                None => None,
            };
            Ok(NativeBinding {
                name: builtin.name(),
                native,
                id,
                bound: hash.as_deref() == Some(expected),
                hash,
            })
        })
        .collect()
}

/// Matches each text native with the definition it replaces, by content hash.
pub fn bind_text_natives(g: &Globals) -> Result<Vec<TextBinding>, ResourceError> {
    bind_natives(g, TEXT_NATIVES)
}

/// The content hash (DESIGN.md §11) of the prelude's `Int`, which the
/// `bigint` representation was written for. It covers the constructors,
/// their order, names and fields, and `Nat`. The representation is one
/// contract with its constructors' and matching's JS, the boundary codec,
/// the `.d.ts` type and every integer native, so all of those apply exactly
/// when this matches; otherwise `Int` is compiled as the ordinary data type
/// it is, with the ordinary codec (docs/proposals/integers.md, "Two separate
/// fallbacks"). A test fails until the representation has been checked
/// against a changed `Int` and this updated.
const INT_DATA_HASH: &str = "428aec701d06adbd62795fdbc01b7976c1beac83cdcb385d8d4eaebd14ce4b30";

/// The content hash (DESIGN.md §11) of the prelude's `Nat`, which the
/// `bigint` representation was written for. It covers the constructors,
/// their order, names and fields. The representation is one contract with
/// its constructors' and matching's JS, the boundary codec and the native
/// number operations, so all of those apply exactly when this matches;
/// otherwise `Nat` is compiled as the ordinary data type it is, with the
/// ordinary codec and its operations from their definitions. A test fails
/// until the representation has been checked against a changed `Nat` and
/// this updated.
pub const NAT_DATA_HASH: &str = "281ae0d5e9e49941a6eddd8b4d6b3f3f38a80ea3f95f9692e66096aae10040f5";

/// The content hash (DESIGN.md §11) of the prelude's `Text`, which the JS
/// string representation was written for. It covers its constructor, its
/// name and field, and `List` and `Char`. The representation is one contract
/// with its constructors' and matching's JS, the boundary codec, the `.d.ts`
/// type and every text native, so all of those apply exactly when this
/// matches; otherwise `Text` is compiled as the ordinary data type it is,
/// with the ordinary codec (docs/proposals/compact-text.md, option A), and
/// `run --js`, which requires it, refuses. A test fails until the
/// representation has been checked against a changed `Text` and this
/// updated.
pub const TEXT_DATA_HASH: &str = "ee08e0a61923998097b784cb6b883ed71dbc2781c5af31f823eb6706aae44ee8";

/// Whether the `bigint` representation applies to the program's `Int`, and
/// which integer natives apply to its definitions.
pub struct IntBinding {
    /// The prelude's `Int`, if there is one.
    pub data: Option<DataId>,
    /// Its content hash, in hex.
    pub hash: Option<String>,
    /// Whether it's the data type the representation was written for.
    pub bound: bool,
    /// Each native, whether or not the representation applies: a native is
    /// used only if both its definition and the representation are bound.
    pub natives: Vec<NativeBinding<IntNative>>,
}

/// Matches the `bigint` representation with the prelude's `Int`, and each
/// integer native with the definition it replaces, by content hash.
pub fn bind_int(g: &Globals) -> Result<IntBinding, ResourceError> {
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let data = g.registry.data(Builtin::Int);
    let hash = match data {
        Some(d) => data_hash(g, d)?.map(|h| h.hex()),
        None => None,
    };
    Ok(IntBinding {
        data,
        bound: hash.as_deref() == Some(INT_DATA_HASH),
        hash,
        natives: bind_natives(g, INT_NATIVES)?,
    })
}

/// The prelude's `Int`, if the `bigint` representation applies to it
/// ([`bind_int`]). Hashing a checked data type with two constructors of one
/// field each takes a few stack frames, and the hash is remembered.
fn int_data(g: &Globals) -> Option<DataId> {
    let d = g.registry.data(Builtin::Int)?;
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let hash = data_hash(g, d).expect("internal error: hashing `Int` ran out of resources")?;
    (hash.hex() == INT_DATA_HASH).then_some(d)
}

/// The prelude's `Nat`, if the `bigint` representation applies to it
/// ([`NAT_DATA_HASH`]). Hashing a checked data type takes a few stack frames,
/// and the hash is remembered.
fn nat_data(g: &Globals) -> Option<DataId> {
    let d = g.registry.data(Builtin::Nat)?;
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let hash = data_hash(g, d).expect("internal error: hashing `Nat` ran out of resources")?;
    (hash.hex() == NAT_DATA_HASH).then_some(d)
}

/// The prelude's `Text`, if the JS string representation applies to it
/// ([`TEXT_DATA_HASH`]). Hashing a checked data type takes a few stack
/// frames, and the hash is remembered.
fn text_data(g: &Globals) -> Option<DataId> {
    let d = g.registry.data(Builtin::Text)?;
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let hash = data_hash(g, d).expect("internal error: hashing `Text` ran out of resources")?;
    (hash.hex() == TEXT_DATA_HASH).then_some(d)
}

/// A prelude integer operation with a native JS implementation, in generated
/// code where an `Int` is a `bigint` ([`Options::native_int`]). Like the
/// number and text natives, these are trusted, and tested against the
/// definitions they replace (`crates/cli/tests/extract.rs`). A division's
/// proof that the divisor isn't zero is erased, but it exists (or an
/// export's precondition check has just established it), so none of these
/// divides by zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntNative {
    NatToInt,
    IntNeg,
    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    IntMod,
    IntTDiv,
    IntTMod,
    IntFDiv,
    IntFMod,
    IntModNat,
    DecEqInt,
    IntLeq,
    IntLess,
    IntCompare,
    IntNatAbs,
    IntAbs,
    IntToNat,
    IntToNatChecked,
    IntSign,
    IntToText,
    TextToInt,
}

impl IntNative {
    /// Whether it also assumes that a `Text` is a string
    /// ([`Options::native_text`]).
    fn uses_text(self) -> bool {
        matches!(self, IntNative::IntToText | IntNative::TextToInt)
    }
}

/// Each integer native, the prelude definition it replaces, and that
/// definition's content hash, as for [`TEXT_NATIVES`].
const INT_NATIVES: &[(Builtin, IntNative, &str)] = &[
    (
        Builtin::NatToInt,
        IntNative::NatToInt,
        "6e9973e4558cd61d9f97a8a168d3c7c644ee38be27a43c1eb32cc4b60338cb98",
    ),
    (
        Builtin::IntNeg,
        IntNative::IntNeg,
        "347cfafd037525c1413df9f8db0642268050cebc4d5f9b45bb402e53f4c828cd",
    ),
    (
        Builtin::IntAdd,
        IntNative::IntAdd,
        "8e3611484f01b9db8555c2ad9d374082dabdda2863f293adbf109a7dc248eb7f",
    ),
    (
        Builtin::IntSub,
        IntNative::IntSub,
        "5f86c2911011a929b23204a693c68c066b16c39839417876e6e53f96ee9b66f9",
    ),
    (
        Builtin::IntMul,
        IntNative::IntMul,
        "be8f0dc36cee51571529c6f3badbbb2a319ad742a71ca6f8185eba4fba0268d8",
    ),
    (
        Builtin::IntDiv,
        IntNative::IntDiv,
        "00184364ab716015c02cb9fd21b1a087e7dbf106ae1d4afc176e077e59a71e87",
    ),
    (
        Builtin::IntMod,
        IntNative::IntMod,
        "59337e39965a2e98bd60485b9bd781d0bc770b72f9a1d33feaa7b28e8911c8db",
    ),
    (
        Builtin::IntTDiv,
        IntNative::IntTDiv,
        "7b8beafe3bd733da9cc032f34ceff34722d1a765966d4e9d71837f099bf6cd91",
    ),
    (
        Builtin::IntTMod,
        IntNative::IntTMod,
        "48b63851b1fed3d950ea3ddd134e4d0ab56653c636e33dd7e9ec4b338aa7602c",
    ),
    (
        Builtin::IntFDiv,
        IntNative::IntFDiv,
        "fd93a2b681035e898a6ca0ed09c78124e53bc5875c93f2d30b46896dfca56920",
    ),
    (
        Builtin::IntFMod,
        IntNative::IntFMod,
        "c06a2c8bd4fb9fbe9b77c2499f1669a0b1d0ab5abf17130f110ef7a6f025b084",
    ),
    (
        Builtin::IntModNat,
        IntNative::IntModNat,
        "8a2aad6298178d66ea6eea919447ce977dc966504e0cf63e6ef5a89d982a24c6",
    ),
    (
        Builtin::DecEqInt,
        IntNative::DecEqInt,
        "19a294aa23ae9b96c6960af32f50d921968c5921d779ce6dcb550aacadcf2e3f",
    ),
    (
        Builtin::IntLeq,
        IntNative::IntLeq,
        "1076606963454e39dc191da34bbe1321ba54284d5597a50451af3b9c10ebcac6",
    ),
    (
        Builtin::IntLess,
        IntNative::IntLess,
        "206176cbbaa05dc2f9486d7e52c86aedf381cbd28945f337f26e73928221763b",
    ),
    (
        Builtin::IntCompare,
        IntNative::IntCompare,
        "ef69f80765a9b9cca880a9c260b0c82b3521fde01f4cacdcea76eeca685f7212",
    ),
    (
        Builtin::IntNatAbs,
        IntNative::IntNatAbs,
        "ba7abe1722616144bdd8c853b8857234cde73e16cb804dfaa9a0338bbdd6c50a",
    ),
    (
        Builtin::IntAbs,
        IntNative::IntAbs,
        "9c9c66ca4fbfca3668de18a91351c4cea27ae57b6ebaa13c4111d33ec857efb0",
    ),
    (
        Builtin::IntToNat,
        IntNative::IntToNat,
        "ba03131d46190cbd9ce659db558566c7ae783121cd53b42c7214b107bda06eb1",
    ),
    (
        Builtin::IntToNatChecked,
        IntNative::IntToNatChecked,
        "c547e9888ac69af472db81dd6d5d8ad4c37eb090e69144d1c0c72eff07e8634c",
    ),
    (
        Builtin::IntSign,
        IntNative::IntSign,
        "0d3ecb4f6ca1f8fcd622fe27004aa12669b02001eb36f4a8479964458da2edc3",
    ),
    (
        Builtin::IntToText,
        IntNative::IntToText,
        "95601003651a6f560af094a588ce3bac634034f85ca0e574524e32383c6e776d",
    ),
    (
        Builtin::TextToInt,
        IntNative::TextToInt,
        "563e15d014538fc8e81a6607b60b2c064d54fa27e83f114227ec4b3472667b7f",
    ),
];

/// JS for an integer native. The prelude's types have the representation the
/// runtime uses (`Some`'s `value`, the constructors' names as tags). BigInt's
/// `/` and `%` truncate towards zero, and `%` takes the dividend's sign
/// (truncated division); the Euclidean and floored conventions correct that
/// by one step where the remainder has the wrong sign (Leijen, "Division and
/// modulus for computer scientists").
fn int_native_js(op: IntNative) -> &'static str {
    match op {
        IntNative::NatToInt => "(n) => n",
        IntNative::IntNeg => "(a) => -a",
        IntNative::IntAdd => "(a) => (b) => a + b",
        IntNative::IntSub => "(a) => (b) => a - b",
        IntNative::IntMul => "(a) => (b) => a * b",
        // Euclidean: the remainder is never negative.
        IntNative::IntDiv => {
            "(a) => (d) => { const q = a / d, r = a % d; return r < 0n ? (d > 0n ? q - 1n : q + 1n) : q; }"
        }
        IntNative::IntMod => {
            "(a) => (d) => { const r = a % d; return r < 0n ? (d > 0n ? r + d : r - d) : r; }"
        }
        IntNative::IntTDiv => "(a) => (d) => a / d",
        IntNative::IntTMod => "(a) => (d) => a % d",
        // Floored: the remainder has the divisor's sign.
        IntNative::IntFDiv => {
            "(a) => (d) => { const q = a / d, r = a % d; return r !== 0n && (r < 0n) !== (d < 0n) ? q - 1n : q; }"
        }
        IntNative::IntFMod => {
            "(a) => (d) => { const r = a % d; return r !== 0n && (r < 0n) !== (d < 0n) ? r + d : r; }"
        }
        // The divisor is a positive `Nat`.
        IntNative::IntModNat => "(a) => (d) => { const r = a % d; return r < 0n ? r + d : r; }",
        IntNative::DecEqInt => "(a) => (b) => ({ tag: a === b ? \"Yes\" : \"No\" })",
        IntNative::IntLeq => "(a) => (b) => ({ tag: a <= b ? \"True\" : \"False\" })",
        IntNative::IntLess => "(a) => (b) => ({ tag: a < b ? \"True\" : \"False\" })",
        IntNative::IntCompare => {
            "(a) => (b) => ({ tag: a < b ? \"Less\" : a === b ? \"Equal\" : \"Greater\" })"
        }
        IntNative::IntNatAbs | IntNative::IntAbs => "(a) => (a < 0n ? -a : a)",
        IntNative::IntToNat => "(a) => (a < 0n ? 0n : a)",
        IntNative::IntToNatChecked => {
            "(a) => (a < 0n ? { tag: \"None\" } : { tag: \"Some\", value: a })"
        }
        IntNative::IntSign => "(a) => (a > 0n ? 1n : a < 0n ? -1n : 0n)",
        IntNative::IntToText => "(a) => a.toString()",
        // An optional `-`, then what `Text.toNat` accepts: one or more ASCII
        // digits and nothing else. (`BigInt` alone would also accept "",
        // " 12", "+5" and "0x10".) `-0` is `0`.
        IntNative::TextToInt => {
            r#"(t) => {
  const s = t.charCodeAt(0) === 45 ? t.slice(1) : t;
  if (s === "") return { tag: "None" };
  for (let i = 0; i < s.length; i++) {
    const unit = s.charCodeAt(i);
    if (unit < 48 || unit > 57) return { tag: "None" };
  }
  const n = BigInt(s);
  return { tag: "Some", value: s === t ? n : -n };
}"#
        }
    }
}

/// JS for a text native. The runtime's helpers (`TEXT_AS_STRING`) are in
/// scope, and the prelude's types have the representation the runtime uses
/// (`MkChar`'s `code`, `Cons`'s `head` and `tail`, `Some`'s `value`,
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
  if (t === "") return { tag: "None" };
  const code = t.codePointAt(0);
  const c = { tag: "MkChar", code: BigInt(code) };
  return { tag: "Some", value: { tag: "MkPair", fst: c, snd: t.slice(code > 0xffff ? 2 : 1) } };
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
  if (t === "") return { tag: "None" };
  for (let i = 0; i < t.length; i++) {
    const unit = t.charCodeAt(i);
    if (unit < 48 || unit > 57) return { tag: "None" };
  }
  return { tag: "Some", value: BigInt(t) };
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

/// A definition's JS name, from its full logical name (`Std.List.length`):
/// `$` and the name, [`encode`]d. A name starts with a letter or `_`, so a
/// definition's JS name is never `$$…`, which is an export's wrapper's.
fn def_name(path: &str) -> String {
    if path.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') {
        format!("${}", encode(path))
    } else {
        format!("$$${}", encode(path))
    }
}

/// A name of declarations (`Std.List.%res`, `x'`), as JS identifier
/// characters, injectively (docs/proposals/namespaces.md §7.3): ASCII letters,
/// digits and `_` stay; `'` is `$p`, `.` is `$d` and `%` is `$g`; any other
/// character is `$u` and its code as six hex digits. Source names never
/// contain `$`, and each `$` starts exactly one escape, so the name can be
/// read back.
pub fn encode(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for c in name.chars() {
        match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '_' => out.push(c),
            '\'' => out.push_str("$p"),
            '.' => out.push_str("$d"),
            '%' => out.push_str("$g"),
            other => {
                let _ = write!(out, "$u{:06x}", u32::from(other));
            }
        }
    }
    out
}

/// The last component of a qualified name: what an export or a boundary type
/// is called in JS and TypeScript.
fn short_name(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
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

/// The key of field `i` of constructor `c` of data type `d` inside
/// generated code: [`key`], unless the constructor has two fields of that
/// name (a partial definition's request type has a field `_` for each
/// unnamed parameter), when it's `$i`, which no name's key can be.
pub(crate) fn field_key_at(g: &Globals, d: DataId, c: usize, i: usize) -> String {
    let fields = &g.data(d).ctors[c].fields;
    let name = &fields[i].0;
    if fields.iter().filter(|(n, _)| n == name).count() > 1 {
        format!("${i}")
    } else {
        key(g, d, name)
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

/// A data type's name in the TypeScript declarations: its short name, with
/// each prime as `$`. Two types at the boundary with the same short name are
/// refused (`E-EXPORT`).
fn type_name(name: &str) -> String {
    short_name(name).replace('\'', "$")
}

/// The JS name of the description of a data type (see `datatype` in
/// [`RUNTIME`]), from its full logical name.
fn info_name(path: &str) -> String {
    format!("info${}", encode(path))
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
        // `OfNat n` is `n`, and `NegSucc n` is `-n - 1`.
        (Boundary::Int, Value::Ctor(_, c, fields)) => {
            match native::as_nat(g, &fields[0]).map_err(|e| e.to_string())? {
                Some(n) if *c == 0 => Ok(format!("{n}n")),
                Some(n) => Ok(format!("-{}n", n + 1u32)),
                None => Err(stuck()),
            }
        }
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
    use std::collections::HashMap;

    use super::{RUNTIME, def_name, encode, info_name, is_js_identifier, mentions, wrapper_name};

    /// Every name of up to four characters from the characters names can
    /// contain (docs/proposals/namespaces.md §7.3): those the lexer accepts
    /// in a name (letters, digits, `_`, `'`), the `.` of a qualified name,
    /// the `%` of a generated one, and one character beyond ASCII.
    fn names() -> Vec<String> {
        const CHARS: &[char] = &['a', 'Z', '0', '_', '\'', '.', '%', 'é'];
        let mut names = vec![String::new()];
        let mut all = Vec::new();
        for _ in 0..4 {
            names = names
                .iter()
                .flat_map(|n| CHARS.iter().map(move |c| format!("{n}{c}")))
                .collect();
            all.extend(names.iter().cloned());
        }
        all
    }

    #[test]
    fn definition_names_are_distinct_valid_identifiers() {
        let mut seen: HashMap<String, String> = HashMap::new();
        for name in names() {
            let js = def_name(&name);
            assert!(is_js_identifier(&js), "{name:?} is {js:?}");
            if let Some(other) = seen.insert(js.clone(), name.clone()) {
                panic!("{name:?} and {other:?} are both {js:?}");
            }
            assert!(is_js_identifier(&info_name(&name)), "{name:?}");
            assert_eq!(
                encode(&name).contains('$'),
                name.chars().any(|c| !c.is_ascii_alphanumeric() && c != '_')
            );
        }
    }

    /// The generator's naming schemes never meet: definitions are `$` and a
    /// letter, `_` or `$$$`; export wrappers `$$` and a letter (an export's
    /// name is a JS identifier without `$`); descriptions of data types
    /// `info$…`; the runtime's own names have no `$`.
    #[test]
    fn naming_schemes_are_disjoint() {
        let defs: Vec<String> = names().iter().map(|n| def_name(n)).collect();
        for export in ["f", "Shape", "_x", "x1"] {
            let wrapper = wrapper_name(export);
            assert!(!defs.contains(&wrapper), "{wrapper}");
        }
        for name in names() {
            assert!(!def_name(&name).starts_with("info"));
            assert!(info_name(&name).starts_with("info$"));
        }
        let runtime: Vec<&str> = RUNTIME
            .lines()
            .filter_map(|l| {
                l.strip_prefix("const ")
                    .or_else(|| l.strip_prefix("function "))
            })
            .filter_map(|l| {
                l.split(|c: char| !c.is_ascii_alphanumeric() && c != '_' && c != '$')
                    .next()
            })
            .collect();
        assert!(runtime.len() > 5, "{runtime:?}");
        for helper in runtime {
            assert!(!helper.contains('$'), "{helper}");
        }
    }

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
