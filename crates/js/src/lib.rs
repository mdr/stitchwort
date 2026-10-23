//! JavaScript extraction (DESIGN.md §12): erase types and proofs, generate an
//! ES module, and wrap each export in decode → compute → encode.
//!
//! First-milestone scope: exports take and return concrete first-order data
//! (`Nat`, `Bool`, `Text`, `Char`, `List`, and data types built from them,
//! such as `Option Text`), and their proof arguments are checked at runtime.

use std::cell::{Cell, OnceCell, RefCell};
use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use std::rc::Rc;

use stitchwort_core::check::{is_type_former, telescope};
use stitchwort_core::js_repr::{self, JsRepr};
use stitchwort_core::native;
use stitchwort_core::partial::Primitive;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{Head, eval, expand_step, quote};
use stitchwort_core::{
    BigUint, DataId, DefId, Globals, Limits, ResourceError, Sort, Term, Value, pretty,
};
use stitchwort_rt::erasure::{def_shape, reachable, text_literal};
use stitchwort_rt::natives::{
    FloatPrim, Representation, float_data, int_data, nat_data, safe_int_data, safe_nat_data,
    text_data,
};
// Shared with the runtime (D389), and part of this crate's interface.
pub use stitchwort_rt::natives::{
    IntBinding, IntNative, NAT_DATA_HASH, NativeBinding, SAFE_INT_HASH, SAFE_NAT_HASH,
    TEXT_DATA_HASH, TextBinding, TextNative, bind_int, bind_text_natives,
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
    /// `number`, a whole number from 0 to 2^53 - 1: the library's `SafeNat`
    /// (std/Int/Safe.sw), when it's the data type the codec was written for
    /// ([`SAFE_NAT_HASH`]).
    SafeNat,
    /// `number`, a whole number from -(2^53 - 1) to 2^53 - 1: the library's
    /// `SafeInt`, when it's the data type the codec was written for
    /// ([`SAFE_INT_HASH`]).
    SafeInt,
    /// `number`, any number, `NaN`, the infinities and `-0` included: the
    /// library's `Float` (std/Float/Float.sw), when it's the declaration the
    /// kernel binds (docs/proposals/float.md §5, D685). Every NaN denotes
    /// `Float.nan`; the number itself is passed through.
    Float,
    /// `boolean`.
    Bool,
    /// `string`, well-formed (no lone surrogates): the prelude's `Text`, when
    /// it's the data type the representation was written for
    /// ([`TEXT_DATA_HASH`]).
    Text,
    /// `string`, holding exactly one Unicode scalar value.
    Char,
    /// `readonly T[]` as a function's parameter, `T[]` elsewhere.
    List(Box<Boundary>),
    /// The prelude's `Option T` (the `DataId`), as `T | undefined`: in a
    /// record's field, an optional property (D582). An `Option (Option T)`'s
    /// inner `Option` is the tagged [`Boundary::Data`] instead, so `Some None`
    /// and `None` stay apart: see [`Boundary::payload`].
    Option(DataId, Box<Boundary>),
    /// The library's `Map Text V` (the `DataId`), ordered by the library's
    /// `Text` order, as a plain object `{ readonly [k: string]: V }`: the
    /// keys are the map's keys, the values are `V`'s encoding.
    Map(DataId, Box<Boundary>),
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
            Boundary::Option(d, inner) => Boundary::Option(*d, Box::new(inner.instantiate(args))),
            Boundary::Map(d, value) => Boundary::Map(*d, Box::new(value.instantiate(args))),
            Boundary::Data(d, own) => {
                Boundary::Data(*d, own.iter().map(|b| b.instantiate(args)).collect())
            }
            other => other.clone(),
        }
    }

    /// What an `Option` boundary has in place of `undefined`: the type
    /// inside, or, if that's an `Option` too, its tagged data type (its
    /// payload as the argument).
    #[must_use]
    pub fn payload(&self) -> Boundary {
        match self {
            Boundary::Option(_, inner) => match &**inner {
                Boundary::Option(d, j) => Boundary::Data(*d, vec![(**j).clone()]),
                other => other.clone(),
            },
            other => other.clone(),
        }
    }

    /// Whether a map is this type or inside it (not counting the fields of a
    /// data type).
    fn has_map(&self) -> bool {
        match self {
            Boundary::Map(..) => true,
            Boundary::List(elem) | Boundary::Option(_, elem) => elem.has_map(),
            Boundary::Data(_, args) => args.iter().any(Boundary::has_map),
            _ => false,
        }
    }

    /// Whether `leaf` is this type or inside it (not counting the fields of
    /// a data type).
    fn mentions(&self, leaf: &Boundary) -> bool {
        self == leaf
            || match self {
                Boundary::List(elem) | Boundary::Option(_, elem) | Boundary::Map(_, elem) => {
                    elem.mentions(leaf)
                }
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
            // The built-in types with a boundary form of their own, chosen by
            // identity from the registry's one list (D613): a program's own
            // `List` is encoded as the data type it is. Where the codec
            // depends on the declaration, its content hash confirms it;
            // otherwise the type crosses as the data type it is.
            let builtin = g.registry.boundary_form(*d);
            // `SafeNat` and `SafeInt` are records of a `Nat` or `Int` inside
            // generated code, and `number`s at the boundary, which the codec
            // needs the `bigint` representations for.
            match builtin {
                Some(Builtin::SafeNat)
                    if args.is_empty() && safe_nat_data(g) == Some(*d) && nat_data(g).is_some() =>
                {
                    return Ok(Boundary::SafeNat);
                }
                Some(Builtin::SafeInt)
                    if args.is_empty() && safe_int_data(g) == Some(*d) && int_data(g).is_some() =>
                {
                    return Ok(Boundary::SafeInt);
                }
                Some(Builtin::Int) if args.is_empty() && int_data(g) == Some(*d) => {
                    return Ok(Boundary::Int);
                }
                Some(Builtin::Float) if args.is_empty() && float_data(g) == Some(*d) => {
                    return Ok(Boundary::Float);
                }
                Some(Builtin::Nat) if args.is_empty() && nat_data(g) == Some(*d) => {
                    return Ok(Boundary::Nat);
                }
                Some(Builtin::Text) if args.is_empty() && text_data(g) == Some(*d) => {
                    return Ok(Boundary::Text);
                }
                _ => {}
            }
            match (builtin, args.as_slice()) {
                (Some(Builtin::Bool), []) => Ok(Boundary::Bool),
                (Some(Builtin::Char), []) => Ok(Boundary::Char),
                // The library's `Map` is a dictionary: a plain object. Only a
                // map from `Text`, in `Text`'s own order, can be one.
                (Some(Builtin::Map), [key, value, order]) => {
                    let text_key = matches!(key, Value::Data(t, a) if a.is_empty() && text_data(g) == Some(*t));
                    if !text_key {
                        return Err(format!(
                            "`{}` can't cross the JS boundary: only maps from `Text` cross, as plain objects",
                            pretty::value(g, &[], ty)
                        ));
                    }
                    if !is_text_order(g, order) {
                        return Err(format!(
                            "`{}` can't cross the JS boundary: a map crosses only in `Text`'s own \
                             order (`Text.instOrd`), which its keys are sorted by",
                            pretty::value(g, &[], ty)
                        ));
                    }
                    let value = boundary(g, value, params, visiting)?;
                    Ok(Boundary::Map(*d, Box::new(value)))
                }
                (Some(Builtin::List), [elem]) => Ok(Boundary::List(Box::new(boundary(
                    g, elem, params, visiting,
                )?))),
                (Some(Builtin::Option), [elem]) => {
                    let inner = boundary(g, elem, params, visiting)?;
                    check_codec(g, *d, visiting)?;
                    Ok(Boundary::Option(*d, Box::new(inner)))
                }
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

/// Whether `order` is the library's `Text.instOrd`, the ordering a map that
/// crosses as an object is sorted by.
fn is_text_order(g: &Globals, order: &Value) -> bool {
    let Some(text_order) = g.registry.loaded_def(Builtin::TextInstOrd) else {
        return false;
    };
    match order {
        Value::Call(id, spine, _) => *id == text_order && spine.is_empty(),
        Value::Neutral(Head::Def(id), spine) => *id == text_order && spine.is_empty(),
        _ => false,
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
    // (That each field has its own key at the boundary is checked with the
    // rest of the type's names, in `check_names`.)
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
    // Each type's names at the boundary (docs/proposals/attributes.md §4.6):
    // a type with `js.*` attributes had its checked where it's declared; one
    // without is checked here, once an export reaches it (D612), so a type
    // that never crosses may have a field `__proto__`.
    for &d in &boundary_datas {
        let data = g.data(d);
        if data.js.is_some() {
            continue;
        }
        let repr = repr(g, d);
        if let Some(clash) = js_repr::clashes(&repr, data.record).first() {
            let mut diagnostic = Diagnostic::error("E-JS-NAME-CLASH", clash.message(data, &repr))
                .with_label(data.span, "this type crosses the JS boundary");
            let reaches = |sig: &&ExportSig| {
                let mut datas = Vec::new();
                for b in sig.params.iter().map(|(_, b)| b).chain([&sig.result]) {
                    collect_datas(g, b, &mut datas);
                }
                datas.contains(&d)
            };
            if let Some(sig) = exports.iter().find(reaches) {
                diagnostic = diagnostic.with_label(
                    g.def(sig.id).span,
                    format!("`{}` is exported, and reaches it", g.def(sig.id).name),
                );
            }
            return Err(diagnostic.with_note(clash.note()));
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
    // A map that crosses is built and read with the library's own `Map`
    // functions, so they're generated, with the `Text` order they're given.
    let maps_cross = exports
        .iter()
        .flat_map(|sig| sig.params.iter().map(|(_, b)| b).chain([&sig.result]))
        .any(Boundary::has_map)
        || boundary_datas.iter().any(|d| {
            generic_field_boundaries(g, *d)
                .iter()
                .flatten()
                .any(|(_, b)| b.has_map())
        });
    let map_defs: Vec<DefId> = if maps_cross {
        [
            Builtin::MapFromList,
            Builtin::MapToList,
            Builtin::TextInstOrd,
        ]
        .into_iter()
        .map(|b| {
            g.registry
                .loaded_def(b)
                .expect("a map crosses only with the library's `Map` loaded")
        })
        .collect()
    } else {
        Vec::new()
    };
    let checks = checks.chain(map_defs.iter().copied());
    let failure = std::cell::RefCell::new(None);
    let used = reachable(
        g,
        exports.iter().map(|sig| sig.id).chain(checks),
        |id| match codegen.try_info(id) {
            Ok(info) => info.result_erased || codegen.is_native(id) || info.delay.is_some(),
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
    if codegen.float.is_some() {
        js.push_str(FLOAT_BITS);
    }
    if codegen.text.is_some() {
        js.push_str(TEXT_AS_STRING);
        js.push_str(CHARS_OF_TEXT);
        js.push_str(TEXT_OF_CHARS);
    } else {
        js.push_str(TEXT_AS_LIST);
        js.push_str(CHARS_OF_TEXT);
    }
    // `INT` only where it's used.
    let crosses = |leaf: Boundary| {
        let at_boundary = |b: &Boundary| b.mentions(&leaf);
        exports
            .iter()
            .flat_map(|sig| sig.params.iter().map(|(_, b)| b).chain([&sig.result]))
            .any(at_boundary)
            || boundary_datas.iter().any(|d| {
                generic_field_boundaries(g, *d)
                    .iter()
                    .flatten()
                    .any(|(_, b)| at_boundary(b))
            })
    };
    let safe_nat_crosses = crosses(Boundary::SafeNat);
    let safe_int_crosses = crosses(Boundary::SafeInt);
    if let Some(int) = int_data(g).filter(|_| safe_int_crosses || crosses(Boundary::Int)) {
        js.push_str(&codegen.int_codec(int));
    }
    if crosses(Boundary::Float) {
        js.push_str(FLOAT_CODEC);
    }
    if safe_nat_crosses || safe_int_crosses {
        js.push_str(&codegen.safe_codecs(
            safe_nat_data(g).filter(|_| safe_nat_crosses),
            safe_int_data(g).filter(|_| safe_int_crosses),
        ));
    }
    js.push_str(RUNTIME_CODECS);
    js.push('\n');
    // Every data type is declared before any is defined, so their fields'
    // types can refer to each other (and themselves).
    for &d in &boundary_datas {
        let data = g.data(d);
        let tag_key = repr(g, d).tag_key.clone();
        // The tag key, unless it's the default (or the type is a record).
        let key = if data.record || tag_key == js_repr::DEFAULT_TAG_KEY {
            String::new()
        } else {
            format!(", {}", js_string_literal(&tag_key))
        };
        let _ = writeln!(
            js,
            "const {} = datatype({}{key});",
            info_name(&data.path),
            js_string_literal(&data.name)
        );
    }
    // How the runtime builds and takes apart an `Option`.
    if let Some(&d) = boundary_datas
        .iter()
        .find(|d| g.registry.is_data(Builtin::Option, **d))
    {
        let data = g.data(d);
        let some = &data.ctors[1];
        let _ = writeln!(
            js,
            "const OPTION_SHAPE = {{ info: {}, none: {}, some: {}, key: {} }};",
            info_name(&data.path),
            js_string_literal(&data.ctors[0].name),
            js_string_literal(&some.name),
            js_string_literal(&field_key_at(g, d, 1, 0)),
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
    let wanted: Vec<DefId> = (0..g.defs.len())
        .map(DefId)
        .filter(|id| used[id.0] && codegen.info(*id).delay.is_none())
        .collect();
    for id in dependency_order(g, &wanted) {
        // Only an admitted definition has a body. The driver doesn't extract
        // a module with errors, but if it were asked to, the JS would call a
        // function that isn't there.
        let def = g.def(id);
        if def.body().is_none() && !codegen.info(id).result_erased && !codegen.is_native(id) {
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
    if maps_cross {
        js.push_str(&codegen.map_shape().map_err(Diagnostic::from)?);
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
    // `Option` has a declaration only where a nested one is the tagged union.
    let tagged_option = exports
        .iter()
        .flat_map(|sig| sig.params.iter().map(|(_, b)| b).chain([&sig.result]))
        .any(|b| names_option(g, b))
        || boundary_datas.iter().any(|d| {
            generic_field_boundaries(g, *d)
                .iter()
                .flatten()
                .any(|(_, b)| names_option(g, b))
        });
    for &d in &boundary_datas {
        if g.registry.is_data(Builtin::Option, d) && !tagged_option {
            continue;
        }
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

/// Whether `b` has the prelude's `Option` as a tagged data type in it: a
/// nested one (not counting the fields of data types).
fn names_option(g: &Globals, b: &Boundary) -> bool {
    match b {
        Boundary::List(elem) | Boundary::Map(_, elem) => names_option(g, elem),
        Boundary::Option(..) => names_option(g, &b.payload()),
        Boundary::Data(d, args) => {
            g.registry.is_data(Builtin::Option, *d) || args.iter().any(|a| names_option(g, a))
        }
        _ => false,
    }
}

fn collect_datas(g: &Globals, b: &Boundary, out: &mut Vec<DataId>) {
    match b {
        Boundary::Nat
        | Boundary::Int
        | Boundary::SafeNat
        | Boundary::SafeInt
        | Boundary::Float
        | Boundary::Bool
        | Boundary::Text
        | Boundary::Char
        | Boundary::Param(_) => {}
        Boundary::List(elem) | Boundary::Map(_, elem) => collect_datas(g, elem, out),
        Boundary::Option(d, _) => {
            // The runtime needs `Option`'s description (for the tags of a
            // nested one) whenever an `Option` crosses.
            if !out.contains(d) {
                out.push(*d);
                for fields in generic_field_boundaries(g, *d) {
                    for (_, b) in fields {
                        collect_datas(g, &b, out);
                    }
                }
            }
            collect_datas(g, &b.payload(), out);
        }
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
// - `param(i)`, in a field's type, is the data type's parameter `i`;
// - `option(t)` is `undefined` for `None` and `t`'s own encoding for `Some`
//   (D582). In a record's field (marked optional in `define`), `None` is a
//   missing property. An `Option` of an `Option` has the tagged data type
//   (`OPTION_SHAPE.info`) inside instead, so `Some None` and `None` stay
//   apart (`payload`);
// - `map(t)` is a `Map Text t` (the library's), as a plain object: decoding
//   reads the object's own enumerable string keys and builds the map from
//   its entries with the library's own `Map.fromList` (`MAP_SHAPE`), and
//   encoding makes a fresh object, key by key, from `Map.toList`.
// `open` says whether a type mentions a parameter. Each type is made once
// (`list` and `data` give back the same object for the same arguments), so
// two types are the same exactly when they're the same object, and `decode`
// can remember what it has decoded at each. There are only so many: a data
// type's fields can only mention it, and the types defined together with it,
// applied to their own parameters (the positivity check), and otherwise only
// types declared before them, so a boundary type has finitely many types
// inside it.
const LEAF = 0, LIST = 1, DATA = 2, PARAM = 3, OPTION = 4, MAP = 5;
let typeCount = 0;
const leaf = (dec, enc) => ({ kind: LEAF, open: false, id: typeCount++, dec, enc });
const list = (elem) => (elem.list ??= { kind: LIST, open: elem.open, id: typeCount++, elem });
const option = (elem) => (elem.option ??= { kind: OPTION, open: elem.open, id: typeCount++, elem });
const map = (elem) => (elem.map ??= { kind: MAP, open: elem.open, id: typeCount++, elem });
// What an option has in place of `undefined`: its type, or if that's an
// option too, the tagged data type with that one's type as its argument.
const payload = (t) =>
  (t.payload ??= t.elem.kind === OPTION ? data(OPTION_SHAPE.info, [t.elem.elem]) : t.elem);
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
// A data type's description. `tagKey` is the property its objects' tag is
// in at the boundary; inside generated code it's always `tag`.
const datatype = (name, tagKey = "$tag") => ({
  name, tagKey, ctors: new Map(), internal: new Map(), flat: new Set(), tags: "",
  instances: new Map(), record: undefined, checks: [],
});
// Each constructor's tag, and its fields' keys and types, in order. A
// constructor is `flat` if all its fields are leaves. A record has one
// constructor, whose fields are `info.record`, and no tag; `checks` are its
// proof fields' runtime checks, each a message and a function of a decoded
// object saying whether the proof holds. Names at the boundary may differ
// from those inside generated code (`js.tag`, `js.name`): `ctors` finds a
// constructor by its tag at the boundary, `internal` by its tag inside.
const define = (info, ctors, record = false, checks = []) => {
  // A constructor is `[tag, fields]`, or `[tag, fields, tag at the
  // boundary]`. A field is `[key, type]`, `[key, type, true]` for an
  // optional property, or `[key, type, optional, key inside]`.
  const entries = ctors.map(([tag, fields, external = tag]) => ({
    tag,
    external,
    fields: fields.map(([key, type, optional = false, inside = key]) => [key, type, optional, inside]),
  }));
  if (record) info.record = entries[0].fields;
  info.checks = checks;
  for (const entry of entries) {
    info.ctors.set(entry.external, entry);
    info.internal.set(entry.tag, entry);
    if (entry.fields.every(([, t]) => t.kind === LEAF)) info.flat.add(entry.external);
  }
  const tags = entries.map((e) => JSON.stringify(e.external));
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
  : t.kind === OPTION ? option(close(t.elem, args))
  : t.kind === MAP ? map(close(t.elem, args))
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
// that the message stays short: a run of the same step, or of a cycle of up
// to three steps, is written once with a count, and the middle of a long path
// is left out.
// A map's key is any string: one that isn't a name is quoted, and a long one
// is cut short.
const step = (s) =>
  typeof s === "number" ? `[${s}]`
  : s.length <= 40 && /^[A-Za-z_$][A-Za-z0-9_$]*$/.test(s) ? `.${s}`
  : `[${JSON.stringify(s.length > 40 ? `${s.slice(0, 40)}…` : s)}]`;
const pathText = (root, path) => {
  if (path.length <= 12) return root + path.map(step).join("");
  const runs = [];
  for (let i = 0; i < path.length; ) {
    let length = 0, count = 0;
    for (let l = 1; l <= 3 && i + l <= path.length; l++) {
      let n = 1;
      while (i + (n + 1) * l <= path.length) {
        let same = true;
        for (let k = 0; k < l; k++) {
          if (path[i + n * l + k] !== path[i + k]) { same = false; break; }
        }
        if (!same) break;
        n++;
      }
      if (n > 3) { length = l; count = n; break; }
    }
    if (count > 3) {
      const block = path.slice(i, i + length).map(step).join("");
      runs.push({ text: `(${block} ×${count})`, steps: length * count });
      i += length * count;
    } else {
      runs.push({ text: step(path[i]), steps: 1 });
      i++;
    }
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
const threw = (e) => {
  let what = "an error";
  try {
    what = e instanceof Error ? `${e.name}: ${e.message}` : String(e);
  } catch {}
  return refuse(`reading it threw ${what.length > 80 ? `${what.slice(0, 80)}…` : what}`, e);
};
const own = (x, key) => {
  try {
    return hasOwn(x, key) ? x[key] : key in x ? INHERITED : MISSING;
  } catch (e) {
    return threw(e);
  }
};

// The keys of an object that is to be a `Map Text V`: its own enumerable
// string keys (symbols and inherited or non-enumerable properties aren't
// entries), in the engine's order. `__proto__` is a key like any other when
// it's an own property (`JSON.parse` makes one), and nothing here assigns to
// an object by key. The object must be a plain one, made by `{}`, `JSON.parse`
// or `Object.create(null)`: a `Map`, a `Date` or a class instance has
// something else to say, and reading no keys from it would silently give an
// empty map. (An `Object.prototype` from another realm, as in a `vm` context
// or an iframe, is a plain one too: a prototype with no prototype that has
// the `Object.prototype` methods of its own.)
const plainKeys = (x) => {
  if (typeof x !== "object" || x === null) refuse("expected an object");
  if (Array.isArray(x)) refuse("expected an object, not an array");
  try {
    const proto = Object.getPrototypeOf(x);
    const plain =
      proto === null ||
      proto === Object.prototype ||
      (Object.getPrototypeOf(proto) === null && hasOwn(proto, "isPrototypeOf"));
    if (!plain) {
      refuse("expected a plain object, not a Map, a class instance or another kind of object");
    }
    return Object.keys(x);
  } catch (e) {
    if (e instanceof Refusal) throw e;
    return threw(e);
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
      // An `Option` is `undefined`, or what's inside it: `null` is neither.
      while (t.kind === OPTION) {
        if (x === undefined) {
          value = { tag: OPTION_SHAPE.none };
          break;
        }
        if (x === null) refuse("expected a value or undefined, not null");
        frames.push({ t, opt: true });
        t = payload(t);
      }
      if (value !== NONE) {
        // `None`.
      } else if (t.kind === LEAF) {
        value = t.dec(x);
      } else {
        if (t.kind === LIST) {
          if (!Array.isArray(x)) refuse("expected an array");
        } else if (t.kind === MAP) {
          // The keys are read once the object turns out not to be known.
          if (typeof x !== "object" || x === null) refuse("expected an object");
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
        } else if (t.kind === MAP) {
          const keys = plainKeys(x);
          done.set(x, INSIDE);
          frames.push({ t, x, done, fields: undefined, keys, key: undefined, i: 0, n: keys.length, out: [] });
        } else if (t.info.record !== undefined) {
          const fields = t.info.record;
          done.set(x, INSIDE);
          frames.push({ t, x, done, fields, i: 0, n: fields.length, out: {} });
        } else {
          const key = t.info.tagKey;
          const tag = own(x, key);
          if (tag === MISSING) refuse(`no ${key}; expected ${t.info.tags}`);
          if (tag === INHERITED) refuse(`its ${key} is inherited, not its own property`);
          const ctor = t.info.ctors.get(tag);
          if (ctor === undefined) refuse(`unknown ${key} ${describe(tag)}; expected ${t.info.tags}`);
          const fields = ctor.fields;
          if (t.info.flat.has(tag)) done = undefined;
          else done.set(x, INSIDE);
          frames.push({ t, x, done, fields, i: 0, n: fields.length, out: { tag: ctor.tag } });
        }
      }
      // Give `value` to the frame waiting for it, and finish frames, until
      // one has another element or field to decode, or the outermost is done.
      for (;;) {
        const f = frames[frames.length - 1];
        if (value !== NONE) {
          if (f === undefined) return value;
          if (f.opt) {
            // `Some`: the option has no step of its own in the path.
            frames.pop();
            value = { tag: OPTION_SHAPE.some, [OPTION_SHAPE.key]: value };
            continue;
          }
          if (f.keys !== undefined) {
            f.out.push({ tag: MAP_SHAPE.pair, [MAP_SHAPE.fst]: f.key, [MAP_SHAPE.snd]: value });
          } else if (f.fields === undefined) f.out.push(value);
          else f.out[f.fields[f.i][3]] = value;
          f.i++;
          path.pop();
        }
        if (f.i < f.n) {
          if (f.keys !== undefined) {
            const key = f.keys[f.i];
            path.push(key);
            try {
              f.key = TEXT.dec(key);
            } catch (e) {
              if (e instanceof Refusal) refuse(`the key isn't well-formed text: ${e.message}`);
              throw e;
            }
            x = own(f.x, key);
            if (x === MISSING || x === INHERITED) refuse("the property is gone");
            t = f.t.elem;
          } else if (f.fields === undefined) {
            path.push(f.i);
            x = own(f.x, f.i);
            if (x === MISSING || x === INHERITED) refuse("a hole in the array");
            t = f.t.elem;
          } else {
            const [key, type, optional] = f.fields[f.i];
            path.push(key);
            x = own(f.x, key);
            if (x === MISSING && optional) x = undefined;
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
          // The map of the entries, by the library's own `Map.fromList`.
          if (f.keys !== undefined) value = MAP_SHAPE.fromList(value);
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
    while (t.kind === OPTION) {
      if (v.tag === OPTION_SHAPE.none) {
        value = undefined;
        break;
      }
      frames.push({ t, opt: true });
      v = v[OPTION_SHAPE.key];
      t = payload(t);
    }
    if (value !== NONE) {
      // `None`.
    } else if (t.kind === LEAF) {
      value = t.enc(v);
    } else if (t.kind === LIST) {
      frames.push({ t, v, fields: undefined, out: [] });
    } else if (t.kind === MAP) {
      // `v` is the rest of the entries, in key order. The object is a plain
      // one, and each key is defined on it as an ordinary property: a key
      // like `__proto__` or `constructor` is data, not the prototype or a
      // method, and no setter anywhere is called.
      frames.push({ t, v: MAP_SHAPE.toList(v), fields: undefined, map: true, key: undefined, out: {} });
    } else {
      const record = t.info.record;
      if (record !== undefined) {
        frames.push({ t, v, fields: record, i: 0, out: {} });
      } else {
        const ctor = t.info.internal.get(v.tag);
        frames.push({ t, v, fields: ctor.fields, i: 0, out: { [t.info.tagKey]: ctor.external } });
      }
    }
    for (;;) {
      const f = frames[frames.length - 1];
      if (value !== NONE) {
        if (f === undefined) return value;
        if (f.opt) {
          frames.pop();
          continue;
        }
        if (f.map) {
          Object.defineProperty(f.out, f.key, {
            value, writable: true, enumerable: true, configurable: true,
          });
        } else if (f.fields === undefined) f.out.push(value);
        else {
          const [key, , optional] = f.fields[f.i++];
          // `None` in an optional property is no property.
          if (!(optional && value === undefined)) f.out[key] = value;
        }
      }
      if (f.map) {
        // `f.v` is the rest of the entries: pairs of a key and a value.
        if (f.v.tag === "Cons") {
          const entry = f.v.head;
          f.key = TEXT.enc(entry[MAP_SHAPE.fst]);
          v = entry[MAP_SHAPE.snd];
          f.v = f.v.tail;
          t = f.t.elem;
          break;
        }
      } else if (f.fields === undefined) {
        // `f.v` is the rest of the list.
        if (f.v.tag === "Cons") {
          v = f.v.head;
          f.v = f.v.tail;
          t = f.t.elem;
          break;
        }
      } else if (f.i < f.fields.length) {
        const [, type, , inside] = f.fields[f.i];
        v = f.v[inside];
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
    /// The library's `Float`, if it's loaded: then a `Float` is a JS
    /// `number` (docs/proposals/float.md §3.5).
    float: Option<DataId>,
    /// The `Float` operations with native JS, and which.
    float_natives: HashMap<DefId, FloatPrim>,
    /// Per definition, computed on first use ([`Gen::try_info`]).
    infos: Vec<OnceCell<DefInfo>>,
    /// The prelude's `ifThenElse`, which `if` becomes.
    if_then_else: Option<DefId>,
    /// For `stitchwort run --js` ([`run`]): a `Delay` is a real value that
    /// the runner steps, rather than the erased token, so partial
    /// definitions are generated, and `Delay`'s constants build
    /// `StitchwortDelay` objects.
    run_delay: bool,
    /// While a loop's body is being generated ([`Gen::self_tail_loop`]): the
    /// variables that stand for a call to the definition itself, which was
    /// an argument to a helper that's been inlined ([`Gen::tail`]), by
    /// level, with what the next turn of the loop would be passed.
    holes: RefCell<Vec<(usize, Passed)>>,
    /// Whether such a variable was used any way but in tail position, or
    /// as a field of a constructor in tail position, where it can't be
    /// compiled.
    hole_misused: Cell<bool>,
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
/// What a turn of a loop is passed: parameter levels and JS values.
type Passed = Vec<(usize, String)>;

/// The cells a constructor makes (`Gen::cons_cells`): the outermost, the
/// innermost, its field that takes the rest, and what the next turn is passed.
type Cells = (String, String, String, Passed);

struct SelfCall {
    id: DefId,
    /// Whether any call was turned into a loop.
    used: Cell<bool>,
    /// Whether a call in a constructor's field, in tail position, is a turn
    /// of the loop too (tail recursion modulo constructor): the loop builds
    /// the result a cell at a time.
    cons: bool,
    /// Whether any was.
    cons_used: Cell<bool>,
    /// Whether to inline a helper that a call to the definition is an
    /// argument of, in tail position.
    inline: bool,
    /// How many helpers are being inlined, and a counter for names.
    inlining: Cell<usize>,
    fresh: Cell<usize>,
}

impl SelfCall {
    fn new(id: DefId, cons: bool, inline: bool) -> Self {
        SelfCall {
            id,
            used: Cell::new(false),
            cons,
            cons_used: Cell::new(false),
            inline,
            inlining: Cell::new(0),
            fresh: Cell::new(0),
        }
    }

    fn fresh(&self) -> usize {
        self.fresh.set(self.fresh.get() + 1);
        self.fresh.get()
    }
}

impl<'g> Gen<'g> {
    fn new(g: &'g Globals, options: Options) -> Result<Self, Diagnostic> {
        let Representation {
            nat,
            text,
            text_natives,
            int,
            int_natives,
            float,
            float_natives,
        } = Representation::new(g, options.native_text, options.native_int)
            .map_err(Diagnostic::from)?;
        Ok(Gen {
            g,
            nat,
            text,
            text_natives,
            int,
            int_natives,
            float,
            float_natives,
            infos: g.defs.iter().map(|_| OnceCell::new()).collect(),
            if_then_else: g.registry.def(Builtin::IfThenElse),
            run_delay: false,
            holes: RefCell::new(Vec::new()),
            hole_misused: Cell::new(false),
        })
    }

    /// Which kernel-native implementation applies to `id`, if any: the
    /// number natives assume the `bigint` representation, so they apply only
    /// with it ([`nat_data`]).
    fn kernel_native(&self, id: DefId) -> Option<native::Native> {
        self.nat.and(self.g.builtins.native(id))
    }

    /// Whether `id` is replaced by native JS of any kind.
    pub(crate) fn is_native(&self, id: DefId) -> bool {
        self.kernel_native(id).is_some()
            || self.text_natives.contains_key(&id)
            || self.int_natives.contains_key(&id)
            || self.float_natives.contains_key(&id)
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
        // `Delay`'s constants have no body, so no arity: when they're run,
        // each takes all of its parameters ([`run::primitive_js`]).
        let shape = def_shape(g, id, self.run_delay)?;
        let delay = (shape.partial && !self.run_delay).then(|| shape.params.clone());
        let mask = shape.mask().to_vec();
        let result_erased = shape.result_erased;
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
        if let Some(op) = self.float_natives.get(&id) {
            return Ok(format!(
                "const {} = {};\n",
                def_name(&def.path),
                float_native_js(*op)
            ));
        }
        let Some(body) = def.run_body() else {
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
        // The most it can do first: calls modulo constructors, through
        // inlined helpers. If that can't be compiled (a helper uses the
        // result some other way), less, and last, only direct tail calls.
        // Inlining without cons comes last: `List.decEq`'s step has no
        // constructor to build, only the call's result to return.
        for (cons, inline) in [(true, true), (true, false), (false, false), (false, true)] {
            let call = SelfCall::new(id, cons, inline);
            self.holes.borrow_mut().clear();
            self.hole_misused.set(false);
            let block = self.tree(tree, env, 2, Some(&call))?;
            let ok = call.used.get() && !self.hole_misused.get() && (!cons || call.cons_used.get());
            self.holes.borrow_mut().clear();
            self.hole_misused.set(false);
            if ok {
                return Ok(Some(Self::loop_block(env, &block, cons)));
            }
        }
        Ok(None)
    }

    /// The loop of [`Gen::self_tail_loop`], around the case tree's `block`.
    /// With `cons`, the result is built by a chain of cells (a constructor's
    /// object) that the loop links as it makes them: `h$` is the first, `l$`
    /// the last, and `k$` the name of its field that the rest goes in.
    fn loop_block(env: &[bool], block: &str, cons: bool) -> String {
        let slots: Vec<usize> = (0..env.len()).filter(|level| !env[*level]).collect();
        let copy = |from: fn(usize) -> String, to: fn(usize) -> String| {
            slots
                .iter()
                .map(|level| format!("{} = {}", to(*level), from(*level)))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let chain = if cons {
            "  let h$ = null, l$ = null, k$ = null;\n"
        } else {
            ""
        };
        format!(
            "{{\n  let {};\n{chain}  for (;;) {{\n    const {};\n{block}  }}\n}}",
            copy(var, slot),
            copy(slot, var)
        )
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
            let scrutinee = self.scrutinee(env, *ix);
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
        // A match on the result of the call to itself (inside an inlined
        // helper) that gives the same constructor back, as `List.decCons`'s
        // `Yes q => Yes ..` and `No r => No ..` do once proofs are erased, is
        // that result: the call is in tail position after all.
        if let Some(call) = self_call
            && self.hole_at(env.len() - 1 - *ix).is_some()
            && self.is_identity_match(*d, branches)
        {
            return self.tail(&Term::Var(*ix), env, depth, call);
        }
        let data = self.g.data(*d);
        let scrutinee = self.scrutinee(env, *ix);
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
                if !erased && Some(*d) == self.float {
                    // A `Float` is a `number`: its one runtime field is
                    // its bits.
                    let _ = writeln!(
                        out,
                        "{pad}const {} = toCanonicalBits({scrutinee});",
                        var(level + f)
                    );
                } else if !erased && Some(*d) != self.nat && Some(*d) != self.int {
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

    /// Whether a match on a value of data type `d` gives back, in each
    /// branch, the constructor it matched, whose fields are all erased (a
    /// decision's `Yes` and `No`, once their proofs are): so the match is the
    /// value itself.
    fn is_identity_match(&self, d: DataId, branches: &[Branch]) -> bool {
        let data = self.g.data(d);
        if data.sort == Sort::Prop
            || data.record
            || Some(d) == self.float
            || Some(d) == self.text
            || Some(d) == self.nat
            || Some(d) == self.int
        {
            return false;
        }
        branches.iter().enumerate().all(|(c, b)| {
            data.ctors[c].field_erased.iter().all(|erased| *erased)
                && matches!(
                    b.body.as_ref().map(|body| body.strip_loc()),
                    Some(Term::Ctor(d2, c2, _)) if *d2 == d && *c2 == c
                )
        })
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
        // A variable that stands for a call to itself, in a helper that's
        // been inlined: the next turn.
        if let Term::Var(ix) = term.strip_loc()
            && let Some(passed) = self.hole_at(env.len() - 1 - ix)
        {
            call.used.set(true);
            return Ok(Self::next_turn(&pad, &passed));
        }
        // A constructor with the call in a field: the call is the next turn,
        // and its result will be put in that field of this cell.
        if call.cons
            && let Term::Ctor(..) = term.strip_loc()
            && self.hole_path(term, env, call).is_some()
        {
            let mut out = String::new();
            let (cell, last_cell, key, passed) =
                self.cons_cells(term, env, &pad, call, &mut out)?;
            call.cons_used.set(true);
            call.used.set(true);
            let _ = writeln!(
                out,
                "{pad}if (l$ === null) {{ h$ = {cell}; }} else {{ l$[k$] = {cell}; }}"
            );
            let _ = writeln!(
                out,
                "{pad}l$ = {last_cell}; k$ = {};",
                js_string_literal(&key)
            );
            out.push_str(&Self::next_turn(&pad, &passed));
            return Ok(out);
        }
        let (head, args) = term.spine();
        let Term::Def(id) = head else {
            return self.leaf_return(term, env, &pad, call);
        };
        if *id == call.id && args.len() == self.g.def(*id).arity {
            call.used.set(true);
            let mut passed = Vec::new();
            for (level, arg) in args.iter().enumerate() {
                if !env[level] {
                    passed.push((level, self.expr(arg, env)?));
                }
            }
            return Ok(Self::next_turn(&pad, &passed));
        }
        if call.inline
            && call.inlining.get() < 3
            && let Some(out) = self.inline_helper(*id, &args, env, depth, call)?
        {
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
        self.leaf_return(term, env, &pad, call)
    }

    /// `term`, a leaf of a loop that isn't another turn, is its result. If
    /// the loop is building a chain of cells, it's the rest of the chain.
    fn leaf_return(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        pad: &str,
        call: &SelfCall,
    ) -> Fallible<String> {
        let value = self.expr(term, env)?;
        Ok(if call.cons {
            format!(
                "{pad}{{ const r$ = {value}; if (l$ === null) return r$; l$[k$] = r$; return h$; }}\n"
            )
        } else {
            format!("{pad}return {value};\n")
        })
    }

    /// The next turn of a loop, passing `passed` (parameter level and JS
    /// value).
    fn next_turn(pad: &str, passed: &[(usize, String)]) -> String {
        let mut out = String::new();
        for (level, value) in passed {
            let _ = writeln!(out, "{pad}{} = {value};", slot(*level));
        }
        let _ = writeln!(out, "{pad}continue;");
        out
    }

    /// What the next turn would be passed, if variable `level` stands for a
    /// call to the definition itself.
    fn hole_at(&self, level: usize) -> Option<Vec<(usize, String)>> {
        self.holes
            .borrow()
            .iter()
            .rev()
            .find(|(l, _)| *l == level)
            .map(|(_, passed)| passed.clone())
    }

    /// The variable for `ix`, as a case's scrutinee. A variable that stands
    /// for a call to itself has no value, so it can't be matched on.
    fn scrutinee(&self, env: &[bool], ix: usize) -> String {
        let level = env.len() - 1 - ix;
        if self.hole_at(level).is_some() {
            self.hole_misused.set(true);
        }
        var(level)
    }

    /// If `term` is a call to the definition itself, or a variable that
    /// stands for one, what the next turn would be passed.
    fn hole_passed(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        call: &SelfCall,
    ) -> Fallible<Option<Vec<(usize, String)>>> {
        if let Term::Var(ix) = term.strip_loc() {
            return Ok(self.hole_at(env.len() - 1 - ix));
        }
        let (head, args) = term.spine();
        if let Term::Def(id) = head
            && *id == call.id
            && args.len() == self.g.def(*id).arity
        {
            let mut passed = Vec::new();
            for (level, arg) in args.iter().enumerate() {
                if !env[level] {
                    passed.push((level, self.expr(arg, env)?));
                }
            }
            return Ok(Some(passed));
        }
        Ok(None)
    }

    /// Whether `term` has a call to the definition itself (or a variable
    /// that stands for one) as a field, or in a constructor in a field:
    /// which field, if only one has it. (Nothing is generated.)
    fn hole_path(&self, term: &Term, env: &[bool], call: &SelfCall) -> Option<usize> {
        let Term::Ctor(d, _, args) = term.strip_loc() else {
            return None;
        };
        let data = self.g.data(*d);
        if data.sort == Sort::Prop
            || Some(*d) == self.text
            || Some(*d) == self.nat
            || Some(*d) == self.int
            || Some(*d) == self.float
        {
            return None;
        }
        let mut found = None;
        for (i, arg) in args.iter().enumerate() {
            let is_hole = match arg.strip_loc() {
                Term::Var(ix) => self.hole_at(env.len() - 1 - ix).is_some(),
                Term::Ctor(..) => self.hole_path(arg, env, call).is_some(),
                other => {
                    let (head, args) = other.spine();
                    matches!(head, Term::Def(id) if *id == call.id
                        && args.len() == self.g.def(*id).arity)
                }
            };
            if is_hole {
                if found.is_some() {
                    return None;
                }
                found = Some(i);
            }
        }
        // The field mustn't be erased, or there's no cell to put it in.
        let ctor_erased = |c: usize, i: usize| self.g.data(*d).ctors[c].field_erased[i];
        let Term::Ctor(_, c, _) = term.strip_loc() else {
            return None;
        };
        found.filter(|i| !ctor_erased(*c, *i))
    }

    /// Statements that make the cells of `term` (a constructor with a call
    /// to itself in a field, [`Gen::hole_path`]), and what to do next:
    /// the outermost cell, the innermost, the field of the innermost that
    /// takes the rest, and what the next turn is passed. The cells' other
    /// fields are computed now, as the whole constructor would have been.
    fn cons_cells(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        pad: &str,
        call: &SelfCall,
        out: &mut String,
    ) -> Fallible<Cells> {
        let Term::Ctor(d, c, args) = term.strip_loc() else {
            unreachable!("`hole_path` found a constructor");
        };
        let hole = self
            .hole_path(term, env, call)
            .expect("`hole_path` found a hole");
        let data = self.g.data(*d);
        let ctor = &data.ctors[*c];
        let mut fields = Vec::new();
        if !data.record {
            fields.push(format!("tag: \"{}\"", ctor.name));
        }
        let mut inner = None;
        for (f, (erased, arg)) in ctor.field_erased.iter().zip(args.iter()).enumerate() {
            if *erased {
                continue;
            }
            let key = field_key_at(self.g, *d, *c, f);
            let value = if f != hole {
                self.expr(arg, env)?
            } else if let Term::Ctor(..) = arg.strip_loc() {
                let (cell, last, last_key, passed) = self.cons_cells(arg, env, pad, call, out)?;
                inner = Some((last, last_key, passed));
                cell
            } else {
                let passed = self
                    .hole_passed(arg, env, call)?
                    .expect("`hole_path` found a call");
                inner = Some((String::new(), key.clone(), passed));
                "null".to_string()
            };
            fields.push(format!("{}: {value}", ts_key(&key)));
        }
        let cell = format!("c{}$", call.fresh());
        let _ = writeln!(out, "{pad}const {cell} = {{ {} }};", fields.join(", "));
        let (last, key, passed) = inner.expect("the hole's field is not erased");
        // A direct call: this cell is the last, and the field is its own.
        let last = if last.is_empty() { cell.clone() } else { last };
        Ok((cell, last, key, passed))
    }

    /// A call to `id`, with `args`, in tail position, where some of the
    /// arguments are calls to the definition itself: if `id` is a helper
    /// that only matches on its other arguments, it's inlined, so that
    /// the calls are in tail position in its case tree: `List.filter`'s
    /// `List.filterStep x (List.filter p xs) (p x)`, where the step has
    /// the rest as the tail of a `Cons`, or as itself. The calls' results
    /// are variables that can only be used in tail position or in a
    /// constructor there ([`Gen::hole_misused`]).
    fn inline_helper(
        &self,
        id: DefId,
        args: &[&Term],
        env: &mut Vec<bool>,
        depth: usize,
        call: &SelfCall,
    ) -> Fallible<Option<String>> {
        let def = self.g.def(id);
        if id == call.id || def.arity != args.len() || self.is_native(id) {
            return Ok(None);
        }
        let Some(info) = self.infos[id.0].get() else {
            return Ok(None);
        };
        if info.convention != Convention::Function || info.delay.is_some() {
            return Ok(None);
        }
        let Some(body) = def.run_body() else {
            return Ok(None);
        };
        // The arguments, in this call's environment. A call to itself isn't
        // made: it's the next turn, if the helper puts it in tail position.
        let mut bound: Vec<Option<Result<String, Passed>>> = Vec::new();
        let mut any_hole = false;
        for (i, arg) in args.iter().enumerate() {
            if info.mask[i] {
                bound.push(None);
            } else if let Some(passed) = self.hole_passed(arg, env, call)? {
                any_hole = true;
                bound.push(Some(Err(passed)));
            } else {
                bound.push(Some(Ok(self.expr(arg, env)?)));
            }
        }
        if !any_hole {
            return Ok(None);
        }
        let pad = "  ".repeat(depth);
        let base = env.len();
        let mut out = String::new();
        let mut registered = 0;
        for (i, b) in bound.into_iter().enumerate() {
            match b {
                None => env.push(true),
                Some(Ok(value)) => {
                    let _ = writeln!(out, "{pad}const {} = {value};", var(base + i));
                    env.push(false);
                }
                Some(Err(passed)) => {
                    // The values are computed now, as the call's arguments
                    // would have been; the next turn is passed them.
                    let mut named = Vec::new();
                    for (level, value) in passed {
                        let name = format!("p{}_{level}$", call.fresh());
                        let _ = writeln!(out, "{pad}const {name} = {value};");
                        named.push((level, name));
                    }
                    self.holes.borrow_mut().push((base + i, named));
                    registered += 1;
                    env.push(false);
                }
            }
        }
        call.inlining.set(call.inlining.get() + 1);
        let tree = body.peel_lams(def.arity);
        let result = self.tree(tree, env, depth, Some(call));
        call.inlining.set(call.inlining.get() - 1);
        env.truncate(base);
        let mut holes = self.holes.borrow_mut();
        let keep = holes.len() - registered;
        holes.truncate(keep);
        drop(holes);
        out.push_str(&result?);
        Ok(Some(out))
    }

    fn expr(&self, term: &Term, env: &mut Vec<bool>) -> Fallible<String> {
        self.g.budget.nesting(PASS)?;
        Ok(match term {
            Term::Loc(_, t) | Term::Ann(t, _) => self.expr(t, env)?,
            Term::Var(ix) => {
                let level = env.len() - 1 - ix;
                if self.hole_at(level).is_some() {
                    self.hole_misused.set(true);
                }
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
                let head = self.expr(head, env)?;
                // An erased function (a proof parameter) applied to
                // anything is erased too.
                if head == "undefined" {
                    return Ok(head);
                }
                let mut out = format!("({head})");
                for arg in args {
                    let _ = write!(out, "({})", self.expr(arg, env)?);
                }
                out
            }
            Term::Lam(_, _, body)
                if self.run_delay && stitchwort_rt::erasure::is_done_continuation(self.g, body) =>
            {
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
                if Some(*d) == self.float {
                    // A `number`: a literal from the bits if they're known
                    // (never the source's spelling, docs/proposals/float.md
                    // §2.3), otherwise the double they encode.
                    return Ok(
                        match self
                            .nat_literal(&args[0])
                            .and_then(|b| u64::try_from(b).ok())
                        {
                            Some(bits) => float_literal_js(bits),
                            None => format!("fromCanonicalBits({})", self.expr(&args[0], env)?),
                        },
                    );
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

    /// The runtime's `SAFE_NAT` and `SAFE_INT` codecs, for the library's
    /// `SafeNat` and `SafeInt` (only those that cross, given their data
    /// types). At the boundary each is a `number` that is a whole number
    /// within the bounds the types' proof fields state; inside generated
    /// code it's a record with one field, which holds the `Nat` or `Int`.
    /// Decoding refuses a `bigint` or anything but a `number`, a fraction,
    /// `NaN`, an infinity and anything out of range (a whole `number` beyond
    /// 2^53 - 1 may already have been rounded, so it can't be trusted), and
    /// reads `-0` as 0. Encoding is exact, as the bounds hold of every value.
    fn safe_codecs(&self, nat: Option<DataId>, int: Option<DataId>) -> String {
        let mut out = String::from(
            "\n// A whole number a `number` holds exactly (the library's `SafeNat` and\n\
             // `SafeInt`), as a `bigint`.\n\
             const safeNumber = (x, lowest) => {\n  \
               if (typeof x !== \"number\") refuse(\"expected a number\");\n  \
               if (!Number.isInteger(x)) refuse(\"expected a whole number\");\n  \
               if (x < lowest || x > 9007199254740991) {\n    \
                 refuse(`expected a whole number from ${lowest} to 9007199254740991`);\n  \
               }\n  \
               return BigInt(x);\n\
             };\n",
        );
        let field = |d: DataId| {
            let data = self.g.data(d);
            let name = &data.ctors[0].fields[0].0;
            let k = key(self.g, d, name);
            (ts_key(&k), member(&k))
        };
        if let Some(d) = nat {
            let (k, m) = field(d);
            let _ = writeln!(
                out,
                "const SAFE_NAT = leaf((x) => ({{ {k}: safeNumber(x, 0) }}), (v) => Number(v{m}));"
            );
        }
        if let Some(d) = int {
            let (k, m) = field(d);
            let _ = writeln!(
                out,
                "const SAFE_INT = leaf(\n  (x) => ({{ {k}: INT.dec(safeNumber(x, -9007199254740991)) }}),\n  (v) => Number(INT.enc(v{m})),\n);"
            );
        }
        out
    }

    /// How the runtime builds and takes apart a `Map Text V` (only when one
    /// crosses): `fromList` and `toList` are the library's own `Map.fromList`
    /// and `Map.toList`, at `Text`'s order, so a decoded map is made by
    /// inserting its entries, and its ordering invariant holds as it does for
    /// any map; a pair is `MkPair`'s tag and its fields' keys.
    fn map_shape(&self) -> Fallible<String> {
        let g = self.g;
        let registry = &g.registry;
        let (pair, ctor) = registry
            .ctor(Builtin::MkPair)
            .expect("a checked program has pairs");
        let at = |b: Builtin| {
            registry
                .loaded_def(b)
                .expect("a map crosses only with the library's `Map` loaded")
        };
        // The type arguments are erased, so any term serves for them.
        let ty = Term::Sort(Sort::Type(0));
        let order = Term::Def(at(Builtin::TextInstOrd));
        let mut env = Vec::new();
        let from_list = self.def_ref(at(Builtin::MapFromList), &[&ty, &ty, &order], &mut env)?;
        let to_list = self.def_ref(at(Builtin::MapToList), &[&ty, &ty, &order], &mut env)?;
        Ok(format!(
            "\n// A map that crosses is built and read by the library's own functions.\n\
             const MAP_SHAPE = {{\n  \
               pair: {}, fst: {}, snd: {},\n  \
               fromList: {from_list},\n  \
               toList: {to_list},\n\
             }};\n",
            js_string_literal(&g.data(pair).ctors[ctor].name),
            js_string_literal(&field_key_at(g, pair, ctor, 0)),
            js_string_literal(&field_key_at(g, pair, ctor, 1)),
        ))
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
            Boundary::SafeNat => "SAFE_NAT".into(),
            Boundary::SafeInt => "SAFE_INT".into(),
            Boundary::Float => "FLOAT".into(),
            Boundary::Bool => "BOOL".into(),
            Boundary::Text => "TEXT".into(),
            Boundary::Char => "CHAR".into(),
            Boundary::List(elem) => format!("list({})", self.type_expr(elem)),
            Boundary::Option(_, inner) => format!("option({})", self.type_expr(inner)),
            Boundary::Map(_, value) => format!("map({})", self.type_expr(value)),
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
    ///
    /// A constructor is `[tag, fields]`, with its tag at the boundary third
    /// when that isn't its name; a field is `[key, type]`, with `true` third
    /// for an optional property, and its key inside generated code fourth
    /// when that isn't its key at the boundary. Both come from the type's
    /// one [`repr`].
    fn define(&self, d: DataId) -> Fallible<String> {
        let data = self.g.data(d);
        let repr = repr(self.g, d);
        let mut out = format!("define({}, [\n", info_name(&data.path));
        for (c, (ctor, fields)) in data
            .ctors
            .iter()
            .zip(generic_field_boundaries(self.g, d))
            .enumerate()
        {
            let internal = (0..ctor.fields.len())
                .filter(|&i| !ctor.field_erased[i])
                .map(|i| field_key_at(self.g, d, c, i));
            let fields: Vec<String> = fields
                .iter()
                .zip(external_keys(&repr, c))
                .zip(internal)
                .zip(external_optional(&repr, c))
                .map(|((((_, b), external), internal), flag)| {
                    // A record's `Option` field is an optional property, and
                    // so is a variant's with `js.optional`.
                    let optional = flag || (data.record && matches!(b, Boundary::Option(..)));
                    let rest = if internal != external {
                        format!(", {optional}, {}", js_string_literal(&internal))
                    } else if optional {
                        ", true".to_string()
                    } else {
                        String::new()
                    };
                    format!(
                        "[{}, {}{rest}]",
                        js_string_literal(external),
                        self.type_expr(b)
                    )
                })
                .collect();
            let tag = &repr.ctors[c].tag;
            let external = if data.record || *tag == *ctor.name {
                String::new()
            } else {
                format!(", {}", js_string_literal(tag))
            };
            let _ = writeln!(
                out,
                "  [{}, [{}]{external}],",
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

    /// A function's parameters are `readonly`, so a caller may pass either; its
    /// result, and every list inside a data type's declaration, is a
    /// mutable `T[]`. The codec copies arrays both ways, so a caller who gets
    /// one may keep and change it, and a type an app wrote with `T[]` is
    /// assignable both ways (`readonly T[]` isn't assignable to `T[]`).
    /// `params` names a data type's parameters, inside its alias.
    fn ts_type(&self, b: &Boundary, readonly: bool, params: &[String]) -> String {
        match b {
            Boundary::Nat | Boundary::Int => "bigint".into(),
            Boundary::SafeNat | Boundary::SafeInt | Boundary::Float => "number".into(),
            Boundary::Bool => "boolean".into(),
            Boundary::Text | Boundary::Char => "string".into(),
            Boundary::Option(..) => {
                format!(
                    "{} | undefined",
                    self.ts_type(&b.payload(), readonly, params)
                )
            }
            // A dictionary: inputs are read-only, as lists are.
            Boundary::Map(_, value) => format!(
                "{{ {}[k: string]: {} }}",
                if readonly { "readonly " } else { "" },
                self.ts_type(value, readonly, params)
            ),
            Boundary::List(elem) if readonly => {
                // `readonly readonly T[][]` isn't TypeScript, and a union
                // needs its parentheses too.
                let text = self.ts_type(elem, true, params);
                if text.starts_with("readonly ") || matches!(**elem, Boundary::Option(..)) {
                    format!("readonly ({text})[]")
                } else {
                    format!("readonly {text}[]")
                }
            }
            Boundary::List(elem) if matches!(**elem, Boundary::Option(..)) => {
                format!("({})[]", self.ts_type(elem, false, params))
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
        let repr = repr(self.g, d);
        let params = self.ts_params(d);
        let variants: Vec<String> = generic_field_boundaries(self.g, d)
            .into_iter()
            .enumerate()
            .map(|(c, fields)| {
                let mut parts = Vec::new();
                if !data.record {
                    parts.push(format!(
                        "readonly {}: {}",
                        ts_key(&repr.tag_key),
                        js_string_literal(&repr.ctors[c].tag)
                    ));
                }
                for (((_, b), key), flag) in fields
                    .iter()
                    .zip(external_keys(&repr, c))
                    .zip(external_optional(&repr, c))
                {
                    // A record's `Option` field is an optional property, and
                    // so is a variant's with `js.optional`.
                    let (optional, b) = match b {
                        Boundary::Option(..) if data.record || flag => ("?", b.payload()),
                        _ => ("", b.clone()),
                    };
                    // Lists in a declaration are mutable, `T[]`: an app's own
                    // types say `T[]`, and `readonly T[]` isn't assignable to
                    // it (see `ts_type`).
                    parts.push(format!(
                        "readonly {}{optional}: {}",
                        ts_key(key),
                        self.ts_type(&b, false, &params)
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

/// The one module that reinterprets a `Float`'s bits (docs/proposals/float.md
/// §3.5, D701): the only place a typed array or a `DataView` appears in
/// generated code (a test checks). A `Float` is a `number`, and a NaN may
/// have any payload in JS; these see every NaN as the one NaN.
/// `toCanonicalBits(fromCanonicalBits(b)) === b` for every valid canonical
/// `b`, and `Object.is(fromCanonicalBits(toCanonicalBits(x)), x)` for every
/// `number` `x`.
pub const FLOAT_BITS: &str = r#"// `Float` bit reinterpretation: a double's 64 bits, any NaN as the one NaN.
const floatView = new DataView(new ArrayBuffer(8));
const toCanonicalBits = (x) => {
  if (x !== x) return 0x7ff8000000000000n;
  floatView.setFloat64(0, x);
  return floatView.getBigUint64(0);
};
const fromCanonicalBits = (b) => {
  floatView.setBigUint64(0, b);
  return floatView.getFloat64(0);
};
"#;

/// The runtime's `FLOAT` codec (docs/proposals/float.md §5, D685): a `Float`
/// is a `number` inside generated code and at the boundary. Decoding accepts
/// every `number`, `NaN`, the infinities and `-0` included (finiteness
/// belongs on the application's own types, D702), and refuses anything else;
/// encoding passes the number on.
const FLOAT_CODEC: &str = "\n// `Float` is a `number`, any number, inside generated code too.\n\
const FLOAT = leaf((x) => (typeof x === \"number\" ? x : refuse(\"expected a number\")), (v) => v);\n";

/// JS for the double with valid `bits`: the shortest decimal that reads back
/// as it (Rust's `{:?}`, which a JS engine parses exactly, having at most 17
/// significant digits), `-0`, `NaN` or an infinity.
pub fn float_literal_js(bits: u64) -> String {
    let x = f64::from_bits(bits);
    if x.is_nan() {
        "NaN".into()
    } else if x.is_infinite() {
        if x > 0.0 { "Infinity" } else { "-Infinity" }.into()
    } else if x == 0.0 && x.is_sign_negative() {
        "-0".into()
    } else {
        let text = format!("{x:?}");
        if text.starts_with('-') {
            format!("({text})")
        } else {
            text
        }
    }
}

/// JS for a `Float` native: IEEE 754 doubles, as JS has them. `==` is
/// `Object.is` (the same double), JS's `===` is `Float.ieeeEq`.
fn float_native_js(op: FloatPrim) -> &'static str {
    match op {
        FloatPrim::Add => "(a) => (b) => a + b",
        FloatPrim::Sub => "(a) => (b) => a - b",
        FloatPrim::Neg => "(a) => -a",
        FloatPrim::Abs => "(a) => Math.abs(a)",
        FloatPrim::IsNaN => "(a) => ({ tag: a !== a ? \"True\" : \"False\" })",
        FloatPrim::DecEq => "(a) => (b) => ({ tag: Object.is(a, b) ? \"Yes\" : \"No\" })",
        FloatPrim::IeeeEq => "(a) => (b) => ({ tag: a === b ? \"True\" : \"False\" })",
        FloatPrim::FromBits => "fromCanonicalBits",
        FloatPrim::Bits => "toCanonicalBits",
    }
}

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

/// How data type `d` crosses the boundary (docs/proposals/attributes.md
/// §4.6): what its `js.*` attributes resolved to where it was declared, or
/// for a type without any, the default names, whose clashes `check_names`
/// reports before any code is generated. The codec tables
/// ([`Gen::define`]), the declarations ([`Gen::ts_alias`]) and
/// [`boundary_literal`] all read this, never names of their own.
fn repr(g: &Globals, d: DataId) -> Rc<JsRepr> {
    let data = g.data(d);
    data.js
        .clone()
        .unwrap_or_else(|| Rc::new(js_repr::names(data, &js_repr::Requested::default())))
}

/// The keys at the boundary of constructor `c`'s fields that have one (not
/// erased), in order: alongside [`data_fields`].
fn external_keys(repr: &JsRepr, c: usize) -> Vec<&str> {
    repr.ctors[c]
        .keys
        .iter()
        .flatten()
        .map(String::as_str)
        .collect()
}

/// For each of constructor `c`'s fields that has a key, whether `js.optional`
/// is written on it: alongside [`external_keys`].
fn external_optional(repr: &JsRepr, c: usize) -> Vec<bool> {
    let ctor = &repr.ctors[c];
    ctor.keys
        .iter()
        .zip(&ctor.optional)
        .filter(|(key, _)| key.is_some())
        .map(|(_, &optional)| optional)
        .collect()
}

/// The key of a constructor's field in a JS object inside generated code
/// (at the boundary, a field's key is its [`repr`]'s, which the codec
/// translates to and from this): its name, with each prime as `$`. A name
/// the internal representation already uses (`tag` for the constructor, and
/// `__proto__`, which sets an object's prototype) gets a `$` in front: a
/// field `tag` is `$tag`. Stitchwort names can't contain `$` or start with a
/// prime, so two fields never get the same key, and no field's key is
/// `tag`.
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
        // A `Float` with known bits is its `number`.
        (Boundary::Float, Value::Ctor(_, _, fields)) => {
            match native::as_nat(g, &fields[0]).map_err(|e| e.to_string())? {
                Some(n) => Ok(float_literal_js(
                    u64::try_from(n).map_err(|_| "bits beyond 64".to_string())?,
                )),
                None => Err(stuck()),
            }
        }
        // A `SafeNat` or `SafeInt` record is its first field, as a `number`.
        (Boundary::SafeNat, Value::Ctor(_, _, fields)) => {
            match native::as_nat(g, &fields[0]).map_err(|e| e.to_string())? {
                Some(n) => Ok(n.to_string()),
                None => Err(stuck()),
            }
        }
        (Boundary::SafeInt, Value::Ctor(_, _, fields)) => match &fields[0] {
            Value::Ctor(_, c, inner) => {
                match native::as_nat(g, &inner[0]).map_err(|e| e.to_string())? {
                    Some(n) if *c == 0 => Ok(n.to_string()),
                    Some(n) => Ok(format!("-{}", n + 1u32)),
                    None => Err(stuck()),
                }
            }
            _ => Err(stuck()),
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
        // A map is its tree's entries, in key order, as an object's own
        // properties (`Object.fromEntries` makes a key `__proto__` one too).
        (Boundary::Map(_, element), Value::Ctor(_, 0, fields)) => {
            let mut entries = Vec::new();
            map_entries(g, element, fields[0].clone(), &mut entries)?;
            Ok(format!("Object.fromEntries([{}])", entries.join(", ")))
        }
        (Boundary::Option(..), Value::Ctor(_, c, fields)) => {
            if *c == 0 {
                return Ok("undefined".into());
            }
            // An `Option` inside is its tagged data type.
            boundary_literal(g, &b.payload(), &fields[0])
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
            let repr = repr(g, *d);
            let boundaries = &field_boundaries(g, *d, args)[*c];
            let mut parts = Vec::new();
            if !data.record {
                parts.push(format!(
                    "{}: {}",
                    ts_key(&repr.tag_key),
                    js_string_literal(&repr.ctors[*c].tag)
                ));
            }
            let runtime = fields
                .iter()
                .zip(&ctor.field_erased)
                .filter(|(_, erased)| !**erased)
                .map(|(field, _)| field);
            for ((((_, b), field), key), flag) in boundaries
                .iter()
                .zip(runtime)
                .zip(external_keys(&repr, *c))
                .zip(external_optional(&repr, *c))
            {
                let literal = boundary_literal(g, b, field)?;
                // `None` in a record's `Option` field, or a variant's with
                // `js.optional`, is no property.
                if (data.record || flag)
                    && matches!(b, Boundary::Option(..))
                    && literal == "undefined"
                {
                    continue;
                }
                parts.push(format!("{}: {literal}", ts_key(key)));
            }
            Ok(format!("{{ {} }}", parts.join(", ")))
        }
        _ => Err(stuck()),
    }
}

/// The entries of a map's tree, in key order, as JS `[key, value]` pairs. A
/// balanced tree is as deep as the logarithm of its size.
fn map_entries(
    g: &Globals,
    element: &Boundary,
    tree: Value,
    out: &mut Vec<String>,
) -> Result<(), String> {
    match expand_step(g, tree) {
        Value::Ctor(_, 0, _) => Ok(()),
        // `Bin size left key value right`
        Value::Ctor(_, 1, parts) => {
            map_entries(g, element, parts[1].clone(), out)?;
            let key = boundary_literal(g, &Boundary::Text, &parts[2])?;
            let value = boundary_literal(g, element, &parts[3])?;
            out.push(format!("[{key}, {value}]"));
            map_entries(g, element, parts[4].clone(), out)
        }
        other => Err(format!("not a fully evaluated value: {other:?}")),
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

/// `ids` (in declaration order) reordered so that a definition comes after
/// the definitions its body refers to, where it can: a lifted helper (a
/// `match`'s) is declared after its owner, but a constant computed when
/// the module loads (`const halves = toOption(...)`) uses it at once, so it
/// must already exist. A cycle is a group, whose members are functions or
/// thunks that look each other up only when called, so any order serves
/// there: the back edge is ignored.
pub(crate) fn dependency_order(g: &Globals, ids: &[DefId]) -> Vec<DefId> {
    let wanted: HashSet<DefId> = ids.iter().copied().collect();
    let mut state: HashMap<DefId, bool> = HashMap::new(); // false: open, true: done
    let mut out = Vec::with_capacity(ids.len());
    for &root in ids {
        if state.contains_key(&root) {
            continue;
        }
        state.insert(root, false);
        // (definition, the definitions it refers to, how many are handled)
        let mut stack = vec![(root, refs(g, root, &wanted), 0)];
        while let Some((id, deps, next)) = stack.last_mut() {
            if let Some(&dep) = deps.get(*next) {
                *next += 1;
                if let std::collections::hash_map::Entry::Vacant(e) = state.entry(dep) {
                    e.insert(false);
                    stack.push((dep, refs(g, dep, &wanted), 0));
                }
            } else {
                let id = *id;
                state.insert(id, true);
                out.push(id);
                stack.pop();
            }
        }
    }
    out
}

/// The wanted definitions `id`'s body refers to, in order.
fn refs(g: &Globals, id: DefId, wanted: &HashSet<DefId>) -> Vec<DefId> {
    let mut found: Vec<DefId> = g
        .def(id)
        .run_body()
        .into_iter()
        .flat_map(|b| b.subterms())
        .filter_map(|(t, _)| match t {
            Term::Def(d) if wanted.contains(d) && *d != id => Some(*d),
            _ => None,
        })
        .collect();
    let mut seen = HashSet::new();
    found.retain(|d| seen.insert(*d));
    found
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
