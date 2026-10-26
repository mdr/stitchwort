//! JavaScript extraction (DESIGN.md §12): erase types and proofs, generate an
//! ES module, and wrap each export in decode → compute → encode.
//!
//! First-milestone scope: exports take and return concrete first-order data
//! (`Nat`, `Bool`, `Text`, `Char`, `List`, and data types built from them,
//! such as `Option Text`), and their proof arguments are checked at runtime.

use std::cell::{Cell, OnceCell, RefCell};
use std::fmt::Write;
use std::rc::Rc;

use stitchwort_core::check::{is_type_former, telescope};
use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::globals::FieldDefault;
use stitchwort_core::js_repr::{self, JsRepr};
use stitchwort_core::native;
use stitchwort_core::partial::Primitive;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{Head, eval, expand_step, quot_mk_rep, quote};
use stitchwort_core::{
    BigUint, DataId, DefId, Globals, Icit, Limits, QuotForm, ResourceError, Sort, Term, Value,
    pretty,
};
use stitchwort_rt::erasure::{def_shape, text_literal};
use stitchwort_rt::hoist::SigMaps;
use stitchwort_rt::natives::{
    FloatPrim, Representation, float_data, int_data, nat_data, safe_int_data, safe_nat_data,
    text_data,
};
use stitchwort_rt::specialise::{self, Specialiser};
// Shared with the runtime (D389), and part of this crate's interface.
pub use stitchwort_rt::natives::{
    IntBinding, IntNative, NAT_DATA_HASH, NativeBinding, SAFE_INT_HASH, SAFE_NAT_HASH,
    TEXT_DATA_HASH, TextBinding, TextNative, bind_int, bind_text_natives,
};
use stitchwort_syntax::Diagnostic;

mod effect;
mod fast;
pub mod run;
pub mod sourcemap;

pub use sourcemap::Mapping;

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
    /// The library's `Map K V` (the `DataId`), as a plain object
    /// `{ readonly [k: string]: V }`: the keys are the map's keys, the values
    /// are `V`'s encoding. The key (the first [`Boundary`]) is
    /// [`Boundary::Text`], in `Text`'s own order, or a `js.unboxed` record
    /// over `Text` in its derived order, which is the same (D1068): either
    /// way a key is a string inside generated code (D866).
    Map(DataId, Box<Boundary>, Box<Boundary>),
    /// A tagged object union, with the type's arguments if it has parameters.
    /// A `js.unboxed` record (no arguments) is its one field's JS form
    /// instead (docs/proposals/microtypes.md, D1065).
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
            Boundary::Map(d, key, value) => {
                Boundary::Map(*d, key.clone(), Box::new(value.instantiate(args)))
            }
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
                Boundary::List(elem) | Boundary::Option(_, elem) => elem.mentions(leaf),
                Boundary::Map(_, key, elem) => key.mentions(leaf) || elem.mentions(leaf),
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
                || pretty::value_ascii(g, &names, ty),
                |t| pretty::term_ascii(g, &names, t),
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
        let boundary = boundary(g, ty, 0, &mut HashSet::default())
            .map_err(|why| refuse(format!("parameter `{js_name}`: {why}")))?;
        params.push((js_name, boundary));
        param_positions.push(i);
    }
    let result = boundary(g, &tel.result, 0, &mut HashSet::default())
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
        Value::Neutral(Head::Var(level, _), elims) if elims.is_empty() && *level < params => {
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
                // map from `Text`, in `Text`'s own order, can be one, or from
                // a `js.unboxed` record over `Text` in its derived order,
                // which compares the one field by `Text`'s (D1068).
                (Some(Builtin::Map), [key, value, order]) => {
                    let key = match key {
                        Value::Data(t, a) if a.is_empty() && text_data(g) == Some(*t) => {
                            if !is_text_order(g, order) {
                                return Err(format!(
                                    "`{}` can't cross the JS boundary: a map crosses only in \
                                     `Text`'s own order (`Text.instOrd`), which its keys are \
                                     sorted by",
                                    pretty::value(g, &[], ty)
                                ));
                            }
                            Boundary::Text
                        }
                        Value::Data(k, a) if a.is_empty() && unboxed_over_text(g, *k) => {
                            if !is_derived_order(g, *k, order) {
                                let key_name = &g.data(*k).name;
                                return Err(format!(
                                    "`{}` can't cross the JS boundary: a map from `{key_name}` \
                                     crosses only in `{key_name}`'s derived order, which is \
                                     `Text`'s, and this map has another",
                                    pretty::value(g, &[], ty)
                                ));
                            }
                            check_codec(g, *k, visiting)?;
                            Boundary::Data(*k, Vec::new())
                        }
                        _ => {
                            return Err(format!(
                                "`{}` can't cross the JS boundary: only maps from `Text`, or from \
                                 a `js.unboxed` record over `Text`, cross, as plain objects",
                                pretty::value(g, &[], ty)
                            ));
                        }
                    };
                    let value = boundary(g, value, params, visiting)?;
                    Ok(Boundary::Map(*d, Box::new(key), Box::new(value)))
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

/// Whether `d` is a `js.unboxed` record whose one field is the prelude's
/// `Text`: a map key that crosses as a string (D1068).
fn unboxed_over_text(g: &Globals, d: DataId) -> bool {
    let data = g.data(d);
    if !data.js.as_ref().is_some_and(|r| r.unboxed) {
        return false;
    }
    let Some(i) = data.unboxed_field() else {
        return false;
    };
    let mut env: Vec<Value> = (0..data.params.len()).map(Value::var).collect();
    env.extend((0..i).map(|j| Value::var(data.params.len() + j)));
    matches!(
        eval(g, &env, &data.ctors[0].fields[i].1).expect(OUTSIDE_LIMITS),
        Value::Data(t, a) if a.is_empty() && text_data(g) == Some(t)
    )
}

/// Whether `order` is record `d`'s derived `Ord` instance, `d.%instOrd`
/// (derive_ord.rs; no program can write a name with `%`). For a record over
/// `Text` it compares the field by `Text.instOrd`, so it sorts keys as a
/// `Map Text V` does.
fn is_derived_order(g: &Globals, d: DataId, order: &Value) -> bool {
    let id = match order {
        Value::Call(id, spine, _) if spine.is_empty() => *id,
        Value::Neutral(Head::Def(id), spine) if spine.is_empty() => *id,
        _ => return false,
    };
    *g.def(id).name == *format!("{}.%instOrd", g.data(d).name)
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
            let b = boundary(g, &field_ty, data.params.len(), visiting)
                .map_err(|why| format!("`{}`'s field `{field}`: {why}", data.name))?;
            if repr(g, d).unboxed {
                unboxed_field_crosses(g, d, &field, &b)?;
            }
        }
    }
    Ok(())
}

/// The checks on `js.unboxed` record `d`'s one field, `field`, crossing as
/// `b`, that its declaration couldn't make: its JS form isn't
/// `T | undefined` (an `Option` through a synonym: the attribute check
/// refuses one written as such), and it isn't `d` again, directly or through
/// other unboxed records, which would be a value that is only itself.
fn unboxed_field_crosses(g: &Globals, d: DataId, field: &str, b: &Boundary) -> Result<(), String> {
    let name = &g.data(d).name;
    if matches!(b, Boundary::Option(..)) {
        return Err(format!(
            "`{name}` is `js.unboxed`, so it would cross as its field `{field}`, which crosses \
             as `T | undefined`: an `Option` of `{name}` couldn't be told apart from `None`"
        ));
    }
    // Follow the unboxed records inside, by their fields' types (each one's
    // own field is checked when its codec is).
    let mut seen = vec![d];
    let mut next = match b {
        Boundary::Data(e, _) => Some(*e),
        _ => None,
    };
    while let Some(e) = next.filter(|e| repr(g, *e).unboxed) {
        if seen.contains(&e) {
            return Err(format!(
                "`{name}` is `js.unboxed`, and its field `{field}` is unboxed into `{name}` \
                 again, so it would cross as nothing but itself"
            ));
        }
        seen.push(e);
        next = data_fields(g, e)
            .into_iter()
            .flatten()
            .next()
            .and_then(|(_, ty)| match ty {
                Value::Data(f, _) => Some(f),
                _ => None,
            });
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
                    let b = boundary(g, &ty, params, &mut HashSet::default())
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
    /// Where generated definitions and export wrappers came from, in order
    /// of position in `js` (docs/proposals/js-source-maps.md): [`sourcemap`]
    /// turns them into a source map. `js` doesn't depend on them.
    pub mappings: Vec<Mapping>,
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
    /// The effect runtime counts its work (docs/proposals/effect-runtime.md
    /// §9.3, stage 4a): run-loop steps, pushes and pops of pending
    /// continuations, operations routed through a fold or a `translate`, and
    /// resumptions, in `globalThis.__stitchwortEffectCounts`. For tests that
    /// check how the work grows; off in what users get.
    pub effect_counters: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            native_text: true,
            native_int: true,
            effect_counters: false,
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
    let mut short_exports: HashMap<&str, DefId> = HashMap::default();
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
            return Err(diagnostic.with_note(clash.note(&repr)));
        }
    }
    let mut short_types: HashMap<String, DataId> = HashMap::default();
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
    let boundary_datas = check_names(g, &exports)?;
    input_datas(g, &boundary_datas).map(|_| ())
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
    let inputs = input_datas(g, &boundary_datas)?;

    erasable(g)?;
    let codegen = Gen::new(g, options)?;
    // Only what the exports use, in declaration order. That's dependency
    // order: the kernel admits each group only once what it uses is final,
    // so a definition refers only to earlier ones and to members of its own
    // group. Those are thunks or functions, never values, so they look each
    // other up only when called, after all of them are defined.
    // What records' proof-field checks use, too.
    // And the helpers of their fields' defaults, which decoders call for
    // missing properties (docs/proposals/named-arguments.md §5.3).
    let checks = boundary_datas
        .iter()
        .flat_map(|d| &g.data(*d).validators)
        .flat_map(|v| v.decision.subterms())
        .filter_map(|(t, _)| match t {
            Term::Def(id) => Some(*id),
            _ => None,
        })
        .chain(boundary_datas.iter().flat_map(|d| {
            g.data(*d)
                .defaults
                .iter()
                .flat_map(|table| table.iter().flatten().flatten())
                .map(|default| default.helper)
        }));
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
    let wanted = codegen.set_reach(exports.iter().map(|sig| sig.id).chain(checks), &[], true)?;
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
    js.push_str(RUNTIME_FAST);
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
    if wanted.iter().any(|id| codegen.info(*id).delay.is_some()) {
        js.push_str("// A partial computation, which nothing here can run.\nconst delayed = Symbol(\"Delay\");\n\n");
    }
    if let Some(effect) = &codegen.effect
        && wanted.iter().any(|id| effect.native(*id).is_some())
    {
        js.push_str(effect.runtime());
        js.push('\n');
    }
    let while_generating = |id: DefId| {
        move |e: ResourceError| {
            Diagnostic::from(e).with_label(g.def(id).span, "while generating JavaScript for this")
        }
    };
    let wanted: Vec<DefId> = wanted
        .into_iter()
        .filter(|id| codegen.info(*id).delay.is_none())
        .collect();
    let mut mapper = sourcemap::Mapper::new(&js);
    for id in dependency_order(&codegen, &wanted) {
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
        let text = codegen.def(id).map_err(while_generating(id))?;
        mapper.chunk(&js, &text, def.span, &def.name);
        js.push_str(&text);
    }
    mapper.end(&js);
    if maps_cross {
        js.push_str(&codegen.map_shape().map_err(Diagnostic::from)?);
    }
    for sig in &exports {
        let text = codegen.wrapper(sig).map_err(while_generating(sig.id))?;
        mapper.chunk(&js, &text, g.def(sig.id).span, &sig.name);
        js.push_str(&text);
    }
    mapper.end(&js);
    js.push_str(&codegen.fast.borrow().module_text());
    js.push_str(&codegen.hoisted_vars());
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
        dts.push_str(&codegen.ts_alias(d, None));
        // Its input shape, next to it, if it has one.
        if inputs.contains(&d) {
            dts.push_str(&codegen.ts_alias(d, Some(&inputs)));
        }
    }
    for sig in &exports {
        let params: Vec<String> = sig
            .params
            .iter()
            .map(|(x, b)| format!("{x}: {}", codegen.ts_type(b, true, &[], Some(&inputs))))
            .collect();
        let _ = writeln!(
            dts,
            "export declare function {}({}): {};",
            sig.name,
            params.join(", "),
            codegen.ts_type(&sig.result, false, &[], None)
        );
    }
    Ok(Output {
        js,
        dts,
        mappings: mapper.finish(),
    })
}

/// Whether `b` has the prelude's `Option` as a tagged data type in it: a
/// nested one (not counting the fields of data types).
fn names_option(g: &Globals, b: &Boundary) -> bool {
    match b {
        Boundary::List(elem) | Boundary::Map(_, _, elem) => names_option(g, elem),
        Boundary::Option(..) => names_option(g, &b.payload()),
        Boundary::Data(d, args) => {
            g.registry.is_data(Builtin::Option, *d) || args.iter().any(|a| names_option(g, a))
        }
        _ => false,
    }
}

/// Which data types have an input shape in the TypeScript declarations, as
/// a set: given to [`Gen::ts_type`] for an export's parameters, `None` for
/// its result.
type Inputs<'a> = Option<&'a HashSet<DataId>>;

/// What an input shape's name adds to the type's: `RangeOptionsInput`.
const INPUT_SUFFIX: &str = "Input";

/// The data types at the boundary that need an input shape
/// (docs/proposals/named-arguments.md §5.3, D1101): those with a field with
/// a default, which an input may leave out, and, all the way down, those
/// whose fields' types mention one (`JobInput`, with
/// `options: RangeOptionsInput`). A type parameter isn't a reason: a
/// generic type's input is written with input arguments, `Box<RangeOptionsInput>`.
/// A `js.unboxed` record is its one field at the boundary, so its own
/// default never applies there. Each input shape's name must be free among
/// the boundary's types.
fn input_datas(g: &Globals, boundary_datas: &[DataId]) -> Result<HashSet<DataId>, Diagnostic> {
    let own_default = |d: DataId| {
        let data = g.data(d);
        !repr(g, d).unboxed
            && data.ctors.iter().enumerate().any(|(c, ctor)| {
                (0..ctor.fields.len())
                    .any(|i| !ctor.field_erased[i] && field_default(g, d, c, i).is_some())
            })
    };
    let mut inputs: HashSet<DataId> = boundary_datas
        .iter()
        .copied()
        .filter(|d| own_default(*d))
        .collect();
    fn mentions(b: &Boundary, inputs: &HashSet<DataId>) -> bool {
        match b {
            Boundary::List(elem) | Boundary::Option(_, elem) => mentions(elem, inputs),
            Boundary::Map(_, key, value) => mentions(key, inputs) || mentions(value, inputs),
            Boundary::Data(d, args) => {
                inputs.contains(d) || args.iter().any(|a| mentions(a, inputs))
            }
            _ => false,
        }
    }
    loop {
        let more: Vec<DataId> = boundary_datas
            .iter()
            .copied()
            .filter(|d| {
                !inputs.contains(d)
                    && generic_field_boundaries(g, *d)
                        .iter()
                        .flatten()
                        .any(|(_, b)| mentions(b, &inputs))
            })
            .collect();
        if more.is_empty() {
            break;
        }
        inputs.extend(more);
    }
    for &d in boundary_datas.iter().filter(|d| inputs.contains(d)) {
        let input = format!("{}{INPUT_SUFFIX}", type_name(&g.data(d).name));
        if let Some(&other) = boundary_datas
            .iter()
            .find(|e| type_name(&g.data(**e).name) == input)
        {
            return Err(Diagnostic::error(
                "E-EXPORT",
                format!(
                    "`{}`'s input shape and `{}` would both be called `{input}` in the \
                     TypeScript declarations",
                    g.data(d).name,
                    g.data(other).name
                ),
            )
            .with_label(g.data(d).span, format!("its input shape is `{input}`"))
            .with_label(
                g.data(other).span,
                "and this type crosses the JS boundary too",
            )
            .with_note(format!(
                "a parameter's `{}` may leave out fields with defaults, in it or inside it, \
                 so its type is `{input}`; rename one of the types",
                type_name(&g.data(d).name)
            )));
        }
    }
    Ok(inputs)
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
        Boundary::List(elem) => collect_datas(g, elem, out),
        Boundary::Map(_, key, elem) => {
            collect_datas(g, key, out);
            collect_datas(g, elem, out);
        }
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
//   encoding makes a fresh object, key by key, from `Map.toList`. With a
//   second type, `map(t, k)`, the keys are `k`, a `js.unboxed` record over
//   `Text` in its derived order (which is `Text`'s): a string inside
//   generated code too, whose proof fields are checked;
// - a `js.unboxed` record (`bare` in `define`) is its one field's JS form,
//   and inside generated code that field's value (D866): it's decoded and
//   encoded as the field, and then its proof fields are checked.
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
// A map's keys are `TEXT`, or a `js.unboxed` record over it (`key`).
const map = (elem, key = TEXT) => {
  const maps = (elem.maps ??= new Map());
  let t = maps.get(key);
  if (t === undefined) maps.set(key, (t = { kind: MAP, open: elem.open, id: typeCount++, elem, key }));
  return t;
};
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
  name, tagKey, ctors: new Map(), internal: new Map(), flat: undefined, tags: "",
  instances: new Map(), record: undefined, checks: [],
});
// Each constructor's tag, and its fields' keys and types, in order. A
// constructor is `flat` if all its fields are shallow (`flatOf`). A record has one
// constructor, whose fields are `info.record`, and no tag; `checks` are its
// proof fields' runtime checks, each a message and a function of a decoded
// value saying whether the proof holds. A record that is `unboxed` has one
// field, and inside generated code it is that field's value, with no object
// around it (D866): decoding takes the field out of the object it reads, and
// encoding puts it back in one. Names at the boundary may differ
// from those inside generated code (`js.tag`, `js.name`): `ctors` finds a
// constructor by its tag at the boundary, `internal` by its tag inside.
const define = (
  info, ctors, record = false, checks = [], strings = false, unboxed = false, bare = false,
) => {
  // A constructor is `[tag, fields]`, or `[tag, fields, tag at the
  // boundary]`. A field is `[key, type]`, `[key, type, true]` for an
  // optional property, `[key, type, optional, key inside]`, or, for a field
  // with a default, `[key, type, false, key inside, default]`: `default` is a
  // function of the object decoded so far (the earlier fields, by their keys
  // inside), giving the field's value when its property is missing.
  const entries = ctors.map(([tag, fields, external = tag]) => ({
    tag,
    external,
    fields: fields.map(([key, type, optional = false, inside = key, dflt]) =>
      [key, type, optional, inside, dflt]),
  }));
  if (record) {
    info.record = entries[0].fields;
    info.recordTag = entries[0].external;
  }
  info.checks = checks;
  info.unboxed = unboxed;
  // `js.unboxed`: at the boundary too, a value is its one field's.
  info.bare = bare;
  // A string union (`js.enum`): a value is one constructor's string at the
  // boundary, in place of an object.
  info.strings = strings;
  for (const entry of entries) {
    info.ctors.set(entry.external, entry);
    info.internal.set(entry.tag, entry);
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
  : t.kind === MAP ? map(close(t.elem, args), t.key)
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
const hasIsWellFormed = typeof "".isWellFormed === "function";
const wellFormed = (x) => {
  if (typeof x !== "string") refuse("expected a string");
  if (hasIsWellFormed && x.isWellFormed()) return x;
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
// `flat` constructor (a record's too), whose fields are all `shallow`, can't
// contain itself or share anything, and decoding it takes as long as decoding
// its fields, so it's decoded again each time it's reached, which is quicker
// than remembering it.
const INSIDE = Symbol("inside");
// A value with nothing inside it that could be shared or contain itself: a leaf,
// a string union, or an `Option` of one, or a `js.unboxed` record over one.
const shallow = (t) =>
  t.kind === LEAF ||
  (t.kind === DATA && t.info.strings) ||
  (t.kind === DATA && t.info.bare && shallow(t.info.record[0][1])) ||
  (t.kind === OPTION && t.elem.kind !== OPTION && shallow(t.elem));
// The tags of a data type's flat constructors (a record's one is `flat` if it's
// in it), found on first use, when every type is defined.
const flatOf = (info) => {
  if (info.flat === undefined) {
    info.flat = new Set();
    for (const [tag, entry] of info.ctors) {
      if (entry.fields.every(([, t]) => shallow(t))) info.flat.add(tag);
    }
  }
  return info.flat;
};
const decode = (t, x, root, seen = new Map()) => {
  const frames = [];
  const path = [];
  try {
    for (;;) {
      // Start on `x`: a leaf is done at once, as is an array or object
      // already decoded at this type; otherwise it gets a frame.
      let value = NONE;
      // An `Option` is `undefined`, or what's inside it: `null` is neither.
      // A `js.unboxed` record is its field, checked once that's decoded.
      // Neither has a step of its own in the path.
      while (t.kind === OPTION || (t.kind === DATA && t.info.bare)) {
        if (t.kind === DATA) {
          frames.push({ t, bare: true });
          t = t.info.record[0][1];
          continue;
        }
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
      } else if (t.kind === DATA && t.info.strings) {
        // A string union: exactly one of the constructors' strings.
        const ctor = typeof x === "string" ? t.info.ctors.get(x) : undefined;
        if (ctor === undefined) refuse(`expected ${t.info.tags}, not ${describe(x)}`);
        value = { tag: ctor.tag };
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
          if (flatOf(t.info).has(t.info.recordTag)) done = undefined;
          else done.set(x, INSIDE);
          frames.push({ t, x, done, fields, i: 0, n: fields.length, out: {} });
        } else {
          const key = t.info.tagKey;
          const tag = own(x, key);
          if (tag === MISSING) refuse(`no ${key}; expected ${t.info.tags}`);
          if (tag === INHERITED) refuse(`its ${key} is inherited, not its own property`);
          const ctor = t.info.ctors.get(tag);
          if (ctor === undefined) refuse(`unknown ${key} ${describe(tag)}; expected ${t.info.tags}`);
          const fields = ctor.fields;
          if (flatOf(t.info).has(tag)) done = undefined;
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
          if (f.bare) {
            // A `js.unboxed` record: its field's value, if its proofs hold.
            frames.pop();
            for (const [message, holds] of f.t.info.checks) if (!holds(value)) refuse(message);
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
            // A `js.unboxed` key is the string, if its proofs hold.
            if (f.t.key !== TEXT) {
              for (const [message, holds] of f.t.key.info.checks) {
                if (!holds(f.key)) refuse(`the key's ${message}`);
              }
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
            const [key, type, optional, , dflt] = f.fields[f.i];
            path.push(key);
            x = own(f.x, key);
            // A missing property of a field with a default is the default,
            // computed from the fields before it; a present one, `undefined`
            // too, is decoded as given (D1114).
            if (x === MISSING && dflt !== undefined) {
              value = dflt(f.out);
              continue;
            }
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
          value = f.t.info.unboxed ? f.out[f.fields[0][3]] : f.out;
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
    while (t.kind === OPTION || (t.kind === DATA && t.info.bare)) {
      // A `js.unboxed` record is its field, inside and out.
      if (t.kind === DATA) {
        t = t.info.record[0][1];
        continue;
      }
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
    } else if (t.kind === DATA && t.info.strings) {
      value = t.info.internal.get(v.tag).external;
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
        v = f.t.info.unboxed ? f.v : f.v[inside];
        t = close(type, f.t.args);
        break;
      }
      frames.pop();
      value = f.out;
    }
  }
};
"#;

/// The runtime's fast path: what `decodeFast` and `encodeFast` do around the
/// specialised codecs the generator writes for each type that crosses (see
/// `fast.rs`).
const RUNTIME_FAST: &str = r#"
// The fast path. Each type that crosses has a decoder and an encoder
// specialised to it, written out in this module: they go straight through a
// value, with no description of its type to interpret, no frames and no path
// to keep.
//
// A fast decoder does what `decode` does, with the same bookkeeping, in the
// same order and reading each property once: what it has decoded at each type
// is remembered (in `seen`, the same table `decode` keeps) so that an object
// reached twice is decoded once, and one reached while it's being decoded is
// refused, and objects whose fields are all shallow (`flatOf`) are decoded each
// time. Where it would nest deeper than `MAX_DEPTH` (it recurses, a loop
// doesn't), it hands that value to `decode`, with the same `seen`, which has no
// stack to run out of.
//
// A fast decoder never says why it refuses an input. It throws anything at all
// (`FAIL`, a `Refusal`, a getter's error, a `RangeError` from the stack), and
// then `decode`, the general one, runs on the whole input and gives the
// refusal, with its path, or finds that the input is fine after all (a getter
// that threw once need not throw again). So an input is accepted exactly when
// `decode` accepts it, to the same value, and refused with `decode`'s message.
// The only difference is that an input that's refused has been partly read
// before, by the fast decoder.
//
// The encoders read only values Stitchwort made. They give up on being nested
// deeper than `MAX_DEPTH`, and the general `encode` does it.
const FAIL = { fast: "gave up" };
const fail = () => {
  throw FAIL;
};
const MAX_DEPTH = 100;
let depth = 0, seen = null;
// What has been decoded at type `t` so far.
const memoOf = (t) => {
  let done = seen.get(t);
  if (done === undefined) seen.set(t, (done = new Map()));
  return done;
};
// `decode` for a value inside the fast path's, sharing what it has seen.
const decodeDeep = (t, x) => decode(t, x, "", seen);
// A call into an export from a getter, while another is being decoded, uses
// the counters afresh and leaves them as it found them.
const decodeFast = (fast, t, x, root) => {
  const outerDepth = depth, outerSeen = seen;
  depth = 0;
  seen = new Map();
  try {
    return fast(x);
  } catch {
    // The general decoder will say.
  } finally {
    depth = outerDepth;
    seen = outerSeen;
  }
  return decode(t, x, root);
};
const encodeFast = (fast, t, v) => {
  const outerDepth = depth;
  depth = 0;
  try {
    return fast(v);
  } catch {
    // The general encoder does it.
  } finally {
    depth = outerDepth;
  }
  return encode(t, v);
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
    /// `Decidable.elim`, which `if h: p then a else b` becomes.
    elim_dec: Option<DefId>,
    /// `Ord.compare` and `Ord.fromCompare`: a comparison through an instance
    /// the code names is a call of its `compare` ([`Gen::known_compare`]).
    ord_compare: Option<DefId>,
    ord_from_compare: Option<DefId>,
    /// `Nat.add`, whose calls in tail position a loop can add up as it goes
    /// ([`SelfCall::add`]), with the `bigint` representation of `Nat`.
    nat_add: Option<DefId>,
    /// `List.append`, whose calls in tail position a loop that builds cells
    /// can copy its first argument for ([`SelfCall::cons`]).
    list_append: Option<DefId>,
    /// The effect runtime, which replaces the library functions that take a
    /// computation apart (docs/proposals/effect-runtime.md §9), if the
    /// core is loaded.
    effect: Option<effect::Effect>,
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
    /// While a loop's body is being generated: the variables that stand for
    /// a function whose body is a call to the definition itself, which was
    /// an argument to a helper that's been inlined: the `%rec` of a
    /// definition by `decreasing` (crates/elab/src/decreasing.rs), whose
    /// runtime body is `f.%step x (y c p => f y c) c`.
    fn_holes: RefCell<Vec<FnHole>>,
    /// Whether such a variable was used any way but in tail position, or
    /// as a field of a constructor in tail position, where it can't be
    /// compiled.
    hole_misused: Cell<bool>,
    /// The fast path's generated codecs ([`fast`]).
    fast: RefCell<fast::Fast>,
    /// Decides which calls are at the empty row, and makes the variants
    /// (docs/proposals/effect-polymorphism.md, design E).
    spec: Specialiser<'g>,
    /// Per definition: whether it's used as it is, and whether through its
    /// empty-row variant ([`Gen::set_reach`]).
    used: RefCell<Vec<bool>>,
    empty: RefCell<Vec<bool>>,
    /// Per definition, its empty-row variant's [`DefInfo`].
    empty_infos: Vec<OnceCell<DefInfo>>,
    /// Recognises closed signature maps, which are built once
    /// ([`stitchwort_rt::hoist`], stage 4f).
    sig_maps: Option<SigMaps>,
    /// The closed maps found so far: `sigmap$i` is built by the `i`th.
    hoisted: RefCell<Vec<String>>,
    /// Whether a map's own code is being generated (a map inside it is
    /// built with it, not separately).
    hoisting: Cell<bool>,
    /// The curried forms of uncurried definitions used as values, by name
    /// (`f$c`, built at its first use and kept in a module variable).
    curried: RefCell<Vec<String>>,
}

/// What the generator decides about a definition from its type.
struct DefInfo {
    /// Whether it's a proof or a type.
    result_erased: bool,
    /// Which of its leading parameters (up to its arity) are erased.
    mask: Vec<bool>,
    /// How it's compiled and called, decided once and used at every site.
    convention: Convention,
    /// For a [`Convention::Function`] with two or more runtime parameters:
    /// its JS takes them all in one call, `f(a, b)`, rather than one at a
    /// time (D1173). A call with all of them is one call; a partial
    /// application, or a use as a value, is a closure that takes the rest
    /// one at a time, as every function value does.
    uncurried: bool,
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

/// A variable that stands for `x1 … xk => body`, where `body` is a call to
/// the definition whose loop is being generated ([`Gen::fn_holes`]).
struct FnHole {
    /// The variable's level.
    level: usize,
    /// `k`, and the parameters' names.
    params: Vec<stitchwort_core::Name>,
    /// The body, under the `k` parameters, in an environment of `site`
    /// variables.
    body: Term,
    site: usize,
}

/// The cells a constructor makes (`Gen::cons_cells`): the outermost, the
/// innermost, its field that takes the rest, and what the next turn is passed.
type Cells = (String, String, String, Passed);

struct SelfCall {
    id: DefId,
    /// Whether the loop is the definition's empty-row variant's.
    variant: bool,
    /// Whether any call was turned into a loop.
    used: Cell<bool>,
    /// Whether a call in a constructor's field, in tail position, is a turn
    /// of the loop too (tail recursion modulo constructor): the loop builds
    /// the result a cell at a time.
    cons: bool,
    /// Whether any was.
    cons_used: Cell<bool>,
    /// Whether a call in tail position under `Succ` or `Nat.add` is a turn
    /// of the loop too (tail recursion modulo addition): the loop keeps the
    /// sum of what it was to be added to, `a$`, and adds it to the result.
    /// `List.length`'s `Succ (List.length xs)`.
    add: bool,
    /// Whether any was.
    add_used: Cell<bool>,
    /// Whether to inline a helper that a call to the definition is an
    /// argument of, in tail position.
    inline: bool,
    /// How many helpers are being inlined, and a counter for names.
    inlining: Cell<usize>,
    fresh: Cell<usize>,
    /// The definitions being inlined, innermost last: one isn't inlined
    /// into itself.
    inlined: RefCell<Vec<DefId>>,
}

impl SelfCall {
    fn new(id: DefId, variant: bool, cons: bool, add: bool, inline: bool) -> Self {
        SelfCall {
            id,
            variant,
            used: Cell::new(false),
            cons,
            cons_used: Cell::new(false),
            add,
            add_used: Cell::new(false),
            inline,
            inlining: Cell::new(0),
            fresh: Cell::new(0),
            inlined: RefCell::new(Vec::new()),
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
            elim_dec: g.registry.def(Builtin::ElimDec),
            ord_compare: g.registry.def(Builtin::OrdCompare),
            ord_from_compare: g.registry.def(Builtin::OrdFromCompare),
            nat_add: nat.and(g.registry.def(Builtin::Add)),
            list_append: g.registry.def(Builtin::Append),
            effect: effect::Effect::new(g, options.effect_counters),
            run_delay: false,
            holes: RefCell::new(Vec::new()),
            fn_holes: RefCell::new(Vec::new()),
            hole_misused: Cell::new(false),
            fast: RefCell::default(),
            spec: Specialiser::new(g),
            used: RefCell::new(vec![true; g.defs.len()]),
            empty: RefCell::new(vec![false; g.defs.len()]),
            empty_infos: g.defs.iter().map(|_| OnceCell::new()).collect(),
            sig_maps: SigMaps::new(g),
            hoisted: RefCell::new(Vec::new()),
            hoisting: Cell::new(false),
            curried: RefCell::new(Vec::new()),
        })
    }

    /// What the program uses: the definitions `roots` and the terms
    /// `entries` refer to, directly or indirectly, with calls at the empty
    /// row using the callee's variant ([`specialise::reachable`]). Recorded
    /// for [`Gen::def`], and returned as the definitions to generate, by
    /// [`dependency_order`]. With `delay`, a definition whose result is a
    /// partial computation is opaque, and isn't generated.
    fn set_reach(
        &self,
        roots: impl IntoIterator<Item = DefId>,
        entries: &[&Term],
        delay: bool,
    ) -> Result<Vec<DefId>, Diagnostic> {
        let g = self.g;
        let failure = RefCell::new(None);
        let reach =
            specialise::reachable(&self.spec, roots, entries, |id| match self.try_info(id) {
                Ok(info) => {
                    info.result_erased || self.is_native(id) || (delay && info.delay.is_some())
                }
                Err(e) => {
                    failure.borrow_mut().get_or_insert(e);
                    true
                }
            })?;
        if let Some(e) = failure.into_inner() {
            return Err(e);
        }
        let wanted: Vec<DefId> = (0..g.defs.len())
            .map(DefId)
            .filter(|id| reach.used[id.0] || reach.empty[id.0])
            .collect();
        // `reachable` skips a definition without a body, so make sure of the
        // rest.
        for &id in &wanted {
            self.try_info(id)?;
        }
        *self.used.borrow_mut() = reach.used;
        *self.empty.borrow_mut() = reach.empty;
        Ok(wanted)
    }

    /// Whether `id` applied to `args` is a call of its empty-row variant.
    fn empty_call(&self, id: DefId, args: &[&Term]) -> bool {
        self.empty.borrow()[id.0] && self.spec.empty_call(id, args).unwrap_or(false)
    }

    /// The [`DefInfo`] of `id`'s empty-row variant: its row parameters are
    /// erased.
    fn empty_info(&self, id: DefId) -> &DefInfo {
        self.empty_infos[id.0].get_or_init(|| {
            let info = self.info(id);
            let mask = self
                .spec
                .empty_mask(id, &info.mask)
                .unwrap_or_else(|_| info.mask.clone());
            let convention = if mask.iter().any(|erased| !erased) {
                Convention::Function
            } else {
                Convention::Thunk
            };
            DefInfo {
                result_erased: info.result_erased,
                uncurried: runtime_params(&mask) >= 2,
                mask,
                convention,
                delay: None,
            }
        })
    }

    /// The JS name of `id`, or of its empty-row variant: the name with
    /// `$e`, which no definition's name has, since [`encode`] uses `$`
    /// only for its escapes, none of which is `$e`.
    fn js_name(&self, id: DefId, variant: bool) -> String {
        let name = def_name(&self.g.def(id).path);
        if variant { format!("{name}$e") } else { name }
    }

    /// Whether `id` applied to `args` is a call of the definition whose loop
    /// `call` is generating, with all its arguments: the same definition,
    /// and the variant if the loop is the variant's.
    fn is_self(&self, call: &SelfCall, id: DefId, args: &[&Term]) -> bool {
        id == call.id
            && args.len() == self.g.def(id).arity
            && self.empty_call(id, args) == call.variant
    }

    /// Which kernel-native implementation applies to `id`, if any: the
    /// number natives assume the `bigint` representation, so they apply only
    /// with it ([`nat_data`]).
    fn kernel_native(&self, id: DefId) -> Option<native::Native> {
        self.nat.and(self.g.builtins.native(id))
    }

    /// The one run-time field of a record that generated code stores as
    /// that field's value, with no object around it (D866,
    /// [`stitchwort_core::globals::Data::unboxed_field`]). A `Float` is a
    /// `number` instead, when it has that representation. Only inside
    /// generated code: at the boundary such a record is still an object
    /// with its field, and the codecs unbox and rebox it.
    pub(crate) fn unboxed(&self, d: DataId) -> Option<usize> {
        if Some(d) == self.float {
            return None;
        }
        self.g.data(d).unboxed_field()
    }

    /// Whether `id` is replaced by native JS of any kind.
    pub(crate) fn is_native(&self, id: DefId) -> bool {
        self.kernel_native(id).is_some()
            || self.text_natives.contains_key(&id)
            || self.int_natives.contains_key(&id)
            || self.float_natives.contains_key(&id)
            || self.effect_native(id).is_some()
    }

    /// Which of the library functions the effect runtime replaces `id` is,
    /// if any.
    fn effect_native(&self, id: DefId) -> Option<effect::EffectNative> {
        self.effect.as_ref().and_then(|e| e.native(id))
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
        // A native takes all its arguments at once if its JS can be written
        // so (every native's can, but a check is cheaper than a wrong call).
        let runtime = runtime_params(&mask);
        let uncurried = convention == Convention::Function
            && delay.is_none()
            && runtime >= 2
            && (self.effect_native(id).is_some()
                || self
                    .native_rhs(id)
                    .is_none_or(|js| uncurry_arrows(&js, runtime).is_some()));
        Ok(cell.get_or_init(|| DefInfo {
            result_erased,
            mask,
            convention,
            uncurried,
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

    /// The declaration of `id` if the program uses it as it is, followed by
    /// its empty-row variant's if the program uses that.
    fn def(&self, id: DefId) -> Fallible<String> {
        let mut out = String::new();
        if self.used.borrow()[id.0] {
            out.push_str(&self.def_with(id, false)?);
        }
        if self.empty.borrow()[id.0] {
            out.push_str(&self.def_with(id, true)?);
        }
        Ok(out)
    }

    /// The declaration of `id`, or of its empty-row variant.
    fn def_with(&self, id: DefId, variant: bool) -> Fallible<String> {
        let def = self.g.def(id);
        let DefInfo {
            mask, convention, ..
        } = if variant {
            self.empty_info(id)
        } else {
            self.info(id)
        };
        let convention = *convention;
        if convention == Convention::Erased {
            return Ok(String::new());
        }
        if variant {
            let body = self
                .spec
                .empty_body(id)
                .ok()
                .flatten()
                .expect("a variant is used only if it can be made");
            return self.def_body(id, true, &body, mask, convention);
        }
        // The effect runtime's functions take all their arguments at once
        // already.
        if let Some(op) = self.effect_native(id) {
            return Ok(format!("const {} = {};\n", def_name(&def.path), op.js()));
        }
        if let Some(js) = self.native_rhs(id) {
            let info = self.info(id);
            let js = if info.uncurried {
                uncurry_arrows(&js, runtime_params(&info.mask))
                    .expect("`try_info` checked that it uncurries")
            } else {
                js
            };
            return Ok(format!("const {} = {js};\n", def_name(&def.path)));
        }
        let Some(body) = def.run_body() else {
            unreachable!("`generate_with` refuses a definition without a body");
        };
        let body = body.clone();
        // Its calls of row eliminators with `Empty` inlined, if it has any.
        let simplified = self.spec.generic_body(id).ok().flatten();
        let tree = simplified
            .as_deref()
            .unwrap_or_else(|| body.peel_lams(def.arity));
        self.def_body(id, false, tree, mask, convention)
    }

    /// The JS of `id` if it's native (other than the effect runtime's), as
    /// a function taking its runtime arguments one at a time.
    fn native_rhs(&self, id: DefId) -> Option<String> {
        if self.run_delay
            && let Some(prim) = self.g.builtins.primitive(id)
        {
            return Some(run::primitive_js(prim).into());
        }
        if let Some(op) = self.float_natives.get(&id) {
            return Some(float_native_js(
                *op,
                self.int.is_some(),
                self.text.is_some(),
            ));
        }
        if let Some(op) = self.text_natives.get(&id) {
            return Some(text_native_js(*op).into());
        }
        if let Some(op) = self.int_natives.get(&id) {
            return Some(int_native_js(*op).into());
        }
        self.kernel_native(id).map(|op| native_js(op).into())
    }

    /// `const f = …;` for `id`, or its empty-row variant, with case tree
    /// (or body) `tree` under its parameters.
    fn def_body(
        &self,
        id: DefId,
        variant: bool,
        tree: &Term,
        mask: &[bool],
        convention: Convention,
    ) -> Fallible<String> {
        let name = self.js_name(id, variant);
        let mut env = mask.to_vec();
        let uncurried = if variant {
            self.empty_info(id)
        } else {
            self.info(id)
        }
        .uncurried;
        let runtime: Vec<String> = (0..mask.len())
            .filter(|level| !mask[*level])
            .map(var)
            .collect();
        let params = if runtime.is_empty() {
            String::new()
        } else if uncurried {
            format!("({}) => ", runtime.join(", "))
        } else {
            runtime.iter().map(|v| format!("({v}) => ")).collect()
        };
        let tree = tree.strip_loc();
        let rhs = if matches!(tree, Term::Case(..) | Term::NumCase(..)) {
            if !params.is_empty()
                && let Some(block) = self.self_tail_loop(id, variant, tree, &mut env)?
            {
                return Ok(format!("const {name} = {params}{block};\n"));
            }
            let block = self.tree(tree, &mut env, 1, None)?;
            match convention {
                Convention::Thunk => format!("() => {{\n{block}}}"),
                _ => format!("{{\n{block}}}"),
            }
        } else {
            // Not a case tree, but it may still reach a call to itself in
            // tail position: through a member of its group, inlined (a
            // lifted `match`), or through the `%rec` of a definition by
            // `decreasing`.
            if !params.is_empty()
                && self.may_loop(id, tree)
                && let Some(block) = self.self_tail_loop(id, variant, tree, &mut env)?
            {
                return Ok(format!("const {name} = {params}{block};\n"));
            }
            // After `=>`, leading `let`s are `const`s in a block.
            let rhs = if convention == Convention::Value {
                self.expr(tree, &mut env)?
            } else {
                self.function_body(tree, &mut env)?
            };
            match convention {
                Convention::Thunk => format!("() => {rhs}"),
                _ => rhs,
            }
        };
        Ok(format!("const {name} = {params}{rhs};\n"))
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
        variant: bool,
        tree: &Term,
        env: &mut Vec<bool>,
    ) -> Fallible<Option<String>> {
        // The most it can do first: calls modulo constructors, through
        // inlined helpers. If that can't be compiled (a helper uses the
        // result some other way), less, and last, only direct tail calls.
        // Inlining without cons comes last: `List.decEq`'s step has no
        // constructor to build, only the call's result to return. Calls
        // modulo addition come after those modulo constructors: a result
        // that's a number is never a cell.
        for (cons, add, inline) in [
            (true, false, true),
            (true, false, false),
            (false, true, true),
            (false, true, false),
            (false, false, false),
            (false, false, true),
        ] {
            if add && self.nat_add.is_none() {
                continue;
            }
            let call = SelfCall::new(id, variant, cons, add, inline);
            self.holes.borrow_mut().clear();
            self.fn_holes.borrow_mut().clear();
            self.hole_misused.set(false);
            let block = self.tree(tree, env, 2, Some(&call))?;
            let ok = call.used.get()
                && !self.hole_misused.get()
                && (!cons || call.cons_used.get())
                && (!add || call.add_used.get());
            self.holes.borrow_mut().clear();
            self.fn_holes.borrow_mut().clear();
            self.hole_misused.set(false);
            if ok {
                return Ok(Some(Self::loop_block(env, &block, cons, add)));
            }
        }
        Ok(None)
    }

    /// Whether `body`, the body of definition `id` that isn't a case tree,
    /// mentions `id` or another member of its group: only then is
    /// [`Gen::self_tail_loop`] worth trying.
    fn may_loop(&self, id: DefId, body: &Term) -> bool {
        let group = self.g.def(id).group.as_deref().unwrap_or(&[]);
        body.subterms().any(|(t, _)| match t {
            Term::Def(d) => *d == id || group.contains(d),
            _ => false,
        })
    }

    /// Whether `member`, called in tail position in the loop of `call`'s
    /// definition, is inlined there, so that its own tail calls to that
    /// definition are turns of the loop. It's another member of the group,
    /// not one already being inlined, and either
    ///
    /// - a `match` lifted out of the definition (`f.%match1`, or one nested
    ///   in it), which calls a member: it's inlined wherever it's used,
    ///   since there are only as many as the source has `match`es; or
    /// - a member that calls the definition itself (`isOdd`, in `isEven`'s
    ///   loop). One that only calls other members isn't, so that a big group
    ///   doesn't inline chains of members into each other: a cycle of three
    ///   or more such members still uses a stack frame per call.
    ///
    /// A definition isn't inlined into a `match` lifted out of it:
    /// `f.%match1` calls `f`, which loops, rather than holding a copy of it.
    fn inlines_member(&self, member: DefId, call: &SelfCall) -> bool {
        let def = self.g.def(call.id);
        let Some(group) = def.group.as_deref() else {
            return false;
        };
        // A member's body is the generic one, which a variant's loop
        // doesn't reach: it calls the member's variant instead.
        if call.variant {
            return false;
        }
        if member == call.id || !group.contains(&member) || call.inlined.borrow().contains(&member)
        {
            return false;
        }
        let member_def = self.g.def(member);
        let path = def.path.to_string();
        let member_path = member_def.path.to_string();
        if path.starts_with(&format!("{member_path}.%")) {
            return false;
        }
        let lifted = member_path.starts_with(&format!("{path}.%"));
        member_def.run_body().is_some_and(|body| {
            body.subterms().any(|(t, _)| match t {
                Term::Def(d) => *d == call.id || (lifted && group.contains(d)),
                _ => false,
            })
        })
    }

    /// The loop of [`Gen::self_tail_loop`], around the case tree's `block`.
    /// With `cons`, the result is built by a chain of cells (a constructor's
    /// object) that the loop links as it makes them: `h$` is the first, `l$`
    /// the last, and `k$` the name of its field that the rest goes in. With
    /// `add`, `a$` is what the result is to be added to.
    fn loop_block(env: &[bool], block: &str, cons: bool, add: bool) -> String {
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
        } else if add {
            "  let a$ = 0n;\n"
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
        // A record stored as its one run-time field (D866): that field is the
        // value matched.
        let unboxed = self.unboxed(*d).is_some();
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
                } else if !erased && unboxed {
                    let _ = writeln!(out, "{pad}const {} = {scrutinee};", var(level + f));
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
        // A function that stands for a call to itself, applied: the call,
        // with the arguments bound to its parameters.
        if let Some(reduced) = self.apply_fn_hole(term, env.len())? {
            return self.tail(&reduced, env, depth, call);
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
        if call.add
            && let Some(out) = self.tail_add(term, env, &pad, call)?
        {
            return Ok(out);
        }
        if call.cons
            && let Some(out) = self.tail_append(term, env, &pad, call)?
        {
            return Ok(out);
        }
        let (head, args) = term.spine();
        let Term::Def(id) = head else {
            return self.leaf_return(term, env, &pad, call);
        };
        if self.is_self(call, *id, &args) {
            call.used.set(true);
            let mut passed = Vec::new();
            for (level, arg) in args.iter().enumerate() {
                if !env[level] {
                    passed.push((level, self.expr(arg, env)?));
                }
            }
            return Ok(Self::next_turn(&pad, &passed));
        }
        // `if c then a else b` (`Bool.ifThenElse c (_ => a) (_ => b)`) and
        // `if h: p then a else b` (`Decidable.elim d (h => a) (h => b)`).
        let branches = if Some(*id) == self.if_then_else
            && let [_, cond, then, otherwise] = args.as_slice()
        {
            Some((cond, then, otherwise, "True".to_string()))
        } else if Some(*id) == self.elim_dec
            && let [_, _, cond, then, otherwise] = args.as_slice()
        {
            Some((cond, then, otherwise, self.decision_yes_tag()))
        } else {
            None
        };
        if let Some((cond, then, otherwise, tag)) = branches
            && let (Term::Lam(_, _, then), Term::Lam(_, _, otherwise)) =
                (then.strip_loc(), otherwise.strip_loc())
        {
            let cond = self.expr(cond, env)?;
            // The branches' parameter is a proof (of `Unit`, of `p` or of
            // `Not p`), so it's erased.
            let mut branch = |body: &Term| -> Fallible<String> {
                env.push(true);
                let out = self.tail(body, env, depth + 1, call);
                env.pop();
                out
            };
            let then = branch(then)?;
            let otherwise = branch(otherwise)?;
            return Ok(format!(
                "{pad}if ({cond}.tag === {}) {{\n{then}{pad}}} else {{\n{otherwise}{pad}}}\n",
                js_string_literal(&tag)
            ));
        }
        if call.inline
            && call.inlining.get() < 3
            && let Some(out) = self.inline_helper(*id, &args, env, depth, call)?
        {
            return Ok(out);
        }
        self.leaf_return(term, env, &pad, call)
    }

    /// If `term` is a call to the definition itself (or a variable that
    /// stands for one) under `Succ`s and `Nat.add`s, with the other operands
    /// not mentioning it: the next turn, after adding those operands to
    /// `a$` (tail recursion modulo addition, [`SelfCall::add`]). Addition
    /// is associative and commutative, so `x + f(..)` is `f(..)` with `x`
    /// added to the sum, wherever the call is among the operands.
    fn tail_add(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        pad: &str,
        call: &SelfCall,
    ) -> Fallible<Option<String>> {
        // The other operands, and the call.
        let mut addends: Vec<&Term> = Vec::new();
        let mut ones = 0u64;
        let mut inner = term.strip_loc();
        loop {
            if let Term::Ctor(d, 1, succ) = inner
                && Some(*d) == self.nat
            {
                ones += 1;
                inner = succ[0].strip_loc();
                continue;
            }
            let (head, args) = inner.spine();
            if let Term::Def(id) = head
                && Some(*id) == self.nat_add
                && let [left, right] = args.as_slice()
            {
                let in_left = self.self_call_under_add(left, env, call);
                let in_right = self.self_call_under_add(right, env, call);
                if in_left == in_right {
                    return Ok(None);
                }
                let (operand, rest) = if in_left {
                    (right, left)
                } else {
                    (left, right)
                };
                addends.push(operand);
                inner = rest.strip_loc();
                continue;
            }
            break;
        }
        if addends.is_empty() && ones == 0 {
            return Ok(None);
        }
        let Some(passed) = self.hole_passed(inner, env, call)? else {
            return Ok(None);
        };
        let mut out = String::new();
        for addend in addends {
            let _ = writeln!(out, "{pad}a$ += {};", self.expr(addend, env)?);
        }
        if ones > 0 {
            let _ = writeln!(out, "{pad}a$ += {ones}n;");
        }
        call.add_used.set(true);
        call.used.set(true);
        out.push_str(&Self::next_turn(pad, &passed));
        Ok(Some(out))
    }

    /// Whether `term` is a call to the definition itself, or a variable
    /// that stands for one, under `Succ`s and `Nat.add`s ([`Gen::tail_add`]).
    /// (Nothing is generated.)
    fn self_call_under_add(&self, term: &Term, env: &[bool], call: &SelfCall) -> bool {
        let term = term.strip_loc();
        if let Term::Ctor(d, 1, succ) = term
            && Some(*d) == self.nat
        {
            return self.self_call_under_add(&succ[0], env, call);
        }
        if let Term::Var(ix) = term {
            return self.hole_at(env.len() - 1 - ix).is_some();
        }
        let (head, args) = term.spine();
        match head {
            Term::Def(id) if self.is_self(call, *id, &args) => true,
            Term::Def(id) if Some(*id) == self.nat_add && args.len() == 2 => {
                self.self_call_under_add(args[0], env, call)
                    != self.self_call_under_add(args[1], env, call)
            }
            _ => false,
        }
    }

    /// If `term` is `List.append xs rest`, where `rest` is a call to the
    /// definition itself (or a variable that stands for one): copies of
    /// `xs`'s cells linked onto the chain, then the next turn, whose result
    /// goes after them (tail recursion modulo append: `List.concat`'s
    /// `List.append xs (List.concat xss)`). `List.append` copies its first
    /// argument and shares its second, as this does.
    fn tail_append(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        pad: &str,
        call: &SelfCall,
    ) -> Fallible<Option<String>> {
        let (head, args) = term.spine();
        let Term::Def(id) = head else {
            return Ok(None);
        };
        if Some(*id) != self.list_append || args.len() != self.g.def(*id).arity || args.len() < 2 {
            return Ok(None);
        }
        let (front, rest) = (args[args.len() - 2], args[args.len() - 1]);
        let Some(list) = self.g.registry.data(Builtin::List) else {
            return Ok(None);
        };
        let Some(cons) = self
            .g
            .data(list)
            .ctors
            .iter()
            .position(|c| &*c.name == "Cons")
        else {
            return Ok(None);
        };
        if self.hole_passed_shape(rest, env, call).is_none() {
            return Ok(None);
        }
        // `xs` is computed first, as the call's first argument was.
        let front = self.expr(front, env)?;
        let passed = self
            .hole_passed(rest, env, call)?
            .expect("`hole_passed_shape` found a call");
        let tag = js_string_literal(&self.g.data(list).ctors[cons].name);
        let head_key = field_key_at(self.g, list, cons, 0);
        let tail_key = field_key_at(self.g, list, cons, 1);
        let n = call.fresh();
        let mut out = String::new();
        let _ = writeln!(
            out,
            "{pad}for (let p{n}$ = {front}; p{n}$.tag === {tag}; p{n}$ = p{n}${}) {{",
            member(&tail_key)
        );
        let _ = writeln!(
            out,
            "{pad}  const c{n}$ = {{ tag: {tag}, {}: p{n}${}, {}: null }};",
            ts_key(&head_key),
            member(&head_key),
            ts_key(&tail_key)
        );
        let _ = writeln!(
            out,
            "{pad}  if (l$ === null) {{ h$ = c{n}$; }} else {{ l$[k$] = c{n}$; }}"
        );
        let _ = writeln!(
            out,
            "{pad}  l$ = c{n}$; k$ = {};",
            js_string_literal(&tail_key)
        );
        let _ = writeln!(out, "{pad}}}");
        call.cons_used.set(true);
        call.used.set(true);
        out.push_str(&Self::next_turn(pad, &passed));
        Ok(Some(out))
    }

    /// Whether `term` is a call to the definition itself, or a variable
    /// that stands for one. (Nothing is generated.)
    fn hole_passed_shape(&self, term: &Term, env: &[bool], call: &SelfCall) -> Option<()> {
        if let Term::Var(ix) = term.strip_loc() {
            return self.hole_at(env.len() - 1 - ix).map(|_| ());
        }
        let (head, args) = term.spine();
        matches!(head, Term::Def(id) if self.is_self(call, *id, &args)).then_some(())
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
        } else if call.add && value == "0n" {
            format!("{pad}return a$;\n")
        } else if call.add {
            format!("{pad}return a$ + {value};\n")
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
        if self.hole_at(level).is_some() || self.is_fn_hole(level) {
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
            && self.is_self(call, *id, &args)
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
        // A record stored as its field (D866) is no cell either.
        if data.sort == Sort::Prop
            || Some(*d) == self.text
            || Some(*d) == self.nat
            || Some(*d) == self.int
            || Some(*d) == self.float
            || self.unboxed(*d).is_some()
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
                    matches!(head, Term::Def(id) if self.is_self(call, *id, &args))
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
    ///
    /// The same for an argument that's a function whose body is such a
    /// call, which the helper may only apply, in those places: a
    /// definition by `decreasing` runs `f.%step x (y c p => f y c) c`
    /// ([`Gen::fn_holes`]). And for a call to another member of the
    /// definition's group ([`Gen::inlines_member`]), whose own calls to the
    /// definition are then in tail position here.
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
        let variant = self.empty_call(id, args);
        let info = if variant { self.empty_info(id) } else { info };
        if info.convention != Convention::Function || info.delay.is_some() {
            return Ok(None);
        }
        let tree = if variant {
            match self.spec.empty_body(id) {
                Ok(Some(body)) => body,
                _ => return Ok(None),
            }
        } else {
            match (self.spec.generic_body(id).ok().flatten(), def.run_body()) {
                (Some(simplified), _) => simplified,
                (None, Some(body)) => Rc::new(body.peel_lams(def.arity).clone()),
                (None, None) => return Ok(None),
            }
        };
        // The arguments, in this call's environment. A call to itself isn't
        // made: it's the next turn, if the helper puts it in tail position.
        enum Bound {
            Erased,
            Value(String),
            Hole(Passed),
            /// The parameters, the body, and the environment's size there.
            FnHole(Vec<stitchwort_core::Name>, Term, usize),
        }
        let member = self.inlines_member(id, call);
        let mut bound = Vec::new();
        let mut any_hole = false;
        for (i, arg) in args.iter().enumerate() {
            if info.mask[i] {
                bound.push(Bound::Erased);
            } else if let Some(passed) = self.hole_passed(arg, env, call)? {
                any_hole = true;
                bound.push(Bound::Hole(passed));
            } else if let Some((params, body)) = self.fn_hole_arg(arg, call) {
                any_hole = true;
                bound.push(Bound::FnHole(params, body, env.len()));
            } else if let Term::Var(ix) = arg.strip_loc()
                && let Some(hole) = self
                    .fn_holes
                    .borrow()
                    .iter()
                    .rfind(|h| h.level == env.len() - 1 - ix)
            {
                // Passed on (to a `match` lifted out of `f.%step`): it
                // stands for the same function there.
                any_hole = true;
                bound.push(Bound::FnHole(
                    hole.params.clone(),
                    hole.body.clone(),
                    hole.site,
                ));
            } else {
                bound.push(Bound::Value(self.expr(arg, env)?));
            }
        }
        if !any_hole && !member {
            return Ok(None);
        }
        let pad = "  ".repeat(depth);
        let base = env.len();
        let mut out = String::new();
        let mut registered = 0;
        let mut registered_fns = 0;
        for (i, b) in bound.into_iter().enumerate() {
            match b {
                Bound::Erased => env.push(true),
                Bound::Value(value) => {
                    let _ = writeln!(out, "{pad}const {} = {value};", var(base + i));
                    env.push(false);
                }
                Bound::Hole(passed) => {
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
                Bound::FnHole(params, body, site) => {
                    // Nothing to compute: the function is only applied.
                    self.fn_holes.borrow_mut().push(FnHole {
                        level: base + i,
                        params,
                        body,
                        site,
                    });
                    registered_fns += 1;
                    env.push(false);
                }
            }
        }
        call.inlining.set(call.inlining.get() + 1);
        call.inlined.borrow_mut().push(id);
        let result = self.tree(&tree, env, depth, Some(call));
        call.inlined.borrow_mut().pop();
        call.inlining.set(call.inlining.get() - 1);
        env.truncate(base);
        let mut holes = self.holes.borrow_mut();
        let keep = holes.len() - registered;
        holes.truncate(keep);
        drop(holes);
        let mut fn_holes = self.fn_holes.borrow_mut();
        let keep = fn_holes.len() - registered_fns;
        fn_holes.truncate(keep);
        drop(fn_holes);
        out.push_str(&result?);
        Ok(Some(out))
    }

    /// If `arg` is `x1 … xk => body`, where `body` is a call to `call`'s
    /// definition with all its arguments, the parameters' names and the
    /// body ([`Gen::fn_holes`]).
    fn fn_hole_arg(
        &self,
        arg: &Term,
        call: &SelfCall,
    ) -> Option<(Vec<stitchwort_core::Name>, Term)> {
        let mut params = Vec::new();
        let mut body = arg.strip_loc();
        while let Term::Lam(name, _, inner) = body {
            params.push(name.clone());
            body = inner.strip_loc();
        }
        let (head, args) = body.spine();
        (!params.is_empty() && matches!(head, Term::Def(id) if self.is_self(call, *id, &args)))
            .then(|| (params, body.clone()))
    }

    /// Whether variable `level` stands for a function whose body is a call
    /// to the definition itself ([`Gen::fn_holes`]).
    fn is_fn_hole(&self, level: usize) -> bool {
        self.fn_holes.borrow().iter().any(|h| h.level == level)
    }

    /// If `term`, in an environment of `depth` variables, applies a
    /// function that stands for a call to the definition itself
    /// ([`Gen::fn_holes`]) to all its parameters, or is a constructor with
    /// such an application as a field: the term with the function's body
    /// in place of the application, under `let`s that bind its parameters
    /// to the arguments, in order (so they're computed as the arguments
    /// would have been). A parameter the body doesn't use isn't computed,
    /// as for any `let` whose variable is unused.
    fn apply_fn_hole(&self, term: &Term, depth: usize) -> Fallible<Option<Term>> {
        let holes = self.fn_holes.borrow();
        if holes.is_empty() {
            return Ok(None);
        }
        let applied = |t: &Term| -> Option<(usize, Vec<Term>)> {
            let (head, args) = t.strip_loc().spine();
            let Term::Var(ix) = head.strip_loc() else {
                return None;
            };
            let level = depth.checked_sub(ix + 1)?;
            let h = holes.iter().rposition(|h| h.level == level)?;
            (holes[h].params.len() == args.len()).then(|| (h, args.into_iter().cloned().collect()))
        };
        // The body, under the parameters, moved from its own environment
        // to this one.
        let body_here = |h: &FnHole| h.body.shift(self.g, depth - h.site, h.params.len());
        let (h, args, inner) = if let Some((h, args)) = applied(term) {
            let inner = body_here(&holes[h])?;
            (h, args, inner)
        } else if let Term::Ctor(d, c, fields) = term.strip_loc() {
            let found: Vec<_> = fields
                .iter()
                .enumerate()
                .filter_map(|(i, f)| applied(f).map(|a| (i, a)))
                .collect();
            let [(at, (h, args))] = found.as_slice() else {
                return Ok(None);
            };
            let k = holes[*h].params.len();
            let mut moved = Vec::new();
            for (i, f) in fields.iter().enumerate() {
                moved.push(Rc::new(if i == *at {
                    body_here(&holes[*h])?
                } else {
                    f.shift(self.g, k, 0)?
                }));
            }
            (*h, args.clone(), Term::Ctor(*d, *c, moved))
        } else {
            return Ok(None);
        };
        let params = &holes[h].params;
        let mut out = inner;
        for (j, (name, arg)) in params.iter().zip(&args).enumerate().rev() {
            let unused = !out.mentions(0);
            out = Term::Let(
                name.clone(),
                Rc::new(Term::Sort(Sort::Prop)),
                Rc::new(arg.shift(self.g, j, 0)?),
                Rc::new(out),
                unused,
            );
        }
        Ok(Some(out))
    }

    /// A lambda applied where it's made, `(x1 … xk => body) a1 … ak rest…`,
    /// as `let x1 := a1; …; let xk := ak; body rest…`, so that it's
    /// generated as `let`s ([`Gen::inline_let`], [`Gen::function_body`]),
    /// not as a closure made and called on the spot. The elaborator writes
    /// `a == b` and `x ∈ xs` that way, with the operands bound
    /// (`(a => toBool (decEq a b)) x`, elab's `bind.rs`), so inside a
    /// callback the closure would be made once for each element. Each `let`
    /// computes its argument before the body, as the call would have; one
    /// the body doesn't use isn't computed.
    fn beta_lets(&self, head: &Term, args: &[&Term]) -> Fallible<Option<Term>> {
        let mut head = head;
        while let Term::Loc(_, t) | Term::Ann(t, _) = head {
            head = t;
        }
        let mut names = Vec::new();
        let mut body = head;
        while names.len() < args.len()
            && let Term::Lam(x, _, inner) = body
        {
            names.push(x.clone());
            body = inner.strip_loc();
        }
        let k = names.len();
        if k == 0 {
            return Ok(None);
        }
        let mut out = body.clone();
        for arg in &args[k..] {
            out = Term::app(out, arg.shift(self.g, k, 0)?);
        }
        for (j, name) in names.into_iter().enumerate().rev() {
            let unused = !out.mentions(0);
            out = Term::Let(
                name,
                Rc::new(Term::Sort(Sort::Prop)),
                Rc::new(args[j].shift(self.g, j, 0)?),
                Rc::new(out),
                unused,
            );
        }
        Ok(Some(out))
    }

    /// The body of `let x := value; body` with `value` in place of `x`, if
    /// that computes `value` no more often than the `let` does: `value` is
    /// a variable or a number, or `x` is used at most once, and not inside
    /// a lambda ([`single_use`]). It may then be computed later than the
    /// `let` would have, or not at all, which is fine: generated code is
    /// pure and total (a computation with effects is a value until it's
    /// run), so when it's computed doesn't matter (see `def_ref`).
    fn inline_let(&self, value: &Term, body: &Term) -> Fallible<Option<Term>> {
        let inline = match value.strip_loc() {
            Term::Var(_) => true,
            Term::Nat(_) => !scrutinised(body),
            _ => single_use(self, body),
        };
        Ok(if inline {
            Some(body.instantiate(self.g, value)?)
        } else {
            None
        })
    }

    /// `term`'s JS as an arrow function's body (in `env`, which has the
    /// function's parameters). Leading `let`s that aren't inlined
    /// ([`Gen::inline_let`]) are `const`s in a block, `{ const v3 = …;
    /// return …; }`, rather than a closure made and called each time the
    /// function is: computed once, in order, before the rest.
    fn function_body(&self, term: &Term, env: &mut Vec<bool>) -> Fallible<String> {
        let start = env.len();
        let mut statements = String::new();
        let body = self.function_statements(term, env, &mut statements);
        env.truncate(start);
        let body = body?;
        Ok(if !statements.is_empty() {
            format!("{{ {statements}return {body}; }}")
        } else if body.starts_with('{') {
            // An object literal as an arrow function's body needs
            // parentheses, or it's read as a block.
            format!("({body})")
        } else {
            body
        })
    }

    /// [`Gen::function_body`]'s `const`s, added to `statements`, and the
    /// expression after them.
    fn function_statements(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        statements: &mut String,
    ) -> Fallible<String> {
        let mut term = term.clone();
        loop {
            let next = match term.strip_loc() {
                Term::Let(_, _, _, body, true) => {
                    env.push(true);
                    (**body).clone()
                }
                Term::Let(_, _, value, body, false) => match self.inline_let(value, body)? {
                    Some(inlined) => inlined,
                    None => {
                        let value = self.expr(value, env)?;
                        let _ = write!(statements, "const {} = {value}; ", var(env.len()));
                        env.push(false);
                        (**body).clone()
                    }
                },
                Term::Ann(inner, _) => (**inner).clone(),
                Term::App(..) => {
                    let (head, args) = term.spine();
                    match self.beta_lets(head, &args)? {
                        Some(lets) => lets,
                        None => return self.expr(&term, env),
                    }
                }
                _ => return self.expr(&term, env),
            };
            term = next;
        }
    }

    fn expr(&self, term: &Term, env: &mut Vec<bool>) -> Fallible<String> {
        self.g.budget.nesting(PASS)?;
        Ok(match term {
            Term::Loc(_, t) | Term::Ann(t, _) => self.expr(t, env)?,
            Term::Var(ix) => {
                let level = env.len() - 1 - ix;
                if self.hole_at(level).is_some() || self.is_fn_hole(level) {
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
                if let Some(reduced) = stitchwort_rt::erasure::beta_variable(self.g, head, &args)? {
                    return self.expr(&reduced, env);
                }
                if let Some(lets) = self.beta_lets(head, &args)? {
                    return self.expr(&lets, env);
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
                let body = self.function_body(body, env);
                env.pop();
                format!("(({}) => {})", var(level), body?)
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
                if let Some(inlined) = self.inline_let(value, body)? {
                    return self.expr(&inlined, env);
                }
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
                // A record with one run-time field is that field (D866).
                if let Some(i) = self.unboxed(*d) {
                    return self.expr(&args[i], env);
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
            Term::Data(..)
            | Term::Sort(_)
            | Term::Pi(..)
            | Term::Eq(..)
            | Term::Refl
            | Term::Quot(QuotForm::Type, ..) => "undefined".into(),
            // Quotients (docs/proposals/map-equality.md §7.4.1, D921), as in
            // the Rust runtime: `Quot.mk a` is `a` (`undefined` when the
            // carrier's elements are erased), a lift whose result isn't
            // erased is the application `f q` (§7.4.2), and the rest are
            // proofs or types.
            Term::Quot(QuotForm::Mk, args, false) => self.expr(&args[2], env)?,
            Term::Quot(QuotForm::Lift, args, false) => {
                let f_q = Term::App(args[3].clone(), args[5].clone(), Icit::Explicit);
                self.expr(&f_q, env)?
            }
            Term::Quot(QuotForm::Mk | QuotForm::Lift | QuotForm::Ind | QuotForm::Sound, ..) => {
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
        // A closed signature map (a `translate`'s, say): built at its first
        // use and kept in a module variable, not built again on every call
        // (stitchwort_rt::hoist). Generated code is pure and total, so when
        // it's built doesn't matter, and the first use builds it exactly
        // where the code did before.
        if !self.hoisting.get()
            && let Some(sig_maps) = &self.sig_maps
            && sig_maps.closed_map(self.g, id, args)
        {
            self.hoisting.set(true);
            let value = self.def_call(id, args, env);
            self.hoisting.set(false);
            let value = value?;
            let mut hoisted = self.hoisted.borrow_mut();
            let i = match hoisted.iter().position(|v| *v == value) {
                Some(i) => i,
                None => {
                    hoisted.push(value.clone());
                    hoisted.len() - 1
                }
            };
            return Ok(format!("(sigmap${i} ??= {value})"));
        }
        self.def_call(id, args, env)
    }

    /// The declarations of the module variables that hold the closed
    /// signature maps, if there are any: `var`s, so that a use earlier in
    /// the module (any use, since the definitions come first) is fine.
    pub(crate) fn hoisted_vars(&self) -> String {
        let mut out = String::new();
        let n = self.hoisted.borrow().len();
        if n > 0 {
            let names: Vec<String> = (0..n).map(|i| format!("sigmap${i}")).collect();
            let _ = write!(
                out,
                "\n// Closed signature maps, each built at its first use.\nvar {};\n",
                names.join(", ")
            );
        }
        let curried = self.curried.borrow();
        if !curried.is_empty() {
            let _ = write!(
                out,
                "\n// Definitions used as values, taking their arguments one at a time, each\n\
                 // made at its first use.\nvar {};\n",
                curried.join(", ")
            );
        }
        out
    }

    /// Whether `term` is `Yes _` (or `No _`, with `yes` false), the proof
    /// ignored.
    fn is_decision(&self, term: &Term, yes: bool) -> bool {
        let ctor = self
            .g
            .registry
            .ctor(if yes { Builtin::Yes } else { Builtin::No });
        matches!(term.strip_loc(), Term::Ctor(d, c, _) if Some((*d, *c)) == ctor)
    }

    /// `Decidable.elim d (h => Yes …) (h => No …)`: `d` itself, since the
    /// proofs are erased. A derived `==` on a record with one field to
    /// compare is this, around the field's decision.
    fn decision_itself<'t>(&self, id: DefId, args: &[&'t Term]) -> Option<&'t Term> {
        if Some(id) != self.elim_dec {
            return None;
        }
        let [_, _, decision, yes, no] = args else {
            return None;
        };
        match (yes.strip_loc(), no.strip_loc()) {
            (Term::Lam(_, _, yes), Term::Lam(_, _, no))
                if self.is_decision(yes, true) && self.is_decision(no, false) =>
            {
                Some(decision)
            }
            _ => None,
        }
    }

    /// The comparison of `instance`, an `Ord` instance, if it's a definition
    /// whose own body says which: a record of the fields
    /// (`{ compare = Nat.compare, … }`) or `Ord.fromCompare c …`, with the
    /// comparison a definition. So `Ord.compare Text.instOrd x y` (a derived
    /// `Ord` on a record over `Text` is this) is `Text.compare x y`, a direct
    /// call, rather than a read of the dictionary's field and a call of the
    /// closure there one argument at a time.
    fn known_compare(&self, instance: &Term) -> Option<Rc<Term>> {
        let Term::Def(id) = instance.strip_loc() else {
            return None;
        };
        let def = self.g.def(*id);
        if def.arity != 0 {
            return None;
        }
        let body = def.run_body()?.strip_loc();
        // The field `compare` of a record built by `Ord`'s constructor.
        let field = |term: &Term| -> Option<Rc<Term>> {
            let Term::Ctor(d, 0, fields) = term.strip_loc() else {
                return None;
            };
            let data = self.g.data(*d);
            let k = data.ctors[0]
                .fields
                .iter()
                .position(|(name, _)| &**name == "compare")?;
            Some(fields[k].clone())
        };
        let compare = if let Some(compare) = field(body) {
            compare
        } else {
            let (head, args) = body.spine();
            let Term::Def(from) = head.strip_loc() else {
                return None;
            };
            if Some(*from) != self.ord_from_compare {
                return None;
            }
            // `Ord.fromCompare`'s record names its parameter `compare`: the
            // argument in that place.
            let from = self.g.def(*from);
            let mut inner = from.run_body()?.strip_loc();
            for _ in 0..from.arity {
                let Term::Lam(_, _, b) = inner else {
                    return None;
                };
                inner = b.strip_loc();
            }
            let Term::Var(ix) = field(inner)?.strip_loc().clone() else {
                return None;
            };
            let param = from.arity.checked_sub(ix + 1)?;
            Rc::new((*args.get(param)?).clone())
        };
        matches!(compare.strip_loc(), Term::Def(_)).then_some(compare)
    }

    /// [`Gen::def_ref`], without building a closed map once.
    fn def_call(&self, id: DefId, args: &[&Term], env: &mut Vec<bool>) -> Fallible<String> {
        if let Some(decision) = self.decision_itself(id, args) {
            return self.expr(decision, env);
        }
        if Some(id) == self.ord_compare
            && let [_, instance, rest @ ..] = args
            && let Some(compare) = self.known_compare(instance)
            && let Term::Def(compare) = compare.strip_loc()
        {
            return self.def_ref(*compare, rest, env);
        }
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
        // A state-passing handler at the empty row: its fold runs as a loop
        // with the state in a variable (docs/proposals/effect-runtime.md
        // §9.1.5, stage 4d).
        if let Some(effect) = &self.effect
            && effect.is_fold(id)
            && let Some(fused) = effect.fuse(self.g, args)?
        {
            // `fuse` needs the computation, the seventh argument; any after
            // it are the result's (the state).
            let mut out = format!(
                "effFoldState({}, {}, {}, {})",
                fused.comp,
                self.expr(&fused.done, env)?,
                self.expr(&fused.call, env)?,
                self.expr(args[6], env)?
            );
            for arg in &args[7..] {
                let _ = write!(out, "({})", self.expr(arg, env)?);
            }
            return Ok(out);
        }
        // A call at the empty row calls the variant, which takes no row.
        let variant = self.empty_call(id, args);
        let info = if variant {
            self.empty_info(id)
        } else {
            self.info(id)
        };
        let mask = &info.mask;
        let mut out = match info.convention {
            Convention::Erased => return Ok("undefined".into()),
            Convention::Thunk => format!("{}()", self.js_name(id, variant)),
            Convention::Value | Convention::Function => self.js_name(id, variant),
        };
        // Values the callee is passed before the call's own arguments.
        let mut prefix = Vec::new();
        // A `handle`'s fold: lazy resumption where its carrier (the fourth
        // argument, erased) is a computation (docs/proposals/effect-runtime.md
        // §9.2). The same parameters, so the call is built the same way.
        if let Some(effect) = &self.effect
            && effect.is_fold(id)
            && let Some(carrier) = args.get(3)
        {
            match effect.carrier(carrier) {
                effect::Carrier::Tree => out = "effFoldCompLazy".into(),
                effect::Carrier::Row(row) => {
                    let row = self.expr(row, env)?;
                    if row != "undefined" {
                        out = "effFoldCompIn".into();
                        prefix.push(row);
                    }
                }
                effect::Carrier::Value => {}
            }
        }
        if info.uncurried {
            return self.uncurried_call(out, prefix, mask, args, env);
        }
        debug_assert!(prefix.is_empty(), "only an uncurried fold is passed a row");
        // Used as a value with an erased parameter still unsupplied: the
        // receiver knows only the type, so it passes the type and proof
        // arguments too. A closure over all the remaining parameters takes
        // them and ignores the erased ones (D922). The supplied arguments
        // are computed once, outside it (`$s{i}`), not on every call.
        let closure = args.len() < mask.len() && mask[args.len()..].iter().any(|erased| *erased);
        let mut bound = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            if !mask.get(i).copied().unwrap_or(false) {
                let value = self.expr(arg, env)?;
                if closure && !is_simple(&value) {
                    let _ = write!(out, "($s{i})");
                    bound.push((format!("$s{i}"), value));
                } else {
                    let _ = write!(out, "({value})");
                }
            }
        }
        if closure {
            for (i, erased) in mask.iter().enumerate().skip(args.len()) {
                if !erased {
                    let _ = write!(out, "($p{i})");
                }
            }
            for (i, erased) in mask.iter().enumerate().skip(args.len()).rev() {
                out = if *erased {
                    format!("((_) => {out})")
                } else {
                    format!("(($p{i}) => {out})")
                };
            }
            out = bind_supplied(out, bound);
        }
        Ok(out)
    }

    /// A use of `head`, a definition whose JS takes all its runtime
    /// arguments in one call (D1173), with `prefix` passed first, and then
    /// `args`, whose erasure `mask` gives up to its arity:
    ///
    /// - with all of them, one call, `f(a, b)`, and any beyond its arity
    ///   applied to the result one at a time, `f(a, b)(c)`;
    /// - with fewer, a closure that takes the rest one at a time, as any
    ///   function value does, the erased ones too if any remains (D922):
    ///   `(($p1) => f(a, $p1))`. The supplied arguments are computed once,
    ///   outside it (`$s{i}`). With none supplied but erased ones, the
    ///   closure is the same everywhere: it's made once, at its first use,
    ///   and kept in a module variable (`f$c`).
    fn uncurried_call(
        &self,
        head: String,
        prefix: Vec<String>,
        mask: &[bool],
        args: &[&Term],
        env: &mut Vec<bool>,
    ) -> Fallible<String> {
        if args.len() >= mask.len() {
            let mut values = prefix;
            for (arg, erased) in args.iter().zip(mask) {
                if !erased {
                    values.push(self.expr(arg, env)?);
                }
            }
            let mut out = format!("{head}({})", values.join(", "));
            for arg in &args[mask.len()..] {
                let _ = write!(out, "({})", self.expr(arg, env)?);
            }
            return Ok(out);
        }
        let mut bound = Vec::new();
        let mut values = Vec::new();
        for (j, value) in prefix.into_iter().enumerate() {
            if is_simple(&value) {
                values.push(value);
            } else {
                values.push(format!("$r{j}"));
                bound.push((format!("$r{j}"), value));
            }
        }
        let closed = values.is_empty() && mask[..args.len()].iter().all(|erased| *erased);
        for (i, (arg, erased)) in args.iter().zip(mask).enumerate() {
            if !erased {
                let value = self.expr(arg, env)?;
                if is_simple(&value) {
                    values.push(value);
                } else {
                    values.push(format!("$s{i}"));
                    bound.push((format!("$s{i}"), value));
                }
            }
        }
        for (i, erased) in mask.iter().enumerate().skip(args.len()) {
            if !erased {
                values.push(format!("$p{i}"));
            }
        }
        let mut out = format!("{head}({})", values.join(", "));
        for (i, erased) in mask.iter().enumerate().skip(args.len()).rev() {
            out = if *erased {
                format!("(_) => {out}")
            } else {
                format!("($p{i}) => {out}")
            };
        }
        // The common use as a value: a polymorphic function with its type
        // arguments, `List.map {A} {B}`, passed on.
        if closed && mask[args.len()..].iter().all(|erased| !erased) {
            let name = format!("{head}$c");
            let mut curried = self.curried.borrow_mut();
            if !curried.contains(&name) {
                curried.push(name.clone());
            }
            return Ok(format!("({name} ??= {out})"));
        }
        Ok(bind_supplied(format!("({out})"), bound))
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
        let info = self.info(sig.id);
        if info.convention == Convention::Thunk {
            call.push_str("()");
        }
        // An uncurried definition takes the parameters up to its arity in
        // one call (D1173); any after them are its result's.
        let mut together = Vec::new();
        let mut apart = String::new();
        for ((x, b), position) in sig.params.iter().zip(&sig.param_positions) {
            let _ = writeln!(
                out,
                "    const {} = decodeFast({}, {}, {}, \"{x}\");",
                var(*position),
                self.fast_decoder(b),
                self.type_const(b),
                arg(*position)
            );
            if info.uncurried && *position < info.mask.len() {
                together.push(var(*position));
            } else {
                let _ = write!(apart, "({})", var(*position));
            }
        }
        if info.uncurried {
            let _ = write!(call, "({})", together.join(", "));
        }
        call.push_str(&apart);
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
            "    return encodeFast({}, {}, {call});\n  }} catch (e) {{\n    throw outOfResources(\"{}\", e);\n  }}\n}}",
            self.fast_encoder(&sig.result),
            self.type_const(&sig.result),
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
    /// code it's the `Nat` or `Int` itself, since a record with one run-time
    /// field is stored as that field (D866).
    /// Decoding refuses a `bigint` or anything but a `number`, a fraction,
    /// `NaN`, an infinity and anything out of range (a whole `number` beyond
    /// 2^53 - 1 may already have been rounded, so it can't be trusted), and
    /// reads `-0` as 0. Encoding is exact, as the bounds hold of every value.
    fn safe_codecs(&self, nat: Option<DataId>, int: Option<DataId>) -> String {
        let mut out = String::from(
            "\n// A whole number a `number` holds exactly (the library's `SafeNat` and\n\
             // `SafeInt`), as a `bigint`.\n\
             const safeNumber = (x, lowest) => {\n  \
               if (typeof x === \"number\" && x >= lowest && x <= 9007199254740991 && Number.isInteger(x)) return BigInt(x);\n  \
               if (typeof x !== \"number\") refuse(\"expected a number\");\n  \
               if (!Number.isInteger(x)) refuse(\"expected a whole number\");\n  \
               if (x < lowest || x > 9007199254740991) {\n    \
                 refuse(`expected a whole number from ${lowest} to 9007199254740991`);\n  \
               }\n  \
               return BigInt(x);\n\
             };\n",
        );
        // How the decoded number is stored, and read back: as itself if the
        // record is unboxed (D866), which the library's are, or as its field.
        let field = |d: DataId, value: &str| {
            let data = self.g.data(d);
            if self.unboxed(d) == Some(0) {
                return (value.to_string(), "v".to_string());
            }
            let name = &data.ctors[0].fields[0].0;
            let k = key(self.g, d, name);
            (
                format!("({{ {}: {value} }})", ts_key(&k)),
                format!("v{}", member(&k)),
            )
        };
        if let Some(d) = nat {
            let (dec, enc) = field(d, "safeNumber(x, 0)");
            let _ = writeln!(
                out,
                "const SAFE_NAT = leaf((x) => {dec}, (v) => Number({enc}));"
            );
        }
        if let Some(d) = int {
            let (dec, enc) = field(d, "INT.dec(safeNumber(x, -9007199254740991))");
            let _ = writeln!(
                out,
                "const SAFE_INT = leaf(\n  (x) => {dec},\n  (v) => Number(INT.enc({enc})),\n);"
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
            Boundary::Map(_, key, value) if **key == Boundary::Text => {
                format!("map({})", self.type_expr(value))
            }
            Boundary::Map(_, key, value) => {
                format!("map({}, {})", self.type_expr(value), self.type_expr(key))
            }
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
            let mut entries = Vec::new();
            for ((((_, b), external), i), flag) in fields
                .iter()
                .zip(external_keys(&repr, c))
                .zip(runtime_fields(self.g, d, c))
                .zip(external_optional(&repr, c))
            {
                let internal = field_key_at(self.g, d, c, i);
                let optional = optional_property(self.g, d, c, i, b, flag);
                // A field with a default: a function of the object decoded
                // so far (its earlier fields, by their keys inside), giving
                // the default for a missing property (§5.3).
                let default = self.default_call(d, c, i, &|j| {
                    format!("o{}", member(&field_key_at(self.g, d, c, j)))
                })?;
                let rest = if let Some((reads, call)) = default {
                    let function = if reads.is_empty() {
                        format!("() => {call}")
                    } else {
                        format!("(o) => {{ {reads}return {call}; }}")
                    };
                    format!(", false, {}, {function}", js_string_literal(&internal))
                } else if internal != external {
                    format!(", {optional}, {}", js_string_literal(&internal))
                } else if optional {
                    ", true".to_string()
                } else {
                    String::new()
                };
                entries.push(format!(
                    "[{}, {}{rest}]",
                    js_string_literal(external),
                    self.type_expr(b)
                ));
            }
            let fields = entries;
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
        if repr.string_enum {
            out.push_str(", false, [], true");
        }
        if data.record {
            out.push_str(", true, [");
            for check in self.field_checks(d)? {
                let _ = write!(out, "\n  {check},");
            }
            out.push_str("\n]");
            // Stored as its one run-time field inside generated code (D866),
            // and with `js.unboxed`, at the boundary too.
            if self.unboxed(d).is_some() {
                out.push_str(", false, true");
                if repr.unboxed {
                    out.push_str(", true");
                }
            }
        }
        out.push_str(");\n");
        Ok(out)
    }

    /// The default of field `i` of constructor `c` of `d`, if it has one,
    /// as a call of its helper (docs/proposals/named-arguments.md §5.3):
    /// statements binding the earlier fields the helper takes, each read by
    /// `read` (given the field's index among all the constructor's fields),
    /// and the call. The type's parameters, and erased fields, are types and
    /// proofs, which the call leaves out.
    pub(crate) fn default_call(
        &self,
        d: DataId,
        c: usize,
        i: usize,
        read: &dyn Fn(usize) -> String,
    ) -> Fallible<Option<(String, String)>> {
        let Some(default) = field_default(self.g, d, c, i) else {
            return Ok(None);
        };
        let data = self.g.data(d);
        let ctor = &data.ctors[c];
        let np = data.params.len();
        let mut env: Vec<bool> = vec![true; np];
        env.extend(&ctor.field_erased[..i]);
        let n = env.len();
        let mut reads = String::new();
        let mut call = Term::Def(default.helper);
        for &l in &default.captures {
            if !env[l] {
                let _ = write!(reads, "const {} = {}; ", var(l), read(l - np));
            }
            let icit = if l < np {
                Icit::Implicit
            } else {
                Icit::Explicit
            };
            call = Term::app_icit(call, Term::Var(n - 1 - l), icit);
        }
        let call = self.expr(&call, &mut env)?;
        Ok(Some((reads, call)))
    }

    /// For each proof field of record `d` with a decision procedure: the
    /// message for when it doesn't hold, and a function of the decoded
    /// object saying whether it does.
    fn field_checks(&self, d: DataId) -> Fallible<Vec<String>> {
        let data = self.g.data(d);
        let ctor = &data.ctors[0];
        let np = data.params.len();
        let yes = self.decision_yes_tag();
        let unboxed = self.unboxed(d).is_some();
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
                if !erased && unboxed {
                    // The record is its one run-time field (D866).
                    let _ = write!(reads, "const {} = o; ", var(np + j));
                } else if !erased {
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
                pretty::term_ascii(self.g, &names, &field.1)
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
    ///
    /// With `inputs`, the type is an input's (an export's parameter): a data
    /// type in `inputs` is its input shape, `RangeOptionsInput`, with its
    /// defaulted fields optional (docs/proposals/named-arguments.md §5.3,
    /// D1101). Without, it's a result's, where every field is present.
    fn ts_type(&self, b: &Boundary, readonly: bool, params: &[String], inputs: Inputs) -> String {
        match b {
            Boundary::Nat | Boundary::Int => "bigint".into(),
            Boundary::SafeNat | Boundary::SafeInt | Boundary::Float => "number".into(),
            Boundary::Bool => "boolean".into(),
            Boundary::Text | Boundary::Char => "string".into(),
            Boundary::Option(..) => {
                format!(
                    "{} | undefined",
                    self.ts_type(&b.payload(), readonly, params, inputs)
                )
            }
            // A dictionary: inputs are read-only, as lists are.
            // A `js.unboxed` key is named: its alias is `string`, which an
            // index signature takes.
            Boundary::Map(_, key, value) => format!(
                "{{ {}[k: {}]: {} }}",
                if readonly { "readonly " } else { "" },
                self.ts_type(key, readonly, params, inputs),
                self.ts_type(value, readonly, params, inputs)
            ),
            Boundary::List(elem) if readonly => {
                // `readonly readonly T[][]` isn't TypeScript, and a union
                // needs its parentheses too.
                let text = self.ts_type(elem, true, params, inputs);
                if text.starts_with("readonly ") || matches!(**elem, Boundary::Option(..)) {
                    format!("readonly ({text})[]")
                } else {
                    format!("readonly {text}[]")
                }
            }
            Boundary::List(elem) if matches!(**elem, Boundary::Option(..)) => {
                format!("({})[]", self.ts_type(elem, false, params, inputs))
            }
            Boundary::List(elem) => format!("{}[]", self.ts_type(elem, false, params, inputs)),
            Boundary::Data(d, args) => {
                let mut name = type_name(&self.g.data(*d).name);
                if inputs.is_some_and(|set| set.contains(d)) {
                    name.push_str(INPUT_SUFFIX);
                }
                if args.is_empty() {
                    return name;
                }
                let args: Vec<String> = args
                    .iter()
                    .map(|a| self.ts_type(a, readonly, params, inputs))
                    .collect();
                format!("{name}<{}>", args.join(", "))
            }
            Boundary::Param(i) => params[*i].clone(),
        }
    }

    /// The declaration of data type `d`: its complete shape, which results
    /// have, or with `inputs` (when `d` is in it), its input shape
    /// `RangeOptionsInput`, which parameters have (§5.3, D1101). A field with
    /// a default is optional in the input shape: `step?: bigint`, or for an
    /// `Option`, `colour?: string | undefined`, since there `undefined` is
    /// `None` and a missing property the default (D1114). In the complete
    /// shape, a defaulted `Option` field is always present,
    /// `colour: string | undefined`. Other fields' types are input shapes
    /// too, all the way down.
    fn ts_alias(&self, d: DataId, inputs: Inputs) -> String {
        let data = self.g.data(d);
        let repr = repr(self.g, d);
        let params = self.ts_params(d);
        let mut name = type_name(&data.name);
        if inputs.is_some() {
            name.push_str(INPUT_SUFFIX);
        }
        if repr.unboxed {
            // `js.unboxed`: a plain alias of its field's type (D1066). Its
            // fields are one with a key, and proofs.
            let field = generic_field_boundaries(self.g, d)
                .into_iter()
                .flatten()
                .next()
                .expect("an unboxed record has one field with a property");
            return format!(
                "export type {name} = {};\n",
                self.ts_type(&field.1, false, &params, inputs)
            );
        }
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
                for ((((_, b), key), flag), i) in fields
                    .iter()
                    .zip(external_keys(&repr, c))
                    .zip(external_optional(&repr, c))
                    .zip(runtime_fields(self.g, d, c))
                {
                    // A record's `Option` field is an optional property, and
                    // so is a variant's with `js.optional`; in an input, so
                    // is a field with a default.
                    let (optional, b) = if optional_property(self.g, d, c, i, b, flag) {
                        ("?", b.payload())
                    } else if inputs.is_some() && field_default(self.g, d, c, i).is_some() {
                        ("?", b.clone())
                    } else {
                        ("", b.clone())
                    };
                    // Lists in a declaration are mutable, `T[]`: an app's own
                    // types say `T[]`, and `readonly T[]` isn't assignable to
                    // it (see `ts_type`).
                    parts.push(format!(
                        "readonly {}{optional}: {}",
                        ts_key(key),
                        self.ts_type(&b, false, &params, inputs)
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
            return format!("export type {name}{generics} = {};\n", variants[0]);
        }
        if repr.string_enum {
            // `js.enum`: each constructor is its string.
            let strings: Vec<String> = repr
                .ctors
                .iter()
                .map(|c| js_string_literal(&c.tag))
                .collect();
            return format!("export type {name}{generics} = {};\n", strings.join(" | "));
        }
        if variants.is_empty() {
            // A type without constructors has no values.
            return format!("export type {name}{generics} = never;\n");
        }
        format!(
            "export type {name}{generics} =\n  | {};\n",
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
            | Primitive::Pfix
            | Primitive::FoldD => true,
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
/// `Object.is` (the same double), JS's `===` is `Float.ieeeEq`; `<` is the
/// total order (`Float.compare`), JS's `<` is `Float.ieeeLt`. `native_int`
/// and `native_text` say whether an `Int` is a `bigint` and a `Text` a
/// string in generated code ([`Options`]); otherwise the conversions build
/// and read the constructors.
fn float_native_js(op: FloatPrim, native_int: bool, native_text: bool) -> String {
    let boolean = |test: &str| format!("({{ tag: {test} ? \"True\" : \"False\" }})");
    match op {
        FloatPrim::Add => "(a) => (b) => a + b".into(),
        FloatPrim::Sub => "(a) => (b) => a - b".into(),
        FloatPrim::Mul => "(a) => (b) => a * b".into(),
        FloatPrim::Div => "(a) => (b) => a / b".into(),
        FloatPrim::Rem => "(a) => (b) => a % b".into(),
        FloatPrim::Floor => "(a) => Math.floor(a)".into(),
        FloatPrim::Ceil => "(a) => Math.ceil(a)".into(),
        FloatPrim::Trunc => "(a) => Math.trunc(a)".into(),
        FloatPrim::Round => "(a) => Math.round(a)".into(),
        FloatPrim::OfNat => "(n) => Number(n)".into(),
        FloatPrim::OfInt if native_int => "(n) => Number(n)".into(),
        FloatPrim::OfInt => "(n) => Number(n.tag === \"OfNat\" ? n.n : -n.n - 1n)".into(),
        FloatPrim::ToText if native_text => "(a) => String(a)".into(),
        FloatPrim::ToText => "(a) => ({ tag: \"MkText\", chars: charsOfText(String(a)) })".into(),
        FloatPrim::Neg => "(a) => -a".into(),
        FloatPrim::Abs => "(a) => Math.abs(a)".into(),
        FloatPrim::IsNaN => format!("(a) => {}", boolean("a !== a")),
        FloatPrim::IsFinite => format!("(a) => {}", boolean("Number.isFinite(a)")),
        FloatPrim::DecEq => "(a) => (b) => ({ tag: Object.is(a, b) ? \"Yes\" : \"No\" })".into(),
        FloatPrim::IeeeEq => format!("(a) => (b) => {}", boolean("a === b")),
        FloatPrim::IeeeLt => format!("(a) => (b) => {}", boolean("a < b")),
        FloatPrim::IeeeLe => format!("(a) => (b) => {}", boolean("a <= b")),
        // `BigInt` of a whole number is exact (and `BigInt(-0)` is `0n`).
        FloatPrim::ToInt if native_int => {
            "(a) => (Number.isInteger(a) ? { tag: \"Some\", value: BigInt(a) } : { tag: \"None\" })"
                .into()
        }
        FloatPrim::ToInt => "(a) => {\n  if (!Number.isInteger(a)) return { tag: \"None\" };\n  \
             const n = BigInt(a);\n  \
             return { tag: \"Some\", value: n >= 0n ? { tag: \"OfNat\", n } : { tag: \"NegSucc\", n: -n - 1n } };\n}"
            .into(),
        // IEEE 754's totalOrder, the NaN greatest: ordered numbers by `<`;
        // otherwise equal numbers, two zeros, or a NaN.
        FloatPrim::Compare => "(a) => (b) => ({\n  tag: a < b ? \"Less\" : a > b ? \"Greater\"\n    \
             : a !== a ? (b !== b ? \"Equal\" : \"Greater\") : b !== b ? \"Less\"\n    \
             : Object.is(a, b) ? \"Equal\" : Object.is(a, -0) ? \"Less\" : \"Greater\",\n})"
            .into(),
        FloatPrim::FromBits => "fromCanonicalBits".into(),
        FloatPrim::Bits => "toCanonicalBits".into(),
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
            r#"(t) => (z) => (f) => {
  let acc = z;
  for (let i = t.length - 1; i >= 0; i--) {
    const code = scalarEndingAt(t, i);
    if (code > 0xffff) i--;
    acc = f({ tag: "MkChar", code: BigInt(code) })(acc);
  }
  return acc;
}"#
        }
        // Unicode `White_Space` (as `Char.isWhitespace`): U+0009..U+000D, U+0020,
        // U+0085, U+00A0, U+1680, U+2000..U+200A, U+2028, U+2029, U+202F,
        // U+205F, U+3000. Not JS's `trim`, which adds U+FEFF and omits U+0085.
        TextNative::TextTrim => {
            r#"(t) => {
  const space = (u) =>
    (u >= 9 && u <= 13) || u === 32 || u === 0x85 || u === 0xa0 || u === 0x1680 ||
    (u >= 0x2000 && u <= 0x200a) || u === 0x2028 || u === 0x2029 || u === 0x202f ||
    u === 0x205f || u === 0x3000;
  let start = 0;
  let end = t.length;
  while (start < end && space(t.charCodeAt(start))) start++;
  while (end > start && space(t.charCodeAt(end - 1))) end--;
  return t.slice(start, end);
}"#
        }
        // The first `n` scalar values, or the whole text: a text has at most
        // as many scalar values as code units, so a count that reaches its
        // `length` takes it all without counting, and any other count is a
        // safe integer.
        TextNative::TextTake => {
            r#"(t) => (n) => {
  if (n >= BigInt(t.length)) return t;
  const count = Number(n);
  let i = 0;
  for (let k = 0; k < count && i < t.length; k++) {
    const unit = t.charCodeAt(i);
    i += unit >= 0xd800 && unit <= 0xdbff ? 2 : 1;
  }
  return t.slice(0, i);
}"#
        }
        // The text after its first `n` scalar values, or "".
        TextNative::TextDrop => {
            r#"(t) => (n) => {
  if (n >= BigInt(t.length)) return "";
  const count = Number(n);
  let i = 0;
  for (let k = 0; k < count && i < t.length; k++) {
    const unit = t.charCodeAt(i);
    i += unit >= 0xd800 && unit <= 0xdbff ? 2 : 1;
  }
  return t.slice(i);
}"#
        }
        // In well-formed strings a match of the needle's code units starts
        // with a whole scalar value (never a low surrogate) and ends with
        // one, so it is a match of scalar values. "" occurs in every text.
        TextNative::TextContains => {
            r#"(t) => (needle) => ({ tag: t.includes(needle) ? "True" : "False" })"#
        }
        // The separator is a whole scalar value, and in a well-formed string
        // a match can't start inside a pair. Empty fields are kept, and ""
        // splits into [""], as the definition says.
        TextNative::TextSplit => "(t) => (s) => listOf(t.split(encodeChar(s)))",
        TextNative::TextJoin => {
            r#"(ts) => (s) => {
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

/// Whether variable 0 of `body` (the body of a `let`) is used at most once,
/// not inside a lambda (which may run any number of times) and not as a
/// `match`'s scrutinee (which must be a variable), so that its value can
/// be put in its place without computing it more often. Types and
/// equations, which run as `undefined` (`Gen::expr`), don't count: a
/// decision's proposition (`toBool {a = b} d`) mentions its operands;
/// nor do a definition's erased arguments, or a call that's erased.
fn single_use<'t>(codegen: &Gen, body: &'t Term) -> bool {
    let mut uses = 0;
    let mut pending: Vec<(&'t Term, usize, bool)> = vec![(body, 0, false)];
    while let Some((term, binders, in_lambda)) = pending.pop() {
        let mut visit = |child: &'t Term, under: usize, lambda: bool| {
            pending.push((child, binders + under, in_lambda || lambda));
        };
        match term {
            Term::Var(ix) if *ix == binders => {
                uses += 1;
                if in_lambda || uses > 1 {
                    return false;
                }
            }
            Term::Case(ix, ..) | Term::NumCase(ix, ..) if *ix == binders => return false,
            Term::Data(..)
            | Term::Sort(_)
            | Term::Pi(..)
            | Term::Eq(..)
            | Term::Refl
            | Term::Quot(QuotForm::Type, ..) => {}
            Term::J(_, base, _) => visit(base, 0, false),
            Term::Let(_, _, value, body, _) => {
                visit(value, 0, false);
                visit(body, 1, false);
            }
            Term::Ann(inner, _) => visit(inner, 0, false),
            Term::Lam(_, _, inner) => visit(inner, 1, true),
            Term::App(..) => {
                let (head, args) = term.spine();
                let info = match head {
                    Term::Def(id) => codegen.try_info(*id).ok(),
                    _ => None,
                };
                match info {
                    Some(info) if info.result_erased => {}
                    _ => {
                        visit(head, 0, false);
                        for (i, arg) in args.into_iter().enumerate() {
                            if !info.is_some_and(|info| info.mask.get(i) == Some(&true)) {
                                visit(arg, 0, false);
                            }
                        }
                    }
                }
            }
            _ => term.for_each_child(|child, under| visit(child, under, false)),
        }
    }
    true
}

/// Whether variable 0 of `body` is a `match`'s scrutinee.
fn scrutinised(body: &Term) -> bool {
    body.subterms().any(|(term, binders)| {
        matches!(term, Term::Case(ix, ..) | Term::NumCase(ix, ..) if *ix == binders)
    })
}

fn var(level: usize) -> String {
    format!("v{level}")
}

/// How many of a definition's parameters, by erasure `mask`, are passed at
/// run time.
fn runtime_params(mask: &[bool]) -> usize {
    mask.iter().filter(|erased| !**erased).count()
}

/// Whether the JS of an argument is a variable or a number literal, which
/// costs nothing to compute again, so a closure can mention it rather than
/// a copy computed outside.
fn is_simple(value: &str) -> bool {
    let value = value.strip_suffix('n').unwrap_or(value);
    let value = value.strip_prefix('v').unwrap_or(value);
    !value.is_empty() && value.chars().all(|c| c.is_ascii_digit())
}

/// `out`, a closure, with the names `bound` bound to their values, which
/// are computed once, before it's made: `(($s0) => out)(value)`.
fn bind_supplied<N: std::fmt::Display>(out: String, bound: Vec<(N, String)>) -> String {
    if bound.is_empty() {
        return out;
    }
    let (names, values): (Vec<String>, Vec<String>) = bound
        .into_iter()
        .map(|(name, value)| (name.to_string(), value))
        .unzip();
    format!("(({}) => {out})({})", names.join(", "), values.join(", "))
}

/// A native's JS that takes `k` arguments one at a time, `(a) => (b) =>
/// body`, as one function of all of them, `(a, b) => body` (D1173), if it
/// starts with `k` such parameters.
fn uncurry_arrows(js: &str, k: usize) -> Option<String> {
    let mut rest = js;
    let mut params = Vec::new();
    for _ in 0..k {
        let inner = rest.strip_prefix('(')?;
        let close = inner.find(')')?;
        let param = &inner[..close];
        if !is_js_identifier(param) {
            return None;
        }
        rest = inner[close + 1..].strip_prefix(" => ")?;
        params.push(param);
    }
    Some(format!("({}) => {rest}", params.join(", ")))
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

/// The indices, among all of constructor `c`'s fields, of those that have a
/// key (not erased), in order: alongside [`external_keys`].
fn runtime_fields(g: &Globals, d: DataId, c: usize) -> Vec<usize> {
    let ctor = &g.data(d).ctors[c];
    (0..ctor.fields.len())
        .filter(|&i| !ctor.field_erased[i])
        .collect()
}

/// The default of field `i` of constructor `c` of `d`, if it has one
/// (docs/proposals/named-arguments.md §5.1).
fn field_default(g: &Globals, d: DataId, c: usize, i: usize) -> Option<&FieldDefault> {
    g.data(d).defaults.as_ref()?.get(c)?.get(i)?.as_ref()
}

/// Whether field `i` of constructor `c` of `d`, whose boundary type is `b`,
/// is an optional property, where a missing property and `undefined` are
/// both `None`, and `None` is no property (D582): a record's `Option` field,
/// or a variant's with `js.optional` (`flag`). A field with a default never
/// is: a missing property is its default, and a defaulted `Option` field is
/// always present on output, `None` as `undefined` (D1114).
fn optional_property(g: &Globals, d: DataId, c: usize, i: usize, b: &Boundary, flag: bool) -> bool {
    field_default(g, d, c, i).is_none()
        && (flag || (g.data(d).record && matches!(b, Boundary::Option(..))))
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
        // Its one field is a quotient, `Quot.mk` of a raw map whose field 0
        // is the tree (std/Map/Map.sw).
        (Boundary::Map(_, key, element), Value::Ctor(_, 0, fields)) => {
            let Some(Value::Ctor(_, 0, raw)) = quot_mk_rep(&fields[0]) else {
                return Err(stuck());
            };
            let mut entries = Vec::new();
            map_entries(g, key, element, raw[0].clone(), &mut entries)?;
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
            if repr.string_enum {
                return Ok(js_string_literal(&repr.ctors[*c].tag));
            }
            let boundaries = &field_boundaries(g, *d, args)[*c];
            if repr.unboxed {
                // `js.unboxed`: its one field with a property, as itself.
                let (field, (_, b)) = fields
                    .iter()
                    .zip(&ctor.field_erased)
                    .filter(|(_, erased)| !**erased)
                    .map(|(field, _)| field)
                    .zip(boundaries)
                    .next()
                    .ok_or_else(stuck)?;
                return boundary_literal(g, b, field);
            }
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
            for (((((_, b), field), key), flag), i) in boundaries
                .iter()
                .zip(runtime)
                .zip(external_keys(&repr, *c))
                .zip(external_optional(&repr, *c))
                .zip(runtime_fields(g, *d, *c))
            {
                let literal = boundary_literal(g, b, field)?;
                // `None` in an optional property is no property.
                if optional_property(g, *d, *c, i, b, flag) && literal == "undefined" {
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
    key_type: &Boundary,
    element: &Boundary,
    tree: Value,
    out: &mut Vec<String>,
) -> Result<(), String> {
    match expand_step(g, tree) {
        Value::Ctor(_, 0, _) => Ok(()),
        // `Bin size left key value right`
        Value::Ctor(_, 1, parts) => {
            map_entries(g, key_type, element, parts[1].clone(), out)?;
            let key = boundary_literal(g, key_type, &parts[2])?;
            let value = boundary_literal(g, element, &parts[3])?;
            out.push(format!("[{key}, {value}]"));
            map_entries(g, key_type, element, parts[4].clone(), out)
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
fn dependency_order(codegen: &Gen, ids: &[DefId]) -> Vec<DefId> {
    let wanted: HashSet<DefId> = ids.iter().copied().collect();
    let mut state: HashMap<DefId, bool> = HashMap::default(); // false: open, true: done
    let mut out = Vec::with_capacity(ids.len());
    for &root in ids {
        if state.contains_key(&root) {
            continue;
        }
        state.insert(root, false);
        // (definition, the definitions it refers to, how many are handled)
        let mut stack = vec![(root, refs(codegen, root, &wanted), 0)];
        while let Some((id, deps, next)) = stack.last_mut() {
            if let Some(&dep) = deps.get(*next) {
                *next += 1;
                if let std::collections::hash_map::Entry::Vacant(e) = state.entry(dep) {
                    e.insert(false);
                    stack.push((dep, refs(codegen, dep, &wanted), 0));
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

/// The wanted definitions `id`'s body refers to, in order, then those its
/// empty-row variant's body does, if it's used.
fn refs(codegen: &Gen, id: DefId, wanted: &HashSet<DefId>) -> Vec<DefId> {
    let variant = codegen.empty.borrow()[id.0]
        .then(|| codegen.spec.empty_body(id).ok().flatten())
        .flatten();
    let mut found: Vec<DefId> = codegen
        .g
        .def(id)
        .run_body()
        .into_iter()
        .chain(variant.as_ref())
        .flat_map(|b| b.subterms())
        .filter_map(|(t, _)| match t {
            Term::Def(d) if wanted.contains(d) && *d != id => Some(*d),
            _ => None,
        })
        .collect();
    let mut seen = HashSet::default();
    found.retain(|d| seen.insert(*d));
    found
}
#[cfg(test)]
mod tests {
    use stitchwort_core::collections::HashMap;

    use super::{
        IntNative, RUNTIME, TextNative, def_name, encode, info_name, int_native_js,
        is_js_identifier, is_simple, mentions, native, native_js, text_native_js, uncurry_arrows,
        wrapper_name,
    };

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
        let mut seen: HashMap<String, String> = HashMap::default();
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

    #[test]
    fn uncurries_natives() {
        assert_eq!(
            uncurry_arrows("(m) => (n) => m + n", 2).as_deref(),
            Some("(m, n) => m + n")
        );
        assert_eq!(
            uncurry_arrows("(f) => (z) => (t) => {\n  return z;\n}", 3).as_deref(),
            Some("(f, z, t) => {\n  return z;\n}")
        );
        // Fewer arrows than parameters, or not an arrow at all.
        assert_eq!(uncurry_arrows("(a) => -a", 2), None);
        assert_eq!(uncurry_arrows("charsOfText", 2), None);
        assert_eq!(uncurry_arrows("(a) => (a < 0n ? -a : a)", 2), None);
        // Every native with two or more runtime parameters uncurries.
        for js in [
            native_js(native::Native::Add),
            native_js(native::Native::DivFuel),
            int_native_js(IntNative::IntDiv),
            text_native_js(TextNative::TextFold),
            text_native_js(TextNative::TextJoin),
        ] {
            let arrows = js.matches(") => (").count() + 1;
            assert!(uncurry_arrows(js, arrows).is_some(), "{js}");
        }
    }

    #[test]
    fn simple_arguments() {
        for simple in ["v0", "v12", "3n", "0"] {
            assert!(is_simple(simple), "{simple}");
        }
        for not in ["", "v", "f(v0)", "undefined", "{ tag: \"Nil\" }"] {
            assert!(!is_simple(not), "{not}");
        }
    }
}
