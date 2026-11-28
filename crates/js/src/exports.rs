use super::*;

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
    /// The library's `Array T` (std/Array/Array.sw), as a list is: a version
    /// array inside generated code ([`VERSION_ARRAYS`]), whose elements are
    /// copied in and out.
    Array(Box<Boundary>),
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
            Boundary::Array(elem) => Boundary::Array(Box::new(elem.instantiate(args))),
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
    pub(crate) fn has_map(&self) -> bool {
        match self {
            Boundary::Map(..) => true,
            Boundary::List(elem) | Boundary::Array(elem) | Boundary::Option(_, elem) => {
                elem.has_map()
            }
            Boundary::Data(_, args) => args.iter().any(Boundary::has_map),
            _ => false,
        }
    }

    /// Whether `leaf` is this type or inside it (not counting the fields of
    /// a data type).
    pub(crate) fn mentions(&self, leaf: &Boundary) -> bool {
        self == leaf
            || match self {
                Boundary::List(elem) | Boundary::Array(elem) | Boundary::Option(_, elem) => {
                    elem.mentions(leaf)
                }
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

/// What a [`Gen::forwarder`] does at run time: the position of the
/// parameter it applies, and of the parameters it applies it to.
pub(crate) type Forward = (usize, Vec<usize>);

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
pub fn exportable(g: &View<'_>, id: DefId) -> Result<ExportSig, Diagnostic> {
    let def = g.def(id);
    let refuse = |why: String| {
        Diagnostic::error("E-EXPORT", format!("`{}` can't be exported", def.name()))
            .with_label(def.span(), why)
    };
    // An export is imported in JS by its short name: `Geometry.area` as
    // `area` (docs/proposals/namespaces.md §7.3).
    let export_name = short_name(def.name());
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
    let tel = def_telescope(g, id)?;
    // A partial function, or one taking or returning one: generated code
    // has no way to run a `Delay` (docs/proposals/partial.md §7.6, §10.6).
    // The telescope's own view sees one written behind an opaque nickname
    // the definition unfolds.
    if let Some(delay) = g.env.builtins().primitive_id(Primitive::Delay) {
        // Parameter `i`'s type is read under the `i` before it, the result's
        // under them all.
        let types = tel.params.iter().map(|(_, ty, _)| ty).chain([&tel.result]);
        for (depth, ty) in types.enumerate() {
            // A declaration's own parameter and result types: small.
            #[allow(clippy::disallowed_methods)]
            let read = quote(g, depth, ty)?;
            if read
                .subterms()
                .any(|(t, _)| matches!(t, Term::Def(d) if *d == delay))
            {
                return Err(Diagnostic::error(
                    "E-JS-PARTIAL",
                    format!("`{}` can't be exported", def.name()),
                )
                .with_label(def.span(), "its type mentions `Partial`")
                .with_note("partial functions can't be exported to JavaScript yet: only the runtime (`stitchwort run`, the playground) runs them")
                .with_note("export the total parts instead: the functions a partial loop calls"));
            }
        }
    }
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
            let Some(validator) = def.validators().iter().find(|v| v.param == i) else {
                return Err(refuse(format!(
                    "proof parameter `{x}` has no runtime check"
                )));
            };
            // Describe the precondition as written in the signature.
            let names: Vec<_> = tel.params[..i].iter().map(|(n, _, _)| n.clone()).collect();
            let description = written_param_type(def.ty(), i).map_or_else(
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
            .map_err(|why| why.refuse(|why| refuse(format!("parameter `{js_name}`: {why}"))))?;
        params.push((js_name, boundary));
        param_positions.push(i);
    }
    let result = boundary(g, &tel.result, 0, &mut HashSet::default())
        .map_err(|why| why.refuse(|why| refuse(format!("its result: {why}"))))?;
    Ok(ExportSig {
        id,
        name: export_name.to_string(),
        params,
        param_positions,
        checks,
        result,
    })
}

/// Why a type doesn't cross the boundary: it can't (why, said of the type),
/// or reading it ran out of resources, which says nothing about the type.
#[derive(Debug)]
pub(crate) enum Refusal {
    Cannot(String),
    Resource(Diagnostic),
}

impl From<String> for Refusal {
    fn from(why: String) -> Refusal {
        Refusal::Cannot(why)
    }
}

impl From<ResourceError> for Refusal {
    fn from(e: ResourceError) -> Refusal {
        Refusal::Resource(Diagnostic::from(e))
    }
}

impl Refusal {
    /// The error to report: `refuse(why)` for a type that can't cross, the
    /// resource error as it is.
    pub(crate) fn refuse(self, refuse: impl FnOnce(String) -> Diagnostic) -> Diagnostic {
        match self {
            Refusal::Cannot(why) => refuse(why),
            Refusal::Resource(d) => d,
        }
    }

    /// The reason in context: `within(why)` for one that can't cross.
    pub(crate) fn within(self, within: impl FnOnce(String) -> String) -> Refusal {
        match self {
            Refusal::Cannot(why) => Refusal::Cannot(within(why)),
            resource => resource,
        }
    }
}

/// How `ty` crosses the boundary. In a data type's fields' types, its first
/// `params` variables are the type's parameters.
pub(crate) fn boundary(
    g: &View<'_>,
    ty: &Value,
    params: usize,
    visiting: &mut HashSet<DataId>,
) -> Result<Boundary, Refusal> {
    let cannot = |ty: &Value| {
        format!(
            "`{}` can't cross the JS boundary yet",
            pretty::value(g, &[], ty)
        )
    };
    // A definition's parameters are read glued (`def_telescope`): a type
    // written as a synonym (`Row` for `Vec Bool 5`) is a call until forced.
    let ty = &force(g, ty.clone())?;
    match ty {
        Value::Neutral(Head::Var(level, _, _), elims) if elims.is_empty() && *level < params => {
            Ok(Boundary::Param(*level))
        }
        Value::Data(d, args) => {
            let data = g.data(*d);
            // The built-in types with a boundary form of their own, chosen by
            // identity from the registry's one list (D613): a program's own
            // `List` is encoded as the data type it is. Where the codec
            // depends on the declaration, its content hash confirms it;
            // otherwise the type crosses as the data type it is.
            let builtin = g.env.registry().boundary_form(*d);
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
                    // An argument is read glued too: `Map Name V` with
                    // `def Name: Type := Text`.
                    let key = match &force(g, key.clone())? {
                        Value::Data(t, a) if a.is_empty() && text_data(g) == Some(*t) => {
                            if !is_text_order(g, order) {
                                return Err(Refusal::Cannot(format!(
                                    "`{}` can't cross the JS boundary: a map crosses only in \
                                     `Text`'s own order (`Text.instOrd`), which its keys are \
                                     sorted by",
                                    pretty::value(g, &[], ty)
                                )));
                            }
                            Boundary::Text
                        }
                        Value::Data(k, a) if a.is_empty() && unboxed_over_text(g, *k) => {
                            if !is_derived_order(g, *k, order) {
                                let key_name = g.data(*k).name();
                                return Err(Refusal::Cannot(format!(
                                    "`{}` can't cross the JS boundary: a map from `{key_name}` \
                                     crosses only in `{key_name}`'s derived order, which is \
                                     `Text`'s, and this map has another",
                                    pretty::value(g, &[], ty)
                                )));
                            }
                            check_codec(g, *k, visiting)?;
                            Boundary::Data(*k, Vec::new())
                        }
                        _ => {
                            return Err(Refusal::Cannot(format!(
                                "`{}` can't cross the JS boundary: only maps from `Text`, or from \
                                 a `js.unboxed` record over `Text`, cross, as plain objects",
                                pretty::value(g, &[], ty)
                            )));
                        }
                    };
                    let value = boundary(g, value, params, visiting)?;
                    Ok(Boundary::Map(*d, Box::new(key), Box::new(value)))
                }
                (Some(Builtin::List), [elem]) => Ok(Boundary::List(Box::new(boundary(
                    g, elem, params, visiting,
                )?))),
                // The library's `Array`, which is a version array inside
                // generated code whenever it's loaded (the generator refuses a
                // program whose arrays don't bind).
                (_, [elem]) if g.env.registry().is_data(Builtin::Array, *d) => Ok(Boundary::Array(
                    Box::new(boundary(g, elem, params, visiting)?),
                )),
                (Some(Builtin::Option), [elem]) => {
                    let inner = boundary(g, elem, params, visiting)?;
                    check_codec(g, *d, visiting)?;
                    Ok(Boundary::Option(*d, Box::new(inner)))
                }
                // Decoding would have to check the indices (a `Vec a n`'s
                // length, a `Grid`'s rows): refused wherever it appears in the
                // serialized form (docs/proposals/indexed-families.md §6.8, D147).
                _ if !data.indices().is_empty() => Err(Refusal::Cannot(format!(
                    "`{}` is an indexed family, which can't cross the JS boundary yet: \
                     decoding would have to check its indices",
                    data.name()
                ))),
                _ if data.sort() != Sort::Prop => {
                    let args = args
                        .iter()
                        .map(|arg| boundary(g, arg, params, visiting))
                        .collect::<Result<Vec<_>, _>>()?;
                    check_codec(g, *d, visiting)?;
                    Ok(Boundary::Data(*d, args))
                }
                _ => Err(Refusal::Cannot(cannot(ty))),
            }
        }
        Value::Pi(..) => Err(Refusal::Cannot(
            "functions can't cross the JS boundary yet".into(),
        )),
        other => Err(Refusal::Cannot(cannot(other))),
    }
}

/// Whether `order` is the library's `Text.instOrd`, the ordering a map that
/// crosses as an object is sorted by.
pub(crate) fn is_text_order(g: &View<'_>, order: &Value) -> bool {
    let Some(text_order) = g.env.registry().loaded_def(Builtin::TextInstOrd) else {
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
pub(crate) fn unboxed_over_text(g: &View<'_>, d: DataId) -> bool {
    let data = g.data(d);
    if !g.js(d).is_some_and(|r| r.unboxed) {
        return false;
    }
    let Some(i) = data.unboxed_field() else {
        return false;
    };
    let mut env: Vec<Value> = (0..data.params().len()).map(Value::var).collect();
    env.extend((0..i).map(|j| Value::var(data.params().len() + j)));
    matches!(
        eval(g, &env, &data.ctors()[0].fields[i].1).expect(OUTSIDE_LIMITS),
        Value::Data(t, a) if a.is_empty() && text_data(g) == Some(t)
    )
}

/// Whether `order` is record `d`'s derived `Ord` instance, `d.%instOrd`
/// (derive_ord.rs; no program can write a name with `%`). For a record over
/// `Text` it compares the field by `Text.instOrd`, so it sorts keys as a
/// `Map Text V` does.
pub(crate) fn is_derived_order(g: &View<'_>, d: DataId, order: &Value) -> bool {
    let id = match order {
        Value::Call(id, spine, _) if spine.is_empty() => *id,
        Value::Neutral(Head::Def(id), spine) if spine.is_empty() => *id,
        _ => return false,
    };
    **g.def(id).name() == *format!("{}.%instOrd", g.data(d).name())
}

/// Whether a data type can have a codec: its parameters are types, and its
/// fields all cross the boundary, whatever data the parameters stand for.
/// A type with parameters is described once, and its fields' types are
/// filled in with its arguments as a value is decoded or encoded.
fn check_codec(g: &View<'_>, d: DataId, visiting: &mut HashSet<DataId>) -> Result<(), Refusal> {
    if !visiting.insert(d) {
        return Ok(());
    }
    let data = g.data(d);
    if MODULE_NAMES.contains(&short_name(data.name())) {
        return Err(Refusal::Cannot(format!(
            "`{}` is the name of something else the generated module exports",
            data.name()
        )));
    }
    let mut env = Vec::new();
    for (x, ty) in data.params() {
        if !matches!(
            eval(g, &env, ty).expect(OUTSIDE_LIMITS),
            Value::Sort(Sort::Type(_))
        ) {
            return Err(Refusal::Cannot(format!(
                "`{}`'s parameter `{x}` isn't a type, which can't cross the JS boundary yet",
                data.name()
            )));
        }
        env.push(Value::var(env.len()));
    }
    // (That each field has its own key at the boundary is checked with the
    // rest of the type's names, in `check_names`.)
    for (c, (ctor, fields)) in data.ctors().iter().zip(data_fields(g, d)).enumerate() {
        for (i, (field, _)) in ctor.fields.iter().enumerate() {
            if !ctor.field_erased[i] {
                continue;
            }
            // A record's proof field is established by its decision procedure
            // (docs/proposals/records.md §11.3).
            let proof = ctor.field_sorts[i] == Sort::Prop;
            let checked = data.record()
                && proof
                && data
                    .validators()
                    .iter()
                    .any(|v| v.ctor == c && v.field == i);
            if !checked {
                return Err(Refusal::Cannot(if data.record() && proof {
                    format!(
                        "`{}`'s proof field `{field}` has no runtime check",
                        data.name()
                    )
                } else if data.record() {
                    format!(
                        "`{}`'s field `{field}` is a type, which can't cross the JS boundary",
                        data.name()
                    )
                } else {
                    format!(
                        "`{}` has a proof or type field, which can't be checked at the boundary yet",
                        data.name()
                    )
                }));
            }
        }
        for (field, field_ty) in fields {
            let b = boundary(g, &field_ty, data.params().len(), visiting).map_err(|why| {
                why.within(|why| format!("`{}`'s field `{field}`: {why}", data.name()))
            })?;
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
fn unboxed_field_crosses(g: &View<'_>, d: DataId, field: &str, b: &Boundary) -> Result<(), String> {
    let name = g.data(d).name();
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
pub(crate) fn data_fields(g: &View<'_>, d: DataId) -> Vec<Vec<(String, Value)>> {
    let data = g.data(d);
    data.ctors()
        .iter()
        .map(|ctor| {
            let mut env: Vec<Value> = (0..data.params().len()).map(Value::var).collect();
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
pub fn field_boundaries(
    g: &View<'_>,
    d: DataId,
    args: &[Boundary],
) -> Result<Vec<Vec<(String, Boundary)>>, Diagnostic> {
    Ok(export_field_boundaries(g, d)?
        .into_iter()
        .map(|fields| {
            fields
                .into_iter()
                .map(|(name, b)| (name, b.instantiate(args)))
                .collect()
        })
        .collect())
}

/// [`generic_field_boundaries`] for a caller that reports a [`Diagnostic`]: a
/// type that can't cross is E-EXPORT, a resource refusal is itself.
pub(crate) fn export_field_boundaries(
    g: &View<'_>,
    d: DataId,
) -> Result<Vec<Vec<(String, Boundary)>>, Diagnostic> {
    let data = g.data(d);
    generic_field_boundaries(g, d).map_err(|why| {
        why.refuse(|why| {
            Diagnostic::error("E-EXPORT", format!("`{}` can't be exported", data.name()))
                .with_label(data.span(), why)
        })
    })
}

/// [`field_boundaries`] with the parameters left as [`Boundary::Param`].
pub(crate) fn generic_field_boundaries(
    g: &View<'_>,
    d: DataId,
) -> Result<Vec<Vec<(String, Boundary)>>, Refusal> {
    let params = g.data(d).params().len();
    data_fields(g, d)
        .into_iter()
        .map(|fields| {
            fields
                .into_iter()
                .map(|(name, ty)| {
                    let b = boundary(g, &ty, params, &mut HashSet::default()).map_err(|why| {
                        why.within(|why| format!("`{}`'s field `{name}`: {why}", g.data(d).name()))
                    })?;
                    Ok((name, b))
                })
                .collect::<Result<Vec<_>, Refusal>>()
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
pub(crate) fn check_names(g: &View<'_>, exports: &[ExportSig]) -> Result<Vec<DataId>, Diagnostic> {
    let mut short_exports: HashMap<&str, DefId> = HashMap::default();
    for sig in exports {
        if let Some(other) = short_exports.insert(&sig.name, sig.id) {
            return Err(Diagnostic::error(
                "E-EXPORT",
                format!(
                    "`{}` and `{}` would both be exported as `{}`",
                    g.def(other).name(),
                    g.def(sig.id).name(),
                    sig.name
                ),
            )
            .with_label(g.def(sig.id).span(), "exported here")
            .with_label(g.def(other).span(), "and here")
            .with_note("export only one of them, or rename one"));
        }
    }
    let mut boundary_datas = Vec::new();
    for sig in exports {
        for b in sig.params.iter().map(|(_, b)| b).chain([&sig.result]) {
            collect_datas(g, b, &mut boundary_datas)?;
        }
    }
    // Each type's names at the boundary (docs/proposals/attributes.md §4.6):
    // a type with `js.*` attributes had its checked where it's declared; one
    // without is checked here, once an export reaches it (D612), so a type
    // that never crosses may have a field `__proto__`.
    for &d in &boundary_datas {
        let data = g.data(d);
        if g.js(d).is_some() {
            continue;
        }
        let repr = repr(g, d);
        if let Some(clash) = js_repr::clashes(&repr, data.record()).first() {
            let mut diagnostic = Diagnostic::error("E-JS-NAME-CLASH", clash.message(data, &repr))
                .with_label(data.span(), "this type crosses the JS boundary");
            let mut reaching = None;
            for sig in exports {
                let mut datas = Vec::new();
                for b in sig.params.iter().map(|(_, b)| b).chain([&sig.result]) {
                    collect_datas(g, b, &mut datas)?;
                }
                if datas.contains(&d) {
                    reaching = Some(sig);
                    break;
                }
            }
            if let Some(sig) = reaching {
                diagnostic = diagnostic.with_label(
                    g.def(sig.id).span(),
                    format!("`{}` is exported, and reaches it", g.def(sig.id).name()),
                );
            }
            return Err(diagnostic.with_note(clash.note(&repr)));
        }
    }
    let mut short_types: HashMap<String, DataId> = HashMap::default();
    for &d in &boundary_datas {
        if let Some(other) = short_types.insert(type_name(g.data(d).name()), d) {
            return Err(Diagnostic::error(
                "E-EXPORT",
                format!(
                    "`{}` and `{}` would both be called `{}` in the TypeScript declarations",
                    g.data(other).name(),
                    g.data(d).name(),
                    type_name(g.data(d).name())
                ),
            )
            .with_label(g.data(d).span(), "this type crosses the JS boundary")
            .with_label(g.data(other).span(), "and so does this one")
            .with_note("rename one of them"));
        }
    }
    Ok(boundary_datas)
}

/// Checks that the exports loaded so far can be named in JS and TypeScript
/// together: [`exportable`] checks each on its own.
pub fn exports_fit_together(g: &View<'_>) -> Result<(), Diagnostic> {
    exports_fit_together_among(g, (0..g.env.defs().len()).map(DefId))
}

/// [`exports_fit_together`] for the exports among `ids` only: one
/// namespace's.
pub fn exports_fit_together_among(
    g: &View<'_>,
    ids: impl Iterator<Item = DefId>,
) -> Result<(), Diagnostic> {
    let exports = ids
        .filter(|id| g.def(*id).export())
        .map(|id| exportable(g, id))
        .collect::<Result<Vec<_>, _>>()?;
    let boundary_datas = check_names(g, &exports)?;
    input_datas(g, &boundary_datas).map(|_| ())
}

/// Whether `b` has the prelude's `Option` as a tagged data type in it: a
/// nested one (not counting the fields of data types).
pub(crate) fn names_option(g: &View<'_>, b: &Boundary) -> bool {
    match b {
        Boundary::List(elem) | Boundary::Array(elem) | Boundary::Map(_, _, elem) => {
            names_option(g, elem)
        }
        Boundary::Option(..) => names_option(g, &b.payload()),
        Boundary::Data(d, args) => {
            g.env.registry().is_data(Builtin::Option, *d) || args.iter().any(|a| names_option(g, a))
        }
        _ => false,
    }
}

/// Which data types have an input shape in the TypeScript declarations, as
/// a set: given to [`Gen::ts_type`] for an export's parameters, `None` for
/// its result.
pub(crate) type Inputs<'a> = Option<&'a HashSet<DataId>>;

/// What an input shape's name adds to the type's: `RangeOptionsInput`.
pub(crate) const INPUT_SUFFIX: &str = "Input";

/// The data types at the boundary that need an input shape
/// (docs/proposals/named-arguments.md §5.3, D1101): those with a field with
/// a default, which an input may leave out, and, all the way down, those
/// whose fields' types mention one (`JobInput`, with
/// `options: RangeOptionsInput`). A type parameter isn't a reason: a
/// generic type's input is written with input arguments, `Box<RangeOptionsInput>`.
/// A `js.unboxed` record is its one field at the boundary, so its own
/// default never applies there. Each input shape's name must be free among
/// the boundary's types.
pub(crate) fn input_datas(
    g: &View<'_>,
    boundary_datas: &[DataId],
) -> Result<HashSet<DataId>, Diagnostic> {
    let own_default = |d: DataId| {
        let data = g.data(d);
        !repr(g, d).unboxed
            && data.ctors().iter().enumerate().any(|(c, ctor)| {
                (0..ctor.fields.len())
                    .any(|i| !ctor.field_erased[i] && field_default(g, d, c, i).is_some())
            })
    };
    let mut inputs: HashSet<DataId> = boundary_datas
        .iter()
        .copied()
        .filter(|d| own_default(*d))
        .collect();
    pub(crate) fn mentions(b: &Boundary, inputs: &HashSet<DataId>) -> bool {
        match b {
            Boundary::List(elem) | Boundary::Array(elem) | Boundary::Option(_, elem) => {
                mentions(elem, inputs)
            }
            Boundary::Map(_, key, value) => mentions(key, inputs) || mentions(value, inputs),
            Boundary::Data(d, args) => {
                inputs.contains(d) || args.iter().any(|a| mentions(a, inputs))
            }
            _ => false,
        }
    }
    loop {
        let mut more = Vec::new();
        for &d in boundary_datas.iter().filter(|d| !inputs.contains(d)) {
            let fields = export_field_boundaries(g, d)?;
            if fields.iter().flatten().any(|(_, b)| mentions(b, &inputs)) {
                more.push(d);
            }
        }
        if more.is_empty() {
            break;
        }
        inputs.extend(more);
    }
    for &d in boundary_datas.iter().filter(|d| inputs.contains(d)) {
        let input = format!("{}{INPUT_SUFFIX}", type_name(g.data(d).name()));
        if let Some(&other) = boundary_datas
            .iter()
            .find(|e| type_name(g.data(**e).name()) == input)
        {
            return Err(Diagnostic::error(
                "E-EXPORT",
                format!(
                    "`{}`'s input shape and `{}` would both be called `{input}` in the \
                     TypeScript declarations",
                    g.data(d).name(),
                    g.data(other).name()
                ),
            )
            .with_label(g.data(d).span(), format!("its input shape is `{input}`"))
            .with_label(
                g.data(other).span(),
                "and this type crosses the JS boundary too",
            )
            .with_note(format!(
                "a parameter's `{}` may leave out fields with defaults, in it or inside it, \
                 so its type is `{input}`; rename one of the types",
                type_name(g.data(d).name())
            )));
        }
    }
    Ok(inputs)
}

pub(crate) fn collect_datas(
    g: &View<'_>,
    b: &Boundary,
    out: &mut Vec<DataId>,
) -> Result<(), Diagnostic> {
    pub(crate) fn fields(g: &View<'_>, d: DataId, out: &mut Vec<DataId>) -> Result<(), Diagnostic> {
        for fields in export_field_boundaries(g, d)? {
            for (_, b) in fields {
                collect_datas(g, &b, out)?;
            }
        }
        Ok(())
    }
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
        Boundary::List(elem) | Boundary::Array(elem) => collect_datas(g, elem, out)?,
        Boundary::Map(_, key, elem) => {
            collect_datas(g, key, out)?;
            collect_datas(g, elem, out)?;
        }
        Boundary::Option(d, _) => {
            // The runtime needs `Option`'s description (for the tags of a
            // nested one) whenever an `Option` crosses.
            if !out.contains(d) {
                out.push(*d);
                fields(g, *d, out)?;
            }
            collect_datas(g, &b.payload(), out)?;
        }
        Boundary::Data(d, args) => {
            for arg in args {
                collect_datas(g, arg, out)?;
            }
            if out.contains(d) {
                return Ok(());
            }
            out.push(*d);
            fields(g, *d, out)?;
        }
    }
    Ok(())
}
