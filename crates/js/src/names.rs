use super::*;

/// Where a loop keeps parameter `level`'s value for its next turn.
pub(crate) fn slot(level: usize) -> String {
    format!("s{level}")
}

/// The declaration of an open goal's assumption that stands for data (a
/// `?` the program computes with): it throws an `Error` named
/// `Unreachable`, with the goal's assumption's name as `at` (`half.?1`),
/// when the run reaches it: it's a function whether or not the goal is (one
/// with no runtime parameters is a [`Convention::Thunk`]), so it throws
/// when it's called, never when the module loads.
pub(crate) fn goal_stopper(g: &View<'_>, id: DefId) -> String {
    let def = g.def(id);
    let path = def.path();
    let at = js_string_literal(path);
    let message = match stitchwort_rt::host::goal_of(path) {
        Some((owner, hole)) => js_string_literal(&format!(
            "the program reached open goal {hole} of `{owner}` (a `?`), which has no value to run"
        )),
        None => at.clone(),
    };
    let throw = format!(
        "throw Object.assign(new Error({message}), {{ name: \"Unreachable\", at: {at} }});"
    );
    format!("const {} = () => {{ {throw} }};\n", def_name(path))
}

/// A definition's JS name, from its full logical name (`Std.List.length`):
/// `$` and the name, [`encode`]d. A name starts with a letter or `_`, so a
/// definition's JS name is never `$$…`, which is an export's wrapper's.
pub(crate) fn def_name(path: &str) -> String {
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
pub(crate) fn short_name(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

/// How data type `d` crosses the boundary (docs/proposals/attributes.md
/// §4.6): what its `js.*` attributes resolved to where it was declared, or
/// for a type without any, the default names, whose clashes `check_names`
/// reports before any code is generated. The codec tables
/// ([`Gen::define`]), the declarations ([`Gen::ts_alias`]) and
/// [`boundary_literal`] all read this, never names of their own.
pub(crate) fn repr(g: &View<'_>, d: DataId) -> Rc<JsRepr> {
    let data = g.data(d);
    g.js(d)
        .cloned()
        .unwrap_or_else(|| Rc::new(js_repr::names(data, &js_repr::Requested::default())))
}

/// The keys at the boundary of constructor `c`'s fields that have one (not
/// erased), in order: alongside [`data_fields`].
pub(crate) fn external_keys(repr: &JsRepr, c: usize) -> Vec<&str> {
    repr.ctors[c]
        .keys
        .iter()
        .flatten()
        .map(String::as_str)
        .collect()
}

/// For each of constructor `c`'s fields that has a key, whether `js.optional`
/// is written on it: alongside [`external_keys`].
pub(crate) fn external_optional(repr: &JsRepr, c: usize) -> Vec<bool> {
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
pub(crate) fn runtime_fields(g: &View<'_>, d: DataId, c: usize) -> Vec<usize> {
    let ctor = &g.data(d).ctors()[c];
    (0..ctor.fields.len())
        .filter(|&i| !ctor.field_erased[i])
        .collect()
}

/// The default of field `i` of constructor `c` of `d`, if it has one
/// (docs/proposals/named-arguments.md §5.1).
pub(crate) fn field_default<'a>(
    g: &View<'a>,
    d: DataId,
    c: usize,
    i: usize,
) -> Option<&'a FieldDefault> {
    g.defaults(d)?.get(c)?.get(i)?.as_ref()
}

/// Whether field `i` of constructor `c` of `d`, whose boundary type is `b`,
/// is an optional property, where a missing property and `undefined` are
/// both `None`, and `None` is no property (D582): a record's `Option` field,
/// or a variant's with `js.optional` (`flag`). A field with a default never
/// is: a missing property is its default, and a defaulted `Option` field is
/// always present on output, `None` as `undefined` (D1114).
pub(crate) fn optional_property(
    g: &View<'_>,
    d: DataId,
    c: usize,
    i: usize,
    b: &Boundary,
    flag: bool,
) -> bool {
    field_default(g, d, c, i).is_none()
        && (flag || (g.data(d).record() && matches!(b, Boundary::Option(..))))
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

pub(crate) const RESERVED_KEYS: &[&str] = &["tag", "__proto__"];

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
pub(crate) fn field_key_at(g: &View<'_>, d: DataId, c: usize, i: usize) -> String {
    let fields = &g.data(d).ctors()[c].fields;
    let name = &fields[i].0;
    if fields.iter().filter(|(n, _)| n == name).count() > 1 {
        format!("${i}")
    } else {
        key(g, d, name)
    }
}

/// The key of field `name` of data type `d`.
pub(crate) fn key(g: &View<'_>, d: DataId, name: &str) -> String {
    if g.data(d).record() {
        record_key(name)
    } else {
        field_key(name)
    }
}

/// Reading property `key`: `.key`, or `["key"]` if it isn't an identifier.
pub(crate) fn member(key: &str) -> String {
    if is_js_identifier(key) {
        format!(".{key}")
    } else {
        format!("[{}]", js_string_literal(key))
    }
}

/// A property name in an object literal or a TypeScript object type: as it
/// is if it's an identifier, otherwise quoted.
pub(crate) fn ts_key(key: &str) -> String {
    if is_js_identifier(key) {
        key.to_string()
    } else {
        js_string_literal(key)
    }
}

/// A data type's name in the TypeScript declarations: its short name, with
/// each prime as `$`. Two types at the boundary with the same short name are
/// refused (`E-EXPORT`).
pub(crate) fn type_name(name: &str) -> String {
    short_name(name).replace('\'', "$")
}

/// The JS name of the description of a data type (see `datatype` in
/// [`RUNTIME`]), from its full logical name.
pub(crate) fn info_name(path: &str) -> String {
    format!("info${}", encode(path))
}

/// The JS name of an export's wrapper, which is exported under the export's
/// own name. Definitions are `$name`, so they're never `$$name`.
pub(crate) fn wrapper_name(name: &str) -> String {
    format!("$${name}")
}

/// The JS name of an export's wrapper's parameter at `position`. (Its
/// Stitchwort name is used in the declarations and in error messages.)
pub(crate) fn arg(position: usize) -> String {
    format!("arg{position}")
}

pub(crate) fn is_js_identifier(name: &str) -> bool {
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
pub(crate) const JS_RESERVED: &[&str] = &[
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
pub(crate) const MODULE_NAMES: &[&str] = &["StitchwortInputError", "StitchwortResourceError"];

/// Extraction runs on checked definitions, with no limit but the stack's
/// (see [`generate`]), so evaluating their types can't run out.
pub(crate) const OUTSIDE_LIMITS: &str =
    "internal error: evaluating a checked type ran out of resources";

/// A JS expression for `value`, encoded as it would cross the boundary. Used by
/// differential tests to compare the reference evaluator with generated JS.
pub fn boundary_literal(g: &View<'_>, b: &Boundary, value: &Value) -> Result<String, String> {
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
        // An array is its list.
        (Boundary::Array(elem), Value::Ctor(_, 0, fields)) if fields.len() == 1 => {
            boundary_literal(g, &Boundary::List(elem.clone()), &fields[0])
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
            let ctor = &data.ctors()[*c];
            let repr = repr(g, *d);
            if repr.string_enum {
                return Ok(js_string_literal(&repr.ctors[*c].tag));
            }
            let all = field_boundaries(g, *d, args).map_err(|e| e.message)?;
            let boundaries = &all[*c];
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
            if !data.record() {
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
pub(crate) fn map_entries(
    g: &View<'_>,
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
pub(crate) fn char_value(g: &View<'_>, value: &Value) -> Result<Option<char>, String> {
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
pub(crate) fn dependency_order(codegen: &Gen, ids: &[DefId]) -> Vec<DefId> {
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
pub(crate) fn refs(codegen: &Gen, id: DefId, wanted: &HashSet<DefId>) -> Vec<DefId> {
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
