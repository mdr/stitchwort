//! The fast path of the boundary codec: for each boundary type an export's
//! parameter or result has, a decoder and an encoder specialised to it,
//! generated as straight-line JavaScript (no description of the type is
//! interpreted per value, no frames, no path to keep).
//!
//! They only ever accept or give up. A fast decoder reads each property once,
//! as the general `decode` does, and if anything about the input isn't
//! exactly what it expects (a wrong type, a missing or inherited property, a
//! hole, a getter that throws), or the input is nested deeper than
//! `MAX_DEPTH` or has more than `MAX_WORK` values (shared values, a cycle), it
//! throws, and `decodeFast` runs the general `decode` on the input to say
//! where and why, or to accept it with its own bookkeeping: shared values
//! decoded once, cycles refused, any depth. So what is refused, and how, is
//! the general decoder's alone. The encoder gives up the same way, and its
//! fallback is the general `encode`.

use std::fmt::Write;

use stitchwort_core::DataId;
use stitchwort_core::registry::Builtin;

use super::{
    Boundary, Gen, external_keys, external_optional, field_boundaries, field_key_at,
    generic_field_boundaries, info_name, js_string_literal, member, optional_property, repr,
    runtime_fields, ts_key,
};

/// The functions and type constants generated so far.
#[derive(Default)]
pub(crate) struct Fast {
    names: stitchwort_core::collections::HashMap<String, String>,
    types: stitchwort_core::collections::HashMap<String, String>,
    consts: String,
    functions: String,
    count: usize,
}

impl Fast {
    /// What the generated module adds for the fast path: type constants,
    /// then the functions.
    pub(crate) fn module_text(&self) -> String {
        if self.functions.is_empty() && self.consts.is_empty() {
            return String::new();
        }
        format!(
            "\n// The fast path's codecs, one decoder and one encoder for each type that\n// crosses (see `decodeFast`).\n{}{}",
            self.consts, self.functions
        )
    }
}

/// A property name in an object literal: computed if it's `__proto__`, which
/// would set the prototype otherwise.
fn literal_key(key: &str) -> String {
    if key == "__proto__" {
        "[\"__proto__\"]".to_string()
    } else {
        ts_key(key)
    }
}

fn leaf_name(b: &Boundary) -> Option<&'static str> {
    Some(match b {
        Boundary::Nat => "NAT",
        Boundary::Int => "INT",
        Boundary::SafeNat => "SAFE_NAT",
        Boundary::SafeInt => "SAFE_INT",
        Boundary::Float => "FLOAT",
        Boundary::Bool => "BOOL",
        Boundary::Text => "TEXT",
        Boundary::Char => "CHAR",
        _ => return None,
    })
}

/// One field of a constructor, as the codecs see it.
struct FieldCodec {
    /// Its key at the boundary, and inside generated code.
    external: String,
    inside: String,
    /// Whether a missing property is `None`, and `None` is no property.
    optional: bool,
    /// For a field with a default: the statements binding the earlier fields
    /// its helper takes, and the call that gives the default for a missing
    /// property ([`Gen::default_call`]).
    default: Option<(String, String)>,
    b: Boundary,
}

impl Gen<'_> {
    /// The `const` for a boundary type, as the general codec takes it.
    pub(crate) fn type_const(&self, b: &Boundary) -> String {
        let expr = self.type_expr(b);
        let mut fast = self.fast.borrow_mut();
        if let Some(name) = fast.types.get(&expr) {
            return name.clone();
        }
        let name = format!("ty${}", fast.types.len() + 1);
        let _ = writeln!(fast.consts, "const {name} = {expr};");
        fast.types.insert(expr, name.clone());
        name
    }

    /// The name of the fast decoder for `b`, generating it (and those it
    /// calls) if it's new. A list, a map and a data type have functions; the
    /// others are expressions ([`Gen::dec_expr`]).
    pub(crate) fn fast_decoder(&self, b: &Boundary) -> String {
        self.fast_function(b, true)
    }

    /// The name of the fast encoder for `b`.
    pub(crate) fn fast_encoder(&self, b: &Boundary) -> String {
        self.fast_function(b, false)
    }

    /// A boundary type whose codec is a function of its own: the decoders and
    /// encoders of the others are wrapped in one.
    fn fast_function(&self, b: &Boundary, decode: bool) -> String {
        let key = format!("{} {}", if decode { "d" } else { "e" }, self.type_expr(b));
        let name = {
            let mut fast = self.fast.borrow_mut();
            if let Some(name) = fast.names.get(&key) {
                return name.clone();
            }
            fast.count += 1;
            let name = format!("{}${}", if decode { "dec" } else { "enc" }, fast.count);
            fast.names.insert(key, name.clone());
            name
        };
        let text = match (decode, b) {
            (true, Boundary::List(elem)) => self.dec_list(&name, b, elem),
            (false, Boundary::List(elem)) => self.enc_list(&name, elem),
            (true, Boundary::Map(_, key, value)) => self.dec_map(&name, b, key, value),
            (false, Boundary::Map(_, _, value)) => self.enc_map(&name, value),
            (true, Boundary::Data(d, args)) => self.dec_data(&name, b, *d, args),
            (false, Boundary::Data(d, args)) => self.enc_data(&name, *d, args),
            // Any other type is wrapped, as a function of its own.
            (true, other) => format!(
                "function {name}(x) {{\n  return {};\n}}\n",
                self.dec_expr(other, "x")
            ),
            (false, other) => format!(
                "function {name}(v) {{\n  return {};\n}}\n",
                self.enc_expr(other, "v")
            ),
        };
        self.fast.borrow_mut().functions.push_str(&text);
        name
    }

    /// A JS expression decoding `var` (a name, read once by it) as a value of
    /// type `b`.
    fn dec_expr(&self, b: &Boundary, var: &str) -> String {
        if let Some(leaf) = leaf_name(b) {
            return format!("{leaf}.dec({var})");
        }
        match b {
            Boundary::Option(d, _) => {
                let (none, some, key) = self.option_names(*d);
                let key = ts_key(&key);
                format!(
                    "({var} === undefined ? {{ tag: {none} }} : {var} === null ? fail() : {{ tag: {some}, {key}: {} }})",
                    self.dec_expr(&b.payload(), var)
                )
            }
            Boundary::List(_) | Boundary::Map(..) | Boundary::Data(..) => {
                format!("{}({var})", self.fast_decoder(b))
            }
            // Never in a closed type: the general decoder is left to say.
            _ => "fail()".to_string(),
        }
    }

    /// A JS expression encoding `var`, a value of type `b`.
    fn enc_expr(&self, b: &Boundary, var: &str) -> String {
        if let Some(leaf) = leaf_name(b) {
            return format!("{leaf}.enc({var})");
        }
        match b {
            Boundary::Option(d, _) => {
                let (none, _, key) = self.option_names(*d);
                let payload = format!("{var}{}", member(&key));
                format!(
                    "({var}.tag === {none} ? undefined : {})",
                    self.enc_expr(&b.payload(), &payload)
                )
            }
            Boundary::List(_) | Boundary::Map(..) | Boundary::Data(..) => {
                format!("{}({var})", self.fast_encoder(b))
            }
            _ => "fail()".to_string(),
        }
    }

    /// `None`'s tag and `Some`'s tag, as JS literals, and the key of `Some`'s
    /// field, as it's written in an object literal (`OPTION_SHAPE`).
    fn option_names(&self, d: DataId) -> (String, String, String) {
        debug_assert!(self.g.registry.is_data(Builtin::Option, d));
        let data = self.g.data(d);
        (
            js_string_literal(&data.ctors[0].name),
            js_string_literal(&data.ctors[1].name),
            field_key_at(self.g, d, 1, 0),
        )
    }

    /// Whether a type is decoded without anything inside it that could be
    /// shared or contain itself, as the runtime's `shallow` says: a leaf, a
    /// string union, or an `Option` of one. Its decoding calls no function
    /// that nests, either.
    fn shallow(&self, b: &Boundary) -> bool {
        match b {
            Boundary::Option(_, inner) => {
                !matches!(**inner, Boundary::Option(..)) && self.shallow(inner)
            }
            Boundary::Data(d, _) => {
                let repr = repr(self.g, *d);
                repr.string_enum || (repr.unboxed && self.shallow(&self.unboxed_field(*d)))
            }
            Boundary::List(_) | Boundary::Map(..) | Boundary::Param(_) => false,
            _ => true,
        }
    }

    /// The boundary type of `js.unboxed` record `d`'s one field with a
    /// property (it has no parameters).
    fn unboxed_field(&self, d: DataId) -> Boundary {
        generic_field_boundaries(self.g, d)
            .into_iter()
            .flatten()
            .next()
            .expect("an unboxed record has one field with a property")
            .1
    }

    /// Whether constructor `c` of `d` is flat, as the runtime's `flatOf` says
    /// (by the type's own fields, not any arguments): all its fields shallow.
    fn flat_ctor(&self, d: DataId, c: usize) -> bool {
        generic_field_boundaries(self.g, d)[c]
            .iter()
            .all(|(_, b)| self.shallow(b))
    }

    /// What a decoder of a list, map or constructor that isn't flat does at
    /// its start: gives back what was decoded at this type already (or gives
    /// up if that's still being decoded: the input contains itself), and hands
    /// an input nested too deeply to the general decoder, which has no
    /// recursion to run out of.
    fn memo_lookup(ty: &str, pad: &str) -> String {
        format!(
            "{pad}const done = memoOf({ty});
{pad}const known = done.get(x);
{pad}if (known !== undefined) {{
{pad}  if (known === INSIDE) throw FAIL;
{pad}  return known;
{pad}}}
{pad}if (depth >= MAX_DEPTH) return decodeDeep({ty}, x);
"
        )
    }

    fn dec_list(&self, name: &str, b: &Boundary, elem: &Boundary) -> String {
        let ty = self.type_const(b);
        let lookup = Self::memo_lookup(&ty, "  ");
        let head = self.dec_expr(elem, "r");
        format!(
            "function {name}(x) {{
  if (!Array.isArray(x)) throw FAIL;
{lookup}  done.set(x, INSIDE);
  depth++;
  const n = x.length;
  let first = null, last = null;
  for (let i = 0; i < n; i++) {{
    if (!hasOwn(x, i)) throw FAIL;
    const r = x[i];
    const cell = {{ tag: \"Cons\", head: {head}, tail: null }};
    if (last === null) first = cell; else last.tail = cell;
    last = cell;
  }}
  const nil = {{ tag: \"Nil\" }};
  if (last === null) first = nil; else last.tail = nil;
  depth--;
  done.set(x, first);
  return first;
}}
"
        )
    }

    fn enc_list(&self, name: &str, elem: &Boundary) -> String {
        let shallow = self.shallow(elem);
        let guard = if shallow {
            ""
        } else {
            "  if (++depth > MAX_DEPTH) throw FAIL;\n"
        };
        let unguard = if shallow { "" } else { "  depth--;\n" };
        let item = self.enc_expr(elem, "l.head");
        format!(
            "function {name}(v) {{
{guard}  const out = [];
  for (let l = v; l.tag === \"Cons\"; l = l.tail) out.push({item});
{unguard}  return out;
}}
"
        )
    }

    fn dec_map(&self, name: &str, b: &Boundary, key: &Boundary, value: &Boundary) -> String {
        let ty = self.type_const(b);
        let lookup = Self::memo_lookup(&ty, "  ");
        let entry = self.dec_expr(value, "r");
        // A `js.unboxed` key is the string, if its proof fields hold.
        let checks = match key {
            Boundary::Data(d, _) if !self.g.data(*d).validators.is_empty() => format!(
                "\n    for (const [, holds] of {}.checks) if (!holds(k)) throw FAIL;",
                info_name(&self.g.data(*d).path)
            ),
            _ => String::new(),
        };
        format!(
            "function {name}(x) {{
  if (typeof x !== \"object\" || x === null) throw FAIL;
{lookup}  const keys = plainKeys(x);
  done.set(x, INSIDE);
  depth++;
  const n = keys.length;
  let first = null, last = null;
  for (let i = 0; i < n; i++) {{
    const key = keys[i];
    const k = TEXT.dec(key);{checks}
    if (!hasOwn(x, key)) throw FAIL;
    const r = x[key];
    const cell = {{ tag: \"Cons\", head: {{ tag: MAP_SHAPE.pair, [MAP_SHAPE.fst]: k, [MAP_SHAPE.snd]: {entry} }}, tail: null }};
    if (last === null) first = cell; else last.tail = cell;
    last = cell;
  }}
  const nil = {{ tag: \"Nil\" }};
  if (last === null) first = nil; else last.tail = nil;
  const map = MAP_SHAPE.fromList(first);
  depth--;
  done.set(x, map);
  return map;
}}
"
        )
    }

    fn enc_map(&self, name: &str, value: &Boundary) -> String {
        let shallow = self.shallow(value);
        let guard = if shallow {
            ""
        } else {
            "  if (++depth > MAX_DEPTH) throw FAIL;\n"
        };
        let unguard = if shallow { "" } else { "  depth--;\n" };
        let entry = self.enc_expr(value, "e[MAP_SHAPE.snd]");
        format!(
            "function {name}(v) {{
{guard}  const out = {{}};
  for (let l = MAP_SHAPE.toList(v); l.tag === \"Cons\"; l = l.tail) {{
    const e = l.head;
    Object.defineProperty(out, TEXT.enc(e[MAP_SHAPE.fst]), {{
      value: {entry}, writable: true, enumerable: true, configurable: true,
    }});
  }}
{unguard}  return out;
}}
"
        )
    }

    /// Each constructor's fields, as the codecs see them.
    fn field_codecs(&self, d: DataId, args: &[Boundary]) -> Vec<Vec<FieldCodec>> {
        let g = self.g;
        let repr = repr(g, d);
        field_boundaries(g, d, args)
            .into_iter()
            .enumerate()
            .map(|(c, fields)| {
                let runtime = runtime_fields(g, d, c);
                // Field `j`'s decoded value, `f{k}` for its position `k`
                // among those with a key.
                let decoded = |j: usize| {
                    let k = runtime
                        .iter()
                        .position(|&r| r == j)
                        .expect("a default takes only fields with a key at run time");
                    format!("f{k}")
                };
                fields
                    .into_iter()
                    .zip(external_keys(&repr, c))
                    .zip(&runtime)
                    .zip(external_optional(&repr, c))
                    .map(|((((_, b), external), &i), flag)| FieldCodec {
                        external: external.to_string(),
                        inside: field_key_at(g, d, c, i),
                        optional: optional_property(g, d, c, i, &b, flag),
                        // Running out of stack here leaves the call to
                        // `fail()`: the general decoder then does it.
                        default: self
                            .default_call(d, c, i, &decoded)
                            .unwrap_or_else(|_| Some((String::new(), "fail()".into()))),
                        b,
                    })
                    .collect()
            })
            .collect()
    }

    /// The statements reading each field of `x` and decoding it (to `f0`,
    /// `f1`, …), and the properties of the object that holds them.
    fn dec_fields(&self, fields: &[FieldCodec], pad: &str) -> (String, Vec<String>) {
        let mut out = String::new();
        let mut props = Vec::new();
        for (i, f) in fields.iter().enumerate() {
            let key = js_string_literal(&f.external);
            let read = format!("x{}", member(&f.external));
            if let Some((reads, call)) = &f.default {
                // A missing property is the default; a present one,
                // `undefined` too, is decoded as given (D1114).
                let _ = writeln!(
                    out,
                    "{pad}let f{i};\n{pad}if (hasOwn(x, {key})) {{\n{pad}  const r{i} = {read};\n{pad}  f{i} = {};\n{pad}}} else if ({key} in x) throw FAIL;\n{pad}else {{ {reads}f{i} = {call}; }}",
                    self.dec_expr(&f.b, &format!("r{i}"))
                );
                props.push(format!("{}: f{i}", literal_key(&f.inside)));
                continue;
            }
            if f.optional {
                let _ = writeln!(
                    out,
                    "{pad}let r{i};\n{pad}if (hasOwn(x, {key})) r{i} = {read}; else if ({key} in x) throw FAIL;"
                );
            } else {
                let _ = writeln!(
                    out,
                    "{pad}if (!hasOwn(x, {key})) throw FAIL;\n{pad}const r{i} = {read};"
                );
            }
            let _ = writeln!(
                out,
                "{pad}const f{i} = {};",
                self.dec_expr(&f.b, &format!("r{i}"))
            );
            props.push(format!("{}: f{i}", literal_key(&f.inside)));
        }
        (out, props)
    }

    fn dec_data(&self, name: &str, b: &Boundary, d: DataId, args: &[Boundary]) -> String {
        let g = self.g;
        let data = g.data(d);
        let repr = repr(g, d);
        let codecs = self.field_codecs(d, args);
        if repr.string_enum {
            let mut out = format!("function {name}(x) {{\n  switch (x) {{\n");
            for (c, ctor) in data.ctors.iter().enumerate() {
                let _ = writeln!(
                    out,
                    "    case {}: return {{ tag: {} }};",
                    js_string_literal(&repr.ctors[c].tag),
                    js_string_literal(&ctor.name)
                );
            }
            out.push_str("    default: throw FAIL;\n  }\n}\n");
            return out;
        }
        if repr.unboxed {
            // `js.unboxed`: the field's own JS form, which is also the
            // record's value inside generated code (D866), if its proof
            // fields hold.
            let mut out = format!(
                "function {name}(x) {{\n  const o = {};\n",
                self.dec_expr(&self.unboxed_field(d), "x")
            );
            if data.validators.iter().any(|v| v.ctor == 0) {
                let _ = writeln!(
                    out,
                    "  for (const [, holds] of {}.checks) if (!holds(o)) throw FAIL;",
                    info_name(&data.path)
                );
            }
            out.push_str("  return o;\n}\n");
            return out;
        }
        let ty = self.type_const(b);
        // A constructor that isn't flat is remembered while it's decoded and
        // after, and counts as a level of nesting.
        let flat: Vec<bool> = (0..data.ctors.len())
            .map(|c| self.flat_ctor(d, c))
            .collect();
        let enter = "  done.set(x, INSIDE);\n  depth++;\n";
        let mut out = format!(
            "function {name}(x) {{\n  if (typeof x !== \"object\" || x === null || Array.isArray(x)) throw FAIL;\n"
        );
        if data.record {
            let (reads, props) = self.dec_fields(&codecs[0], "  ");
            if !flat[0] {
                out.push_str(&Self::memo_lookup(&ty, "  "));
                out.push_str(enter);
            }
            out.push_str(&reads);
            if self.unboxed(d).is_some() {
                // Stored as its one run-time field inside generated code
                // (D866).
                out.push_str("  const o = f0;\n");
            } else {
                let _ = writeln!(out, "  const o = {{ {} }};", props.join(", "));
            }
            if data.validators.iter().any(|v| v.ctor == 0) {
                let _ = writeln!(
                    out,
                    "  for (const [, holds] of {}.checks) if (!holds(o)) throw FAIL;",
                    info_name(&data.path)
                );
            }
            if !flat[0] {
                out.push_str("  depth--;\n  done.set(x, o);\n");
            }
            out.push_str("  return o;\n}\n");
            return out;
        }
        if flat.iter().any(|f| !f) {
            out.push_str(&Self::memo_lookup(&ty, "  "));
        }
        let tag_key = js_string_literal(&repr.tag_key);
        let _ = writeln!(
            out,
            "  if (!hasOwn(x, {tag_key})) throw FAIL;\n  switch (x{}) {{",
            member(&repr.tag_key)
        );
        for (c, ctor) in data.ctors.iter().enumerate() {
            let (reads, mut props) = self.dec_fields(&codecs[c], "      ");
            props.insert(0, format!("tag: {}", js_string_literal(&ctor.name)));
            let (open, close) = if flat[c] {
                (String::new(), "")
            } else {
                (
                    "      done.set(x, INSIDE);\n      depth++;\n".to_string(),
                    "      depth--;\n      done.set(x, o);\n",
                )
            };
            let _ = writeln!(
                out,
                "    case {}: {{\n{open}{reads}      const o = {{ {} }};\n{close}      return o;\n    }}",
                js_string_literal(&repr.ctors[c].tag),
                props.join(", ")
            );
        }
        out.push_str("    default: throw FAIL;\n  }\n}\n");
        out
    }

    /// The statements building object `o` from the fields of `v`, or, if
    /// `unboxed` (D866), from `v` itself, the one field's value.
    fn enc_fields(
        &self,
        tag: Option<String>,
        fields: &[FieldCodec],
        unboxed: bool,
        pad: &str,
    ) -> String {
        let mut out = String::new();
        // The leading required fields are in the object literal; once an
        // optional property might be missing, the rest are added in order.
        let mut literal: Vec<String> = tag.into_iter().collect();
        let mut rest = String::new();
        let mut in_literal = true;
        for (i, f) in fields.iter().enumerate() {
            let read = if unboxed {
                "v".to_string()
            } else {
                format!("v{}", member(&f.inside))
            };
            if f.optional {
                in_literal = false;
                let _ = writeln!(
                    rest,
                    "{pad}const q{i} = {};\n{pad}if (q{i} !== undefined) {};",
                    self.enc_expr(&f.b, &read),
                    store("o", &f.external, &format!("q{i}"))
                );
            } else if in_literal {
                literal.push(format!(
                    "{}: {}",
                    literal_key(&f.external),
                    self.enc_expr(&f.b, &read)
                ));
            } else {
                let _ = writeln!(
                    rest,
                    "{pad}{};",
                    store("o", &f.external, &self.enc_expr(&f.b, &read))
                );
            }
        }
        let _ = writeln!(out, "{pad}const o = {{ {} }};", literal.join(", "));
        out.push_str(&rest);
        out
    }

    fn enc_data(&self, name: &str, d: DataId, args: &[Boundary]) -> String {
        let g = self.g;
        let data = g.data(d);
        let repr = repr(g, d);
        let codecs = self.field_codecs(d, args);
        if repr.string_enum {
            let mut out = format!("function {name}(v) {{\n  switch (v.tag) {{\n");
            for (c, ctor) in data.ctors.iter().enumerate() {
                let _ = writeln!(
                    out,
                    "    case {}: return {};",
                    js_string_literal(&ctor.name),
                    js_string_literal(&repr.ctors[c].tag)
                );
            }
            out.push_str("    default: throw FAIL;\n  }\n}\n");
            return out;
        }
        if repr.unboxed {
            // `js.unboxed`: the field's value is the record's (D866).
            return format!(
                "function {name}(v) {{\n  return {};\n}}\n",
                self.enc_expr(&self.unboxed_field(d), "v")
            );
        }
        let shallow = codecs.iter().flatten().all(|f| self.shallow(&f.b));
        let guard = if shallow {
            ""
        } else {
            "  if (++depth > MAX_DEPTH) throw FAIL;\n"
        };
        let unguard = if shallow { "" } else { "depth--; " };
        if data.record {
            let unboxed = self.unboxed(d).is_some();
            let body = self.enc_fields(None, &codecs[0], unboxed, "  ");
            return format!("function {name}(v) {{\n{guard}{body}  {unguard}return o;\n}}\n");
        }
        let mut out = format!("function {name}(v) {{\n{guard}  switch (v.tag) {{\n");
        for (c, ctor) in data.ctors.iter().enumerate() {
            let tag = format!(
                "{}: {}",
                literal_key(&repr.tag_key),
                js_string_literal(&repr.ctors[c].tag)
            );
            let body = self.enc_fields(Some(tag), &codecs[c], false, "      ");
            let _ = writeln!(
                out,
                "    case {}: {{\n{body}      {unguard}return o;\n    }}",
                js_string_literal(&ctor.name)
            );
        }
        out.push_str("    default: throw FAIL;\n  }\n}\n");
        out
    }
}

/// A statement storing `value` as property `key` of `obj`, as an ordinary
/// property: `__proto__` is data, not the prototype.
fn store(obj: &str, key: &str, value: &str) -> String {
    if key == "__proto__" {
        format!(
            "Object.defineProperty({obj}, \"__proto__\", {{ value: {value}, writable: true, enumerable: true, configurable: true }})"
        )
    } else {
        format!("{obj}{} = {value}", member(key))
    }
}
