//! How a data type crosses the JavaScript boundary: its tag key, each
//! constructor's tag value and each field's key (docs/proposals/attributes.md
//! §4.6). The kernel never reads any of this. It is here because both the
//! elaborator, which resolves the `js.*` attributes written on a type where
//! the type is declared, and the JS backend, which resolves an unattributed
//! type's default when an export reaches it (D612), need the one resolver.
//!
//! Attributes are not part of a data type's content hash (D598): a
//! logical hash doesn't identify a JS interface.

use crate::globals::Data;

/// The tag key of a data type without `js.tag`. No Stitchwort field can have
/// it as its default key (a name starts with a letter or `_`, and only its
/// later primes become `$`), so it never clashes with one.
pub const DEFAULT_TAG_KEY: &str = "$tag";

/// A key no field may have: assigning it to an object sets the object's
/// prototype instead of making a property.
pub const PROTO: &str = "__proto__";

/// The external names of one data type, resolved once and read by the codec
/// tables and the `.d.ts` printer alike.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsRepr {
    /// The discriminant's key (a record has none, and ignores it).
    pub tag_key: String,
    pub ctors: Vec<JsCtor>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsCtor {
    /// The discriminant's value.
    pub tag: String,
    /// For each field, its key; `None` for an erased field (a proof or a
    /// type), which has no property.
    pub keys: Vec<Option<String>>,
}

/// What the attributes on a type ask for: `None` wherever the default
/// applies. Shaped like the type: one entry per constructor, one per field.
#[derive(Clone, Debug, Default)]
pub struct Requested {
    pub tag_key: Option<String>,
    pub ctors: Vec<(Option<String>, Vec<Option<String>>)>,
}

/// Why a type's resolved names don't work at the boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Clash {
    /// Constructor `ctor` has the same tag value as the earlier `other`.
    SameTag { ctor: usize, other: usize },
    /// Field `field` of constructor `ctor` has the same key as its earlier
    /// field `other`.
    SameKey {
        ctor: usize,
        field: usize,
        other: usize,
    },
    /// Field `field` of constructor `ctor` has the type's tag key as its key.
    KeyIsTag { ctor: usize, field: usize },
    /// Field `field` of constructor `ctor` has the key `__proto__`.
    ProtoKey { ctor: usize, field: usize },
}

impl Clash {
    /// The constructor, and field if any, the clash is reported at.
    pub fn at(&self) -> (usize, Option<usize>) {
        match *self {
            Clash::SameTag { ctor, .. } => (ctor, None),
            Clash::SameKey { ctor, field, .. }
            | Clash::KeyIsTag { ctor, field }
            | Clash::ProtoKey { ctor, field } => (ctor, Some(field)),
        }
    }

    /// The earlier constructor or field it clashes with, if any.
    pub fn other(&self) -> Option<(usize, Option<usize>)> {
        match *self {
            Clash::SameTag { other, .. } => Some((other, None)),
            Clash::SameKey { ctor, other, .. } => Some((ctor, Some(other))),
            Clash::KeyIsTag { .. } | Clash::ProtoKey { .. } => None,
        }
    }

    /// The message, for `E-JS-NAME-CLASH`.
    pub fn message(&self, data: &Data, repr: &JsRepr) -> String {
        let field = |c: usize, i: usize| {
            let name = &data.ctors[c].fields[i].0;
            if data.record {
                format!("field `{name}` of `{}`", data.name)
            } else {
                format!("field `{name}` of `{}`", data.ctors[c].name)
            }
        };
        let quoted = |s: &str| format!("{s:?}");
        match *self {
            Clash::SameTag { ctor, other } => format!(
                "constructors `{}` and `{}` of `{}` both cross to JavaScript with the tag {}",
                data.ctors[other].name,
                data.ctors[ctor].name,
                data.name,
                quoted(&repr.ctors[ctor].tag)
            ),
            Clash::SameKey {
                ctor,
                field: i,
                other,
            } => format!(
                "{} and `{}` both cross to JavaScript as the key {}",
                field(ctor, other),
                data.ctors[ctor].fields[i].0,
                quoted(repr.ctors[ctor].keys[i].as_deref().unwrap_or_default())
            ),
            Clash::KeyIsTag { ctor, field: i } => format!(
                "{} would cross to JavaScript as the key {}, which is `{}`'s tag key",
                field(ctor, i),
                quoted(&repr.tag_key),
                data.name
            ),
            Clash::ProtoKey { ctor, field: i } => format!(
                "{} can't cross to JavaScript as the key \"__proto__\"",
                field(ctor, i)
            ),
        }
    }

    /// What to do about it.
    pub fn note(&self) -> &'static str {
        match self {
            Clash::SameTag { .. } => {
                "give one of them another tag with `@[js.name \"…\"]` after its `|`"
            }
            Clash::SameKey { .. } => {
                "give one of them another key with `@[js.name \"…\"]` before its name"
            }
            Clash::KeyIsTag { .. } => {
                "give the field another key with `@[js.name \"…\"]` before its name, or choose \
                 another tag key with `@[js.tag \"…\"]` on the type"
            }
            Clash::ProtoKey { .. } => {
                "assigning `__proto__` sets an object's prototype instead of making a property; \
                 give the field another key with `@[js.name \"…\"]` before its name"
            }
        }
    }
}

/// A field's key when it has no `js.name`: its name, with each prime as `$`.
pub fn default_key(name: &str) -> String {
    name.replace('\'', "$")
}

/// The type's representation: the tag key, then each constructor's tag
/// value, then each encoded field's key, each from `requested` or the
/// default; then the checks, on the final names (§4.6). Every clash, in the
/// order of the type's constructors and fields.
pub fn resolve(data: &Data, requested: &Requested) -> Result<JsRepr, Vec<Clash>> {
    let repr = names(data, requested);
    let clashes = clashes(&repr, data.record);
    if clashes.is_empty() {
        Ok(repr)
    } else {
        Err(clashes)
    }
}

/// The names `requested` gives the type, each from the attributes or the
/// default, unchecked: [`resolve`] checks them.
pub fn names(data: &Data, requested: &Requested) -> JsRepr {
    let tag_key = requested
        .tag_key
        .clone()
        .unwrap_or_else(|| DEFAULT_TAG_KEY.to_string());
    let mut ctors = Vec::with_capacity(data.ctors.len());
    for (c, ctor) in data.ctors.iter().enumerate() {
        let asked = requested.ctors.get(c);
        let tag = asked
            .and_then(|(tag, _)| tag.clone())
            .unwrap_or_else(|| ctor.name.to_string());
        let keys = ctor
            .fields
            .iter()
            .enumerate()
            .map(|(i, (name, _))| {
                if ctor.field_erased.get(i).copied().unwrap_or(false) {
                    return None;
                }
                Some(
                    asked
                        .and_then(|(_, keys)| keys.get(i).cloned().flatten())
                        .unwrap_or_else(|| default_key(name)),
                )
            })
            .collect();
        ctors.push(JsCtor { tag, keys });
    }
    JsRepr { tag_key, ctors }
}

/// The clashes among a representation's names. A record has no tag, so its
/// fields can't clash with it.
pub fn clashes(repr: &JsRepr, record: bool) -> Vec<Clash> {
    let mut out = Vec::new();
    for (c, ctor) in repr.ctors.iter().enumerate() {
        if let Some(other) = repr.ctors[..c].iter().position(|o| o.tag == ctor.tag) {
            out.push(Clash::SameTag { ctor: c, other });
        }
        for (i, key) in ctor.keys.iter().enumerate() {
            let Some(key) = key else { continue };
            if key == PROTO {
                out.push(Clash::ProtoKey { ctor: c, field: i });
            } else if !record && *key == repr.tag_key {
                out.push(Clash::KeyIsTag { ctor: c, field: i });
            } else if let Some(other) = ctor.keys[..i]
                .iter()
                .position(|o| o.as_deref() == Some(key.as_str()))
            {
                out.push(Clash::SameKey {
                    ctor: c,
                    field: i,
                    other,
                });
            }
        }
    }
    out
}
