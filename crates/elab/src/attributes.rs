//! Attributes, `@[…]` (docs/proposals/attributes.md, docs/syntax.md
//! "Attributes"): **the** registry of the attributes the compiler accepts,
//! and their validation. The parser keeps attributes on data types,
//! constructors, fields and definitions (and refuses them anywhere else);
//! here each one is either consumed by its target or refused, never
//! silently dropped.
//!
//! Valid `js.*` attributes don't change the checked core declarations, the
//! kernel's judgments, or evaluation: they say how a data type crosses the
//! JavaScript boundary, resolved once into the type's [`JsRepr`], which only
//! the JS backend reads (§4.4, §4.6). They aren't hashed (D598).

use std::rc::Rc;

use stitchwort_core::js_repr::{self, Clash, JsRepr, PROTO, Requested};
use stitchwort_core::registry::Builtin;
use stitchwort_core::{DataId, Term};
use stitchwort_syntax::ast::{self, Attribute, Decl};
use stitchwort_syntax::{Diagnostic, Span};

use crate::{Elaborator, Result};

/// What an attribute can be written on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Target {
    /// A data type with constructors (not a record).
    DataType,
    Ctor,
    /// A constructor's or a record's field that has a property in JS.
    Field,
}

impl Target {
    fn describe(self) -> &'static str {
        match self {
            Target::DataType => "a data type",
            Target::Ctor => "a constructor",
            Target::Field => "a field",
        }
    }
}

/// One attribute the compiler knows.
pub(crate) struct Spec {
    pub(crate) name: &'static str,
    /// Where it may be written.
    targets: &'static [Target],
    /// What its string argument means, for messages: `"KEY"`; empty for an
    /// attribute that takes none (`@[js.optional]`).
    pub(crate) argument: &'static str,
    /// One line, for messages and the reference.
    pub(crate) doc: &'static str,
}

/// Every attribute the compiler accepts (D597: a closed set). All but
/// `js.optional` take one string. Bare names (`@[inline]`) are reserved for language-level
/// attributes; `js.` is the JavaScript backend's.
pub(crate) const REGISTRY: &[Spec] = &[
    Spec {
        name: "js.tag",
        targets: &[Target::DataType],
        argument: "KEY",
        doc: "the key of the property that says which constructor a JS object is (without it, \
              `$tag`)",
    },
    Spec {
        name: "js.enum",
        targets: &[Target::DataType],
        argument: "",
        doc: "a type whose constructors have no fields crosses as a string union, each \
              constructor as a string (its name, or its `js.name`), instead of as tagged \
              objects",
    },
    Spec {
        name: "js.name",
        targets: &[Target::Ctor, Target::Field],
        argument: "NAME",
        doc: "a constructor's tag value, or a field's key, in JS (without it, the Stitchwort \
              name, with each `'` as `$`)",
    },
    Spec {
        name: "js.optional",
        targets: &[Target::Field],
        argument: "",
        doc: "a constructor field of type `Option T` crosses as an optional property `f?: T`, \
              absent for `None`, instead of `f: T | undefined`",
    },
];

/// Where a group of attributes is written, for checking and for messages.
#[derive(Clone, Copy)]
enum Place<'a> {
    Target(Target),
    /// A record type: no tag, so nothing yet applies to it.
    Record,
    /// Something no attribute applies to: `"a theorem"`.
    Other(&'a str),
}

/// The attributes of one place, checked: each one's spec and argument.
struct Checked<'a> {
    attrs: Vec<(&'static Spec, &'a Attribute, &'a str)>,
}

impl Checked<'_> {
    fn get(&self, name: &str) -> Option<(&Attribute, &str)> {
        self.attrs
            .iter()
            .find(|(spec, ..)| spec.name == name)
            .map(|(_, a, arg)| (*a, *arg))
    }
}

/// The note listing what there is.
fn known() -> String {
    let names: Vec<String> = REGISTRY.iter().map(|s| format!("`{}`", s.name)).collect();
    let list = match names.as_slice() {
        [init @ .., last] if !init.is_empty() => format!("{} and {last}", init.join(", ")),
        _ => names.join(""),
    };
    format!("the attributes are {list}")
}

/// The spec of attribute `a`, or `E-ATTRIBUTE-UNKNOWN`.
fn spec(a: &Attribute) -> Result<&'static Spec> {
    if let Some(spec) = REGISTRY.iter().find(|s| s.name == a.name.text) {
        return Ok(spec);
    }
    let mut d = Diagnostic::error(
        "E-ATTRIBUTE-UNKNOWN",
        format!("unknown attribute `{}`", a.name.text),
    )
    .with_label(a.name.span, "not an attribute the compiler knows");
    let near = REGISTRY
        .iter()
        .map(|s| (crate::scope::edit_distance(s.name, &a.name.text), s.name))
        .filter(|(d, _)| *d <= 3)
        .min();
    if let Some((_, best)) = near {
        d = d.with_note(format!("did you mean `{best}`?"));
    }
    Err(d.with_note(known()))
}

/// Checks the attributes written at `place`: each known, allowed there, with
/// its argument, and none twice.
fn check<'a>(attrs: &'a [Attribute], place: Place) -> Result<Checked<'a>> {
    let mut out = Checked { attrs: Vec::new() };
    for a in attrs {
        let spec = spec(a)?;
        let allowed = match place {
            Place::Target(t) => spec.targets.contains(&t),
            Place::Record | Place::Other(_) => false,
        };
        if !allowed {
            let applies: Vec<&str> = spec.targets.iter().map(|t| t.describe()).collect();
            let (what, why) = match place {
                Place::Target(t) => (t.describe(), None),
                Place::Record if spec.name == "js.tag" => (
                    "a record",
                    Some("a record crosses as an object without a tag"),
                ),
                Place::Record if spec.name == "js.enum" => (
                    "a record",
                    Some("a record has fields, and a string union has none"),
                ),
                Place::Record => ("a record type", None),
                Place::Other(what) => (what, None),
            };
            let mut d = Diagnostic::error(
                "E-ATTRIBUTE",
                format!("`{}` can't be used on {what}", spec.name),
            )
            .with_label(a.span, format!("on {what}"));
            if let Some(why) = why {
                d = d.with_note(why);
            }
            return Err(d.with_note(format!(
                "`{}` applies to {}: {}",
                spec.name,
                applies.join(" or "),
                spec.doc
            )));
        }
        if spec.argument.is_empty() {
            if a.arg.is_some() {
                return Err(Diagnostic::error(
                    "E-ATTRIBUTE",
                    format!("`{}` takes no argument", spec.name),
                )
                .with_label(a.span, "has an argument")
                .with_note(format!("write `@[{}]`: {}", spec.name, spec.doc)));
            }
            if let Some((_, first, _)) = out.attrs.iter().find(|(s, ..)| s.name == spec.name) {
                return Err(Diagnostic::error(
                    "E-ATTRIBUTE",
                    format!("`{}` is written twice here", spec.name),
                )
                .with_label(a.span, "again here")
                .with_label(first.span, "first here"));
            }
            out.attrs.push((spec, a, ""));
            continue;
        }
        let Some((arg, _)) = &a.arg else {
            return Err(Diagnostic::error(
                "E-ATTRIBUTE",
                format!("`{}` needs a string", spec.name),
            )
            .with_label(a.span, "no argument")
            .with_note(format!(
                "write `@[{} \"{}\"]`: {}",
                spec.name, spec.argument, spec.doc
            )));
        };
        if let Some((_, first, _)) = out.attrs.iter().find(|(s, ..)| s.name == spec.name) {
            return Err(Diagnostic::error(
                "E-ATTRIBUTE",
                format!("`{}` is written twice here", spec.name),
            )
            .with_label(a.span, "again here")
            .with_label(first.span, "first here"));
        }
        out.attrs.push((spec, a, arg));
    }
    Ok(out)
}

/// `E-ATTRIBUTE` for an empty string.
fn non_empty(a: &Attribute, arg: &str, what: &str) -> Result<()> {
    if arg.is_empty() {
        return Err(
            Diagnostic::error("E-ATTRIBUTE", format!("{what} can't be the empty string"))
                .with_label(a.span, "empty"),
        );
    }
    Ok(())
}

/// Where each field of each constructor is written: its binder's name, and
/// the binder's attributes.
type FieldSites<'a> = Vec<Vec<(Span, &'a [Attribute])>>;

impl Elaborator {
    /// A definition (or theorem, instance, synonym, export) with attributes:
    /// none applies to one yet (`js.name` on an export is stage 3 of
    /// docs/proposals/attributes.md), so each is refused, or unknown.
    pub(crate) fn definition_attributes(&self, signature: &Decl) -> Result<()> {
        let Decl::Signature {
            attrs,
            theorem,
            export,
            synonym,
            instance,
            ..
        } = signature
        else {
            return Ok(());
        };
        if attrs.is_empty() {
            return Ok(());
        }
        let what = if *synonym {
            "a type synonym"
        } else if *instance {
            "an instance"
        } else if *export {
            "an exported definition"
        } else if *theorem {
            "a theorem"
        } else {
            "a definition"
        };
        check(attrs, Place::Other(what)).map(|_| ())
    }

    /// After data type `d` is admitted: checks the attributes on it, its
    /// constructors and its fields, and with any, resolves and checks the
    /// type's representation (§4.6) and keeps it. A type with none is
    /// resolved by the JS backend when an export reaches it (D612).
    pub(crate) fn data_attributes(&mut self, decl: &Decl, d: DataId) -> Result<()> {
        let Decl::Data {
            attrs,
            ctors,
            record,
            interface,
            name,
            ..
        } = decl
        else {
            return Ok(());
        };
        let any = !attrs.is_empty()
            || ctors
                .iter()
                .any(|c| !c.attrs.is_empty() || c.fields.iter().any(|b| !b.attrs.is_empty()));
        if !any {
            return Ok(());
        }
        let first = attrs
            .iter()
            .chain(ctors.iter().flat_map(|c| &c.attrs))
            .chain(ctors.iter().flat_map(|c| &c.fields).flat_map(|b| &b.attrs))
            .next()
            .expect("some attribute");
        // Each attribute is known, whatever else is wrong.
        for a in attrs
            .iter()
            .chain(ctors.iter().flat_map(|c| &c.attrs))
            .chain(ctors.iter().flat_map(|c| &c.fields).flat_map(|b| &b.attrs))
        {
            spec(a)?;
        }
        if *interface {
            return Err(Diagnostic::error(
                "E-ATTRIBUTE",
                format!("`{}` can't be used on an interface", first.name.text),
            )
            .with_label(first.span, "on an interface")
            .with_note("an interface's dictionaries never cross the JS boundary"));
        }
        let g = &self.globals;
        let data = g.data(d);
        if let Some(builtin) = g.registry.boundary_form(d) {
            return Err(Diagnostic::error(
                "E-ATTRIBUTE",
                format!(
                    "`{}` can't be used on `{}` or inside it",
                    first.name.text, data.name
                ),
            )
            .with_label(first.span, "here")
            .with_note(format!(
                "`{}` has a JavaScript form of its own (DESIGN.md §12), which attributes can't \
                 change",
                builtin.name()
            )));
        }
        let mut requested = Requested::default();
        let type_attrs = check(
            attrs,
            if *record {
                Place::Record
            } else {
                Place::Target(Target::DataType)
            },
        )?;
        if let Some((a, key)) = type_attrs.get("js.tag") {
            non_empty(a, key, "a tag key")?;
            if key == PROTO {
                return Err(Diagnostic::error(
                    "E-ATTRIBUTE",
                    "the tag key can't be \"__proto__\"",
                )
                .with_label(a.span, "here")
                .with_note("assigning `__proto__` sets an object's prototype instead of making a property"));
            }
            requested.tag_key = Some(key.to_string());
        }
        if let Some((a, _)) = type_attrs.get("js.enum") {
            if let Some((tag, _)) = type_attrs.get("js.tag") {
                return Err(Diagnostic::error(
                    "E-ATTRIBUTE",
                    "`js.tag` means nothing with `js.enum`",
                )
                .with_label(tag.span, "a string union has no tag key")
                .with_label(a.span, "crosses as a string")
                .with_note(
                    "remove `js.tag`: with `js.enum` a value is its string, not an object",
                ));
            }
            if ctors.is_empty() {
                return Err(Diagnostic::error(
                    "E-ATTRIBUTE",
                    format!(
                        "`js.enum` can't be used on `{}`: it has no constructors",
                        name.text
                    ),
                )
                .with_label(a.span, "no strings to list")
                .with_note("a type without constructors has no values to cross"));
            }
            for (c, ctor) in ctors.iter().enumerate() {
                let core = &data.ctors[c];
                let mut i = 0;
                for binder in &ctor.fields {
                    for n in &binder.names {
                        if !core.field_erased.get(i).copied().unwrap_or(false) {
                            return Err(Diagnostic::error(
                                "E-ATTRIBUTE",
                                format!(
                                    "`js.enum` can't be used on `{}`: constructor `{}` has the \
                                     field `{}`",
                                    name.text, ctor.name.text, n.text
                                ),
                            )
                            .with_label(n.span, "a field, so it has a property in JavaScript")
                            .with_label(a.span, "every constructor must be without fields")
                            .with_note(
                                "a string union can't hold a field's value: remove `js.enum` to \
                                 cross as tagged objects, or the field. A proof or a type \
                                 field, which has no property, is allowed",
                            ));
                        }
                        i += 1;
                    }
                }
            }
            requested.string_enum = true;
        }
        // Where each core field is written: the binders' names in order.
        let mut sites: FieldSites = Vec::new();
        let option = g.registry.data(Builtin::Option);
        for (c, ctor) in ctors.iter().enumerate() {
            let core = &data.ctors[c];
            let ctor_attrs = check(&ctor.attrs, Place::Target(Target::Ctor))?;
            let mut tag = None;
            if let Some((a, value)) = ctor_attrs.get("js.name") {
                non_empty(
                    a,
                    value,
                    if requested.string_enum {
                        "a constructor's string"
                    } else {
                        "a constructor's tag"
                    },
                )?;
                tag = Some(value.to_string());
            }
            let mut keys = Vec::new();
            let mut optionals = Vec::new();
            let mut ctor_sites = Vec::new();
            for binder in &ctor.fields {
                if binder.names.len() > 1
                    && let Some(a) = binder.attrs.first()
                {
                    return Err(Diagnostic::error(
                        "E-ATTRIBUTE",
                        "attributes on a field apply to one field, and these are on several",
                    )
                    .with_label(a.span, "on all of these fields")
                    .with_note(format!(
                        "write each field in brackets of its own: `({} …) ({}: …)`",
                        binder.names[0].text, binder.names[1].text
                    )));
                }
                for n in &binder.names {
                    let i = ctor_sites.len();
                    ctor_sites.push((n.span, binder.attrs.as_slice()));
                    if binder.attrs.is_empty() {
                        keys.push(None);
                        optionals.push(false);
                        continue;
                    }
                    let field_attrs = check(&binder.attrs, Place::Target(Target::Field))?;
                    // Only a field with a property can have attributes: the
                    // kernel's erasure decides, not implicitness (§4.2).
                    if core.field_erased.get(i).copied().unwrap_or(false) {
                        let what = if core.field_sorts.get(i) == Some(&stitchwort_core::Sort::Prop)
                        {
                            "a proof"
                        } else {
                            "a type"
                        };
                        let a = &binder.attrs[0];
                        return Err(Diagnostic::error(
                            "E-ATTRIBUTE",
                            format!(
                                "`{}` can't be used on `{}`: it's {what}, so it has no \
                                 property in JavaScript",
                                a.name.text, n.text
                            ),
                        )
                        .with_label(a.span, format!("`{}` is {what}", n.text)));
                    }
                    let mut key = None;
                    if let Some((a, value)) = field_attrs.get("js.name") {
                        non_empty(a, value, "a field's key")?;
                        key = Some(value.to_string());
                    }
                    keys.push(key);
                    let optional = field_attrs.get("js.optional");
                    if let Some((a, _)) = optional {
                        let is_option = matches!(
                            core.fields[i].1.strip_loc(),
                            Term::Data(od, _) if Some(*od) == option
                        );
                        if *record {
                            return Err(Diagnostic::error(
                                "E-ATTRIBUTE",
                                format!(
                                    "`js.optional` can't be used on the record field `{}`",
                                    n.text
                                ),
                            )
                            .with_label(a.span, "on a record field")
                            .with_note(
                                "a record's `Option` field already crosses as an optional \
                                 property, `f?: T`",
                            ));
                        }
                        if !is_option {
                            return Err(Diagnostic::error(
                                "E-ATTRIBUTE",
                                format!(
                                    "`js.optional` can't be used on `{}`: its type isn't `Option _`",
                                    n.text
                                ),
                            )
                            .with_label(a.span, "this field isn't an `Option`")
                            .with_note(
                                "`js.optional` applies to a constructor field written with the \
                                 type `Option T` itself: it makes the property optional, `f?: T`",
                            ));
                        }
                    }
                    optionals.push(optional.is_some());
                }
            }
            if ctor_sites.len() != core.fields.len() {
                // Not written as declared (a type the compiler made): the
                // spans would be wrong, and nothing here is written anyway.
                return Ok(());
            }
            sites.push(ctor_sites);
            requested.ctors.push((tag, keys));
            requested.optional.push(optionals);
        }
        let repr = js_repr::resolve(data, &requested).map_err(|clashes| {
            let repr = js_repr::names(data, &requested);
            clash_diagnostic(data, &repr, &clashes[0], ctors, &sites, name.span)
        })?;
        self.globals.datas[d.0].js = Some(Rc::new(repr));
        Ok(())
    }
}

/// `E-JS-NAME-CLASH` for `clash`, at the attribute or name that made it.
fn clash_diagnostic(
    data: &stitchwort_core::globals::Data,
    repr: &JsRepr,
    clash: &Clash,
    ctors: &[ast::CtorDecl],
    sites: &FieldSites,
    type_span: Span,
) -> Diagnostic {
    let site = |(c, field): (usize, Option<usize>)| -> Span {
        match field {
            Some(i) => sites
                .get(c)
                .and_then(|s| s.get(i))
                .map_or(type_span, |(span, attrs)| {
                    attrs
                        .iter()
                        .find(|a| a.name.text == "js.name")
                        .map_or(*span, |a| a.span)
                }),
            None => ctors.get(c).map_or(type_span, |ctor| {
                ctor.attrs
                    .iter()
                    .find(|a| a.name.text == "js.name")
                    .map_or(ctor.name.span, |a| a.span)
            }),
        }
    };
    let mut d = Diagnostic::error("E-JS-NAME-CLASH", clash.message(data, repr))
        .with_label(site(clash.at()), "here");
    if let Some(other) = clash.other() {
        d = d.with_label(site(other), "and here");
    }
    d.with_note(clash.note(repr))
}
