//! Generated lemmas about shared-field update (docs/proposals/variant-fields.md
//! §6.6): for a data type `T` that isn't a record, reading a shared field
//! after an update.
//!
//! ```text
//! type Shape =
//!   | Dot (ref: Nat) (id: Text) (start: Nat)
//!   | Circle (ref: Nat) (id: Text) (start: Nat) (text: Text)
//!
//! theorem Shape.start.update.start (x: Shape) (start: Nat): ({ x | start = start }).start = start
//! theorem Shape.start.update.id (x: Shape) (start: Nat): ({ x | start = start }).id = x.id
//! ```
//!
//! `T.f.update.g` is there for each shared field `f` that can be updated
//! and each shared field `g` it can be stated for. Updating `f` also
//! replaces the shared fields whose types mention it (`{ x | n = n, xs = xs }`
//! for `xs: Vec Nat n`), as an update written in source has to. A field `g`
//! is read when it's data and its type mentions no field: otherwise the two
//! sides' types differ (`Vec Nat ({ x | … }).n` and `Vec Nat n`). Neither is
//! made when `f`'s update forces a field that isn't shared, nor for records
//! (their updates compute, so these hold by `rfl`), propositions or indexed
//! families.
//!
//! Each is source, elaborated and checked like a theorem written by hand,
//! proved by one `rfl` per constructor. The update in its statement is the
//! same `match` a written one is, so `rewrite` finds it in any update of the
//! same field (two such `match`es are compared by their case trees). An
//! update of several fields that don't force each other is a different
//! `match`, which these don't match; nested updates are matched one at a
//! time.

use stitchwort_core::{DataId, Name, Sort};
use stitchwort_syntax::Span;
use stitchwort_syntax::ast::{self, BinOp, Bracket, Decl, Expr, Pattern};

use crate::{Elaborator, Result};

/// One lemma to generate: the fields its update replaces (the first is the
/// one it's named after), and the field it reads.
struct Lemma {
    replaced: Vec<Name>,
    read: Name,
}

impl Elaborator {
    /// After data type `d` is admitted, with its accessors: `T.f.update.g`
    /// for each shared field `f` that can be updated and each `g` that can
    /// be read back. Source can't declare such a name itself.
    pub(crate) fn derive_update_lemmas(&mut self, d: DataId, decl: &Decl) -> Result<()> {
        let data = self.globals.data(d);
        if data.record || data.sort == Sort::Prop || !data.indices.is_empty() {
            return Ok(());
        }
        // Each is placed at its updated field's name in the first
        // constructor: navigation shows what it is from there.
        let at = |field: &str| -> Span {
            let Decl::Data { ctors, .. } = decl else {
                return data.span;
            };
            ctors
                .first()
                .and_then(|c| {
                    c.fields
                        .iter()
                        .flat_map(|b| &b.names)
                        .find(|n| n.text == field)
                })
                .map_or(data.span, |n| n.span)
        };
        let lemmas = self.update_lemmas_of(d)?;
        let spans: Vec<Span> = lemmas.iter().map(|l| at(&l.replaced[0])).collect();
        for (lemma, span) in lemmas.into_iter().zip(spans) {
            let suffix = format!("{}.update.{}", lemma.replaced[0], lemma.read);
            self.clear_metas();
            let (signature, equations) = self.update_lemma_source(d, &suffix, &lemma, span);
            let result = self.definition(&signature, &equations);
            self.clear_metas();
            self.forget_dot_calls(span);
            let Decl::Signature { name, .. } = &signature else {
                unreachable!()
            };
            let key = self.declaration_key(name)?;
            match result {
                // A name under the accessor `T.f`, as `f.unfold` is under
                // `f`: dot notation looks these up as local definitions.
                Ok(()) => {
                    let under = key.rsplit_once('.').map(|(k, _)| k.to_string());
                    self.helper_keys.extend(under);
                    self.helper_keys.insert(key);
                }
                Err(e) if e.code == "E-RESOURCE" => return Err(e),
                // Not stated or not proved: left out, its name unknown.
                Err(_) => {
                    self.scope.entries.remove(&key);
                }
            }
        }
        Ok(())
    }

    /// Forgets the dot calls found in source the compiler wrote at `span`.
    /// They're remembered by the receiver's address and the spans, and that
    /// source is dropped once checked, so the next lemma's, written at the
    /// same span, can be allocated at the same address.
    fn forget_dot_calls(&self, span: Span) {
        let ours = |key: &crate::dot::CallKey| key.1 == span || key.2 == span;
        self.dot_heads.borrow_mut().retain(|key, _| !ours(key));
        self.dot_failed.borrow_mut().retain(|(key, ..)| !ours(key));
    }

    /// The lemmas `d` gets, in the shared fields' order.
    fn update_lemmas_of(&self, d: DataId) -> Result<Vec<Lemma>> {
        let shared = self.shared_fields(d)?.shared;
        let data = self.globals.data(d);
        let is_shared = |f: &Name| shared.iter().any(|(s, _)| s == f);
        // Read back: data whose type, in every constructor, mentions no field.
        let readable: Vec<&Name> = shared
            .iter()
            .filter(|(_, positions)| {
                data.ctors.iter().zip(positions).all(|(ctor, &pos)| {
                    ctor.field_sorts[pos] != Sort::Prop
                        && (0..pos).all(|j| !ctor.fields[pos].1.mentions(j))
                })
            })
            .map(|(f, _)| f)
            .collect();
        let mut out = Vec::new();
        for (root, _) in &shared {
            // The fields an update of `root` has to replace: those whose
            // types mention a replaced one, in any constructor.
            let mut replaced: Vec<Name> = vec![root.clone()];
            let mut updatable = true;
            let mut grew = true;
            while grew && updatable {
                grew = false;
                for ctor in &data.ctors {
                    for (j, (field, ty)) in ctor.fields.iter().enumerate() {
                        if replaced.contains(field) {
                            continue;
                        }
                        let forced = (0..j).any(|i| {
                            replaced.contains(&ctor.fields[i].0) && ty.mentions(j - 1 - i)
                        });
                        if !forced {
                            continue;
                        }
                        if !is_shared(field) || ctor.implicit.get(j).copied() == Some(true) {
                            updatable = false;
                        }
                        replaced.push(field.clone());
                        grew = true;
                    }
                }
            }
            if !updatable {
                continue;
            }
            // In the shared fields' order, the root first.
            let mut ordered = vec![root.clone()];
            ordered.extend(
                shared
                    .iter()
                    .map(|(f, _)| f)
                    .filter(|f| *f != root && replaced.contains(f))
                    .cloned(),
            );
            for &read in &readable {
                out.push(Lemma {
                    replaced: ordered.clone(),
                    read: read.clone(),
                });
            }
        }
        Ok(out)
    }

    /// The signature of `T.suffix` and its equations, one per constructor:
    ///
    /// ```text
    /// theorem T.f.update.g [p: _] … (x: T p …) (f: _) …: ({ x | f = f, … }).g = <g or x.g>
    ///   | C _ …, _ … => rfl
    /// ```
    fn update_lemma_source(
        &self,
        d: DataId,
        suffix: &str,
        lemma: &Lemma,
        span: Span,
    ) -> (Decl, Vec<Decl>) {
        let data = self.globals.data(d);
        let ty_name = self.relative_to_root(&data.name);
        let n = |text: &str| ast::Name {
            text: text.to_string(),
            span,
        };
        let var = |text: &str| Expr::Var(n(text));
        let params: Vec<String> = data.params.iter().map(|(x, _)| x.to_string()).collect();
        let mut taken: Vec<String> = params.clone();
        let mut fresh = |base: &str| {
            let mut name = base.to_string();
            while taken.contains(&name) {
                name.push('\'');
            }
            taken.push(name.clone());
            name
        };
        let base = fresh("x");
        let values: Vec<String> = lemma.replaced.iter().map(|f| fresh(f)).collect();
        let this = params.iter().enumerate().fold(var(&ty_name), |f, (j, p)| {
            let arg = if data.auto_params.get(j) == Some(&true) {
                Expr::NamedArg(n(p), Box::new(var(p)), span, Bracket::Square)
            } else {
                var(p)
            };
            Expr::App(Box::new(f), Box::new(arg))
        });
        let update = Expr::Record {
            base: Some(Box::new(var(&base))),
            fields: lemma
                .replaced
                .iter()
                .zip(&values)
                .map(|(f, v)| (n(f), var(v)))
                .collect(),
            span,
        };
        let read = Expr::Field(Box::new(update), n(&lemma.read));
        let expected = match lemma.replaced.iter().position(|f| *f == lemma.read) {
            Some(k) => var(&values[k]),
            None => Expr::Field(Box::new(var(&base)), n(&lemma.read)),
        };
        let pi = |x: &str, implicit: bool, dom: Expr, cod: Expr| Expr::Pi {
            names: vec![n(x)],
            implicit,
            auto: false,
            dom: Box::new(dom),
            cod: Box::new(cod),
            span,
        };
        let mut ty = Expr::Binary(BinOp::Eq, Box::new(read), Box::new(expected));
        for v in values.iter().rev() {
            ty = pi(v, false, Expr::Hole(span), ty);
        }
        ty = pi(&base, false, this, ty);
        for p in params.iter().rev() {
            ty = pi(p, true, Expr::Hole(span), ty);
        }
        let name = n(&format!("{ty_name}.{suffix}"));
        let signature = Decl::Signature {
            name: name.clone(),
            ty,
            theorem: true,
            export: false,
            synonym: false,
            instance: false,
            decreasing: None,
            opaque: false,
            unfolding: Vec::new(),
            defaults: Vec::new(),
            attrs: Vec::new(),
            span,
        };
        // Constructors by their exact keys, so what their names mean where
        // the type is declared doesn't matter.
        let owner = self.data_key(d);
        let equations = data
            .ctors
            .iter()
            .map(|ctor| {
                let key = format!(
                    "{}{}",
                    crate::scope::EXACT_KEY,
                    Self::member_key(&owner, &ctor.name)
                );
                let fields = ctor
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(k, (f, _))| {
                        if ctor.implicit.get(k).copied() == Some(true) {
                            Pattern::Named(n(f), Box::new(Pattern::Wildcard(span)), span)
                        } else {
                            Pattern::Wildcard(span)
                        }
                    })
                    .collect();
                let mut patterns = vec![Pattern::Ctor(n(&key), fields, span)];
                patterns.extend(values.iter().map(|_| Pattern::Wildcard(span)));
                Decl::Equation {
                    name: name.clone(),
                    patterns,
                    rhs: Some(var("rfl")),
                    arm: None,
                    span,
                }
            })
            .collect();
        (signature, equations)
    }
}
