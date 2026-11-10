//! Declarations' content hashes, listed and compared: what a sweep over
//! many files needs to show that every declaration kept its meaning
//! (docs/proposals/theorem-binders.md §5).
//!
//! A project's list comes from [`crate::live::LiveProject::declaration_hashes`]
//! and the library's from [`library_hashes`]. [`compare`] matches two lists
//! by name and applies a [`Promise`], as the project trial does. The
//! library is read once per process, so "before" and "after" a library edit
//! are two processes' lists (`stitchwort trial-edits --std-dir`).

use std::collections::BTreeMap;

use stitchwort_core::hash::{ContentHash, data_hash, def_hash, type_hash};
use stitchwort_core::{DataId, DefId};

use crate::driver::Session;
use crate::live::Promise;
use crate::live::trial::{Decl, Statement};

/// What a declaration is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclKind {
    Data,
    Def,
    Theorem,
}

impl DeclKind {
    pub fn word(self) -> &'static str {
        match self {
            DeclKind::Data => "data",
            DeclKind::Def => "def",
            DeclKind::Theorem => "theorem",
        }
    }
}

/// A declaration's name and hashes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclHash {
    pub kind: DeclKind,
    /// The full name.
    pub name: String,
    /// `None` while the declaration isn't final.
    pub hash: Option<ContentHash>,
    /// The hash of the statement alone, for a definition.
    pub type_hash: Option<ContentHash>,
}

impl DeclHash {
    pub(crate) fn from_decl(decl: &Decl) -> DeclHash {
        let (kind, type_hash) = match &decl.statement {
            Some(s) => (
                if s.theorem {
                    DeclKind::Theorem
                } else {
                    DeclKind::Def
                },
                s.ty,
            ),
            None => (DeclKind::Data, None),
        };
        DeclHash {
            kind,
            name: decl.name.clone(),
            hash: decl.hash,
            type_hash,
        }
    }

    fn to_decl(&self) -> Decl {
        Decl {
            name: self.name.clone(),
            hash: self.hash,
            statement: (self.kind != DeclKind::Data).then_some(Statement {
                theorem: self.kind == DeclKind::Theorem,
                ty: self.type_hash,
            }),
        }
    }
}

/// The hash as 64 hex digits, or `-` if there is none.
pub fn show(hash: Option<ContentHash>) -> String {
    hash.map_or_else(|| "-".to_string(), |h| h.hex())
}

/// Reads a hash back from [`show`]'s text.
pub fn parse_hash(text: &str) -> Option<ContentHash> {
    if text.len() != 64 || !text.is_ascii() {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (i, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&text[2 * i..2 * i + 2], 16).ok()?;
    }
    Some(ContentHash(bytes))
}

/// The declarations a session added after `first` (data types, definitions),
/// in the order they were added, datas first.
pub fn session_hashes(session: &Session, first: (usize, usize)) -> Vec<DeclHash> {
    let g = &session.elab.ev();
    let _op = g.machine.budget.operation(session.elab.options.limits);
    let mut out = Vec::new();
    for i in first.0..g.env.datas().len() {
        out.push(DeclHash {
            kind: DeclKind::Data,
            name: g.env.datas()[i].path().to_string(),
            hash: data_hash(g, DataId(i)).ok().flatten(),
            type_hash: None,
        });
    }
    for i in first.1..g.env.defs().len() {
        let def = &g.env.defs()[i];
        out.push(DeclHash {
            kind: if def.theorem() {
                DeclKind::Theorem
            } else {
                DeclKind::Def
            },
            name: def.path().to_string(),
            hash: def_hash(g, DefId(i)).ok().flatten(),
            type_hash: type_hash(g, DefId(i)).ok().flatten(),
        });
    }
    out
}

/// The core and every library file of the library this process reads, loaded
/// from source, with the hash of each declaration. The error is what failed
/// to load.
pub fn library_hashes(stack: usize) -> Result<Vec<DeclHash>, String> {
    let session = Session::try_eager_library_for_stack(stack)?;
    Ok(session_hashes(&session, (0, 0)))
}

/// A declaration that exists on both sides whose hash isn't what the
/// promise says.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HashChange {
    pub name: String,
    pub kind: DeclKind,
    pub was: Option<ContentHash>,
    pub now: Option<ContentHash>,
}

/// What [`compare`] found.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HashDiff {
    /// Declarations the promise doesn't allow to differ.
    pub changed: Vec<HashChange>,
    /// Under [`Promise::SameStatement`]: theorems whose proof changed with
    /// the statement held, accepted.
    pub proofs_changed: Vec<String>,
    /// Declarations only `after` has.
    pub added: Vec<String>,
    /// Declarations only `before` has (after the promise's renames).
    pub removed: Vec<String>,
    /// The declarations on both sides are not in the same order. Not a
    /// problem: moving a declaration between files keeps its meaning.
    pub reordered: bool,
}

impl HashDiff {
    pub fn is_empty(&self) -> bool {
        self.changed.is_empty() && self.added.is_empty() && self.removed.is_empty()
    }
}

/// `after` against `before`, matched by name (through the promise's
/// renames).
pub fn compare(before: &[DeclHash], after: &[DeclHash], promise: &Promise) -> HashDiff {
    let was: Vec<(String, Decl)> = before
        .iter()
        .map(|d| (promise.renamed(&d.name), d.to_decl()))
        .collect();
    let was_by_name: BTreeMap<&str, &Decl> = was.iter().map(|(n, d)| (n.as_str(), d)).collect();
    let now_names: std::collections::BTreeSet<&str> =
        after.iter().map(|d| d.name.as_str()).collect();
    let mut diff = HashDiff::default();
    for d in after {
        let now = d.to_decl();
        match was_by_name.get(d.name.as_str()) {
            None => diff.added.push(d.name.clone()),
            Some(was) => {
                if !promise.keeps(was, &now) {
                    diff.changed.push(HashChange {
                        name: d.name.clone(),
                        kind: d.kind,
                        was: was.hash,
                        now: d.hash,
                    });
                } else if was.hash != now.hash {
                    diff.proofs_changed.push(d.name.clone());
                }
            }
        }
    }
    for (name, _) in &was {
        if !now_names.contains(name.as_str()) {
            diff.removed.push(name.clone());
        }
    }
    // Declarations generated from a changed or re-proved one (`f.eq1`, a
    // lifted `match`) aren't more places to look.
    let under = |name: &str, owners: &[String]| {
        owners.iter().any(|o| {
            name.len() > o.len() && name.starts_with(o.as_str()) && name.as_bytes()[o.len()] == b'.'
        })
    };
    let changed_owners: Vec<String> = diff.changed.iter().map(|c| c.name.clone()).collect();
    let proof_owners = diff.proofs_changed.clone();
    let all_owners: Vec<String> = changed_owners
        .iter()
        .chain(&proof_owners)
        .cloned()
        .collect();
    diff.changed.retain(|c| !under(&c.name, &changed_owners));
    diff.proofs_changed.retain(|n| !under(n, &proof_owners));
    diff.added.retain(|n| !under(n, &all_owners));
    diff.removed.retain(|n| !under(n, &all_owners));
    let common_before: Vec<&str> = was
        .iter()
        .map(|(n, _)| n.as_str())
        .filter(|n| now_names.contains(n))
        .collect();
    let common_after: Vec<&str> = after
        .iter()
        .map(|d| d.name.as_str())
        .filter(|n| was_by_name.contains_key(n))
        .collect();
    diff.reordered = common_before != common_after;
    diff
}
