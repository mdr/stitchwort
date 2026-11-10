//! Declarations' content hashes, listed and compared: what a sweep over
//! many files needs to show that every declaration kept its meaning
//! (docs/proposals/theorem-binders.md §5).
//!
//! A project's list comes from [`crate::live::LiveProject::declaration_hashes`]
//! and the library's from [`library_hashes`]. [`compare`] matches two lists
//! by name and applies a [`Promise`], as the project trial does. The
//! library is read once per process, so "before" and "after" a library edit
//! are two processes' lists (`stitchwort trial-edits --std-dir`).

use std::collections::{BTreeMap, BTreeSet};

use stitchwort_core::hash::{ContentHash, data_hash, def_hash, type_hash};
use stitchwort_core::{DataId, DefId};

use stitchwort_elab::search::{constants, data_types};

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
    /// The declarations a definition's type and body mention, by full
    /// name, so a comparison can say which re-proved theorem a moved
    /// definition leads to. Empty for a data type, and where the list
    /// came from JSON without them.
    pub uses: Vec<String>,
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
            uses: Vec::new(),
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
            uses: Vec::new(),
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
            uses: def_uses(g, i),
        });
    }
    out
}

/// What definition `i`'s type and body mention, by full name.
pub(crate) fn def_uses(g: &stitchwort_core::Ev, i: usize) -> Vec<String> {
    let def = &g.env.defs()[i];
    let mut terms = vec![def.ty()];
    terms.extend(def.body().map(|b| b.as_ref()));
    let mut uses = BTreeSet::new();
    for t in terms {
        for d in constants(t) {
            if d.0 != i {
                uses.insert(g.env.defs()[d.0].path().to_string());
            }
        }
        for d in data_types(t) {
            uses.insert(g.env.datas()[d].path().to_string());
        }
    }
    uses.into_iter().collect()
}

/// The core and every library file of the library this process reads, loaded
/// from source, with the hash of each declaration. The error is what failed
/// to load.
pub fn library_hashes(stack: usize) -> Result<Vec<DeclHash>, String> {
    let session = Session::try_eager_library_for_stack(stack)?;
    Ok(session_hashes(&session, (0, 0)))
}

/// The declaration a generated one (`t.%match1`, a lifted `match`) is
/// part of: itself if it isn't generated.
pub fn owner(name: &str) -> &str {
    match name.find(".%") {
        Some(at) => &name[..at],
        None => name,
    }
}

/// A declaration that exists on both sides whose hash isn't what the
/// promise says.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HashChange {
    pub name: String,
    pub kind: DeclKind,
    pub was: Option<ContentHash>,
    pub now: Option<ContentHash>,
    /// Another changed declaration this one mentions, if any (when `after`
    /// lists what each mentions): then it may have changed only because of
    /// that one.
    pub uses: Option<String>,
    /// The theorems whose proof changed (and whose statement held) that it
    /// mentions, directly or through other such theorems, and that mention
    /// no other: a definition's hash covers the proofs it mentions, so one
    /// of these may be why it moved. A name generated from a theorem
    /// (`t.%match1`) is part of its proof.
    pub reproved: Vec<String>,
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
    let now_names: BTreeSet<&str> = after.iter().map(|d| d.name.as_str()).collect();
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
                        uses: None,
                        reproved: Vec::new(),
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
    // Every re-proved declaration, and every declaration generated from
    // one (a lifted `match` is part of its theorem's proof, whatever its
    // own kind), for the cones.
    let reproved_all: BTreeSet<String> = proof_owners
        .iter()
        .cloned()
        .chain(
            diff.changed
                .iter()
                .filter(|c| under(&c.name, &proof_owners))
                .map(|c| c.name.clone()),
        )
        .collect();
    let uses_of: BTreeMap<&str, &[String]> = after
        .iter()
        .map(|d| (d.name.as_str(), d.uses.as_slice()))
        .collect();
    // A theorem's own lifted `match` is part of its proof.
    diff.changed.retain(|c| !under(&c.name, &all_owners));
    let changed_names: BTreeSet<String> = diff.changed.iter().map(|c| c.name.clone()).collect();
    for c in &mut diff.changed {
        let mentioned = uses_of.get(c.name.as_str()).copied().unwrap_or(&[]);
        // Through re-proved declarations, and through those generated from
        // this one (a recursive definition's `decreasing` proofs).
        let own = std::slice::from_ref(&c.name);
        let follow = |u: &str| reproved_all.contains(u) || under(u, own);
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        let mut todo: Vec<&str> = mentioned
            .iter()
            .map(String::as_str)
            .filter(|u| follow(u))
            .collect();
        while let Some(name) = todo.pop() {
            if !seen.insert(name) {
                continue;
            }
            for u in uses_of.get(name).copied().unwrap_or(&[]) {
                if follow(u) && !seen.contains(u.as_str()) {
                    todo.push(u);
                }
            }
        }
        // Another change it or its cone mentions: a re-proved theorem may
        // have been re-proved because of it.
        c.uses = mentioned
            .iter()
            .chain(
                seen.iter()
                    .flat_map(|n| uses_of.get(n).copied().unwrap_or(&[])),
            )
            .find(|u| changed_names.contains(*u) && !under(u, own) && **u != c.name)
            .cloned();
        // Only where the change starts: a re-proved theorem whose proof,
        // its lifted matches included (which may call it back), mentions
        // another may have been re-proved because of it.
        let outside: BTreeSet<&str> = seen
            .iter()
            .filter(|n| {
                uses_of
                    .get(**n)
                    .copied()
                    .unwrap_or(&[])
                    .iter()
                    .any(|u| reproved_all.contains(u) && owner(u) != owner(n))
            })
            .map(|n| owner(n))
            .collect();
        c.reproved = seen
            .iter()
            .filter(|n| reproved_all.contains(**n) && !outside.contains(owner(n)))
            .map(|n| n.to_string())
            .collect();
    }
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
