//! The check cache, stage 1 (docs/proposals/check-cache.md): a standard
//! library file's elaborated result, kept between runs, so a later run loads
//! it instead of elaborating the file again.
//!
//! - **What an entry holds** (§5.1): everything loading the file adds that
//!   later code reads. That is the kernel's new definitions and data types,
//!   with every flag, and the elaborator's side tables: the names it
//!   declares, records, interfaces, instances, abilities, the data types'
//!   owners, why `==`/`show`/`compare` aren't derived, lifted helpers,
//!   local definitions' keys, and what code navigation recorded.
//!   Declarations are referred to by full path and the content hash they
//!   are expected to have, never by load-order ids, and spans as (file
//!   path, byte range).
//! - **Loading is replay** (§5.2): the declarations go to the kernel through
//!   the same `declare_*`/`define_*` functions the elaborator uses, so the
//!   kernel checks every one again (option A, D277). Only elaboration is
//!   skipped. `Elaborator::admit_replayed` is the one place that submits
//!   them.
//! - **The key** (§4.2) is computed before anything is elaborated: the
//!   compiler build, the format, the modes and limits that change results,
//!   the file's path and text (and the core's), and the keys of the library
//!   files it needs.
//! - **An entry that doesn't fit is a miss**: a corrupt one (checksum), one
//!   for another key or cache directory (salt), one whose dependencies don't
//!   have the expected hashes, or one the kernel refuses (whose effects are
//!   undone). The file is then elaborated, and the entry rewritten.
//!
//! This module only encodes and replays. Where entries are kept is the
//! [`Store`] a host gives the elaborator (the CLI's is a directory).

mod codec;
mod dump;

use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use stitchwort_core::check as kernel;
use stitchwort_core::globals::State;
use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::registry::Builtin;
use stitchwort_core::{DataId, DefId, Globals, Name, Sort, Term};
use stitchwort_syntax::{FileId, Span};

use crate::effects::AbilityInfo;
use crate::interfaces::{InstanceInfo, InstanceParam, InterfaceInfo};
use crate::library::PendingKind;
use crate::nav::{LocalUse, Noted};
use crate::records::RecordInfo;
use crate::scope::ScopeOp;
use crate::{Elaborator, Global};
use codec::{Bad, Read, ReadRefs, Reader, Refs, TermWriter, Terms, Writer, bad};

/// The version of the entry format, part of every key: a change to what an
/// entry holds or how it is written bumps it, and old entries are misses.
pub const FORMAT: u32 = 1;

const MAGIC: &[u8; 8] = b"SWCHECK\0";

/// A dependency in an entry's header: kind (0 a definition, 1 a data
/// type), full path, and the content hash it must have.
type Dep = (u8, String, ContentHash);

/// A key: a BLAKE3 hash.
pub type Key = [u8; 32];

/// Where entries are kept, by unit (a library file) and key.
pub trait Store {
    /// The compiler build, part of every key: its version and a
    /// fingerprint of its source.
    fn compiler(&self) -> &str;
    /// The cache directory's random salt (§3.1): an entry written with
    /// another is a miss.
    fn salt(&self) -> [u8; 16];
    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>>;
    /// Best effort: a cache that can't be written just means elaborating
    /// again next time.
    fn write(&self, unit: &str, key: &Key, entry: &[u8]);
}

/// What the cache did in a session.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// Library files loaded from an entry.
    pub hits: usize,
    /// Library files elaborated: no entry, or one that didn't fit.
    pub misses: usize,
    /// Entries written.
    pub written: usize,
    /// Library files elaborated that can't be cached (see
    /// `Elaborator::encode_library_file`).
    pub uncacheable: usize,
}

/// What a library file's load is compared against, to see what it added.
pub(crate) struct Before {
    defs: usize,
    datas: usize,
    abilities: usize,
    lifted: usize,
    tests: usize,
    scope: HashMap<String, (Global, Span)>,
    instances: HashMap<(DataId, DataId), (DefId, bool)>,
    helper_keys: HashSet<String>,
    /// The sizes of the tables keyed by data type (`by_data`).
    by_data: Vec<usize>,
    nav: Option<(usize, usize, usize)>,
}

impl Elaborator {
    /// Keeps library files' results in `store` between runs, and loads them
    /// from it (see [`crate::cache`]).
    pub fn set_check_cache(&mut self, store: Rc<dyn Store>) {
        self.check_cache = Some(store);
    }

    /// What the cache has done so far.
    pub fn check_cache_stats(&self) -> Stats {
        self.cache_stats
    }

    /// Whether library files may be loaded from, and written to, the cache
    /// now. Not for the library test target, whose tests are part of the
    /// result. (A session whose core isn't the index's finds its entries'
    /// dependencies have other hashes: misses.)
    fn cache_usable(&self) -> bool {
        self.check_cache.is_some() && !self.library_tests
    }

    /// The name of the unit an entry is for: the library file, and whether
    /// navigation is recorded (an entry made without it can't give it).
    fn cache_unit(&self, f: usize) -> String {
        let index = self.library_index().expect("a library is installed");
        let path = index.files[f]
            .path
            .trim_end_matches(".sw")
            .replace('/', ".");
        let nav = if self.nav.is_some() { "+nav" } else { "" };
        format!("std.{path}{nav}")
    }

    /// The key of library file `f` (§4.2), and of the files it needs.
    pub(crate) fn library_key(&self, f: usize) -> Key {
        let index = self.library_index().expect("a library is installed");
        let store = self.check_cache.as_ref().expect("a cache is set");
        let mut keys: HashMap<usize, Key> = HashMap::new();
        // Dependencies first: the edges never form a cycle (the index is
        // checked), so a work list in post-order ends.
        let mut stack = vec![(f, false)];
        while let Some((file, ready)) = stack.pop() {
            if keys.contains_key(&file) {
                continue;
            }
            if !ready {
                stack.push((file, true));
                stack.extend(index.files[file].edges.iter().map(|&e| (e, false)));
                continue;
            }
            let mut h = blake3::Hasher::new();
            let mut part = |bytes: &[u8]| {
                h.update(&(bytes.len() as u64).to_le_bytes());
                h.update(bytes);
            };
            part(b"stitchwort check cache");
            part(&FORMAT.to_le_bytes());
            part(store.compiler().as_bytes());
            part(self.modes().as_bytes());
            part(index.files[0].text.as_bytes());
            part(index.files[file].path.as_bytes());
            part(index.files[file].text.as_bytes());
            for e in &index.files[file].edges {
                part(&keys[e]);
            }
            keys.insert(file, *h.finalize().as_bytes());
        }
        keys[&f]
    }

    /// Everything else that changes what elaborating a library file gives.
    fn modes(&self) -> String {
        let g = &self.globals;
        let l = self.limits;
        format!(
            "natives {} compact {} succ {} limits {} {} {} {} rewrite {:?} instances {:?} uniform {} nav {}",
            !g.builtins.disable_natives,
            g.builtins.compact_literals().is_some(),
            self.numbers_as_succ,
            l.work,
            l.stack,
            l.size,
            l.frames,
            self.rewrite_budget,
            self.instance_budget,
            self.uniform_operators,
            self.nav.is_some(),
        )
    }

    /// Before library file `f` loads: whether to try the cache, and if
    /// so, its unit and key.
    pub(crate) fn cache_lookup(&self, f: usize) -> Option<(String, Key)> {
        if !self.cache_usable() {
            return None;
        }
        Some((self.cache_unit(f), self.library_key(f)))
    }

    /// Loads library file `f` from the entry for `key`, if there is one and
    /// it fits; `false` if it has to be elaborated instead (and then
    /// nothing has changed).
    pub(crate) fn load_from_cache(&mut self, f: usize, unit: &str, key: &Key) -> bool {
        let store = self.check_cache.clone().expect("a cache is set");
        let Some(bytes) = store.read(unit, key) else {
            self.cache_stats.misses += 1;
            return false;
        };
        match self.replay(f, &bytes, key, store.salt()) {
            Ok(()) => {
                self.cache_stats.hits += 1;
                true
            }
            Err(Bad(_why)) => {
                self.cache_stats.misses += 1;
                false
            }
        }
    }

    /// What to compare with once library file `f` has loaded, to see what
    /// it added; and starts noting the names it declares.
    pub(crate) fn cache_before(&mut self) -> Before {
        self.scope.log = Some(Vec::new());
        Before {
            defs: self.globals.defs.len(),
            datas: self.globals.datas.len(),
            abilities: self.abilities.len(),
            lifted: self.lifted.len(),
            tests: self.tests.len(),
            scope: self.scope.entries.clone(),
            instances: self
                .instances
                .iter()
                .map(|(k, v)| (*k, (v.def, v.valid)))
                .collect(),
            helper_keys: self.helper_keys.clone(),
            by_data: self.by_data().iter().map(|t| t.len()).collect(),
            nav: self.nav.as_ref().map(|nav| {
                let nav = nav.borrow();
                (nav.locals.len(), nav.binders.len(), nav.outline.len())
            }),
        }
    }

    /// The side tables keyed by data type, as `(data type, row)` lists:
    /// records, interfaces, owners, and why `==`, `show` and `compare`
    /// aren't derived. Loading a file only adds rows for its own types.
    fn by_data(&self) -> Vec<Vec<DataId>> {
        vec![
            self.records.keys().copied().collect(),
            self.interfaces.keys().copied().collect(),
            self.data_owners.keys().copied().collect(),
            self.no_eq.keys().copied().collect(),
            self.no_show.keys().copied().collect(),
            self.no_ord.keys().copied().collect(),
        ]
    }

    /// After library file `f` loaded: writes its entry, if it checked and
    /// can be cached.
    pub(crate) fn cache_after(
        &mut self,
        f: usize,
        before: Before,
        ok: bool,
        unit: &str,
        key: &Key,
    ) {
        let log = self.scope.log.take().unwrap_or_default();
        if !ok {
            return;
        }
        let store = self.check_cache.clone().expect("a cache is set");
        match self.encode_library_file(f, &before, &log, key, store.salt()) {
            Ok(entry) => {
                store.write(unit, key, &entry);
                self.cache_stats.written += 1;
            }
            Err(_why) => self.cache_stats.uncacheable += 1,
        }
    }
}

// ---- Writing --------------------------------------------------------------

/// How an entry refers to declarations and files while it is written.
struct Out<'g> {
    g: &'g Globals,
    base_defs: usize,
    base_datas: usize,
    /// Declarations outside the entry, by their place in `deps`.
    ext_defs: HashMap<DefId, usize>,
    ext_datas: HashMap<DataId, usize>,
    /// What the entry depends on: kind (0 a definition, 1 a data type),
    /// full path, and content hash.
    deps: Vec<Dep>,
    /// How many final definitions and data types have each path: only a
    /// path that names one declaration can be a reference.
    def_paths: HashMap<&'g str, usize>,
    data_paths: HashMap<&'g str, usize>,
    /// The library's files, by id, as their place in the index.
    std_files: HashMap<FileId, usize>,
    files: Vec<usize>,
    file_ids: HashMap<FileId, usize>,
    /// Why this can't be cached, once something can't be written.
    problem: Option<String>,
}

impl Out<'_> {
    fn fail(&mut self, why: String) {
        if self.problem.is_none() {
            self.problem = Some(why);
        }
    }
}

impl Refs for Out<'_> {
    fn def(&mut self, w: &mut Writer, id: DefId) {
        if id.0 >= self.base_defs {
            w.uint(((id.0 - self.base_defs) as u64) << 1);
            return;
        }
        if let Some(&i) = self.ext_defs.get(&id) {
            w.uint(((i as u64) << 1) | 1);
            return;
        }
        let def = self.g.def(id);
        let hash = match def_hash(self.g, id) {
            Ok(Some(hash)) => hash,
            _ => {
                self.fail(format!("`{}` has no content hash", def.path));
                ContentHash([0; 32])
            }
        };
        if self.def_paths.get(&*def.path) != Some(&1) {
            self.fail(format!("`{}` names more than one definition", def.path));
        }
        let i = self.deps.len();
        self.deps.push((0, def.path.to_string(), hash));
        self.ext_defs.insert(id, i);
        w.uint(((i as u64) << 1) | 1);
    }

    fn data(&mut self, w: &mut Writer, id: DataId) {
        if id.0 >= self.base_datas {
            w.uint(((id.0 - self.base_datas) as u64) << 1);
            return;
        }
        if let Some(&i) = self.ext_datas.get(&id) {
            w.uint(((i as u64) << 1) | 1);
            return;
        }
        let data = self.g.data(id);
        let hash = match data_hash(self.g, id) {
            Ok(Some(hash)) => hash,
            _ => {
                self.fail(format!("`{}` has no content hash", data.path));
                ContentHash([0; 32])
            }
        };
        if self.data_paths.get(&*data.path) != Some(&1) {
            self.fail(format!("`{}` names more than one data type", data.path));
        }
        let i = self.deps.len();
        self.deps.push((1, data.path.to_string(), hash));
        self.ext_datas.insert(id, i);
        w.uint(((i as u64) << 1) | 1);
    }

    fn span(&mut self, w: &mut Writer, span: Span) {
        let file = match self.file_ids.get(&span.file) {
            Some(&i) => i,
            None => match self.std_files.get(&span.file) {
                Some(&f) => {
                    self.files.push(f);
                    self.file_ids.insert(span.file, self.files.len() - 1);
                    self.files.len() - 1
                }
                None => {
                    self.fail("a span outside the library".to_string());
                    0
                }
            },
        };
        if span.end < span.start {
            self.fail("a span that ends before it starts".to_string());
        }
        w.usize(file);
        w.uint(u64::from(span.start));
        w.uint(u64::from(span.end.saturating_sub(span.start)));
    }
}

/// An entry's parts while it is written: the terms and strings, and the
/// rest.
struct Encoding<'g> {
    out: Out<'g>,
    terms: TermWriter,
    w: Writer,
}

impl Encoding<'_> {
    fn str(&mut self, s: &str) {
        let i = self.terms.string(s);
        self.w.uint(u64::from(i));
    }

    fn term(&mut self, t: &Term) {
        match self.terms.term(&mut self.out, t) {
            Ok(id) => self.w.uint(u64::from(id)),
            Err(_) => self.out.fail("a term with a metavariable".to_string()),
        }
    }

    fn def(&mut self, id: DefId) {
        self.out.def(&mut self.w, id);
    }

    fn data(&mut self, id: DataId) {
        self.out.data(&mut self.w, id);
    }

    fn span(&mut self, span: Span) {
        self.out.span(&mut self.w, span);
    }

    fn global(&mut self, e: &Elaborator, global: Global) {
        match global {
            Global::Def(id) => {
                self.w.u8(0);
                self.def(id);
            }
            Global::Data(d) => {
                self.w.u8(1);
                self.data(d);
            }
            Global::Ctor(d, c) => {
                self.w.u8(2);
                self.data(d);
                self.w.usize(c);
            }
            Global::Ability(i) => {
                self.w.u8(3);
                self.data(e.abilities[i].op_data);
            }
            Global::Op(i, j) => {
                self.w.u8(4);
                self.data(e.abilities[i].op_data);
                self.w.usize(j);
            }
            Global::Pending(f, kind) => {
                self.w.u8(5);
                self.w.usize(f);
                self.w.u8(pending_tag(kind));
            }
            Global::Unchecked(_) | Global::Failed => {
                self.out.fail("a name that failed".to_string());
                self.w.u8(6);
            }
        }
    }
}

fn pending_tag(kind: PendingKind) -> u8 {
    match kind {
        PendingKind::Def => 0,
        PendingKind::Data => 1,
        PendingKind::Ctor => 2,
        PendingKind::Op => 3,
        PendingKind::Other => 4,
    }
}

fn pending_kind(tag: u8) -> Read<PendingKind> {
    Ok(match tag {
        0 => PendingKind::Def,
        1 => PendingKind::Data,
        2 => PendingKind::Ctor,
        3 => PendingKind::Op,
        4 => PendingKind::Other,
        _ => return bad("an unknown kind of pending name"),
    })
}

impl Elaborator {
    /// The entry for library file `f`, which has just loaded without
    /// errors, or why it can't be cached: a declaration the kernel didn't
    /// admit, a built-in bound or an export made (the library has none, so
    /// this isn't encoded), a test kept, or a reference that can't be
    /// written by path.
    fn encode_library_file(
        &self,
        f: usize,
        before: &Before,
        log: &[ScopeOp],
        key: &Key,
        salt: [u8; 16],
    ) -> Result<Vec<u8>, String> {
        let g = &self.globals;
        let index = self.library_index().expect("a library is installed");
        let _op = g.budget.operation(self.limits);
        let (defs, datas) = (before.defs..g.defs.len(), before.datas..g.datas.len());
        for id in defs.clone().map(DefId) {
            let def = g.def(id);
            if def.state() != State::Final || def.body().is_none() {
                return Err(format!("`{}` isn't admitted with a body", def.path));
            }
            if def.export || !def.validators.is_empty() {
                return Err(format!("`{}` is exported", def.path));
            }
            if g.registry.def_builtin(id).is_some() || g.builtins.primitive(id).is_some() {
                return Err(format!("`{}` is a built-in", def.path));
            }
        }
        for d in datas.clone().map(DataId) {
            let data = g.data(d);
            if data.state() != State::Final || !data.validators.is_empty() {
                return Err(format!("`{}` isn't admitted plainly", data.path));
            }
            if Builtin::ALL.iter().any(|b| g.registry.data(*b) == Some(d)) {
                return Err(format!("`{}` is a built-in", data.path));
            }
        }
        if self.tests.len() != before.tests {
            return Err("a test was kept".to_string());
        }
        let old_rows = self
            .by_data()
            .iter()
            .map(|t| t.iter().filter(|d| d.0 < before.datas).count())
            .collect::<Vec<_>>();
        if old_rows != before.by_data {
            return Err("a row for an older data type changed".to_string());
        }
        if self.instances.iter().any(|(k, v)| {
            before
                .instances
                .get(k)
                .is_some_and(|old| *old != (v.def, v.valid))
        }) {
            return Err("an instance from before changed".to_string());
        }

        let mut def_paths: HashMap<&str, usize> = HashMap::new();
        for def in &g.defs {
            *def_paths.entry(&def.path).or_default() += 1;
        }
        let mut data_paths: HashMap<&str, usize> = HashMap::new();
        for data in &g.datas {
            *data_paths.entry(&data.path).or_default() += 1;
        }
        let mut e = Encoding {
            out: Out {
                g,
                base_defs: before.defs,
                base_datas: before.datas,
                ext_defs: HashMap::new(),
                ext_datas: HashMap::new(),
                deps: Vec::new(),
                def_paths,
                data_paths,
                std_files: index
                    .files
                    .iter()
                    .enumerate()
                    .map(|(i, f)| (f.id, i))
                    .collect(),
                files: Vec::new(),
                file_ids: HashMap::new(),
                problem: None,
            },
            terms: TermWriter::default(),
            w: Writer::default(),
        };

        // The kernel's declarations.
        e.w.usize(defs.len());
        for id in defs.clone().map(DefId) {
            let def = g.def(id);
            e.str(&def.name);
            e.str(&def.path);
            e.w.bool(def.theorem);
            e.w.bool(def.instance);
            e.w.bool(def.fold);
            e.span(def.span);
            e.term(&def.ty);
            e.term(def.body().expect("checked above"));
            let group = def.group.as_ref().expect("a final definition has a group");
            e.w.usize(group.len());
            for m in group.iter() {
                if m.0 < before.defs {
                    return Err(format!("`{}`'s group is older", def.path));
                }
                e.w.usize(m.0 - before.defs);
            }
        }
        e.w.usize(datas.len());
        for d in datas.clone().map(DataId) {
            let data = g.data(d);
            e.str(&data.name);
            e.str(&data.path);
            e.w.usize(data.params.len());
            for (x, ty) in &data.params {
                e.str(x);
                e.term(ty);
            }
            e.w.usize(data.auto_params.len());
            for a in &data.auto_params {
                e.w.bool(*a);
            }
            e.w.usize(data.indices.len());
            for (x, ty) in &data.indices {
                e.str(x);
                e.term(ty);
            }
            codec::sort(&mut e.w, data.sort);
            e.w.usize(data.ctors.len());
            for ctor in &data.ctors {
                e.str(&ctor.name);
                e.w.usize(ctor.fields.len());
                for (x, ty) in &ctor.fields {
                    e.str(x);
                    e.term(ty);
                }
                e.w.usize(ctor.implicit.len());
                for i in &ctor.implicit {
                    e.w.bool(*i);
                }
                e.w.usize(ctor.result.len());
                for r in &ctor.result {
                    e.term(r);
                }
            }
            e.w.bool(data.record);
            e.w.usize(data.group.len());
            for m in data.group.iter() {
                if m.0 < before.datas {
                    return Err(format!("`{}`'s group is older", data.path));
                }
                e.w.usize(m.0 - before.datas);
            }
            if data.defs_before < before.defs || data.datas_before < before.datas {
                return Err(format!("`{}` is declared before the file", data.path));
            }
            e.w.usize(data.defs_before - before.defs);
            e.w.usize(data.datas_before - before.datas);
            e.span(data.span);
        }

        // The names: those that changed, then the new ones in the order
        // they were declared, then the members marked.
        let mut changed: Vec<(&String, &(Global, Span))> = self
            .scope
            .entries
            .iter()
            .filter(|(k, v)| before.scope.get(*k).is_some_and(|old| old != *v))
            .collect();
        changed.sort_by_key(|(k, _)| *k);
        e.w.usize(changed.len());
        for (k, (global, span)) in changed {
            e.str(k);
            e.global(self, *global);
            e.span(*span);
        }
        let new: Vec<(&str, bool)> = log
            .iter()
            .filter_map(|op| match op {
                ScopeOp::New(k, follower) => Some((k.as_str(), *follower)),
                ScopeOp::Member(_) => None,
            })
            .collect();
        e.w.usize(new.len());
        for (k, follower) in new {
            let Some((global, span)) = self.scope.entries.get(k) else {
                return Err(format!("`{k}` was declared and is gone"));
            };
            e.str(k);
            e.global(self, *global);
            e.span(*span);
            e.w.bool(follower);
        }
        let members: Vec<&str> = log
            .iter()
            .filter_map(|op| match op {
                ScopeOp::Member(k) => Some(k.as_str()),
                ScopeOp::New(..) => None,
            })
            .collect();
        e.w.usize(members.len());
        for k in members {
            e.str(k);
        }

        // The elaborator's tables.
        let new_data = |d: &DataId| d.0 >= before.datas;
        let mut records: Vec<(&DataId, &RecordInfo)> =
            self.records.iter().filter(|(d, _)| new_data(d)).collect();
        records.sort_by_key(|(d, _)| d.0);
        e.w.usize(records.len());
        for (d, info) in records {
            e.data(*d);
            e.w.usize(info.projections.len());
            for p in &info.projections {
                e.w.bool(p.is_some());
                if let Some(p) = p {
                    e.def(*p);
                }
            }
        }
        let mut interfaces: Vec<(&DataId, &InterfaceInfo)> = self
            .interfaces
            .iter()
            .filter(|(d, _)| new_data(d))
            .collect();
        interfaces.sort_by_key(|(d, _)| d.0);
        e.w.usize(interfaces.len());
        for (d, info) in interfaces {
            e.data(*d);
            e.str(&info.dict);
            e.w.usize(info.supers.len());
            for (i, s) in &info.supers {
                e.w.usize(*i);
                e.data(*s);
            }
            e.w.usize(info.projections.len());
            for p in &info.projections {
                e.def(*p);
            }
            e.w.usize(info.methods.len());
            for m in &info.methods {
                e.def(*m);
            }
            e.w.usize(info.relations.len());
            for (r, d) in &info.relations {
                e.w.usize(*r);
                e.w.usize(*d);
            }
        }
        let mut instances: Vec<(&(DataId, DataId), &InstanceInfo)> = self
            .instances
            .iter()
            .filter(|(k, _)| !before.instances.contains_key(k))
            .collect();
        instances.sort_by_key(|(k, _)| (k.0.0, k.1.0));
        e.w.usize(instances.len());
        for ((iface, head), info) in instances {
            e.data(*iface);
            e.data(*head);
            e.def(info.def);
            e.str(&info.name);
            e.span(info.span);
            e.w.usize(info.params.len());
            for p in &info.params {
                match p {
                    InstanceParam::Head(k) => {
                        e.w.u8(0);
                        e.w.usize(*k);
                    }
                    InstanceParam::Prerequisite => e.w.u8(1),
                }
            }
            e.w.bool(info.valid);
        }
        for table in [&self.data_owners, &self.no_eq, &self.no_show, &self.no_ord] {
            let mut rows: Vec<(&DataId, &String)> =
                table.iter().filter(|(d, _)| new_data(d)).collect();
            rows.sort_by_key(|(d, _)| d.0);
            e.w.usize(rows.len());
            for (d, s) in rows {
                e.data(*d);
                e.str(s);
            }
        }
        e.w.usize(self.abilities.len() - before.abilities);
        for a in &self.abilities[before.abilities..] {
            e.str(&a.name);
            e.data(a.op_data);
            e.def(a.res);
            e.def(a.elim);
            e.w.usize(a.ops.len());
            for op in &a.ops {
                e.str(op);
            }
            e.w.bool(a.order.0);
            e.str(&a.order.1);
        }
        e.w.usize(self.lifted.len() - before.lifted);
        for (id, span) in &self.lifted[before.lifted..] {
            e.def(*id);
            e.span(*span);
        }
        let mut helpers: Vec<&String> = self.helper_keys.difference(&before.helper_keys).collect();
        helpers.sort();
        e.w.usize(helpers.len());
        for k in helpers {
            e.str(k);
        }

        // What code navigation recorded in the file.
        let file_id = index.files[f].id;
        match (&self.nav, before.nav) {
            (Some(nav), Some((locals, binders, outline))) => {
                let nav = nav.borrow();
                if !nav.pending.is_empty() || nav.outline.len() != outline {
                    return Err("navigation left something unfinished".to_string());
                }
                e.w.bool(true);
                let mut refs: Vec<(&Span, &Noted)> = nav
                    .refs
                    .iter()
                    .filter(|(at, _)| at.file == file_id)
                    .collect();
                refs.sort_by_key(|(at, _)| (at.start, at.end));
                e.w.usize(refs.len());
                for (at, noted) in refs {
                    e.span(*at);
                    e.str(&noted.key);
                    e.span(noted.target);
                    e.global(self, noted.global);
                    e.w.bool(noted.dot.is_some());
                    if let Some(dot) = &noted.dot {
                        e.str(dot);
                    }
                }
                let mut types: Vec<(&(FileId, u32), &String)> = nav
                    .local_types
                    .iter()
                    .filter(|((file, _), _)| *file == file_id)
                    .collect();
                types.sort_by_key(|((_, at), _)| *at);
                e.w.usize(types.len());
                for ((_, at), ty) in types {
                    e.w.uint(u64::from(*at));
                    e.str(ty);
                }
                for uses in [&nav.locals[locals..], &nav.binders[binders..]] {
                    e.w.usize(uses.len());
                    for u in uses {
                        e.span(u.span);
                        e.str(&u.name);
                        e.span(u.binder);
                    }
                }
                let mut fields: Vec<(&(Span, String), &Span)> = nav
                    .field_spans
                    .iter()
                    .filter(|((at, _), _)| at.file == file_id)
                    .collect();
                fields.sort_by_key(|((at, name), _)| (at.start, at.end, name.as_str()));
                e.w.usize(fields.len());
                for ((at, name), span) in fields {
                    e.span(*at);
                    e.str(name);
                    e.span(*span);
                }
            }
            (None, None) => e.w.bool(false),
            _ => return Err("navigation was turned on while loading".to_string()),
        }

        if let Some(problem) = e.out.problem {
            return Err(problem);
        }
        // The body: strings, files, terms, then the rest.
        let mut body = Writer::default();
        body.usize(e.terms.strings.len());
        for s in &e.terms.strings {
            body.str(s);
        }
        body.usize(e.out.files.len());
        for &file in &e.out.files {
            body.str(&index.files[file].path);
        }
        body.usize(e.terms.node_count());
        body.raw(&e.terms.nodes.bytes);
        body.raw(&e.w.bytes);
        Ok(seal(key, salt, &e.out.deps, &body.bytes))
    }
}

/// The whole entry: the header, the body and a checksum (§5.3).
fn seal(key: &Key, salt: [u8; 16], deps: &[Dep], body: &[u8]) -> Vec<u8> {
    let mut w = Writer::default();
    w.raw(MAGIC);
    w.raw(&FORMAT.to_le_bytes());
    w.raw(key);
    w.raw(&salt);
    w.usize(deps.len());
    for (kind, path, hash) in deps {
        w.u8(*kind);
        w.str(path);
        w.raw(&hash.0);
    }
    w.blob(body);
    let sum = blake3::hash(&w.bytes);
    w.raw(sum.as_bytes());
    w.bytes
}

/// The header's dependencies and the body, if `bytes` is a whole entry for
/// `key` written with `salt`.
fn open<'a>(bytes: &'a [u8], key: &Key, salt: [u8; 16]) -> Read<(Vec<Dep>, &'a [u8])> {
    if bytes.len() < 32 {
        return bad("too short");
    }
    let (content, sum) = bytes.split_at(bytes.len() - 32);
    if blake3::hash(content).as_bytes() != sum {
        return bad("the checksum doesn't match");
    }
    let mut r = Reader::new(content);
    if r.raw(MAGIC.len())? != MAGIC {
        return bad("not an entry");
    }
    if r.array::<4>()? != FORMAT.to_le_bytes() {
        return bad("another format");
    }
    if &r.array::<32>()? != key {
        return bad("another key");
    }
    if r.array::<16>()? != salt {
        return bad("another cache's entry");
    }
    let n = r.count(34)?;
    let mut deps = Vec::with_capacity(n);
    for _ in 0..n {
        let kind = r.u8()?;
        let path = r.string()?;
        deps.push((kind, path, ContentHash(r.array::<32>()?)));
    }
    let body = r.blob()?;
    if !r.done() {
        return bad("bytes after the body");
    }
    Ok((deps, body))
}

// ---- Reading --------------------------------------------------------------

/// How an entry's references are read back in this session.
struct In {
    base_defs: usize,
    base_datas: usize,
    n_defs: usize,
    n_datas: usize,
    ext_defs: Vec<DefId>,
    ext_datas: Vec<DataId>,
    files: Vec<FileId>,
}

impl ReadRefs for In {
    fn def(&self, r: &mut Reader) -> Read<DefId> {
        let v = r.usize()?;
        let i = v >> 1;
        if v & 1 == 0 {
            if i >= self.n_defs {
                return bad("a definition out of range");
            }
            return Ok(DefId(self.base_defs + i));
        }
        self.ext_defs
            .get(i)
            .copied()
            .ok_or_else(|| Bad("a dependency out of range".to_string()))
    }

    fn data(&self, r: &mut Reader) -> Read<DataId> {
        let v = r.usize()?;
        let i = v >> 1;
        if v & 1 == 0 {
            if i >= self.n_datas {
                return bad("a data type out of range");
            }
            return Ok(DataId(self.base_datas + i));
        }
        self.ext_datas
            .get(i)
            .copied()
            .ok_or_else(|| Bad("a dependency out of range".to_string()))
    }

    fn span(&self, r: &mut Reader) -> Read<Span> {
        let Some(&file) = self.files.get(r.usize()?) else {
            return bad("a file out of range");
        };
        let start = r.u32()?;
        let len = r.u32()?;
        let Some(end) = start.checked_add(len) else {
            return bad("a span out of range");
        };
        Ok(Span::new(file, start, end))
    }
}

/// A definition, read.
struct DefEntry {
    name: Name,
    path: Name,
    theorem: bool,
    instance: bool,
    fold: bool,
    span: Span,
    ty: Term,
    body: Term,
    group: Vec<usize>,
}

/// A constructor, read.
struct CtorEntry {
    name: Name,
    fields: Vec<(Name, Term)>,
    implicit: Vec<bool>,
    result: Vec<Term>,
}

/// A data type, read.
struct DataEntry {
    name: Name,
    path: Name,
    params: Vec<(Name, Term)>,
    auto_params: Vec<bool>,
    indices: Vec<(Name, Term)>,
    sort: Sort,
    ctors: Vec<CtorEntry>,
    record: bool,
    group: Vec<usize>,
    defs_before: usize,
    datas_before: usize,
    span: Span,
}

/// A global, read: an ability by its operations' data type, which is
/// found once the abilities are replayed.
#[derive(Clone, Copy)]
enum GlobalEntry {
    Plain(Global),
    Ability(DataId),
    Op(DataId, usize),
}

/// Everything an entry holds besides the kernel's declarations.
struct Tables {
    changed: Vec<(String, GlobalEntry, Span)>,
    new: Vec<(String, GlobalEntry, Span, bool)>,
    members: Vec<String>,
    records: Vec<(DataId, RecordInfo)>,
    interfaces: Vec<(DataId, InterfaceInfo)>,
    instances: Vec<((DataId, DataId), InstanceInfo)>,
    /// `data_owners`, `no_eq`, `no_show`, `no_ord`.
    by_data: [Vec<(DataId, String)>; 4],
    abilities: Vec<AbilityInfo>,
    lifted: Vec<(DefId, Span)>,
    helper_keys: Vec<String>,
    nav: Option<NavEntry>,
}

struct NavEntry {
    refs: Vec<(Span, String, Span, GlobalEntry, Option<String>)>,
    local_types: Vec<(u32, String)>,
    locals: Vec<(Span, String, Span)>,
    binders: Vec<(Span, String, Span)>,
    fields: Vec<(Span, String, Span)>,
}

/// An entry's body being read.
struct Body<'a> {
    r: Reader<'a>,
    terms: Terms,
    refs: In,
}

impl Body<'_> {
    fn str(&mut self) -> Read<Name> {
        self.terms.name(&mut self.r)
    }

    fn string(&mut self) -> Read<String> {
        Ok(self.str()?.to_string())
    }

    fn term(&mut self) -> Read<Term> {
        self.terms.term(&mut self.r)
    }

    fn def(&mut self) -> Read<DefId> {
        self.refs.def(&mut self.r)
    }

    fn data(&mut self) -> Read<DataId> {
        self.refs.data(&mut self.r)
    }

    fn span(&mut self) -> Read<Span> {
        self.refs.span(&mut self.r)
    }

    fn count(&mut self) -> Read<usize> {
        self.r.count(1)
    }

    fn global(&mut self, files: usize) -> Read<GlobalEntry> {
        Ok(match self.r.u8()? {
            0 => GlobalEntry::Plain(Global::Def(self.def()?)),
            1 => GlobalEntry::Plain(Global::Data(self.data()?)),
            2 => GlobalEntry::Plain(Global::Ctor(self.data()?, self.r.usize()?)),
            3 => GlobalEntry::Ability(self.data()?),
            4 => GlobalEntry::Op(self.data()?, self.r.usize()?),
            5 => {
                let f = self.r.usize()?;
                if f >= files {
                    return bad("a library file out of range");
                }
                GlobalEntry::Plain(Global::Pending(f, pending_kind(self.r.u8()?)?))
            }
            _ => return bad("an unknown kind of name"),
        })
    }

    fn named_terms(&mut self) -> Read<Vec<(Name, Term)>> {
        let n = self.count()?;
        (0..n).map(|_| Ok((self.str()?, self.term()?))).collect()
    }

    fn bools(&mut self) -> Read<Vec<bool>> {
        let n = self.count()?;
        (0..n).map(|_| self.r.bool()).collect()
    }

    fn offsets(&mut self, below: usize) -> Read<Vec<usize>> {
        let n = self.count()?;
        (0..n)
            .map(|_| {
                let i = self.r.usize()?;
                if i < below {
                    Ok(i)
                } else {
                    bad("a group member out of range")
                }
            })
            .collect()
    }
}

/// Finds a declaration by its path, if exactly one has it.
fn unique<T: Copy>(map: &HashMap<&str, Option<T>>, path: &str) -> Option<T> {
    map.get(path).copied().flatten()
}

impl Elaborator {
    /// Loads library file `f` from an entry. On any problem, nothing has
    /// changed, and the reason is returned.
    fn replay(&mut self, f: usize, bytes: &[u8], key: &Key, salt: [u8; 16]) -> Read<()> {
        let (deps, body) = open(bytes, key, salt)?;
        let index = self.library_index().expect("a library is installed");
        let g = &self.globals;
        let op = g.budget.operation(self.limits);

        // The dependencies: each path names one final declaration, with the
        // hash it had when the entry was written.
        let mut def_paths: HashMap<&str, Option<DefId>> = HashMap::new();
        for (i, def) in g.defs.iter().enumerate() {
            def_paths
                .entry(&def.path)
                .and_modify(|e| *e = None)
                .or_insert(Some(DefId(i)));
        }
        let mut data_paths: HashMap<&str, Option<DataId>> = HashMap::new();
        for (i, data) in g.datas.iter().enumerate() {
            data_paths
                .entry(&data.path)
                .and_modify(|e| *e = None)
                .or_insert(Some(DataId(i)));
        }
        let mut ext_defs = vec![DefId(usize::MAX); deps.len()];
        let mut ext_datas = vec![DataId(usize::MAX); deps.len()];
        for (i, (kind, path, hash)) in deps.iter().enumerate() {
            let found = match kind {
                0 => unique(&def_paths, path).and_then(|id| {
                    ext_defs[i] = id;
                    def_hash(g, id).ok().flatten()
                }),
                1 => unique(&data_paths, path).and_then(|id| {
                    ext_datas[i] = id;
                    data_hash(g, id).ok().flatten()
                }),
                _ => return bad("an unknown kind of dependency"),
            };
            if found != Some(*hash) {
                return bad(format!("`{path}` isn't what the entry was made with"));
            }
        }

        // The body, read completely before anything changes.
        let mut r = Reader::new(body);
        let strings = Terms::read_strings(&mut r)?;
        let n = r.count(1)?;
        let mut files = Vec::with_capacity(n);
        for _ in 0..n {
            let path = r.string()?;
            match index.files.iter().find(|f| f.path == path) {
                Some(file) => files.push(file.id),
                None => return bad(format!("no library file `{path}`")),
            }
        }
        // The counts of the entry's own declarations come after the terms,
        // which may refer to them: read the terms with room for any, and
        // check the references once the counts are known.
        let node_count = r.count(1)?;
        let mut body = Body {
            r,
            terms: Terms {
                nodes: Vec::new(),
                strings,
            },
            refs: In {
                base_defs: g.defs.len(),
                base_datas: g.datas.len(),
                n_defs: usize::MAX >> 2,
                n_datas: usize::MAX >> 2,
                ext_defs,
                ext_datas,
                files,
            },
        };
        let Body { r, terms, refs } = &mut body;
        terms.read_nodes(r, refs, node_count)?;

        let n = body.count()?;
        let mut defs = Vec::with_capacity(n);
        for _ in 0..n {
            defs.push(DefEntry {
                name: body.str()?,
                path: body.str()?,
                theorem: body.r.bool()?,
                instance: body.r.bool()?,
                fold: body.r.bool()?,
                span: body.span()?,
                ty: body.term()?,
                body: body.term()?,
                group: body.offsets(n)?,
            });
        }
        let n_defs = defs.len();
        let n = body.count()?;
        let mut datas = Vec::with_capacity(n);
        for _ in 0..n {
            let name = body.str()?;
            let path = body.str()?;
            let params = body.named_terms()?;
            let auto_params = body.bools()?;
            let indices = body.named_terms()?;
            let sort = codec::read_sort(&mut body.r)?;
            let k = body.count()?;
            let mut ctors = Vec::with_capacity(k);
            for _ in 0..k {
                let name = body.str()?;
                let fields = body.named_terms()?;
                let implicit = body.bools()?;
                let m = body.count()?;
                let result = (0..m).map(|_| body.term()).collect::<Read<_>>()?;
                ctors.push(CtorEntry {
                    name,
                    fields,
                    implicit,
                    result,
                });
            }
            datas.push(DataEntry {
                name,
                path,
                params,
                auto_params,
                indices,
                sort,
                ctors,
                record: body.r.bool()?,
                group: body.offsets(n)?,
                defs_before: body.r.usize()?,
                datas_before: body.r.usize()?,
                span: body.span()?,
            });
        }
        let n_datas = datas.len();
        body.refs.n_defs = n_defs;
        body.refs.n_datas = n_datas;
        // Every reference the terms make to the entry's own declarations is
        // to one it has.
        let (base_defs, base_datas) = (body.refs.base_defs, body.refs.base_datas);
        for t in &body.terms.nodes {
            let mut ok = true;
            match t.as_ref() {
                Term::Def(id) => ok = id.0 < base_defs + n_defs,
                Term::Data(d, _) | Term::Ctor(d, _, _) | Term::Case(_, d, _) => {
                    ok = d.0 < base_datas + n_datas;
                }
                _ => {}
            }
            if !ok {
                return bad("a term refers to a declaration the entry doesn't have");
            }
        }

        let tables = read_tables(&mut body, index.files.len())?;
        if !body.r.done() {
            return bad("bytes after the tables");
        }
        if tables.nav.is_some() != self.nav.is_some() {
            return bad("navigation recorded or not");
        }
        // Every ability a name refers to is one there will be.
        let abilities: HashSet<DataId> = self
            .abilities
            .iter()
            .chain(&tables.abilities)
            .map(|a| a.op_data)
            .collect();
        let globals = tables.changed.iter().map(|(_, g, _)| g);
        let globals = globals.chain(tables.new.iter().map(|(_, g, _, _)| g));
        let globals = globals.chain(tables.nav.iter().flat_map(|n| n.refs.iter().map(|r| &r.3)));
        for g in globals {
            if let GlobalEntry::Ability(d) | GlobalEntry::Op(d, _) = g
                && !abilities.contains(d)
            {
                return bad("a name refers to an ability there isn't");
            }
        }
        drop(op);

        self.admit_replayed(&defs, &datas)?;
        self.replay_tables(f, tables);
        Ok(())
    }

    /// Submits an entry's declarations to the kernel, through the same
    /// functions the elaborator uses, so it checks each one again: only
    /// elaboration is skipped (option A, D277). This is the one place a
    /// replay reaches the kernel.
    ///
    /// The declarations are made in their original order (a data group
    /// goes where its `defs_before` and `datas_before` say), and each group
    /// is defined as soon as everything it refers to is final, which is no
    /// later than the elaborator defined it. If the kernel refuses
    /// anything, what was added is removed and the file is elaborated
    /// instead.
    fn admit_replayed(&mut self, defs: &[DefEntry], datas: &[DataEntry]) -> Read<()> {
        let base_defs = self.globals.defs.len();
        let base_datas = self.globals.datas.len();
        let module = self.globals.module.clone();
        let result = self.submit(defs, datas, base_defs, base_datas);
        self.globals.module = module;
        if let Err(why) = result {
            // Undo: nothing else refers to what was added yet.
            let g = &mut self.globals;
            g.defs.truncate(base_defs);
            g.datas.truncate(base_datas);
            g.hashes.borrow_mut().retain(|k, _| match k {
                stitchwort_core::globals::HashKey::Def(id) => id.0 < base_defs,
                stitchwort_core::globals::HashKey::Data(d) => d.0 < base_datas,
            });
            return Err(why);
        }
        Ok(())
    }

    fn submit(
        &mut self,
        defs: &[DefEntry],
        datas: &[DataEntry],
        base_defs: usize,
        base_datas: usize,
    ) -> Read<()> {
        let refused = |d: stitchwort_syntax::Diagnostic| Bad(format!("refused: {}", d.message));
        // The groups, each with the entry's own declarations its terms
        // refer to (besides its members).
        struct Group {
            data: bool,
            members: Vec<usize>,
            needs_defs: BTreeSet<usize>,
            needs_datas: BTreeSet<usize>,
            done: bool,
        }
        let mut groups: Vec<Group> = Vec::new();
        let mut seen = HashSet::new();
        for (i, def) in defs.iter().enumerate() {
            if !def.group.contains(&i) {
                return bad("a definition outside its own group");
            }
            if !seen.insert(def.group[0]) {
                continue;
            }
            let mut needs_defs = BTreeSet::new();
            let mut needs_datas = BTreeSet::new();
            for &m in &def.group {
                if defs[m].group != def.group {
                    return bad("members disagree about their group");
                }
                codec::references(
                    &defs[m].body,
                    &mut |id| {
                        if id.0 >= base_defs {
                            needs_defs.insert(id.0 - base_defs);
                        }
                    },
                    &mut |d| {
                        if d.0 >= base_datas {
                            needs_datas.insert(d.0 - base_datas);
                        }
                    },
                );
            }
            for m in &def.group {
                needs_defs.remove(m);
            }
            groups.push(Group {
                data: false,
                members: def.group.clone(),
                needs_defs,
                needs_datas,
                done: false,
            });
        }
        let mut data_groups: Vec<usize> = Vec::new();
        let mut seen = HashSet::new();
        for (j, data) in datas.iter().enumerate() {
            let Some(&first) = data.group.first() else {
                return bad("an empty data group");
            };
            if first != j {
                if !seen.contains(&first) || datas[first].group != data.group {
                    return bad("a data group out of order");
                }
                continue;
            }
            seen.insert(j);
            if data.group.iter().enumerate().any(|(k, m)| *m != j + k) || data.datas_before != j {
                return bad("a data group out of order");
            }
            let mut needs_defs = BTreeSet::new();
            let mut needs_datas = BTreeSet::new();
            for &m in &data.group {
                for ctor in &datas[m].ctors {
                    for t in ctor.fields.iter().map(|(_, t)| t).chain(&ctor.result) {
                        codec::references(
                            t,
                            &mut |id| {
                                if id.0 >= base_defs {
                                    needs_defs.insert(id.0 - base_defs);
                                }
                            },
                            &mut |d| {
                                if d.0 >= base_datas {
                                    needs_datas.insert(d.0 - base_datas);
                                }
                            },
                        );
                    }
                }
            }
            for m in &data.group {
                needs_datas.remove(m);
            }
            data_groups.push(groups.len());
            groups.push(Group {
                data: true,
                members: data.group.clone(),
                needs_defs,
                needs_datas,
                done: false,
            });
        }

        let mut def_final = vec![false; defs.len()];
        let mut data_final = vec![false; datas.len()];
        let (mut next_def, mut next_data_group) = (0, 0);
        loop {
            // Define every group that can be.
            let mut progress = true;
            while progress {
                progress = false;
                for group in groups.iter_mut().filter(|g| !g.done) {
                    let declared = if group.data {
                        group
                            .members
                            .iter()
                            .all(|m| *m < self.globals.datas.len() - base_datas)
                    } else {
                        group.members.iter().all(|m| *m < next_def)
                    };
                    if !declared
                        || !group.needs_defs.iter().all(|d| def_final[*d])
                        || !group.needs_datas.iter().all(|d| data_final[*d])
                    {
                        continue;
                    }
                    if group.data {
                        let members = group
                            .members
                            .iter()
                            .map(|&m| {
                                let data = &datas[m];
                                let ctors = data
                                    .ctors
                                    .iter()
                                    .map(|c| kernel::CtorDecl {
                                        name: c.name.clone(),
                                        fields: c
                                            .fields
                                            .iter()
                                            .map(|(x, t)| (x.clone(), t.clone(), data.span))
                                            .collect(),
                                        result: c.result.clone(),
                                        implicit: c.implicit.clone(),
                                    })
                                    .collect();
                                (DataId(base_datas + m), ctors)
                            })
                            .collect();
                        self.kernel_op(|g| kernel::define_data_group(g, members))
                            .map_err(refused)?;
                        for m in &group.members {
                            data_final[*m] = true;
                        }
                    } else {
                        let members: Vec<(DefId, Term)> = group
                            .members
                            .iter()
                            .map(|&m| (DefId(base_defs + m), defs[m].body.clone()))
                            .collect();
                        self.kernel_op(|g| kernel::define_group(g, &members))
                            .map_err(refused)?;
                        for m in &group.members {
                            def_final[*m] = true;
                        }
                    }
                    group.done = true;
                    progress = true;
                }
            }
            // Then the next declaration.
            let next_data = data_groups
                .get(next_data_group)
                .map(|&gi| groups[gi].members[0]);
            if let Some(j) = next_data
                && datas[j].defs_before == next_def
            {
                let gi = data_groups[next_data_group];
                let first = &datas[j];
                let members = groups[gi]
                    .members
                    .iter()
                    .map(|&m| kernel::DataDecl {
                        name: datas[m].name.clone(),
                        span: datas[m].span,
                        record: datas[m].record,
                        indices: datas[m].indices.clone(),
                    })
                    .collect();
                self.globals.module = module_of(&first.name, &first.path)?;
                let (params, sort) = (first.params.clone(), first.sort);
                let ids = self
                    .kernel_op(|g| kernel::declare_indexed_data_group(g, params, sort, members))
                    .map_err(refused)?;
                for (&m, id) in groups[gi].members.iter().zip(&ids) {
                    let data = &datas[m];
                    if id.0 != base_datas + m || self.globals.data(*id).path != data.path {
                        return bad("a data type came out differently");
                    }
                    if data.params.len() != first.params.len() || data.sort != first.sort {
                        return bad("a data group's members disagree");
                    }
                    if !data.auto_params.is_empty() {
                        kernel::mark_auto_params(&mut self.globals, *id, data.auto_params.clone());
                    }
                }
                next_data_group += 1;
                continue;
            }
            if next_def < defs.len() {
                let def = &defs[next_def];
                self.globals.module = module_of(&def.name, &def.path)?;
                let id = self
                    .kernel_op(|g| {
                        kernel::declare_def(g, &def.name, &def.ty, def.theorem, false, def.span)
                    })
                    .map_err(refused)?;
                if id.0 != base_defs + next_def || self.globals.def(id).path != def.path {
                    return bad("a definition came out differently");
                }
                if def.fold {
                    kernel::mark_folded(&mut self.globals, id);
                }
                if def.instance {
                    kernel::mark_instance(&mut self.globals, id);
                }
                next_def += 1;
                continue;
            }
            break;
        }
        if groups.iter().any(|g| !g.done) || next_data_group < data_groups.len() {
            return bad("some declarations could never be defined");
        }
        Ok(())
    }

    /// Runs one kernel call as its own operation, with its own resource
    /// limits, as elaborating each component does.
    fn kernel_op<T>(&mut self, f: impl FnOnce(&mut Globals) -> T) -> T {
        let saved = self.globals.budget.start(self.limits);
        let result = f(&mut self.globals);
        self.globals.budget.restore(saved);
        result
    }

    /// Puts an entry's side tables in place, through the same insertion
    /// functions elaboration uses, once its declarations are admitted.
    fn replay_tables(&mut self, f: usize, t: Tables) {
        self.abilities.extend(t.abilities);
        let ability = |e: &Elaborator, op_data: DataId| {
            e.abilities
                .iter()
                .position(|a| a.op_data == op_data)
                .expect("checked when read (`replay`)")
        };
        let global = |e: &Elaborator, g: GlobalEntry| match g {
            GlobalEntry::Plain(g) => g,
            GlobalEntry::Ability(d) => Global::Ability(ability(e, d)),
            GlobalEntry::Op(d, j) => Global::Op(ability(e, d), j),
        };
        for (key, g, span) in t.changed {
            let g = global(self, g);
            self.scope.insert(&key, g, span, false);
        }
        for (key, g, span, follower) in t.new {
            let g = global(self, g);
            self.scope.insert(&key, g, span, follower);
        }
        for key in t.members {
            self.scope.mark_member(&key);
        }
        self.records.extend(t.records);
        self.interfaces.extend(t.interfaces);
        self.instances.extend(t.instances);
        let [owners, no_eq, no_show, no_ord] = t.by_data;
        self.data_owners.extend(owners);
        self.no_eq.extend(no_eq);
        self.no_show.extend(no_show);
        self.no_ord.extend(no_ord);
        self.lifted.extend(t.lifted);
        self.helper_keys.extend(t.helper_keys);
        if let (Some(nav), Some(entry)) = (&self.nav, t.nav) {
            let file = self.library_index().expect("installed").files[f].id;
            for (at, key, target, g, dot) in entry.refs {
                let global = global(self, g);
                self.note(
                    at,
                    Noted {
                        key,
                        target,
                        global,
                        dot,
                    },
                );
            }
            let mut nav = nav.borrow_mut();
            for (at, ty) in entry.local_types {
                nav.local_types.insert((file, at), ty);
            }
            for (span, name, binder) in entry.locals {
                nav.locals.push(LocalUse { span, name, binder });
            }
            for (span, name, binder) in entry.binders {
                nav.binders.push(LocalUse { span, name, binder });
            }
            for (at, name, span) in entry.fields {
                nav.field_spans.insert((at, name), span);
            }
        }
    }
}

/// The module a declaration was declared in, from its name and its path
/// (`Std` for `List.length` at `Std.List.length`), so declaring it again
/// gives the same path.
fn module_of(name: &str, path: &str) -> Read<Name> {
    if path == name {
        return Ok("".into());
    }
    match path.strip_suffix(name).and_then(|m| m.strip_suffix('.')) {
        Some(module) if !module.is_empty() => Ok(module.into()),
        _ => bad(format!("`{path}` isn't `{name}` in a module")),
    }
}

/// The side tables of an entry, read; any ability a name refers to must
/// be one known after replay.
fn read_tables(b: &mut Body, files: usize) -> Read<Tables> {
    let mut t = Tables {
        changed: Vec::new(),
        new: Vec::new(),
        members: Vec::new(),
        records: Vec::new(),
        interfaces: Vec::new(),
        instances: Vec::new(),
        by_data: [Vec::new(), Vec::new(), Vec::new(), Vec::new()],
        abilities: Vec::new(),
        lifted: Vec::new(),
        helper_keys: Vec::new(),
        nav: None,
    };
    let n = b.count()?;
    for _ in 0..n {
        t.changed.push((b.string()?, b.global(files)?, b.span()?));
    }
    let n = b.count()?;
    for _ in 0..n {
        t.new
            .push((b.string()?, b.global(files)?, b.span()?, b.r.bool()?));
    }
    let n = b.count()?;
    for _ in 0..n {
        t.members.push(b.string()?);
    }
    let n = b.count()?;
    for _ in 0..n {
        let d = b.data()?;
        let k = b.count()?;
        let mut projections = Vec::with_capacity(k);
        for _ in 0..k {
            projections.push(if b.r.bool()? { Some(b.def()?) } else { None });
        }
        t.records.push((d, RecordInfo { projections }));
    }
    let n = b.count()?;
    for _ in 0..n {
        let d = b.data()?;
        let dict = b.string()?;
        let k = b.count()?;
        let supers = (0..k)
            .map(|_| Ok((b.r.usize()?, b.data()?)))
            .collect::<Read<_>>()?;
        let k = b.count()?;
        let projections = (0..k).map(|_| b.def()).collect::<Read<_>>()?;
        let k = b.count()?;
        let methods = (0..k).map(|_| b.def()).collect::<Read<_>>()?;
        let k = b.count()?;
        let relations = (0..k)
            .map(|_| Ok((b.r.usize()?, b.r.usize()?)))
            .collect::<Read<_>>()?;
        t.interfaces.push((
            d,
            InterfaceInfo {
                dict,
                supers,
                projections,
                methods,
                relations,
            },
        ));
    }
    let n = b.count()?;
    for _ in 0..n {
        let key = (b.data()?, b.data()?);
        let def = b.def()?;
        let name = b.string()?;
        let span = b.span()?;
        let k = b.count()?;
        let mut params = Vec::with_capacity(k);
        for _ in 0..k {
            params.push(match b.r.u8()? {
                0 => InstanceParam::Head(b.r.usize()?),
                1 => InstanceParam::Prerequisite,
                _ => return bad("an unknown kind of instance parameter"),
            });
        }
        let valid = b.r.bool()?;
        t.instances.push((
            key,
            InstanceInfo {
                def,
                name,
                span,
                params,
                valid,
            },
        ));
    }
    for table in &mut t.by_data {
        let n = b.count()?;
        for _ in 0..n {
            table.push((b.data()?, b.string()?));
        }
    }
    let n = b.count()?;
    for _ in 0..n {
        let name = b.string()?;
        let op_data = b.data()?;
        let res = b.def()?;
        let elim = b.def()?;
        let k = b.count()?;
        let ops = (0..k).map(|_| b.string()).collect::<Read<_>>()?;
        let order = (b.r.bool()?, b.string()?);
        t.abilities.push(AbilityInfo {
            name,
            op_data,
            res,
            elim,
            ops,
            order,
        });
    }
    let n = b.count()?;
    for _ in 0..n {
        t.lifted.push((b.def()?, b.span()?));
    }
    let n = b.count()?;
    for _ in 0..n {
        t.helper_keys.push(b.string()?);
    }
    if b.r.bool()? {
        let mut nav = NavEntry {
            refs: Vec::new(),
            local_types: Vec::new(),
            locals: Vec::new(),
            binders: Vec::new(),
            fields: Vec::new(),
        };
        let n = b.count()?;
        for _ in 0..n {
            let at = b.span()?;
            let key = b.string()?;
            let target = b.span()?;
            let global = b.global(files)?;
            let dot = if b.r.bool()? { Some(b.string()?) } else { None };
            nav.refs.push((at, key, target, global, dot));
        }
        let n = b.count()?;
        for _ in 0..n {
            nav.local_types.push((b.r.u32()?, b.string()?));
        }
        for uses in [&mut nav.locals, &mut nav.binders] {
            let n = b.count()?;
            for _ in 0..n {
                uses.push((b.span()?, b.string()?, b.span()?));
            }
        }
        let n = b.count()?;
        for _ in 0..n {
            nav.fields.push((b.span()?, b.string()?, b.span()?));
        }
        t.nav = Some(nav);
    }
    Ok(t)
}

#[doc(hidden)]
pub use dump::canonical_dump;
