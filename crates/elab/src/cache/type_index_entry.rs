//! What each library candidate's type names once folded, kept in the check
//! cache for `search` (docs/proposals/search-cache.md §3, SW-4956): an entry
//! per library file, `tix.` and the file's unit, under the file's own
//! library key, mapping a declaration's [`Item::stable_key`] to the
//! definitions, data types and constructors that its type, evaluated and
//! read back folded, names beyond those it names as written.
//!
//! **Not trusted, and not admitted into the kernel.** An entry holds names
//! (paths), nothing that is a term, a declaration or a proof, and is only
//! read by `search_candidates` to fill [`Index`], which the search uses to
//! filter and rank candidates. A wrong entry could make a search miss or
//! show a candidate, never make the kernel accept anything. Still, an entry
//! is read only as an exact hit (this build, this library interface, a
//! session that carried nothing over), under the file's own key (which
//! covers its text, what it needs and the modes), and for the same gluing
//! switch it was made with; names are resolved through the scope, and
//! those that don't resolve make the item a miss. An item's names are
//! stored only if resolving them gives back the same declarations, and
//! only if the fold succeeded (a fold that ran out of budget or was
//! cancelled is never kept).
//!
//! Declarations outside the library (the project's) have no entry and are
//! worked out each time, as they are with no cache. A store that doesn't
//! keep the entry ([`Store::keeps`]) is read from but nothing is encoded
//! for it.

use super::*;
use crate::search::{Index, Item};

/// What an item's folded type names beyond what it names as written, by
/// path.
#[derive(Clone, Default)]
struct Extras {
    defs: Vec<String>,
    datas: Vec<String>,
    ctors: Vec<(String, usize)>,
}

/// One library file's entry, as read and as it has grown.
struct FileEntry {
    unit: String,
    key: Key,
    /// Whether anything may be written back for it.
    keep: bool,
    items: HashMap<String, Extras>,
    changed: bool,
}

/// The type index entries a `search_candidates` call reads and adds to.
pub(crate) struct TypeIndexCache {
    store: Rc<dyn Store>,
    salt: [u8; 16],
    gluing: bool,
    files: HashMap<usize, FileEntry>,
    tally: [usize; 3],
}

impl Elaborator {
    /// The cache for this call, if entries may be read and written now.
    pub(crate) fn type_index_cache(&self) -> Option<TypeIndexCache> {
        if !self.cache_usable()
            || self.scope.log.is_some()
            || self.scope.loading.is_some()
            || self.unit.namespace_capture.is_some()
        {
            return None;
        }
        let lib = self.session.library.as_ref()?;
        if !lib.stack.is_empty() {
            return None;
        }
        let store = self.options.check_cache.clone()?;
        Some(TypeIndexCache {
            salt: store.salt(),
            store,
            gluing: self.gluing(),
            files: HashMap::default(),
            tally: [0; 3],
        })
    }

    /// `item`'s index of type `ty`: the folded half from its file's entry
    /// if it has one, else worked out (and kept for next time).
    pub(crate) fn cached_type_index(
        &self,
        cache: &mut TypeIndexCache,
        item: Item,
        ty: &Term,
    ) -> Index {
        let g = &self.ev();
        let path = item.path(g);
        let Some(f) = self
            .library_index()
            .and_then(|index| index.owner_of_path(&path))
        else {
            return self.type_index(ty);
        };
        let file = cache.files.entry(f).or_insert_with(|| {
            self.read_type_index_entry(&*cache.store, cache.salt, cache.gluing, f)
        });
        let key = item.stable_key(g);
        let mut index = crate::search::syntactic_index(ty);
        if let Some(extras) = file.items.get(&key)
            && let Some(folded) = self.resolve_extras(extras)
        {
            cache.tally[0] += 1;
            index.absorb(folded);
            return index;
        }
        cache.tally[1] += 1;
        let Some(folded) = self.folded_index(ty) else {
            return index;
        };
        if file.keep {
            let extras = self.extras_beyond(&index, &folded);
            if self.resolve_extras(&extras).is_some_and(|back| {
                back.ty == folded.ty.difference(&index.ty).copied().collect()
                    && back.data == folded.data.difference(&index.data).copied().collect()
                    && back.ctors == folded.ctors.difference(&index.ctors).copied().collect()
            }) {
                file.items.insert(key, extras);
                file.changed = true;
            }
        }
        index.absorb(folded);
        index
    }

    /// Writes back the entries that grew, and counts for
    /// [`Elaborator::check_cache_stats`].
    pub(crate) fn finish_type_index_cache(&self, cache: TypeIndexCache) {
        let mut tally = cache.tally;
        if !self.carried_anything() && !self.kernel.machine.budget.cancelled() {
            for file in cache.files.values().filter(|file| file.changed) {
                cache.store.write(
                    &file.unit,
                    &file.key,
                    &self.seal_type_index_entry(file, &cache),
                );
                tally[2] += 1;
            }
        }
        let was = self.session.type_index_tally.get();
        self.session.type_index_tally.set([
            was[0] + tally[0],
            was[1] + tally[1],
            was[2] + tally[2],
        ]);
    }

    /// Library file `f`'s entry, as far as it can be read; an empty one
    /// (to be written) if there is none or it isn't usable.
    fn read_type_index_entry(
        &self,
        store: &dyn Store,
        salt: [u8; 16],
        gluing: bool,
        f: usize,
    ) -> FileEntry {
        let unit = format!("tix.{}", self.cache_unit(f));
        let key = self.library_key(f);
        let mut entry = FileEntry {
            keep: store.keeps(&unit) && !self.carried_anything(),
            unit,
            key,
            items: HashMap::default(),
            changed: false,
        };
        let Some(bytes) = store.read(&entry.unit, &entry.key) else {
            return entry;
        };
        match self.parse_type_index_entry(&bytes, &entry.key, salt, gluing, store) {
            Ok(items) => entry.items = items,
            Err(Bad(why)) => {
                debug(&format!("{}: a miss: {why}", entry.unit));
                entry.changed = true;
            }
        }
        entry
    }

    fn parse_type_index_entry(
        &self,
        bytes: &[u8],
        key: &Key,
        salt: [u8; 16],
        gluing: bool,
        store: &dyn Store,
    ) -> Read<HashMap<String, Extras>> {
        let (stamp, deps, body) = open(bytes, key, salt)?;
        if !stamp.exact
            || stamp.compiler != store.compiler()
            || stamp.interface != self.library_interface()
        {
            return bad("not written by this build in a session that carried nothing over");
        }
        if !deps.is_empty() {
            return bad("a type index entry with dependencies of its own");
        }
        let mut r = Reader::new(body);
        if r.bool()? != gluing {
            return bad("made with the other gluing switch");
        }
        let n = r.count(4)?;
        let mut items = HashMap::default();
        for _ in 0..n {
            let k = r.string()?;
            let mut extras = Extras::default();
            for _ in 0..r.count(1)? {
                extras.defs.push(r.string()?);
            }
            for _ in 0..r.count(1)? {
                extras.datas.push(r.string()?);
            }
            for _ in 0..r.count(2)? {
                let d = r.string()?;
                extras.ctors.push((d, r.usize()?));
            }
            if items.insert(k, extras).is_some() {
                return bad("an item with two records");
            }
        }
        if !r.done() {
            return bad("bytes after the items");
        }
        Ok(items)
    }

    fn seal_type_index_entry(&self, file: &FileEntry, cache: &TypeIndexCache) -> Vec<u8> {
        let stamp = Stamp {
            kernel: cache.store.kernel().to_string(),
            compiler: cache.store.compiler().to_string(),
            interface: self.library_interface(),
            exact: !self.carried_anything(),
            digest: [0; 32],
        };
        let mut items: Vec<_> = file.items.iter().collect();
        items.sort_by(|a, b| a.0.cmp(b.0));
        let mut w = Writer::default();
        w.bool(cache.gluing);
        w.usize(items.len());
        for (k, extras) in items {
            w.str(k);
            w.usize(extras.defs.len());
            extras.defs.iter().for_each(|d| w.str(d));
            w.usize(extras.datas.len());
            extras.datas.iter().for_each(|d| w.str(d));
            w.usize(extras.ctors.len());
            for (d, c) in &extras.ctors {
                w.str(d);
                w.usize(*c);
            }
        }
        seal(&file.key, cache.salt, &stamp, &[], &w.bytes)
    }

    /// The names `folded` has beyond `written`.
    fn extras_beyond(&self, written: &Index, folded: &Index) -> Extras {
        let g = &self.ev();
        Extras {
            defs: (folded.ty.difference(&written.ty))
                .map(|id| g.def(*id).path().to_string())
                .collect(),
            datas: (folded.data.difference(&written.data))
                .map(|d| g.data(DataId(*d)).path().to_string())
                .collect(),
            ctors: (folded.ctors.difference(&written.ctors))
                .map(|(d, c)| (g.data(DataId(*d)).path().to_string(), *c))
                .collect(),
        }
    }

    /// The declarations `extras` name, as an index; `None` if one isn't in
    /// scope as a declaration of that kind.
    fn resolve_extras(&self, extras: &Extras) -> Option<Index> {
        let mut index = Index::default();
        for path in &extras.defs {
            match self.scope.get(path)? {
                (Global::Def(id), _) => index.ty.insert(id),
                _ => return None,
            };
        }
        for path in &extras.datas {
            match self.scope.get(path)? {
                (Global::Data(d), _) => index.data.insert(d.0),
                _ => return None,
            };
        }
        for (path, c) in &extras.ctors {
            match self.scope.get(path)? {
                (Global::Data(d), _) => index.ctors.insert((d.0, *c)),
                _ => return None,
            };
        }
        Some(index)
    }
}
