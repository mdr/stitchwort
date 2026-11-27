//! The deferred equations of a library file (or the core), kept in the check
//! cache beside the file's own entry (docs/proposals/search-cache.md §2,
//! D3768): an entry per file, `eqs.` and the file's unit, under the file's
//! own key, holding one **segment** per definition whose equations
//! [`Elaborator::generate_deferred_equations`] made. A segment is a whole
//! entry in the format of a library file's, encoded from what making that
//! one definition's equations wrote, so replaying it goes through the same
//! decoder and [`Elaborator::admit_replayed`], with its own dependency
//! header: every declaration it names, by path and the hash it had, `f`
//! itself among them.
//!
//! Only commands that list every equation read these entries (`search`,
//! `doc`); a program's on-demand equations (`load_needs`) are always made
//! fresh (§2.5). A segment is admitted only where making it fresh would
//! give the same declarations in the same order:
//!
//! 1. the container and the segment are exact hits: written by this build,
//!    against this core and library index, in a session that carried
//!    nothing over (no carried-over hit here, whatever `--carry-over` says);
//! 2. the file is loaded (generation walks loaded files only) and owns the
//!    key;
//! 3. the key's equations aren't made yet: not in `equations_done`, its
//!    first equation's name not in scope (else, as `ensure_equations_of`
//!    does, it is only marked done), no name the segment declares in scope,
//!    and no key the segment marks done done already; and the segment marks
//!    the key itself done (which segment is filed under which key is the
//!    container's word only);
//! 4. the definition is there and final;
//! 5. every dependency has the recorded hash (`decode`);
//! 6. the kernel admits it ([`Elaborator::admit_replayed`], as a unit that
//!    binds no built-in and holds no primitive), on the trusted path or,
//!    with `--recheck`, through its checking calls. A refusal is undone
//!    there and the equations are made fresh.
//!
//! Segments are replayed in the order fresh generation makes them (the
//! core, then each loaded file in load order, each file's keys in source
//! order), so every declaration gets the id it would have had.

use super::*;
use crate::library::LoadState;

type Result<T> = std::result::Result<T, Diagnostic>;

/// The prefix of an equations entry's unit, before the file's own unit.
const UNIT_PREFIX: &str = "eqs.";

impl Elaborator {
    /// Makes the deferred equations of `keys`, the definitions of file `f`
    /// (0 the core) in source order, from the check cache where it holds
    /// them and fresh otherwise; and writes the file's equations entry when
    /// anything was made fresh.
    pub(crate) fn ensure_file_equations(&mut self, f: usize, keys: &[String]) -> Result<()> {
        let lookup = (!keys.is_empty())
            .then(|| self.equations_lookup(f))
            .flatten();
        let Some((unit, key)) = lookup else {
            return self.ensure_equations(keys);
        };
        let store = self.options.check_cache.clone().expect("a cache is set");
        let salt = store.salt();
        let read = self.read_equations_entry(&*store, &unit, &key);
        let mut changed = read.is_none();
        let mut segments = read.unwrap_or_default();
        let mut made = HashMap::default();
        stitchwort_core::budget::within(self, |elab| {
            for k in keys {
                // As `ensure_equations_of` would leave it: nothing to make,
                // or (made with the definition) only to mark done.
                if !elab.equations_pending(f, k) || !elab.first_equation_unmade(f, k) {
                    elab.ensure_equations_of_key(k)?;
                    continue;
                }
                if let Some((bytes, hit)) = segments.get(k) {
                    match elab.replay_equations_segment(k, bytes, &key, salt, *hit) {
                        Ok(()) => {
                            elab.session.cache_stats.equation_hits += 1;
                            if hit.recheck {
                                elab.session.cache_stats.equation_rechecked += 1;
                            }
                            continue;
                        }
                        Err(Bad(why)) => {
                            debug(&format!("{unit}: `{k}`'s equations: a miss: {why}"));
                        }
                    }
                }
                elab.session.cache_stats.equation_misses += 1;
                changed |= segments.remove(k).is_some();
                if let Some(bytes) = elab.make_equations_segment(f, k, &key, salt)? {
                    made.insert(k.clone(), bytes);
                }
            }
            Ok::<(), Diagnostic>(())
        })?;
        if (changed || !made.is_empty())
            && !self.carried_anything()
            && !self.kernel.machine.budget.cancelled()
        {
            let mut all: Vec<(String, Vec<u8>)> = (segments.into_iter())
                .map(|(k, (bytes, _))| (k, bytes))
                .chain(made)
                .collect();
            all.sort();
            store.write(&unit, &key, &self.seal_equations_entry(&all, &key, salt));
            self.session.cache_stats.equation_entries_written += 1;
        }
        Ok(())
    }

    /// One key's equations, made as `ensure_equations` makes them.
    fn ensure_equations_of_key(&mut self, key: &String) -> Result<()> {
        self.ensure_equations(std::iter::once(key))
    }

    /// The unit and key of file `f`'s equations entry, if they may be read
    /// and written now: with a check cache, outside any library file's load
    /// or unit's capture (whose write-set the segments' would join).
    fn equations_lookup(&self, f: usize) -> Option<(String, Key)> {
        if !self.cache_usable() || self.scope.log.is_some() || self.scope.loading.is_some() {
            return None;
        }
        let lib = self.session.library.as_ref()?;
        if !lib.stack.is_empty() {
            return None;
        }
        Some((
            format!("{UNIT_PREFIX}{}", self.cache_unit(f)),
            self.library_key(f),
        ))
    }

    /// Checks 2 to 4 of the module's doc, as `ensure_equations_of` makes
    /// them before making anything: whether `key`'s equations are still to
    /// be made, from file `f`'s source.
    fn equations_pending(&self, f: usize, key: &str) -> bool {
        let Some(lib) = &self.session.library else {
            return false;
        };
        if f != 0 && lib.state[f] != LoadState::Loaded {
            return false;
        }
        if lib.index.owner(key) != Some(f) || self.tables.equations_done.iter().any(|k| k == key) {
            return false;
        }
        self.lookup_def(key)
            .is_some_and(|id| self.kernel.def(id).state() == State::Final)
    }

    /// Whether `key`'s first equation is not in scope yet: otherwise it was
    /// made with its definition (by the file's own proofs), and
    /// `ensure_equations_of` only marks it done.
    fn first_equation_unmade(&self, f: usize, key: &str) -> bool {
        let Some(lib) = &self.session.library else {
            return false;
        };
        let index = lib.index.clone();
        let file = &index.files[f];
        let Some(span) = (file.names.iter()).find(|n| n.key == key).map(|n| n.span) else {
            return false;
        };
        let Some((_, equations)) = crate::project::grouped(&file.module().decls)
            .into_iter()
            .find(|(d, _)| {
                matches!(d, stitchwort_syntax::ast::Decl::Signature { name, .. } if name.span == span)
            })
        else {
            return false;
        };
        crate::equations::source_suffixes(equations)
            .first()
            .is_some_and(|s| self.scope.get(&format!("{key}.{s}")).is_none())
    }

    /// Makes `key`'s equations fresh, capturing what that wrote as a segment
    /// of file `f`'s entry (the equations, or only why each was skipped):
    /// `None` if it didn't mark `key` done, loaded a library file (whose
    /// unit the write-set would take in), was cancelled, or can't be
    /// encoded.
    fn make_equations_segment(
        &mut self,
        f: usize,
        key: &String,
        entry_key: &Key,
        salt: [u8; 16],
    ) -> Result<Option<Vec<u8>>> {
        let loaded = self.loaded_library_files().len();
        let capture = self.cache_before();
        let made = self.ensure_equations_of_key(key);
        let log = self.scope.log.take().unwrap_or_default();
        let segment = (made.is_ok()
            && self.tables.equations_done.iter().any(|k| k == key)
            && self.loaded_library_files().len() == loaded
            && !self.kernel.machine.budget.cancelled())
        .then(|| self.encode_library_file(f, &capture, &log, entry_key, salt))
        .and_then(|encoded| {
            encoded
                .map_err(|why| debug(&format!("`{key}`'s equations can't be cached: {why}")))
                .ok()
        });
        self.commit(capture.transaction);
        made.map(|()| segment)
    }

    /// The segments of the equations entry `unit` at `key`, by definition
    /// key, each with how it may be used; `None` if there is none that is an
    /// exact hit (check 1).
    fn read_equations_entry(
        &self,
        store: &dyn Store,
        unit: &str,
        key: &Key,
    ) -> Option<HashMap<String, (Vec<u8>, Hit)>> {
        let salt = store.salt();
        let bytes = store.read(unit, key)?;
        let read = || -> Read<HashMap<String, (Vec<u8>, Hit)>> {
            let (stamp, deps, body) = open(&bytes, key, salt)?;
            let hit = self.exact_hit(&stamp, store)?;
            if !deps.is_empty() {
                return bad("an equations entry with dependencies of its own");
            }
            let mut r = Reader::new(body);
            let n = r.count(2)?;
            let mut segments = HashMap::default();
            for _ in 0..n {
                let k = r.string()?;
                let segment = r.blob()?;
                let (stamp, ..) = open(segment, key, salt)?;
                self.exact_hit(&stamp, store)?;
                if segments.insert(k, (segment.to_vec(), hit)).is_some() {
                    return bad("a definition with two segments");
                }
            }
            if !r.done() {
                return bad("bytes after the segments");
            }
            Ok(segments)
        };
        match read() {
            Ok(segments) => Some(segments),
            Err(Bad(why)) => {
                debug(&format!("{unit}: a miss: {why}"));
                None
            }
        }
    }

    /// How an entry stamped `stamp` may be used, if only as an exact hit.
    fn exact_hit(&self, stamp: &Stamp, store: &dyn Store) -> Read<Hit> {
        match self.usable(stamp, store)? {
            hit if hit.exact => Ok(hit),
            _ => bad("not written by this build in a session that carried nothing over"),
        }
    }

    /// Replays the segment for definition `def` (checks 3, 5 and 6), in a
    /// unit of its own as a library file's entry is replayed. On any
    /// problem, nothing has changed.
    fn replay_equations_segment(
        &mut self,
        def: &str,
        bytes: &[u8],
        key: &Key,
        salt: [u8; 16],
        hit: Hit,
    ) -> Read<()> {
        let (_, deps, body) = open(bytes, key, salt)?;
        let head = self.read_head(body, &self.std_file_ids())?;
        if !head.pre.is_empty() {
            return bad("an equations segment with a namespace's parts");
        }
        let d = self.decode(&deps, head, &[], true)?;
        if !d.rest.tables.tests.is_empty() || !d.rest.changed.is_empty() {
            return bad("an equations segment with tests or changed names");
        }
        // The segment is filed under `def` by the container only: what it
        // made is what it marks done.
        if !d.rest.tables.equations_done().iter().any(|k| k == def) {
            return bad(format!("a segment that doesn't make `{def}`'s equations"));
        }
        if let Some((k, ..)) = (d.rest.new.iter()).find(|(k, ..)| self.scope.get(k).is_some()) {
            return bad(format!("`{k}` is in scope already"));
        }
        let done = &self.tables.equations_done;
        if let Some(k) = (d.rest.tables.equations_done().iter()).find(|k| done.contains(k)) {
            return bad(format!("`{k}`'s equations are made already"));
        }
        let outer = self.session.owners.enter(self.ids());
        self.unit_changed();
        let admitted = self.admit_replayed(&d.defs, &d.datas, &d.bound, &d.rest.tables, false, hit);
        if admitted.is_ok() {
            self.replay_tables(d.rest, &[]);
        }
        self.session.owners.leave(self.ids(), outer);
        self.unit_changed();
        admitted
    }

    /// The equations entry holding `segments` (by definition key, sorted),
    /// stamped as this session's entries are.
    fn seal_equations_entry(
        &self,
        segments: &[(String, Vec<u8>)],
        key: &Key,
        salt: [u8; 16],
    ) -> Vec<u8> {
        let store = self.options.check_cache.as_ref().expect("a cache is set");
        let stamp = Stamp {
            kernel: store.kernel().to_string(),
            compiler: store.compiler().to_string(),
            interface: self.library_interface(),
            exact: !self.carried_anything(),
            digest: [0; 32],
        };
        let mut w = Writer::default();
        w.usize(segments.len());
        for (k, bytes) in segments {
            w.str(k);
            w.blob(bytes);
        }
        seal(key, salt, &stamp, &[], &w.bytes)
    }

    /// For tests: the unit and key of the equations entry of library file
    /// `path` (`A.sw`), if the session has a check cache.
    #[doc(hidden)]
    pub fn equations_entry_of(&self, path: &str) -> Option<(String, Key)> {
        let f = (self.library_index()?.files.iter()).position(|file| file.path == path)?;
        self.cache_usable().then(|| {
            (
                format!("{UNIT_PREFIX}{}", self.cache_unit(f)),
                self.library_key(f),
            )
        })
    }

    /// For tests: the equations entry `bytes`, written under `from` in this
    /// session's store, sealed again under `to` with this session's stamp,
    /// each segment filed under `rename` of its definition, as if the key
    /// had missed an input. `None` if `bytes` isn't such an entry.
    #[doc(hidden)]
    pub fn equations_entry_forged(
        &self,
        bytes: &[u8],
        from: &Key,
        to: &Key,
        rename: impl Fn(&str) -> String,
    ) -> Option<Vec<u8>> {
        let store = self.options.check_cache.as_ref()?;
        let salt = store.salt();
        let (_, _, body) = open(bytes, from, salt).ok()?;
        let mut r = Reader::new(body);
        let mut segments = Vec::new();
        for _ in 0..r.count(2).ok()? {
            let k = r.string().ok()?;
            let (stamp, deps, body) = open(r.blob().ok()?, from, salt).ok()?;
            let stamp = Stamp {
                kernel: store.kernel().to_string(),
                compiler: store.compiler().to_string(),
                interface: self.library_interface(),
                exact: true,
                ..stamp
            };
            segments.push((rename(&k), seal(to, salt, &stamp, &deps, body)));
        }
        segments.sort();
        Some(self.seal_equations_entry(&segments, to, salt))
    }
}
