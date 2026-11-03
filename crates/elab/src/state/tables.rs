//! [`Tables`]: what the elaborator records about checked declarations that
//! later units read (docs/proposals/elaborator-state.md §4.2). A new table
//! that a later unit reads belongs here, and each mechanism over it is a
//! method that destructures `Tables`: [`Tables::mark`], [`Tables::rewind`],
//! [`Tables::encode_since`], [`Tables::decode`] (whose [`Delta`] is built
//! whole), [`Tables::replay`] and [`Tables::dump`]. So a field doesn't
//! compile until each says what it does with it, and a table of a kind
//! ([`super::table`]) has all of that supplied by its kind.
//!
//! `instances` and `helper_keys` are [`Logged`] (§4.8.2): a rewind's
//! checkpoint puts them back from their logs ([`Tables::logged`]). An
//! instance's row belongs to the unit of its definition, which alone may
//! write it ([`Instances`], §4.8.4); any unit may add a helper's key. A
//! check cache entry holds the rows a copy taken before the unit hasn't
//! ([`Copies`]), until entries are made from write-sets (§4.8.3, step 6c).
//! `namespace_defs` and `prelude_defs` aren't in an entry: the replay of a
//! namespace sets its range from the definitions it admits, and the
//! prelude is never cached. A mark copies them (one row per project
//! namespace).

use std::collections::BTreeMap;
use std::ops::Range;
use std::rc::Rc;

use stitchwort_core::{DataId, DefId};
use stitchwort_syntax::Span;

use super::journal::{Copied, Logged, LoggedSet, Logs};
use super::owners::Owners;
use super::table::{Codec, Dump, GrowVec, Ids, OwnedBy, OwnedMark, Table, owned};
use crate::TestDecl;
use crate::cache::{Body, Encoding, Read};
use crate::effects::AbilityInfo;
use crate::interfaces::{InstanceInfo, InterfaceInfo};
use crate::lift::MatchColumns;
use crate::records::RecordInfo;

#[derive(Default)]
pub(crate) struct Tables {
    /// The tests declared, in the order they run.
    pub(crate) tests: GrowVec<TestDecl>,
    /// The abilities declared; `Global::Ability(i)` is the `i`th.
    pub(crate) abilities: GrowVec<AbilityInfo>,
    /// Every lifted helper so far, with its `match`, for naming the `match`
    /// in diagnostics instead of the helper (`Elaborator::explain_lifted`).
    pub(crate) lifted: GrowVec<(DefId, Span)>,
    /// The equations the source implies that weren't generated, by key,
    /// with the reason: naming one is `E-NO-EQUATION` (D2176).
    pub(crate) equation_skips: GrowVec<(DefId, String, String)>,
    /// The library's and the core's definitions whose equations were made
    /// on demand (`Elaborator::ensure_equations`), by key.
    pub(crate) equations_done: GrowVec<String>,
    /// The record types declared so far (docs/proposals/records.md).
    pub(crate) records: OwnedBy<DataId, RecordInfo>,
    /// The interfaces declared so far (docs/proposals/interfaces.md §5.1).
    pub(crate) interfaces: OwnedBy<DataId, InterfaceInfo>,
    /// The module that declared each data type (§5.6 rule 1).
    pub(crate) data_owners: OwnedBy<DataId, String>,
    /// Why `DecEq` isn't derived for a data type or record, for the note
    /// when `==` is used on it (`derive.rs`).
    pub(crate) no_eq: OwnedBy<DataId, String>,
    /// The same for `Show` (`derive_show.rs`).
    pub(crate) no_show: OwnedBy<DataId, String>,
    /// The same for `Ord` (`derive_ord.rs`).
    pub(crate) no_ord: OwnedBy<DataId, String>,
    /// The same for `Finite` (`derive_finite.rs`).
    pub(crate) no_finite: OwnedBy<DataId, String>,
    /// Why a `Prop` record has no derived decision (`derive_decide.rs`), for
    /// the note when one is wanted.
    pub(crate) no_decide: OwnedBy<DataId, String>,
    /// The `D.All` generated for each container of the program a nested
    /// type is in, by container (`derive_induct.rs`).
    pub(crate) generated_alls: OwnedBy<DataId, DefId>,
    /// Each lifted `match`'s helper's parameters it matches (SW-1074).
    pub(crate) match_columns: OwnedBy<DefId, Rc<MatchColumns>>,
    /// The definitions checked again with their bare row variables total
    /// (D1215), with where the first check failed.
    pub(crate) total_rows: OwnedBy<DefId, Span>,
    /// The global instances, by interface and head (interfaces.md §5.6).
    pub(crate) instances: Instances,
    /// Every local definition's key, so dot notation never finds one
    /// (docs/proposals/syntax-conveniences.md §3.6).
    pub(crate) helper_keys: LoggedSet<String>,
    /// In a project: the definitions each namespace checked so far made.
    pub(crate) namespace_defs: BTreeMap<String, Range<usize>>,
    /// How many definitions the prelude made.
    pub(crate) prelude_defs: usize,
}

/// Where [`Tables`] are: for a rewind, or for the rows a unit's check
/// cache entry holds.
pub(crate) struct Mark {
    tests: usize,
    abilities: usize,
    lifted: usize,
    equation_skips: usize,
    equations_done: usize,
    records: OwnedMark,
    interfaces: OwnedMark,
    data_owners: OwnedMark,
    no_eq: OwnedMark,
    no_show: OwnedMark,
    no_ord: OwnedMark,
    no_finite: OwnedMark,
    no_decide: OwnedMark,
    generated_alls: OwnedMark,
    match_columns: OwnedMark,
    total_rows: OwnedMark,
    namespace_defs: BTreeMap<String, Range<usize>>,
    prelude_defs: usize,
}

/// What a check cache entry holds of [`Tables`], read back.
#[derive(Default)]
pub(crate) struct Delta {
    pub(crate) tests: Vec<TestDecl>,
    pub(crate) abilities: Vec<AbilityInfo>,
    lifted: Vec<(DefId, Span)>,
    equation_skips: Vec<(DefId, String, String)>,
    equations_done: Vec<String>,
    records: Vec<(DataId, RecordInfo)>,
    interfaces: Vec<(DataId, InterfaceInfo)>,
    data_owners: Vec<(DataId, String)>,
    no_eq: Vec<(DataId, String)>,
    no_show: Vec<(DataId, String)>,
    no_ord: Vec<(DataId, String)>,
    no_finite: Vec<(DataId, String)>,
    no_decide: Vec<(DataId, String)>,
    generated_alls: Vec<(DataId, DefId)>,
    match_columns: Vec<(DefId, Rc<MatchColumns>)>,
    total_rows: Vec<(DefId, Span)>,
    instances: Vec<((DataId, DataId), InstanceInfo)>,
    helper_keys: Vec<String>,
}

impl Mark {
    /// How many tests there were.
    pub(crate) fn tests(&self) -> usize {
        self.tests
    }
}

impl Tables {
    /// Where the tables are, with `ids` declarations made so far.
    pub(crate) fn mark(&self, ids: Ids) -> Mark {
        let Tables {
            tests,
            abilities,
            lifted,
            equation_skips,
            equations_done,
            records,
            interfaces,
            data_owners,
            no_eq,
            no_show,
            no_ord,
            no_finite,
            no_decide,
            generated_alls,
            match_columns,
            total_rows,
            // Logged ([`Tables::logged`]).
            instances: _,
            helper_keys: _,
            namespace_defs,
            prelude_defs,
        } = self;
        Mark {
            tests: tests.mark(ids),
            abilities: abilities.mark(ids),
            lifted: lifted.mark(ids),
            equation_skips: equation_skips.mark(ids),
            equations_done: equations_done.mark(ids),
            records: records.mark(ids),
            interfaces: interfaces.mark(ids),
            data_owners: data_owners.mark(ids),
            no_eq: no_eq.mark(ids),
            no_show: no_show.mark(ids),
            no_ord: no_ord.mark(ids),
            no_finite: no_finite.mark(ids),
            no_decide: no_decide.mark(ids),
            generated_alls: generated_alls.mark(ids),
            match_columns: match_columns.mark(ids),
            total_rows: total_rows.mark(ids),
            namespace_defs: namespace_defs.clone(),
            prelude_defs: *prelude_defs,
        }
    }

    /// Back to `m`.
    pub(crate) fn rewind(&mut self, m: &Mark) {
        let Tables {
            tests,
            abilities,
            lifted,
            equation_skips,
            equations_done,
            records,
            interfaces,
            data_owners,
            no_eq,
            no_show,
            no_ord,
            no_finite,
            no_decide,
            generated_alls,
            match_columns,
            total_rows,
            // Put back by the journal.
            instances: _,
            helper_keys: _,
            namespace_defs,
            prelude_defs,
        } = self;
        tests.rewind(&m.tests);
        abilities.rewind(&m.abilities);
        lifted.rewind(&m.lifted);
        equation_skips.rewind(&m.equation_skips);
        equations_done.rewind(&m.equations_done);
        records.rewind(&m.records);
        interfaces.rewind(&m.interfaces);
        data_owners.rewind(&m.data_owners);
        no_eq.rewind(&m.no_eq);
        no_show.rewind(&m.no_show);
        no_ord.rewind(&m.no_ord);
        no_finite.rewind(&m.no_finite);
        no_decide.rewind(&m.no_decide);
        generated_alls.rewind(&m.generated_alls);
        match_columns.rewind(&m.match_columns);
        total_rows.rewind(&m.total_rows);
        *namespace_defs = m.namespace_defs.clone();
        *prelude_defs = m.prelude_defs;
    }

    /// Writes what the unit being encoded added since `m`, in the entry
    /// format's order (`cache::FORMAT`), which puts two parts that aren't
    /// tables between them: `kernel`, the side facts of the unit's
    /// declarations (after the records), and `extensions`, the extensions
    /// the namespace declares (before the tests).
    pub(crate) fn encode_since(
        &self,
        m: &Mark,
        copies: &Copies,
        e: &mut Encoding<'_>,
        kernel: impl FnOnce(&mut Encoding<'_>),
        extensions: impl FnOnce(&mut Encoding<'_>),
    ) -> Result<(), String> {
        let Tables {
            tests,
            abilities,
            lifted,
            equation_skips,
            equations_done,
            records,
            interfaces,
            data_owners,
            no_eq,
            no_show,
            no_ord,
            no_finite,
            no_decide,
            generated_alls,
            match_columns,
            total_rows,
            instances,
            helper_keys,
            // Not in an entry (see the module's comment).
            namespace_defs: _,
            prelude_defs: _,
        } = self;
        if instances.iter().any(|(k, v)| {
            copies
                .instances
                .get(k)
                .is_some_and(|old| (old.def, old.valid) != (v.def, v.valid))
        }) {
            return Err("an instance from before changed".to_string());
        }
        records.encode_since(&m.records, e)?;
        kernel(e);
        interfaces.encode_since(&m.interfaces, e)?;
        let mut new: Vec<(&(DataId, DataId), &InstanceInfo)> = instances
            .iter()
            .filter(|(k, _)| !copies.instances.contains_key(*k))
            .collect();
        new.sort_by_key(|(k, _)| (k.0.0, k.1.0));
        e.count(new.len());
        for (k, info) in new {
            k.encode(e);
            info.encode(e);
        }
        data_owners.encode_since(&m.data_owners, e)?;
        no_eq.encode_since(&m.no_eq, e)?;
        no_show.encode_since(&m.no_show, e)?;
        no_ord.encode_since(&m.no_ord, e)?;
        no_finite.encode_since(&m.no_finite, e)?;
        no_decide.encode_since(&m.no_decide, e)?;
        generated_alls.encode_since(&m.generated_alls, e)?;
        abilities.encode_since(&m.abilities, e)?;
        lifted.encode_since(&m.lifted, e)?;
        match_columns.encode_since(&m.match_columns, e)?;
        let mut helpers: Vec<&String> = (helper_keys.keys())
            .filter(|k| !copies.helper_keys.contains_key(*k))
            .collect();
        helpers.sort();
        e.count(helpers.len());
        for k in helpers {
            k.encode(e);
        }
        equation_skips.encode_since(&m.equation_skips, e)?;
        equations_done.encode_since(&m.equations_done, e)?;
        total_rows.encode_since(&m.total_rows, e)?;
        extensions(e);
        tests.encode_since(&m.tests, e)?;
        Ok(())
    }

    /// Reads what [`Tables::encode_since`] wrote, with the parts between
    /// the tables read by `kernel` and `extensions`.
    pub(crate) fn decode(
        b: &mut Body<'_>,
        kernel: impl FnOnce(&mut Body<'_>) -> Read<()>,
        extensions: impl FnOnce(&mut Body<'_>) -> Read<()>,
    ) -> Read<Delta> {
        let records = OwnedBy::decode(b)?;
        kernel(b)?;
        let interfaces = OwnedBy::decode(b)?;
        let n = b.count()?;
        let instances = (0..n)
            .map(|_| Ok((Codec::decode(b)?, Codec::decode(b)?)))
            .collect::<Read<_>>()?;
        let data_owners = OwnedBy::decode(b)?;
        let no_eq = OwnedBy::decode(b)?;
        let no_show = OwnedBy::decode(b)?;
        let no_ord = OwnedBy::decode(b)?;
        let no_finite = OwnedBy::decode(b)?;
        let no_decide = OwnedBy::decode(b)?;
        let generated_alls = OwnedBy::decode(b)?;
        let abilities = GrowVec::decode(b)?;
        let lifted = GrowVec::decode(b)?;
        let match_columns = OwnedBy::decode(b)?;
        let n = b.count()?;
        let helper_keys = (0..n).map(|_| String::decode(b)).collect::<Read<_>>()?;
        let equation_skips = GrowVec::decode(b)?;
        let equations_done = GrowVec::decode(b)?;
        let total_rows = OwnedBy::decode(b)?;
        extensions(b)?;
        let tests = GrowVec::decode(b)?;
        Ok(Delta {
            tests,
            abilities,
            lifted,
            equation_skips,
            equations_done,
            records,
            interfaces,
            data_owners,
            no_eq,
            no_show,
            no_ord,
            no_finite,
            no_decide,
            generated_alls,
            match_columns,
            total_rows,
            instances,
            helper_keys,
        })
    }

    /// Adds what an entry holds, read back.
    pub(crate) fn replay(&mut self, d: Delta, owners: &Owners) {
        let Tables {
            tests,
            abilities,
            lifted,
            equation_skips,
            equations_done,
            records,
            interfaces,
            data_owners,
            no_eq,
            no_show,
            no_ord,
            no_finite,
            no_decide,
            generated_alls,
            match_columns,
            total_rows,
            instances,
            helper_keys,
            // Set by the replay of a namespace (`replay_namespace`).
            namespace_defs: _,
            prelude_defs: _,
        } = self;
        let Delta {
            tests: d_tests,
            abilities: d_abilities,
            lifted: d_lifted,
            equation_skips: d_equation_skips,
            equations_done: d_equations_done,
            records: d_records,
            interfaces: d_interfaces,
            data_owners: d_data_owners,
            no_eq: d_no_eq,
            no_show: d_no_show,
            no_ord: d_no_ord,
            no_finite: d_no_finite,
            no_decide: d_no_decide,
            generated_alls: d_generated_alls,
            match_columns: d_match_columns,
            total_rows: d_total_rows,
            instances: d_instances,
            helper_keys: d_helper_keys,
        } = d;
        tests.replay(d_tests, owners);
        abilities.replay(d_abilities, owners);
        lifted.replay(d_lifted, owners);
        equation_skips.replay(d_equation_skips, owners);
        equations_done.replay(d_equations_done, owners);
        records.replay(d_records, owners);
        interfaces.replay(d_interfaces, owners);
        data_owners.replay(d_data_owners, owners);
        no_eq.replay(d_no_eq, owners);
        no_show.replay(d_no_show, owners);
        no_ord.replay(d_no_ord, owners);
        no_finite.replay(d_no_finite, owners);
        no_decide.replay(d_no_decide, owners);
        generated_alls.replay(d_generated_alls, owners);
        match_columns.replay(d_match_columns, owners);
        total_rows.replay(d_total_rows, owners);
        for (k, info) in d_instances {
            instances.insert(owners, k, info);
        }
        for k in d_helper_keys {
            helper_keys.add(k);
        }
    }

    /// The whole of every table, for the canonical dump.
    pub(crate) fn dump(&self, out: &mut String) {
        let Tables {
            tests,
            abilities,
            lifted,
            equation_skips,
            equations_done,
            records,
            interfaces,
            data_owners,
            no_eq,
            no_show,
            no_ord,
            no_finite,
            no_decide,
            generated_alls,
            match_columns,
            total_rows,
            instances,
            helper_keys,
            namespace_defs,
            prelude_defs,
        } = self;
        records.dump("record", out);
        interfaces.dump("interface", out);
        data_owners.dump("owner", out);
        no_eq.dump("no_eq", out);
        no_show.dump("no_show", out);
        no_ord.dump("no_ord", out);
        no_finite.dump("no_finite", out);
        no_decide.dump("no_decide", out);
        generated_alls.dump("generated_all", out);
        match_columns.dump("match columns", out);
        total_rows.dump("total_row", out);
        let mut lines: Vec<String> = instances
            .iter()
            .map(|((i, h), info)| {
                let mut s = format!("instance {} {} ", i.0, h.0);
                info.dump(&mut s);
                s
            })
            .collect();
        lines.extend(helper_keys.keys().map(|k| format!("helper {k}")));
        lines.extend(
            namespace_defs
                .iter()
                .map(|(n, r)| format!("namespace {n} {r:?}")),
        );
        lines.sort();
        for line in lines {
            out.push_str(&line);
            out.push('\n');
        }
        // A cached run may make these in another order; no reader depends
        // on it.
        equation_skips.dump_sorted("equation_skip", out);
        equations_done.dump_sorted("equations_done", out);
        abilities.dump("ability", out);
        lifted.dump("lifted", out);
        tests.dump("test", out);
        out.push_str(&format!("prelude_defs {prelude_defs}\n"));
    }
}

/// What the check cache compares a unit's instances and helpers' keys with:
/// copies taken before it (`cache::Before`), until its entries are made
/// from write-sets (§4.8.3, step 6c).
pub(crate) struct Copies {
    instances: Copied<(DataId, DataId), InstanceInfo>,
    helper_keys: Copied<String, ()>,
}

/// Where [`Tables`]' logged tables' logs are.
pub(crate) struct Positions {
    instances: usize,
    helper_keys: usize,
}

impl Tables {
    pub(crate) fn copies(&self) -> Copies {
        Copies {
            instances: self.instances.rows.copy(),
            helper_keys: self.helper_keys.copy(),
        }
    }

    /// The logged tables, with what each does in [`Logs`]'s methods.
    fn logged(&mut self) -> [&mut dyn Logs<Positions = usize>; 2] {
        let Tables {
            instances,
            helper_keys,
            // Of a kind with its own mark, or copied by one.
            tests: _,
            abilities: _,
            lifted: _,
            equation_skips: _,
            equations_done: _,
            records: _,
            interfaces: _,
            data_owners: _,
            no_eq: _,
            no_show: _,
            no_ord: _,
            no_finite: _,
            no_decide: _,
            generated_alls: _,
            match_columns: _,
            total_rows: _,
            namespace_defs: _,
            prelude_defs: _,
        } = self;
        [&mut instances.rows, helper_keys]
    }

    fn logged_ref(&self) -> [&dyn Logs<Positions = usize>; 2] {
        [&self.instances.rows, &self.helper_keys]
    }
}

impl Logs for Tables {
    type Positions = Positions;

    fn positions(&self) -> Positions {
        Positions {
            instances: self.instances.rows.position(),
            helper_keys: self.helper_keys.position(),
        }
    }

    fn undo_to(&mut self, at: &Positions) -> usize {
        let Positions {
            instances,
            helper_keys,
        } = at;
        let [a, b] = self.logged();
        a.undo_to(instances) + b.undo_to(helper_keys)
    }

    fn set_generation(&mut self, g: Option<u32>) {
        self.logged().into_iter().for_each(|t| t.set_generation(g));
    }

    fn entries(&self) -> usize {
        self.logged_ref().iter().map(|t| t.entries()).sum()
    }

    fn bytes(&self) -> usize {
        self.logged_ref().iter().map(|t| t.bytes()).sum()
    }

    fn distinct_keys(&self) -> usize {
        self.logged_ref().iter().map(|t| t.distinct_keys()).sum()
    }
}

/// The global instances, by interface and head: [`Logged`], and a row is
/// owned by the unit of its definition (`info.def`), which alone writes it
/// (§4.8.4), as [`OwnedBy`]'s rows are by their key's. Its key can't say:
/// an orphan instance's interface and head may both be older units'.
#[derive(Default)]
pub(crate) struct Instances {
    rows: Logged<(DataId, DataId), InstanceInfo>,
}

impl std::ops::Deref for Instances {
    type Target = Logged<(DataId, DataId), InstanceInfo>;
    fn deref(&self) -> &Self::Target {
        &self.rows
    }
}

impl Instances {
    /// Sets the instance for `key`; `owners` say which unit is being
    /// elaborated, which must be the one that made `info.def`, and the
    /// one that made any instance it replaces.
    pub(crate) fn insert(&mut self, owners: &Owners, key: (DataId, DataId), info: InstanceInfo) {
        owned(owners, info.def);
        if let Some(old) = self.rows.get(&key) {
            owned(owners, old.def);
        }
        self.rows.insert(key, info);
    }

    /// Changes `key`'s instance by `f`, as [`Instances::insert`]; whether
    /// there is one. `f` keeps its definition.
    pub(crate) fn update(
        &mut self,
        owners: &Owners,
        key: (DataId, DataId),
        f: impl FnOnce(&mut InstanceInfo),
    ) -> bool {
        let Some(def) = self.rows.get(&key).map(|i| i.def) else {
            return false;
        };
        owned(owners, def);
        self.rows.update(&key, |info| {
            f(info);
            assert_eq!(info.def, def, "an instance's definition changed");
        })
    }
}

#[cfg(test)]
mod tests {
    use std::panic::{AssertUnwindSafe, catch_unwind};

    use super::*;

    fn instance(def: usize) -> InstanceInfo {
        InstanceInfo {
            def: DefId(def),
            name: format!("inst{def}"),
            span: Span::point(stitchwort_syntax::SourceMap::new().add("test", ""), 0),
            params: Vec::new(),
            valid: false,
        }
    }

    /// An instance's row is its definition's unit's (§4.8.4): an outer unit
    /// can't change one a unit nested in it made, even under a key whose
    /// types are its own; the unit that made it can.
    #[test]
    fn an_instance_is_written_by_its_definitions_unit_only() {
        let ids = |defs| Ids { defs, datas: 0 };
        let mut owners = Owners::default();
        let mut t = Instances::default();
        let key = (DataId(1), DataId(2));
        owners.begin(ids(10));
        let a = owners.enter(ids(10));
        t.insert(&owners, key, instance(10));
        assert!(t.update(&owners, key, |i| i.valid = true));
        owners.leave(ids(11), a);
        let update = catch_unwind(AssertUnwindSafe(|| {
            t.update(&owners, key, |i| i.valid = false)
        }));
        assert!(update.is_err());
        let replace = catch_unwind(AssertUnwindSafe(|| t.insert(&owners, key, instance(11))));
        assert!(replace.is_err());
        assert!(t.get(&key).is_some_and(|i| i.valid && i.def == DefId(10)));
    }
}
