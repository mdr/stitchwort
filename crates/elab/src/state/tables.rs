//! [`Tables`]: what the elaborator records about checked declarations that
//! later units read (docs/proposals/elaborator-state.md §4.2). A new table
//! that a later unit reads belongs here, and each mechanism over it is a
//! method that destructures `Tables`: [`Tables::mark`], [`Tables::rewind`],
//! [`Tables::encode_since`], [`Tables::decode`] (whose [`Delta`] is built
//! whole), [`Tables::replay`] and [`Tables::dump`]. So a field doesn't
//! compile until each says what it does with it, and a table of a kind
//! ([`super::table`]) has all of that supplied by its kind.
//!
//! Three tables are of no kind yet. `instances` and `helper_keys` are any
//! of whose rows a later unit may change (an instance's `valid` flag): a
//! mark copies them, and an entry holds the rows the copy hasn't, until
//! they become undo logs (§7 step 6, which also moves the scope here).
//! `namespace_defs` and `prelude_defs` aren't in an entry: the replay of a
//! namespace sets its range from the definitions it admits, and the
//! prelude is never cached.

use std::collections::BTreeMap;
use std::ops::Range;
use std::rc::Rc;

use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::{DataId, DefId};
use stitchwort_syntax::Span;

use super::table::{Codec, Dump, GrowVec, Ids, OwnedBy, OwnedMark, Table};
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
    pub(crate) instances: HashMap<(DataId, DataId), InstanceInfo>,
    /// Every local definition's key, so dot notation never finds one
    /// (docs/proposals/syntax-conveniences.md §3.6).
    pub(crate) helper_keys: HashSet<String>,
    /// In a project: the definitions each namespace checked so far made.
    pub(crate) namespace_defs: BTreeMap<String, Range<usize>>,
    /// How many definitions the prelude made.
    pub(crate) prelude_defs: usize,
    /// The first declarations of the unit being elaborated: rows of an
    /// `OwnedBy` table for older ones are another unit's.
    start: Ids,
}

/// Where [`Tables`] are: for a rewind, or for the rows a unit's check
/// cache entry holds.
pub(crate) struct Mark {
    start: Ids,
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
    instances: HashMap<(DataId, DataId), InstanceInfo>,
    helper_keys: HashSet<String>,
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
    /// Says that a unit whose first declarations are `start` is elaborated
    /// from now on, and gives the start there was, to put back when a unit
    /// nested in another is done.
    pub(crate) fn begin_unit(&mut self, start: Ids) -> Ids {
        let Tables {
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
            start: old,
            // Not owned by a unit.
            tests: _,
            abilities: _,
            lifted: _,
            equation_skips: _,
            equations_done: _,
            instances: _,
            helper_keys: _,
            namespace_defs: _,
            prelude_defs: _,
        } = self;
        records.set_floor(start);
        interfaces.set_floor(start);
        data_owners.set_floor(start);
        no_eq.set_floor(start);
        no_show.set_floor(start);
        no_ord.set_floor(start);
        no_finite.set_floor(start);
        no_decide.set_floor(start);
        generated_alls.set_floor(start);
        match_columns.set_floor(start);
        total_rows.set_floor(start);
        std::mem::replace(old, start)
    }

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
            instances,
            helper_keys,
            namespace_defs,
            prelude_defs,
            start,
        } = self;
        Mark {
            start: *start,
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
            instances: instances.clone(),
            helper_keys: helper_keys.clone(),
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
            instances,
            helper_keys,
            namespace_defs,
            prelude_defs,
            start,
        } = self;
        *start = m.start;
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
        *instances = m.instances.clone();
        *helper_keys = m.helper_keys.clone();
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
            start: _,
        } = self;
        if instances.iter().any(|(k, v)| {
            m.instances
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
            .filter(|(k, _)| !m.instances.contains_key(k))
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
        let mut helpers: Vec<&String> = helper_keys.difference(&m.helper_keys).collect();
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
    pub(crate) fn replay(&mut self, d: Delta) {
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
            start: _,
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
        tests.replay(d_tests);
        abilities.replay(d_abilities);
        lifted.replay(d_lifted);
        equation_skips.replay(d_equation_skips);
        equations_done.replay(d_equations_done);
        records.replay(d_records);
        interfaces.replay(d_interfaces);
        data_owners.replay(d_data_owners);
        no_eq.replay(d_no_eq);
        no_show.replay(d_no_show);
        no_ord.replay(d_no_ord);
        no_finite.replay(d_no_finite);
        no_decide.replay(d_no_decide);
        generated_alls.replay(d_generated_alls);
        match_columns.replay(d_match_columns);
        total_rows.replay(d_total_rows);
        instances.extend(d_instances);
        helper_keys.extend(d_helper_keys);
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
            // Where the unit being elaborated starts: not a fact about what
            // was checked.
            start: _,
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
        lines.extend(helper_keys.iter().map(|k| format!("helper {k}")));
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
