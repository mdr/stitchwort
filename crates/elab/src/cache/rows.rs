//! How each row of `state::Tables` is written in an entry and read back
//! ([`Codec`]). Which rows an entry holds, and how they are put back, is
//! the table's kind's (`state::table`); the canonical dump of a row is
//! written separately, in `dump.rs`.

use std::rc::Rc;

use stitchwort_core::globals::{FieldDefault, FieldDefaults, ParamDefaults, UpdateShown};
use stitchwort_core::js_repr::{JsCtor, JsRepr};
use stitchwort_core::{DataId, DefId};
use stitchwort_syntax::Span;

use super::codec::{Read, bad};
use super::{Body, Encoding};
use crate::TestDecl;
use crate::effects::AbilityInfo;
use crate::interfaces::{InstanceInfo, InstanceParam, InterfaceInfo};
use crate::lift::MatchColumns;
use crate::reading::{ReadingInfo, TestHead};
use crate::records::RecordInfo;
use crate::state::Codec;

impl Codec for DefId {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.def(*self);
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        b.def()
    }
}

impl Codec for DataId {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.data(*self);
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        b.data()
    }
}

impl Codec for Span {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.span(*self);
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        b.span()
    }
}

impl Codec for String {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.str(self);
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        b.string()
    }
}

impl<A: Codec, B: Codec> Codec for (A, B) {
    fn encode(&self, e: &mut Encoding<'_>) {
        self.0.encode(e);
        self.1.encode(e);
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        Ok((A::decode(b)?, B::decode(b)?))
    }
}

impl<A: Codec, B: Codec, C: Codec> Codec for (A, B, C) {
    fn encode(&self, e: &mut Encoding<'_>) {
        self.0.encode(e);
        self.1.encode(e);
        self.2.encode(e);
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        Ok((A::decode(b)?, B::decode(b)?, C::decode(b)?))
    }
}

impl Codec for RecordInfo {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.w.usize(self.projections.len());
        for p in &self.projections {
            e.w.bool(p.is_some());
            if let Some(p) = p {
                e.def(*p);
            }
        }
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        let k = b.count()?;
        let mut projections = Vec::with_capacity(k);
        for _ in 0..k {
            projections.push(if b.r.bool()? { Some(b.def()?) } else { None });
        }
        Ok(RecordInfo { projections })
    }
}

impl Codec for InterfaceInfo {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.str(&self.dict);
        e.w.usize(self.supers.len());
        for (i, s) in &self.supers {
            e.w.usize(*i);
            e.data(*s);
        }
        e.w.usize(self.projections.len());
        for p in &self.projections {
            e.def(*p);
        }
        e.w.usize(self.methods.len());
        for m in &self.methods {
            e.def(*m);
        }
        e.w.usize(self.relations.len());
        for (r, d) in &self.relations {
            e.w.usize(*r);
            e.w.usize(*d);
        }
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
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
        Ok(InterfaceInfo {
            dict,
            supers,
            projections,
            methods,
            relations,
        })
    }
}

impl Codec for InstanceInfo {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.def(self.def);
        e.str(&self.name);
        e.span(self.span);
        e.w.usize(self.params.len());
        for p in &self.params {
            match p {
                InstanceParam::Head(k) => {
                    e.w.u8(0);
                    e.w.usize(*k);
                }
                InstanceParam::Prerequisite => e.w.u8(1),
            }
        }
        e.w.bool(self.valid);
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
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
        Ok(InstanceInfo {
            def,
            name,
            span,
            params,
            valid,
        })
    }
}

impl Codec for Rc<MatchColumns> {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.w.usize(self.cols.len());
        for (col, eq) in self.cols.iter().zip(&self.eqs) {
            e.w.usize(*col);
            e.w.usize(eq.map_or(0, |q| q + 1));
        }
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        let k = b.count()?;
        let mut c = MatchColumns {
            cols: Vec::new(),
            eqs: Vec::new(),
        };
        for _ in 0..k {
            c.cols.push(b.r.usize()?);
            c.eqs.push(b.r.usize()?.checked_sub(1));
        }
        Ok(Rc::new(c))
    }
}

impl Codec for Rc<ReadingInfo> {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.w.bool(self.polarity);
        match self.head {
            TestHead::Def(f) => {
                e.w.usize(0);
                e.def(f);
            }
            TestHead::And => e.w.usize(1),
            TestHead::Or => e.w.usize(2),
        }
        e.w.usize(self.slots.len());
        for slot in self.slots.iter() {
            e.w.usize(*slot);
        }
        e.w.usize(self.pure_rows.len());
        for k in self.pure_rows.iter() {
            e.w.usize(*k);
        }
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        let polarity = b.r.bool()?;
        let head = match b.r.usize()? {
            0 => TestHead::Def(b.def()?),
            1 => TestHead::And,
            2 => TestHead::Or,
            _ => return bad("a reading's head"),
        };
        let k = b.count()?;
        let slots = (0..k).map(|_| b.r.usize()).collect::<Read<Vec<_>>>()?;
        let k = b.count()?;
        let pure_rows = (0..k).map(|_| b.r.usize()).collect::<Read<Vec<_>>>()?;
        Ok(Rc::new(ReadingInfo {
            polarity,
            head,
            slots: slots.into(),
            pure_rows: pure_rows.into(),
        }))
    }
}

impl Codec for AbilityInfo {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.str(&self.name);
        e.data(self.op_data);
        e.def(self.res);
        e.def(self.elim);
        e.w.usize(self.ops.len());
        for op in &self.ops {
            e.str(op);
        }
        e.w.bool(self.order.0);
        e.str(&self.order.1);
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        let name = b.string()?;
        let op_data = b.data()?;
        let res = b.def()?;
        let elim = b.def()?;
        let k = b.count()?;
        let ops = (0..k).map(|_| b.string()).collect::<Read<_>>()?;
        let order = (b.r.bool()?, b.string()?);
        Ok(AbilityInfo {
            name,
            op_data,
            res,
            elim,
            ops,
            order,
        })
    }
}

/// A project's test (a library file's entry has none): replayed as not a
/// library test.
impl Codec for TestDecl {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.str(&self.name);
        e.str(&self.namespace);
        e.def(self.def);
        e.span(self.span);
        match &self.probe {
            None => e.w.bool(false),
            Some(probe) => {
                e.w.bool(true);
                e.probe(probe);
            }
        }
        match &self.unfinished {
            None => e.w.bool(false),
            Some(name) => {
                e.w.bool(true);
                e.str(name);
            }
        }
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        let name = b.string()?;
        let namespace = b.string()?;
        let def = b.def()?;
        let span = b.span()?;
        let probe = if b.r.bool()? { Some(b.probe(0)?) } else { None };
        let unfinished = if b.r.bool()? { Some(b.string()?) } else { None };
        Ok(TestDecl {
            library: false,
            name,
            namespace,
            def,
            span,
            probe,
            unfinished,
        })
    }
}

impl Codec for () {
    fn encode(&self, _: &mut Encoding<'_>) {}
    fn decode(_: &mut Body<'_>) -> Read<Self> {
        Ok(())
    }
}

/// A default's helper and the parameters it takes (`None`: no default).
fn encode_default(e: &mut Encoding<'_>, default: &Option<FieldDefault>) {
    e.w.bool(default.is_some());
    if let Some(default) = default {
        e.def(default.helper);
        e.w.usize(default.captures.len());
        for &l in &default.captures {
            e.w.usize(l);
        }
    }
}

fn decode_default(b: &mut Body<'_>) -> Read<Option<FieldDefault>> {
    Ok(if b.r.bool()? {
        let helper = b.def()?;
        let c = b.count()?;
        let captures = (0..c).map(|_| b.r.usize()).collect::<Read<_>>()?;
        Some(FieldDefault { helper, captures })
    } else {
        None
    })
}

impl Codec for Rc<FieldDefaults> {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.w.usize(self.len());
        for fields in self.iter() {
            e.w.usize(fields.len());
            fields.iter().for_each(|field| encode_default(e, field));
        }
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        let k = b.count()?;
        let mut ctors = Vec::with_capacity(k);
        for _ in 0..k {
            let m = b.count()?;
            ctors.push((0..m).map(|_| decode_default(b)).collect::<Read<_>>()?);
        }
        Ok(Rc::new(ctors))
    }
}

impl Codec for Rc<ParamDefaults> {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.w.usize(self.header);
        e.w.usize(self.params.len());
        self.params
            .iter()
            .for_each(|param| encode_default(e, param));
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        let header = b.count()?;
        let m = b.count()?;
        let params = (0..m).map(|_| decode_default(b)).collect::<Read<_>>()?;
        Ok(Rc::new(ParamDefaults { header, params }))
    }
}

impl Codec for Rc<UpdateShown> {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.w.usize(self.params);
        e.term(&self.base);
        e.w.usize(self.fields.len());
        for (field, value) in &self.fields {
            e.str(field);
            e.term(value);
        }
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        let params = b.count()?;
        let base = b.term()?;
        let m = b.count()?;
        let mut fields = Vec::with_capacity(m);
        for _ in 0..m {
            fields.push((b.str()?, b.term()?));
        }
        Ok(Rc::new(UpdateShown {
            params,
            base,
            fields,
        }))
    }
}

impl Codec for Rc<JsRepr> {
    fn encode(&self, e: &mut Encoding<'_>) {
        e.str(&self.tag_key);
        e.w.bool(self.string_enum);
        e.w.bool(self.unboxed);
        e.w.usize(self.ctors.len());
        for ctor in &self.ctors {
            e.str(&ctor.tag);
            e.w.usize(ctor.keys.len());
            for key in &ctor.keys {
                e.w.bool(key.is_some());
                if let Some(key) = key {
                    e.str(key);
                }
            }
            for &optional in &ctor.optional {
                e.w.bool(optional);
            }
        }
    }
    fn decode(b: &mut Body<'_>) -> Read<Self> {
        let tag_key = b.string()?;
        let string_enum = b.r.bool()?;
        let unboxed = b.r.bool()?;
        let k = b.count()?;
        let mut ctors = Vec::with_capacity(k);
        for _ in 0..k {
            let tag = b.string()?;
            let m = b.count()?;
            let keys = (0..m)
                .map(|_| Ok(if b.r.bool()? { Some(b.string()?) } else { None }))
                .collect::<Read<_>>()?;
            let optional = (0..m).map(|_| b.r.bool()).collect::<Read<_>>()?;
            ctors.push(JsCtor {
                tag,
                keys,
                optional,
            });
        }
        Ok(Rc::new(JsRepr {
            tag_key,
            ctors,
            string_enum,
            unboxed,
        }))
    }
}
