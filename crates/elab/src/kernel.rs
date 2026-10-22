//! The kernel's checking API, as the elaborator uses it. Everything is
//! re-exported unchanged except the declare and define calls, which are
//! timed for `STITCHWORT_TIMINGS` (`timings.rs`). The kernel crate itself
//! has no timing code.

use stitchwort_core::check as k;
use stitchwort_core::{DataId, DefId, Globals, Name, Sort, Term};
use stitchwort_syntax::{Diagnostic, Span};

pub use k::*;

use crate::timings::kernel_call;

type Result<T> = std::result::Result<T, Diagnostic>;

pub fn define_def(g: &mut Globals, id: DefId, body: &Term) -> Result<()> {
    kernel_call(|| k::define_def(g, id, body))
}

pub fn define_group(g: &mut Globals, members: &[(DefId, Term)]) -> Result<()> {
    kernel_call(|| k::define_group(g, members))
}

pub fn declare_def(
    g: &mut Globals,
    name: &Name,
    ty: &Term,
    theorem: bool,
    export: bool,
    span: Span,
) -> Result<DefId> {
    kernel_call(|| k::declare_def(g, name, ty, theorem, export, span))
}

#[allow(dead_code)]
pub fn declare_data(
    g: &mut Globals,
    name: Name,
    params: Vec<(Name, Term)>,
    sort: Sort,
    span: Span,
) -> Result<DataId> {
    kernel_call(|| k::declare_data(g, name, params, sort, span))
}

pub fn declare_data_group(
    g: &mut Globals,
    params: Vec<(Name, Term)>,
    sort: Sort,
    members: Vec<(Name, Span)>,
) -> Result<Vec<DataId>> {
    kernel_call(|| k::declare_data_group(g, params, sort, members))
}

#[allow(dead_code)]
pub fn declare_data_group_as(
    g: &mut Globals,
    params: Vec<(Name, Term)>,
    sort: Sort,
    members: Vec<(Name, Span, bool)>,
) -> Result<Vec<DataId>> {
    kernel_call(|| k::declare_data_group_as(g, params, sort, members))
}

pub fn declare_indexed_data_group(
    g: &mut Globals,
    params: Vec<(Name, Term)>,
    sort: Sort,
    members: Vec<DataDecl>,
) -> Result<Vec<DataId>> {
    kernel_call(|| k::declare_indexed_data_group(g, params, sort, members))
}

#[allow(dead_code)]
pub fn define_ctors(g: &mut Globals, d: DataId, ctors: Vec<CtorDecl>) -> Result<()> {
    kernel_call(|| k::define_ctors(g, d, ctors))
}

pub fn define_data_group(g: &mut Globals, members: Vec<(DataId, Vec<CtorDecl>)>) -> Result<()> {
    kernel_call(|| k::define_data_group(g, members))
}
