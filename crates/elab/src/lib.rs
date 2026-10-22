//! Elaboration: turns surface syntax into complete core terms. It resolves
//! names, desugars (numbers, lists, `+`), fills in implicit arguments by
//! unification, and compiles pattern-matching equations into case trees.
//!
//! Every declaration it produces is then re-checked by the kernel
//! (`stitchwort-core`), so a bug here can cause a confusing error but can't
//! make the kernel accept something false.

mod auto;
mod autobind;
mod bind;
pub mod cache;
mod calc;
mod check;
mod data_auto;
mod decreasing;
mod derive;
mod derive_ext;
mod derive_ord;
mod derive_show;
mod dot;
mod effects;
mod families;
mod interfaces;
mod kernel;
mod library;
#[cfg(test)]
mod library_tests;
mod lift;
mod local;
mod logic;
mod matching;
mod module;
mod nav;
pub use nav::{NavIndex, NavRef, NavSymbol, NavTarget, std_source};
mod numbers;
mod partial;
mod patlet;
mod pipe;
pub mod project;
mod records;
mod rewind;
mod rewrite;
mod scope;
pub mod timings;
pub use library::{LIBRARY_FILES, LibraryIndex};
pub use rewind::Mark;
pub use scope::edit_distance;
mod undo;
mod unify;

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use num_bigint::BigUint;
use stitchwort_core::chars;
use stitchwort_core::native::{self, Native};
use stitchwort_core::partial::Primitive;
use stitchwort_core::registry::{self, Builtin};
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::{Head, eval, force, quote};
use stitchwort_core::{DataId, DefId, Globals, Icit, Limits, Name, Sort, Term, Value, pretty};
use stitchwort_syntax::ast::{Decl, Expr, Pattern};
use stitchwort_syntax::{Diagnostic, Span, ast};

use check::{Ctx, check, check_type, infer};
use module::Phase;

/// Defines [`PRELUDE`], the core: the files of `std/core/`, in this order,
/// joined as they are (checked as one module, so declarations are as they
/// would be in one file), and [`CORE_LAYOUT`], each file's path and length,
/// which is how a position in the core is traced to its file. The text is in
/// the program once: a length is computed without keeping the text.
macro_rules! core_files {
    ($($name:literal),* $(,)?) => {
        pub const PRELUDE: &str = concat!($(include_str!(concat!("std/core/", $name, ".sw"))),*);
        pub const CORE_LAYOUT: &[(&str, usize)] = &[$((
            concat!("core/", $name, ".sw"),
            include_str!(concat!("std/core/", $name, ".sw")).len(),
        )),*];
    };
}

// Dependency order: each file uses only what the files before it declare.
// `Imports` is first, and its imports cover them all. A test checks this
// lists every file in `std/core/`.
core_files!(
    "Imports",
    "Logic",
    "Data",
    "Equality",
    "Decidable",
    "Char",
    "Division",
    "ListOptionPair",
    "Ordering",
    "Helpers",
    "Text",
    "Int",
    "Effect",
    "IO",
    "DecEq",
    "Compare",
    "CompareData",
    "Ord",
    "OrdDerived",
    "Show",
    "Arith",
    "AddMul",
);

/// The core's file that holds `offset` of [`PRELUDE`]: its path (under
/// `std/`), where it starts in [`PRELUDE`], and its index in
/// [`CORE_LAYOUT`].
pub fn core_file_at(offset: usize) -> (&'static str, usize, usize) {
    let mut start = 0;
    for (i, (path, len)) in CORE_LAYOUT.iter().enumerate() {
        if offset < start + len || i + 1 == CORE_LAYOUT.len() {
            return (path, start, i);
        }
        start += len;
    }
    unreachable!("the core has files")
}

type Result<T> = std::result::Result<T, Diagnostic>;

/// The constructor name of the unit pattern `()` the compiler writes: the
/// prelude's `UnitValue`, by identity. Source can't spell it.
const UNIT_PATTERN: &str = "%unit";

/// Names with built-in meanings, which can't be redefined.
const RESERVED: &[&str] = &["rfl", "J", "Partial"];

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Global {
    Def(DefId),
    Data(DataId),
    Ctor(DataId, usize),
    /// An ability, by its index in `Elaborator::abilities`.
    Ability(usize),
    /// Operation `i` of an ability.
    Op(usize, usize),
    /// Declared by this item of the module being elaborated, which hasn't
    /// been checked yet (`module::ModuleState::items`).
    Unchecked(usize),
    /// Declared by a declaration that failed before it was checked.
    Failed,
    /// Declared by a library file that isn't loaded yet: the name index's
    /// entry (`library.rs`). Resolution sees it like any declaration; what
    /// it names is only checked once the file loads.
    Pending(usize, library::PendingKind),
}

/// A `test "name" = expr` declaration, checked as a definition of type `Bool`.
pub struct TestDecl {
    /// A test of the core or of a library file: run by the library test
    /// target, never by a project's `stitchwort test`
    /// (docs/proposals/std-library.md §4.7).
    pub library: bool,
    pub name: String,
    /// The namespace of the module that declares it; empty if the module
    /// has none.
    pub namespace: String,
    pub def: DefId,
    pub span: Span,
    /// For a test that is a comparison, its two sides, so a failure can show
    /// their values.
    pub sides: Option<TestSides>,
}

/// The two sides of a comparison that is a test, in the order the user wrote
/// them (`a > b` is elaborated as `b < a`, but its left side is `a`).
pub struct TestSides {
    /// The operator as written: `==`, `!=`, `=`, `<`, `<=`, `>` or `>=`.
    pub op: &'static str,
    pub left: Term,
    pub right: Term,
}

/// What elaborating a test records of its top-level comparison (`numbers.rs`):
/// the span to watch for, then the sides found.
#[derive(Default)]
pub(crate) struct SidesCapture {
    target: Option<Span>,
    found: Option<TestSides>,
}

#[derive(Default)]
pub struct Elaborator {
    pub globals: Globals,
    pub tests: Vec<TestDecl>,
    sides_capture: RefCell<SidesCapture>,
    /// Every declaration, by its full name (`scope.rs`).
    scope: scope::Scope,
    /// The current module's key prefix: `Day05.` in namespace `Day05`, empty
    /// for a file without a namespace line. Kept after the module is
    /// elaborated, so names typed in afterwards (`eval`, the REPL, `main`)
    /// are read as in the file.
    namespace_root: String,
    /// The project's namespaces (`project::set_project_namespaces`).
    project_namespaces: BTreeSet<String>,
    /// Every prefix of a project namespace's name, the namespace included.
    project_prefixes: BTreeSet<String>,
    /// What `import N (..)` brings from each project namespace whose files
    /// parsed (`project::set_project_names`).
    project_names: BTreeMap<String, BTreeSet<String>>,
    /// In a project: the definitions each namespace checked so far made.
    namespace_defs: BTreeMap<String, std::ops::Range<usize>>,
    /// How many definitions the prelude made.
    prelude_defs: usize,
    /// While a single file from inside a project is loaded: what to say
    /// when it uses the project (`E-FILE-MODE`).
    pub file_mode: Option<project::FileModeContext>,
    /// Where `include` reads from, and where each source file is in it
    /// (`project::read_include`). Without them `include` is
    /// `E-INCLUDE-UNAVAILABLE`.
    include_files: Option<Rc<dyn project::IncludeFiles>>,
    include_locations: HashMap<stitchwort_syntax::FileId, String>,
    next_include_location: Option<String>,
    /// Auto arguments still to be proved in the current declaration.
    obligations: RefCell<Vec<auto::Obligation>>,
    /// Metavariables that literals made `Nat` in the current declaration.
    defaulted: RefCell<Vec<numbers::Defaulted>>,
    /// The characters whose patterns became number patterns (by span), so
    /// a missing case can be reported as characters.
    char_patterns: RefCell<HashMap<Span, char>>,
    /// The spans of the `_` a char pattern puts for its proof field
    /// (`'a'` is `MkChar 97 _`), so an arm can make the matched character
    /// the literal itself (`canonical`).
    char_proofs: RefCell<std::collections::HashSet<Span>>,
    /// While the prelude is loaded, its built-in types and natively
    /// implemented definitions are registered with the kernel by name.
    pub loading_prelude: bool,
    /// Evaluation steps one `rewrite`'s comparisons may use between them;
    /// `None` is the default (`rewrite.rs`). Tests set it small.
    pub rewrite_budget: Option<u64>,
    /// The standard library's files, once the core is loaded
    /// (`library.rs`).
    library: Option<library::LibraryState>,
    /// Whether the `test`s of the core and the library files are checked
    /// (the library test target), instead of skipped.
    pub library_tests: bool,
    abilities: Vec<effects::AbilityInfo>,
    /// Resource limits for checking each declaration.
    pub limits: Limits,
    /// For tests only: compile number patterns the old way, as nested `Succ`
    /// patterns, even where a number case would do. Only usable with small
    /// numbers. Tests compare the two compilations.
    pub numbers_as_succ: bool,
    /// The module being elaborated, and what's being checked in it.
    module: module::ModuleState,
    /// Warnings found while elaborating the current declaration. Only
    /// declaration-level code (`&mut self`) adds them, so an attempt undone
    /// by `undo.rs` can't have added any.
    warnings: Vec<Diagnostic>,
    /// `W-LAMBDA-SHADOW` warnings, found while checking a lambda, where only
    /// a shared reference to the elaborator is at hand. One per lambda
    /// (checking can reach the same lambda twice); drained with `warnings`.
    lambda_warnings: RefCell<Vec<Diagnostic>>,
    /// Errors from the other bad branches of a case whose first bad branch's
    /// error is the one returned. Where only a shared reference to the
    /// elaborator is at hand; a definition that fails reports them after its
    /// own error, and one that succeeds (the check was an attempt that was
    /// undone) drops them.
    branch_errors: RefCell<Vec<Diagnostic>>,
    /// Arms of the definition being checked that a case on an indexed family
    /// dropped because their constructor can't be there, with a reason, and
    /// the arms that were reached: those dropped and never reached are
    /// `W-UNREACHABLE` (`families.rs`).
    pub(crate) arm_reach: RefCell<families::ArmReach>,
    /// Above zero while an application is elaborated again the old way
    /// after its expected result type was used first and failed: no
    /// application inside uses its expected type first
    /// (docs/proposals/syntax-conveniences.md §7.4).
    no_propagation: std::cell::Cell<usize>,
    /// What each receiver's dot call was found to call, by the receiver
    /// expression and the field written after it: so a chain `x.f.g.h` finds
    /// each head once instead of inferring the receiver again at every
    /// level (`dot::prefix_form`).
    pub(crate) dot_heads:
        RefCell<std::collections::HashMap<dot::CallKey, (dot::TyHead, stitchwort_core::DefId)>>,
    /// Dot calls whose prefix form failed, with the metavariable state it
    /// failed in: not tried again until that changes (`dot::infer_call`).
    pub(crate) dot_failed: RefCell<std::collections::HashSet<(dot::CallKey, usize, usize)>>,
    /// The address of the condition whose `Bool` reading `logic::condition`
    /// is trying, or 0: a proposition there isn't decided into a `Bool` by
    /// `check::decide_to_bool`, as the condition's proposition reading does
    /// that its own way.
    condition: std::cell::Cell<usize>,
    /// While the body of a definition with `decreasing` is elaborated: what
    /// its recursive calls stand for (`decreasing.rs`).
    decreasing: RefCell<Option<decreasing::Active>>,
    /// While the members of a partial recursive group are described: their
    /// private recursion signature (`partial.rs`).
    recursion: Option<effects::Recursion>,
    /// The record types declared so far (docs/proposals/records.md).
    records: HashMap<DataId, records::RecordInfo>,
    /// Why `DecEq` isn't derived for a data type or record, for the note
    /// when `==` is used on it (`derive.rs`).
    no_eq: HashMap<DataId, String>,
    /// The same for `Show` (`derive_show.rs`).
    no_show: HashMap<DataId, String>,
    /// The same for `Ord` (`derive_ord.rs`).
    no_ord: HashMap<DataId, String>,
    /// Helpers elaborated in the current declaration and not yet lifted
    /// (`lift.rs`). Part of the inference state `undo.rs` restores.
    drafts: RefCell<Vec<lift::Draft>>,
    /// While lifting, the `let`s each draft's terms are folded back to
    /// (`lift::Arounds`); empty otherwise.
    arounds: RefCell<lift::Arounds>,
    /// Every lifted helper so far, with its `match`, for naming the `match`
    /// in diagnostics instead of the helper (`Elaborator::explain_lifted`).
    lifted: Vec<(DefId, Span)>,
    /// While a declaration is elaborated: its key, then the names of the
    /// local definitions being elaborated inside it, for their keys
    /// (`local.rs`).
    owner: RefCell<Vec<String>>,
    /// The keys of the local definitions met in the current declaration,
    /// for `E-DUPLICATE`. Part of the inference state `undo.rs` restores.
    local_keys: RefCell<Vec<(String, Span)>>,
    /// Local definitions admitted after an attempt at their owner's body
    /// failed, by key, for the next attempt (`local.rs`).
    preadmitted: RefCell<HashMap<String, lift::Resolved>>,
    /// The local definitions lifted from the declaration (or group) being
    /// checked, bound in the module's scope once it's final.
    local_helpers: Vec<(String, DefId, Span)>,
    /// Every local definition's key, so dot notation never finds one
    /// (docs/proposals/syntax-conveniences.md §3.6).
    pub(crate) helper_keys: std::collections::HashSet<String>,
    /// The frozen metavariables standing for local definitions, with their
    /// names, for messages.
    pub(crate) local_metas: RefCell<HashMap<usize, String>>,
    /// For each definition, by `DefId`, once worked out: the data type its
    /// result type is (after all its parameters), if it is one. The decision
    /// search (`auto::decision_procedures`) reads it instead of evaluating
    /// every definition's type each time. Only worked out for a final
    /// definition, whose type, and everything it refers to, never changes;
    /// definitions are only ever added, so an entry never goes stale.
    pub(crate) result_heads: RefCell<Vec<Option<Option<DataId>>>>,
    /// Whether a call of final definition `id` with `n` explicit arguments
    /// reaches a computation type (`effects::def_performs_after`), once
    /// worked out: asked for every call in every expression checked, and
    /// fixed once the definition is, like `result_heads`.
    pub(crate) performs: RefCell<HashMap<(DefId, usize, usize, bool), bool>>,
    /// The interfaces declared so far (docs/proposals/interfaces.md §5.1).
    interfaces: HashMap<DataId, interfaces::InterfaceInfo>,
    /// The global instances, by interface and head (§5.6).
    instances: HashMap<(DataId, DataId), interfaces::InstanceInfo>,
    /// The module that declared each data type (§5.6 rule 1).
    data_owners: HashMap<DataId, String>,
    /// The instance steps each obligation tree has taken so far (§5.5 step
    /// 7), by its first metavariable. Not part of the inference state
    /// `undo.rs` restores: steps spent aren't refunded.
    instance_steps: RefCell<HashMap<usize, usize>>,
    /// For tests: the instance step budget, instead of the default.
    pub instance_budget: Option<usize>,
    /// For tests: `+ * < <=` on `Nat` and `Int` always find their
    /// dictionary and project its field, instead of building the term the
    /// projection would give directly when no dictionary of the interface is
    /// in scope (docs/proposals/interfaces.md §5.13, D187: the two must be
    /// the same).
    pub uniform_operators: bool,
    /// For tests: how many times finding an instance has had to wait
    /// (`auto.rs`), in this session.
    pub instance_waits: std::cell::Cell<usize>,
    /// Whether an instance's signature is being elaborated: there, a data
    /// type's `auto` parameter must be written as a variable
    /// (docs/proposals/interfaces.md §7.5).
    in_instance_signature: std::cell::Cell<bool>,
    /// What the code navigation index records, when it's on (`nav.rs`).
    nav: Option<RefCell<nav::Recorder>>,
    /// Where library files' results are kept between runs, if anywhere
    /// (`cache`).
    check_cache: Option<Rc<dyn cache::Store>>,
    cache_stats: cache::Stats,
    /// For the check cache: each project namespace's sources, hashed by
    /// the host (`cache::Elaborator::set_namespace_sources`), and each
    /// namespace's key once worked out (the keys of its dependencies are
    /// part of it).
    namespace_sources: HashMap<String, cache::Key>,
    namespace_keys: HashMap<String, cache::Key>,
    /// While a project namespace that may be cached is elaborated: what it
    /// is compared against at the end (`cache`).
    namespace_capture: Option<cache::Capture>,
    /// The namespace's files were already walked for navigation by a
    /// replay that failed part way (`cache`): don't walk them again.
    skip_navigation_walk: bool,
    /// The names such a replay declared (as failures) before it failed:
    /// the namespace's first pass claims them again rather than finding
    /// them taken (`cache`, `new_module_name`).
    replayed_names: std::collections::HashSet<String>,
    /// For tests: every namespace replay fails part way
    /// (`fail_namespace_replays_late`).
    fail_replays_late: bool,
    /// For the rewind test: a project's driver checks each namespace, rewinds
    /// to just before it, and checks it again (`rewind.rs`).
    #[doc(hidden)]
    pub recheck_namespaces: bool,
    /// The files `include` read in the namespace being elaborated, with a
    /// hash of their text, for its cache entry.
    include_trace: RefCell<Vec<(String, cache::Key)>>,
    /// A hash of the whole standard library's text, for the keys of
    /// project namespaces.
    library_digest: std::cell::OnceCell<cache::Key>,
}

/// A pattern that matches a constructor.
struct CtorPattern<'a> {
    data: DataId,
    ctor: usize,
    args: Vec<Pat<'a>>,
    span: Span,
}

/// A pattern during compilation: one from the source, or one made by the
/// compiler (a wildcard for a field, or `n - 1` inside a number pattern `n`).
type Pat<'a> = Cow<'a, Pattern>;

/// The variable a pattern binds, if it's a variable from the source.
fn pattern_var<'a>(pattern: &Pat<'a>) -> Option<&'a ast::Name> {
    match pattern {
        Cow::Borrowed(Pattern::Var(x)) => Some(x),
        _ => None,
    }
}

/// The variables the patterns bind, left to right as written.
pub(crate) fn written_names(patterns: &[Pattern]) -> Vec<&str> {
    fn walk<'a>(pattern: &'a Pattern, out: &mut Vec<&'a str>) {
        match pattern {
            Pattern::Var(x) => out.push(&x.text),
            Pattern::Ctor(_, args, _) => args.iter().for_each(|p| walk(p, out)),
            Pattern::Tuple(a, b, _) | Pattern::Cons(a, b, _) => {
                walk(a, out);
                walk(b, out);
            }
            Pattern::Record { fields, .. } => fields.iter().for_each(|(_, p)| walk(p, out)),
            Pattern::Named(_, p, _) => walk(p, out),
            Pattern::Wildcard(_)
            | Pattern::Absurd(_)
            | Pattern::Num(..)
            | Pattern::NegNum(..)
            | Pattern::Char(..)
            | Pattern::Nil(_) => {}
        }
    }
    let mut out = Vec::new();
    patterns.iter().for_each(|p| walk(p, &mut out));
    out
}

/// One equation during pattern-match compilation: the patterns still to be
/// matched, and the pattern variables already bound (to de Bruijn levels).
#[derive(Clone)]
struct Row<'a> {
    pats: Vec<Pat<'a>>,
    aliases: Vec<(&'a str, usize)>,
    /// The variables the equation's patterns bind, in the order written.
    written: Vec<&'a str>,
    /// `None` for an equation with an absurd pattern `()`.
    rhs: Option<&'a Expr>,
    span: Span,
}

/// A compiled pattern match, before its right-hand sides are checked.
enum Tree<'a> {
    Leaf {
        aliases: Vec<(&'a str, usize)>,
        /// The variables the arm binds, in the order written.
        written: Vec<&'a str>,
        /// The levels of char patterns' proof fields (`canonical`).
        canon: Vec<usize>,
        rhs: Option<&'a Expr>,
        span: Span,
    },
    /// The variable at `level` has a type with no values.
    Absurd { level: usize, span: Span },
    /// No arm matches this constructor of an indexed family: right if it
    /// can't be here, or if one of the variables at `columns` has a type
    /// with no possible constructor (docs/proposals/indexed-families.md §7.3).
    Missing { columns: Vec<usize>, span: Span },
    Case {
        /// The level of the variable being matched.
        level: usize,
        data: DataId,
        branches: Vec<(Vec<Name>, Tree<'a>)>,
        span: Span,
    },
    /// The variable at `level` is a `Nat`, compared with numbers in
    /// increasing order (docs/proposals/number-patterns.md).
    NumCase {
        level: usize,
        arms: Vec<(BigUint, Tree<'a>)>,
        default: Box<Tree<'a>>,
        span: Span,
    },
}

/// What a pattern column's type is, as far as number patterns go.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NumberKind {
    Nat,
    Int,
    /// Some other type, or not known.
    Other,
}

/// The indefinite article for a type name: `an` before a vowel, `a` otherwise.
pub(crate) fn article(name: &str) -> &'static str {
    match name.chars().next() {
        Some('A' | 'E' | 'I' | 'O' | 'U' | 'a' | 'e' | 'i' | 'o' | 'u') => "an",
        _ => "a",
    }
}

/// The error for a negative number pattern where a `Nat` is matched.
fn negative_nat(span: Span) -> Diagnostic {
    Diagnostic::error("E-TYPE-MISMATCH", "a `Nat` can't be negative")
        .with_label(span, "this is negative, but it matches a `Nat`")
        .with_note("use an `Int` for numbers that can be negative")
}

/// Lists numbers for an error: all of up to five, or the first five and `…`.
/// `count` is how many `keys` yields.
/// A character as written inside single quotes in source.
fn escape_char(c: char) -> String {
    match c {
        '\n' => "\\n".into(),
        '\t' => "\\t".into(),
        '\r' => "\\r".into(),
        '\\' => "\\\\".into(),
        '\'' => "\\'".into(),
        c if c.is_ascii_graphic() || c == ' ' || c.is_alphanumeric() => c.to_string(),
        c => format!("\\u{{{:X}}}", u32::from(c)),
    }
}

fn list_numbers(keys: impl Iterator<Item = String>, count: usize) -> String {
    let mut shown: Vec<String> = keys.take(5).collect();
    match (count, shown.pop()) {
        (n, Some(last)) if n <= 5 && !shown.is_empty() => {
            format!("{} and {last}", shown.join(", "))
        }
        (n, Some(last)) if n <= 5 => last,
        (_, last) => format!("{}, {}, …", shown.join(", "), last.unwrap_or_default()),
    }
}

fn error(code: &'static str, span: Span, message: impl Into<String>) -> Diagnostic {
    let message = message.into();
    Diagnostic::error(code, message.clone()).with_label(span, message)
}

fn name(n: &ast::Name) -> Name {
    n.text.as_str().into()
}

impl Elaborator {
    pub fn new() -> Self {
        let e = Self::default();
        // Glued evaluation (docs/proposals/folded-calls.md) is built in
        // stages and off by default; `STITCHWORT_GLUE=1` turns it on while
        // elaborating, to test the stages before it is.
        e.globals
            .glue
            .set(std::env::var("STITCHWORT_GLUE").is_ok_and(|v| v == "1"));
        e
    }

    /// Elaborates a closed expression, and infers its type with the kernel.
    /// One operation, with its own resource limits.
    pub fn infer_expr(&self, expr: &Expr) -> Result<(Term, Value)> {
        let _op = self.globals.budget.operation(self.limits);
        self.infer_expr_in_operation(expr)
            .map_err(|d| self.locate(d, expr.span()))
    }

    /// The definition with key `key` (its full name), if there is one.
    pub fn lookup_def(&self, key: &str) -> Option<DefId> {
        match self.scope.get(key) {
            Some((Global::Def(id), _)) => Some(id),
            _ => None,
        }
    }

    /// The definitions checked as part of namespace `namespace` of the
    /// project, as indices into `globals.defs`; empty if it wasn't checked.
    pub fn namespace_def_range(&self, namespace: &str) -> std::ops::Range<usize> {
        self.namespace_defs.get(namespace).cloned().unwrap_or(0..0)
    }

    /// Whether anything at all has key `key`.
    pub fn has_key(&self, key: &str) -> bool {
        self.scope.get(key).is_some()
    }

    /// The single-component names directly under namespace `namespace`
    /// (`namespace.x`, not `%` names), from the scope: what `import N (..)`
    /// brings once `N` is checked.
    pub fn direct_keys(&self, namespace: &str) -> std::collections::BTreeSet<String> {
        let prefix = format!("{namespace}.");
        self.scope
            .keys()
            .filter_map(|k| k.strip_prefix(&prefix))
            .filter(|x| !x.contains('.') && !x.starts_with('%'))
            .map(str::to_string)
            .collect()
    }

    /// The keys of the definitions whose keys start with `prefix`, sorted.
    pub fn def_keys_under(&self, prefix: &str) -> Vec<String> {
        let mut keys: Vec<String> = self
            .scope
            .keys()
            .filter(|k| k.starts_with(prefix))
            .filter(|k| matches!(self.scope.get(k), Some((Global::Def(_), _))))
            .cloned()
            .collect();
        keys.sort();
        keys
    }

    /// Forgets the module's namespace and imports, so names typed in
    /// afterwards (the `run` call, `eval`) see no namespace and no imports,
    /// and reach a project's names only qualified
    /// (docs/proposals/multi-file.md §9.1).
    pub fn leave_namespace(&mut self) {
        self.namespace_root = String::new();
        self.scope.clear_imports();
        self.module = module::ModuleState::default();
    }

    /// Adds `import` lines typed into the REPL to the imports names typed in
    /// see, after any the loaded file has: they accumulate. Returns the
    /// errors and warnings, as a file's imports would give.
    pub fn add_session_imports(
        &mut self,
        imports: &[stitchwort_syntax::ast::Import],
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        self.add_imports(imports, false, &mut diagnostics);
        self.add_imports(imports, true, &mut diagnostics);
        diagnostics
    }

    /// Ends loading the core: every core built-in must be bound by now. (A
    /// library built-in is bound when its file loads.)
    pub fn finish_core(&mut self) -> Result<()> {
        self.loading_prelude = false;
        // The prelude's imports are its own.
        self.scope.clear_imports();
        self.prelude_defs = self.globals.defs.len();
        registry::check_complete_core(&self.globals)
    }

    /// Checks that every built-in is bound, library ones too: for a test
    /// that has loaded every library file.
    pub fn check_registry_complete(&self) -> Result<()> {
        registry::check_complete(&self.globals)
    }

    /// Elaborates and evaluates a closed expression: its value and its type,
    /// printed. One operation, with its own resource limits, including
    /// printing the value.
    pub fn eval_expr(&self, expr: &Expr) -> Result<(String, String)> {
        let _op = self.globals.budget.operation(self.limits);
        let run = || -> Result<(String, String)> {
            let (term, ty) = self.infer_expr_in_operation(expr)?;
            let value = eval(&self.globals, &[], &term)?;
            let g = &self.globals;
            let show = |v: &Value| -> std::result::Result<String, stitchwort_core::ResourceError> {
                pretty::term_in_full(g, &[], &stitchwort_core::value::quote(g, 0, v)?)
            };
            Ok((show(&value)?, show(&ty)?))
        };
        run().map_err(|d| self.locate(d, expr.span()))
    }

    /// A diagnostic without a location (running out of resources) is
    /// reported at `span`.
    fn locate(&self, d: Diagnostic, span: Span) -> Diagnostic {
        if d.labels.is_empty() {
            d.with_label(span, "while evaluating this")
        } else {
            d
        }
    }

    fn infer_expr_in_operation(&self, expr: &Expr) -> Result<(Term, Value)> {
        self.clear_metas();
        let (term, ty) = {
            let mut cx = Ctx::new(self, expr.span());
            let (mut term, mut ty) = infer(&mut cx, expr)?;
            // A call gets its trailing implicit and auto arguments too (so
            // `div 7 2` gets its proof); a bare name like `length` keeps its
            // polymorphic type.
            if matches!(expr, Expr::App(..) | Expr::Binary(..)) {
                (term, ty) = check::insert(&mut cx, term, ty)?;
            }
            (term, cx.quote(&ty)?)
        };
        let term = self.finish(&term, 0)?;
        self.finish(&ty, 0)?;
        self.clear_metas();
        kernel::without_glue(&self.globals, || {
            kernel::infer_closed(&self.globals, &term, expr.span())
        })
    }

    pub fn eval(&self, term: &Term) -> std::result::Result<Value, stitchwort_core::ResourceError> {
        eval(&self.globals, &[], term)
    }

    /// Prints a closed value, as one operation: a part too large or nested
    /// too deeply to print within its limits is shown as `…`.
    pub fn show(&self, value: &Value) -> String {
        let _op = self.globals.budget.operation(self.limits);
        pretty::value(&self.globals, &[], value)
    }

    fn clear_metas(&self) {
        self.flush_navigation();
        self.globals.clear_metas();
        self.drafts.borrow_mut().clear();
        self.local_metas.borrow_mut().clear();
        self.obligations.borrow_mut().clear();
        self.defaulted.borrow_mut().clear();
        self.instance_steps.borrow_mut().clear();
    }

    /// Proves outstanding auto arguments, then substitutes metavariable
    /// solutions into `term`, failing if any are unsolved.
    fn finish(&self, term: &Term, level: usize) -> Result<Term> {
        self.solve_obligations()?;
        self.zonk(term, level)
    }

    /// Substitutes metavariable solutions into `term`, failing if any are
    /// unsolved.
    fn zonk(&self, term: &Term, level: usize) -> Result<Term> {
        self.zonk_keeping(term, level, &|_| false)
    }

    /// [`Elaborator::zonk`], leaving the unsolved metavariables `keep`
    /// allows in place.
    pub(crate) fn zonk_keeping(
        &self,
        term: &Term,
        level: usize,
        keep: &dyn Fn(usize) -> bool,
    ) -> Result<Term> {
        self.zonk_around(term, level, keep, &[])
    }

    /// [`Elaborator::zonk_keeping`] for a term inside the `let`s `lets` of
    /// its context (`unify::zonk_in`).
    pub(crate) fn zonk_around(
        &self,
        term: &Term,
        level: usize,
        keep: &dyn Fn(usize) -> bool,
        lets: &[unify::Around],
    ) -> Result<Term> {
        unify::zonk_in(&self.globals, level, term, keep, lets).map_err(|e| match e {
            unify::ZonkError::Resource(e) => e.into(),
            unify::ZonkError::Unsolved(m) if self.local_metas.borrow().contains_key(&m) => {
                let span = self.globals.metas.borrow()[m].span;
                let name = self.local_metas.borrow()[&m].clone();
                Diagnostic::error(
                    "E-LOCAL-DEFINITION",
                    format!("the local definition `{name}` can't be used here"),
                )
                .with_label(span, "defined here")
                .with_note(
                    "local definitions can be used in a definition's, theorem's or test's \
                     body; here, define it at top level instead",
                )
            }
            unify::ZonkError::Unsolved(m) if self.globals.meta_frozen(m) => {
                let span = self.globals.metas.borrow()[m].span;
                Diagnostic::error(
                    "E-MATCH-MOTIVE",
                    "a `match` can't be used here: it can't be made into a definition",
                )
                .with_label(span, "this `match`")
                .with_note(
                    "a top-level helper with a written signature can always do what this \
                     `match` would: define one and call it",
                )
            }
            unify::ZonkError::Unsolved(m) => {
                let span = self.globals.metas.borrow()[m].span;
                Diagnostic::error("E-UNSOLVED", "can't work out an implicit argument")
                    .with_label(span, "the compiler couldn't work out what goes here")
                    .with_note("supply it explicitly with `f [x := …]`, or add a type annotation")
            }
        })
    }

    fn test(&mut self, name: &str, expr: &Expr, span: Span) -> Result<()> {
        self.module.phase = Phase::Body;
        // A test's name is unique in its namespace in a project, and in the
        // session for a file.
        let from = if self.module.closure.is_some() {
            self.module.first_test
        } else {
            0
        };
        if let Some(earlier) = self.tests[from..].iter().find(|t| t.name == name) {
            return Err(error(
                "E-DUPLICATE",
                span,
                format!("there's already a test called \"{name}\""),
            )
            .with_label(earlier.span, "first defined here"));
        }
        let Some(bool_data) = self.globals.registry.data(Builtin::Bool) else {
            return Err(error(
                "E-UNKNOWN-NAME",
                span,
                "tests need the prelude's `Bool`",
            ));
        };
        let label: Name = if self.loading_prelude {
            format!("test \"{name}\"")
        } else {
            format!("{}test \"{name}\"", self.root())
        }
        .into();
        self.local_helpers.clear();
        self.preadmitted.borrow_mut().clear();
        let shown = ast::Name {
            text: label.to_string(),
            span,
        };
        let body = self.with_local_retries(&label, &shown, |e| {
            *e.sides_capture.borrow_mut() = SidesCapture {
                target: numbers::comparison_span(expr),
                found: None,
            };
            let term = {
                // A condition, as `if` takes: a `Bool`, or a decided proposition.
                let mut cx = Ctx::new(e, span);
                logic::bool_operand(&mut cx, expr, "test")?
            };
            // Nothing refers to the test, so its helpers are admitted first.
            e.lift(&label, false)?;
            let body = e.finish(&term, 0)?;
            // The sides are only for showing a failure: if they can't be
            // finished, the test just has none.
            let found = e.sides_capture.borrow_mut().found.take();
            let sides = found.and_then(|s| {
                Some(TestSides {
                    op: s.op,
                    left: e.finish(&s.left, 0).ok()?,
                    right: e.finish(&s.right, 0).ok()?,
                })
            });
            Ok((body, sides))
        })?;
        let (body, sides) = body;
        self.sides_capture.borrow_mut().target = None;
        self.local_helpers.clear();
        let ty = Term::Data(bool_data, Vec::new());
        let id = kernel::declare_def(&mut self.globals, &label, &ty, false, false, span)?;
        kernel::define_def(&mut self.globals, id, &body)?;
        self.tests.push(TestDecl {
            library: self.loading_prelude,
            name: name.to_string(),
            namespace: self.module.namespace.clone().unwrap_or_default(),
            def: id,
            span,
            sides,
        });
        Ok(())
    }

    /// `ability A params where op : X -> {A params} Y …`, as three generated
    /// declarations (see `effects`): the data type of its operations
    /// (constructors `A.op`), `A.res` giving each operation's result type,
    /// and the eliminator `A.elim` that handlers use.
    fn ability(&mut self, decl: &Decl) -> Result<()> {
        use ast::{Binder, CtorDecl, Expr};
        let Decl::Ability {
            name: ability,
            params,
            ops,
            span,
        } = decl
        else {
            unreachable!()
        };
        let ability_key = self.check_new_name(ability)?;
        let n = |text: String| ast::Name { text, span: *span };
        let var = |text: &str| Expr::Var(n(text.to_string()));
        let apps = |head: Expr, args: Vec<Expr>| {
            args.into_iter()
                .fold(head, |f, a| Expr::App(Box::new(f), Box::new(a)))
        };
        let param_names: Vec<ast::Name> = params.iter().flat_map(|b| b.names.clone()).collect();
        let applied = apps(
            var(&ability.text),
            param_names.iter().map(|p| var(&p.text)).collect(),
        );

        // Each operation is `x : A -> {Ability params} B`.
        let mut sigs = Vec::new();
        for (op, ty) in ops {
            self.check_new_key(&Self::member_key(&ability_key, &op.text), op)?;
            let bad = || {
                error(
                    "E-ABILITY",
                    ty.span(),
                    format!(
                        "an operation's type must be `A -> {{{} …}} B`",
                        ability.text
                    ),
                )
            };
            let (x, dom, row, cod) = match ty {
                Expr::Arrow(a, b) => match b.as_ref() {
                    Expr::Effect(row, cod) => (None, a.as_ref(), row, cod.as_ref()),
                    _ => return Err(bad()),
                },
                Expr::Pi {
                    names,
                    implicit: false,
                    dom,
                    cod,
                    ..
                } if names.len() == 1 => match cod.as_ref() {
                    Expr::Effect(row, cod) => {
                        (Some(names[0].clone()), dom.as_ref(), row, cod.as_ref())
                    }
                    _ => return Err(bad()),
                },
                _ => return Err(bad()),
            };
            let only_self = row.tail.is_none()
                && row.abilities.len() == 1
                && matches!(
                    {
                        let mut h = &row.abilities[0];
                        while let Expr::App(f, _) = h {
                            h = f;
                        }
                        h
                    },
                    Expr::Var(v) if v.text == ability.text
                );
            if !only_self {
                return Err(error(
                    "E-ABILITY",
                    row.span,
                    format!(
                        "an operation of `{}` performs just `{}`",
                        ability.text, ability.text
                    ),
                ));
            }
            // Its argument and result can't use the ability itself: that's
            // Landin's knot (`Cell` in DESIGN.md §8).
            for (part, what) in [(dom, "argument"), (cod, "result")] {
                if mentions_ability(part, &ability.text) {
                    return Err(error(
                        "E-ABILITY",
                        part.span(),
                        format!(
                            "an operation's {what} can't perform `{}` itself",
                            ability.text
                        ),
                    )
                    .with_note(
                        "storing or returning a computation that uses the same ability could \
                         loop forever (Landin's knot)",
                    ));
                }
            }
            sigs.push((op.clone(), x, dom.clone(), cod.clone()));
        }
        // Each operation's constructor has a name source can't write, so the
        // operation's own name is free for the operation (`State.get`).
        let ctor_name = |op: &ast::Name| n(format!("%{}", op.text));
        let ctor_ref = |op: &ast::Name| n(format!("{}.%{}", ability.text, op.text));
        let x_name = |x: &Option<ast::Name>| x.clone().unwrap_or_else(|| n("x".into()));

        // type A params : Type = | A.op (x : X) …
        let data_decl = Decl::Data {
            name: ability.clone(),
            params: params.clone(),
            auto_params: vec![false; params.len()],
            indices: Vec::new(),
            sort: None,
            ctors: sigs
                .iter()
                .map(|(op, x, dom, _)| CtorDecl {
                    name: ctor_name(op),
                    fields: vec![Binder {
                        names: vec![x_name(x)],
                        ty: dom.clone(),
                    }],
                    implicit: Vec::new(),
                    result: None,
                })
                .collect(),
            record: false,
            interface: false,
            span: *span,
        };
        self.data(&data_decl)?;
        let Some((Global::Data(op_data), _)) = self.scope.get(&ability_key) else {
            unreachable!("just declared");
        };

        // A.res : (params) -> A params -> Type
        let res_name = n(format!("{}.%res", ability.text));
        let mut res_ty = Expr::Arrow(Box::new(applied.clone()), Box::new(Expr::Type(0, *span)));
        for binder in params.iter().rev() {
            res_ty = Expr::Pi {
                names: binder.names.clone(),
                implicit: false,
                auto: false,
                dom: Box::new(binder.ty.clone()),
                cod: Box::new(res_ty),
                span: *span,
            };
        }
        let res_sig = Decl::Signature {
            name: res_name.clone(),
            ty: res_ty,
            theorem: false,
            export: false,
            synonym: false,
            instance: false,
            decreasing: None,
            span: *span,
        };
        let res_eqs: Vec<Decl> = sigs
            .iter()
            .map(|(op, x, _, cod)| {
                let mut patterns: Vec<Pattern> = param_names
                    .iter()
                    .map(|p| Pattern::Var(p.clone()))
                    .collect();
                patterns.push(Pattern::Ctor(
                    ctor_ref(op),
                    vec![Pattern::Var(x_name(x))],
                    *span,
                ));
                Decl::Equation {
                    name: res_name.clone(),
                    patterns,
                    rhs: Some(cod.clone()),
                    arm: None,
                    span: *span,
                }
            })
            .collect();
        self.definition(&res_sig, &res_eqs)?;
        let Some((Global::Def(res), _)) = self.scope.get(&Self::member_key(&ability_key, "%res"))
        else {
            unreachable!("just defined");
        };

        // A.elim : [params] -> [r : Type] -> ((x : X) -> (Y -> r) -> r) -> … ->
        //   (o : A params) -> (A.res params o -> r) -> r
        let elim_name = n(format!("{}.%elim", ability.text));
        let r = || var("%r");
        let clause = |i: usize| format!("%clause{i}");
        let res_of_o = apps(
            var(&res_name.text),
            param_names
                .iter()
                .map(|p| var(&p.text))
                .chain([var("%o")])
                .collect(),
        );
        let mut elim_ty = Expr::Pi {
            names: vec![n("%o".into())],
            implicit: false,
            auto: false,
            dom: Box::new(applied.clone()),
            cod: Box::new(Expr::Arrow(
                Box::new(Expr::Arrow(Box::new(res_of_o), Box::new(r()))),
                Box::new(r()),
            )),
            span: *span,
        };
        for (i, (_, x, dom, cod)) in sigs.iter().enumerate().rev() {
            let k_ty = Expr::Arrow(Box::new(cod.clone()), Box::new(r()));
            let clause_ty = Expr::Pi {
                names: vec![x_name(x)],
                implicit: false,
                auto: false,
                dom: Box::new(dom.clone()),
                cod: Box::new(Expr::Arrow(Box::new(k_ty), Box::new(r()))),
                span: *span,
            };
            elim_ty = Expr::Pi {
                names: vec![n(clause(i))],
                implicit: false,
                auto: false,
                dom: Box::new(clause_ty),
                cod: Box::new(elim_ty),
                span: *span,
            };
        }
        elim_ty = Expr::Pi {
            names: vec![n("%r".into())],
            implicit: true,
            auto: false,
            dom: Box::new(Expr::Type(0, *span)),
            cod: Box::new(elim_ty),
            span: *span,
        };
        for binder in params.iter().rev() {
            elim_ty = Expr::Pi {
                names: binder.names.clone(),
                implicit: true,
                auto: false,
                dom: Box::new(binder.ty.clone()),
                cod: Box::new(elim_ty),
                span: *span,
            };
        }
        let elim_sig = Decl::Signature {
            name: elim_name.clone(),
            ty: elim_ty,
            theorem: false,
            export: false,
            synonym: false,
            instance: false,
            decreasing: None,
            span: *span,
        };
        let elim_eqs: Vec<Decl> = sigs
            .iter()
            .enumerate()
            .map(|(i, (op, x, _, _))| {
                let mut patterns: Vec<Pattern> = (0..sigs.len())
                    .map(|j| Pattern::Var(n(clause(j))))
                    .collect();
                patterns.push(Pattern::Ctor(
                    ctor_ref(op),
                    vec![Pattern::Var(x_name(x))],
                    *span,
                ));
                patterns.push(Pattern::Var(n("%k".into())));
                Decl::Equation {
                    name: elim_name.clone(),
                    patterns,
                    rhs: Some(apps(var(&clause(i)), vec![var(&x_name(x).text), var("%k")])),
                    arm: None,
                    span: *span,
                }
            })
            .collect();
        self.definition(&elim_sig, &elim_eqs)?;
        let Some((Global::Def(elim), _)) = self.scope.get(&Self::member_key(&ability_key, "%elim"))
        else {
            unreachable!("just defined");
        };

        let index = self.abilities.len();
        self.abilities.push(effects::AbilityInfo {
            name: scope::display(&ability_key).to_string(),
            op_data,
            res,
            elim,
            ops: sigs.iter().map(|(op, ..)| op.text.clone()).collect(),
            order: (
                !ability_key.starts_with("Std."),
                self.globals
                    .path(&scope::display(&ability_key).into())
                    .to_string(),
            ),
        });
        self.scope
            .insert(&ability_key, Global::Ability(index), ability.span, false);
        for (i, (op, ..)) in sigs.iter().enumerate() {
            let key = Self::member_key(&ability_key, &op.text);
            self.scope.insert(&key, Global::Op(index, i), op.span, true);
        }
        Ok(())
    }

    /// The key a declaration named `n` gets, if it's free.
    fn check_new_name(&self, n: &ast::Name) -> Result<String> {
        let key = self.declaration_key(n)?;
        self.check_new_key(&key, n)?;
        Ok(key)
    }

    fn check_new_key(&self, key: &str, n: &ast::Name) -> Result<()> {
        if RESERVED.contains(&n.text.as_str()) {
            return Err(error(
                "E-DUPLICATE",
                n.span,
                format!("`{}` is built in and can't be redefined", n.text),
            ));
        }
        // Claimed for this declaration when the module's names were
        // collected.
        if let Some((Global::Unchecked(item), _)) = self.scope.get(key)
            && self.module.in_current(item)
        {
            return Ok(());
        }
        if let Some((_, previous)) = self.scope.get(key) {
            return Err(error(
                "E-DUPLICATE",
                n.span,
                format!("`{}` is already defined", n.text),
            )
            .with_label(previous, "first defined here"));
        }
        Ok(())
    }

    /// A data type on its own (one in a component of its own, or one an
    /// ability generates).
    fn data(&mut self, decl: &Decl) -> Result<()> {
        let item = self.module.item;
        match self.data_group(&[(item, decl)]).into_iter().next() {
            Some((_, d)) => Err(d),
            None => Ok(()),
        }
    }

    /// A group of data types whose constructors may mention each other (or
    /// one data type), each with the module item that declares it: every
    /// header, then every constructor, then the kernel admits them together,
    /// or none of them (docs/proposals/mutual-recursion.md §5.4). Members
    /// must have the same parameters and universe, which the kernel checks
    /// once, for the whole group. The diagnostics, each with the item it's
    /// about.
    fn data_group(
        &mut self,
        members: &[(Option<usize>, &Decl)],
    ) -> Vec<(Option<usize>, Diagnostic)> {
        let mut out = Vec::new();
        let mut headers = Vec::new();
        let mut member_indices = Vec::new();
        for &(item, decl) in members {
            if item.is_some() {
                self.module.item = item;
            }
            match self.data_header(decl) {
                Ok((params, indices, sort)) => {
                    headers.push((params, sort));
                    member_indices.push(indices);
                }
                Err(d) => out.push((item, d)),
            }
        }
        if !out.is_empty() {
            return out;
        }
        let ((params, sort), first) = (headers[0].clone(), members[0].1);
        for (&(item, decl), header) in members.iter().zip(&headers).skip(1) {
            if let Err(d) = self.same_header(first, &headers[0], decl, header) {
                out.push((item, d));
            } else if let Err(d) = Self::same_auto_params(first, decl) {
                out.push((item, d));
            }
        }
        if !out.is_empty() {
            return out;
        }
        let names: Vec<kernel::DataDecl> = members
            .iter()
            .zip(member_indices)
            .map(|(&(_, decl), indices)| match decl {
                Decl::Data {
                    name: n,
                    span,
                    record,
                    ..
                } => kernel::DataDecl {
                    name: self
                        .declaration_key(n)
                        .map_or_else(|_| name(n), |k| scope::display(&k).into()),
                    span: *span,
                    record: *record,
                    indices,
                },
                _ => unreachable!(),
            })
            .collect();
        let ids = match kernel::declare_indexed_data_group(&mut self.globals, params, sort, names) {
            Ok(ids) => ids,
            Err(d) => return vec![(members[0].0, d)],
        };
        // Every member can be mentioned in fields now, as a type. None has
        // constructors until the kernel admits them all.
        let owner = self.module_owner();
        let mut group_interfaces = Vec::new();
        for (&(_, decl), d) in members.iter().zip(&ids) {
            kernel::mark_auto_params(&mut self.globals, *d, Self::data_auto_params(decl));
            self.data_owners.insert(*d, owner.clone());
            if let Decl::Data {
                interface: true, ..
            } = decl
            {
                group_interfaces.push(*d);
            }
            if let Decl::Data { name: n, .. } = decl
                && let Ok(key) = self.declaration_key(n)
            {
                self.scope.insert(&key, Global::Data(*d), n.span, false);
            }
        }
        let mut defined = Vec::new();
        for (&(item, decl), d) in members.iter().zip(&ids) {
            if item.is_some() {
                self.module.item = item;
            }
            match self.data_ctors(decl, *d, &group_interfaces) {
                Ok(ctors) => defined.push((*d, ctors)),
                Err(d) => out.push((item, d)),
            }
        }
        if !out.is_empty() {
            self.fail_data_names(members);
            return out;
        }
        if members[0].0.is_some() {
            self.module.item = members[0].0;
        }
        if let Err(d) = kernel::define_data_group(&mut self.globals, defined) {
            self.fail_data_names(members);
            return vec![(members[0].0, d)];
        }
        for (&(item, decl), d) in members.iter().zip(&ids) {
            if let Err(e) = self.after_data(decl, *d) {
                out.push((item, e));
            }
        }
        out
    }

    /// A data group that was declared but not admitted has no constructors
    /// (a record, no field list), so its names stop meaning anything: uses
    /// report that they refer to something that failed.
    fn fail_data_names(&mut self, members: &[(Option<usize>, &Decl)]) {
        for (_, decl) in members {
            if let Decl::Data { name: n, .. } = decl
                && let Ok(key) = self.declaration_key(n)
                && let Some((global, _)) = self.scope.entries.get_mut(&key)
            {
                *global = Global::Failed;
            }
        }
    }

    /// Elaborates a data type's parameters and universe.
    #[allow(clippy::type_complexity)]
    fn data_header(&mut self, decl: &Decl) -> Result<(Vec<(Name, Term)>, Vec<(Name, Term)>, Sort)> {
        let Decl::Data {
            name: data_name,
            params,
            auto_params,
            indices,
            sort,
            record,
            span,
            ..
        } = decl
        else {
            unreachable!()
        };
        self.check_new_name(data_name)?;
        self.clear_metas();
        self.module.phase = Phase::Header;
        let mut cx = Ctx::new(self, *span);
        let mut checked = Vec::new();
        for (binder, auto) in params.iter().zip(auto_params) {
            let (ty, _) = check_type(&mut cx, &binder.ty)?;
            if *auto {
                self.check_data_auto(&mut cx, binder, &ty)?;
            }
            for (k, n) in binder.names.iter().enumerate() {
                let ty = self.finish(&ty.shift(&self.globals, k, 0)?, cx.level())?;
                let value = cx.eval(&ty)?;
                checked.push((name(n), ty));
                cx.bind(&n.text, value);
            }
        }
        // The indices, in the context of the parameters (docs/proposals/indexed-families.md).
        if *record && let Some((_, ty)) = indices.first() {
            return Err(
                error("E-RECORD-INDICES", ty.span(), "a record can't have indices")
                    .with_note("declare it with `|` and a constructor instead of `{ … }`"),
            );
        }
        let mut checked_indices = Vec::new();
        let mut index_sorts = Vec::new();
        for (k, (x, written)) in indices.iter().enumerate() {
            let (ty, s) = check_type(&mut cx, written)?;
            index_sorts.push((s, written.span()));
            let ty = self.finish(&ty, cx.level())?;
            let value = cx.eval(&ty)?;
            let x: Name = x.as_ref().map_or_else(|| format!("i{k}").into(), name);
            cx.bind(&x, value);
            checked_indices.push((x, ty));
        }
        let sort = match sort {
            None => Sort::Type(0),
            Some(e) => {
                let mut cx = Ctx::new(self, e.span());
                match check_type(&mut cx, e)?.0.strip_loc() {
                    Term::Sort(s) => *s,
                    _ => {
                        return Err(error(
                            "E-NOT-A-SORT",
                            e.span(),
                            "expected `Type`, `Type n` or `Prop`",
                        ));
                    }
                }
            }
        };
        if let Decl::Data {
            interface: true, ..
        } = decl
        {
            self.check_interface_header(decl, &checked, sort)?;
        }
        // No large indices (D142): an index's type fits the universe, as a
        // field's must. (The kernel checks it too.)
        if let Some((s, at)) = index_sorts.iter().find(|(s, _)| !s.fits_in(sort)) {
            let show = |s: &Sort| pretty::term(&self.globals, &[], &Term::Sort(*s));
            return Err(error(
                "E-UNIVERSE",
                *at,
                format!(
                    "this index is too large for `{}`: its type is in `{}`, but `{}` is in `{}`",
                    data_name.text,
                    show(s),
                    data_name.text,
                    show(&sort)
                ),
            )
            .with_note(
                "an index's type must fit in the data type's universe, as a field's must: a \
                 type indexed by types lives one universe up, as in `Ty: Type -> Type 1`",
            ));
        }
        Ok((checked, checked_indices, sort))
    }

    /// Whether data type `decl` has the same parameters (names and types) and
    /// universe as `first`, which it's defined together with. The kernel
    /// takes one telescope for the whole group, so this is only for a clear
    /// error.
    fn same_header(
        &self,
        first: &Decl,
        (first_params, first_sort): &(Vec<(Name, Term)>, Sort),
        decl: &Decl,
        (params, sort): &(Vec<(Name, Term)>, Sort),
    ) -> Result<()> {
        let (
            Decl::Data {
                name: first_name, ..
            },
            Decl::Data { name: n, .. },
        ) = (first, decl)
        else {
            unreachable!()
        };
        let g = &self.globals;
        let show_params = |params: &[(Name, Term)]| {
            if params.is_empty() {
                return "no parameters".to_string();
            }
            let mut names: Vec<Name> = Vec::new();
            let mut shown = Vec::new();
            for (x, ty) in params {
                shown.push(format!("({x}: {})", pretty::term(g, &names, ty)));
                names.push(x.clone());
            }
            shown.join(" ")
        };
        let mut same = params.len() == first_params.len();
        let mut env = Vec::new();
        for ((x, ty), (y, first_ty)) in params.iter().zip(first_params) {
            if !same {
                break;
            }
            let level = env.len();
            let (a, b) = (eval(g, &env, ty)?, eval(g, &env, first_ty)?);
            same = x == y && stitchwort_core::value::conv(g, level, &a, &b)?;
            env.push(Value::var(level));
        }
        if !same {
            return Err(Diagnostic::error(
                "E-MUTUAL-PARAMETERS",
                format!(
                    "`{}` and `{}` are defined together, so they must have the same parameters",
                    first_name.text, n.text
                ),
            )
            .with_label(n.span, format!("`{}` has {}", n.text, show_params(params)))
            .with_label(
                first_name.span,
                format!("`{}` has {}", first_name.text, show_params(first_params)),
            )
            .with_note(
                "data types that refer to each other share one list of parameters: write the \
                 same parameters, with the same names, for each",
            ));
        }
        if sort != first_sort {
            let show = |s: &Sort| pretty::term(g, &[], &Term::Sort(*s));
            return Err(Diagnostic::error(
                "E-MUTUAL-PARAMETERS",
                format!(
                    "`{}` and `{}` are defined together, so they must be in the same universe",
                    first_name.text, n.text
                ),
            )
            .with_label(n.span, format!("`{}` is in `{}`", n.text, show(sort)))
            .with_label(
                first_name.span,
                format!("`{}` is in `{}`", first_name.text, show(first_sort)),
            ));
        }
        Ok(())
    }

    /// Elaborates the constructors of data type `d`, declared from `decl`.
    /// `group_interfaces` are the members of its group that are interfaces.
    fn data_ctors(
        &mut self,
        decl: &Decl,
        d: DataId,
        group_interfaces: &[DataId],
    ) -> Result<Vec<kernel::CtorDecl>> {
        let Decl::Data {
            name: data_name,
            ctors,
            span,
            interface,
            ..
        } = decl
        else {
            unreachable!()
        };
        let data_key = self.declaration_key(data_name)?;
        self.module.phase = Phase::Fields;
        let mut core_ctors = Vec::new();
        for (c, ctor) in ctors.iter().enumerate() {
            self.check_new_key(&Self::member_key(&data_key, &ctor.name.text), &ctor.name)?;
            if let Some(earlier) = ctors[..c].iter().find(|e| e.name.text == ctor.name.text) {
                return Err(error(
                    "E-DUPLICATE",
                    ctor.name.span,
                    format!("`{}` is already defined", ctor.name.text),
                )
                .with_label(earlier.name.span, "first defined here"));
            }
            // With indices, a result type or implicit fields
            // (docs/proposals/indexed-families.md §7.1).
            if !self.globals.data(d).indices.is_empty()
                || ctor.result.is_some()
                || ctor.implicit.contains(&true)
            {
                core_ctors.push(self.family_ctor(d, ctor, *span)?);
                continue;
            }
            self.clear_metas();
            let mut cx = Ctx::new(self, *span);
            for (x, ty) in &self.globals.data(d).params {
                let value = cx.eval(ty)?;
                cx.bind(x, value);
            }
            let mut fields = Vec::new();
            for (k, binder) in ctor.fields.iter().enumerate() {
                if let Some(earlier) = ctor.fields[..k]
                    .iter()
                    .flat_map(|b| &b.names)
                    .find(|e| binder.names.iter().any(|n| n.text == e.text))
                {
                    return Err(error(
                        "E-DUPLICATE",
                        binder.names[0].span,
                        format!("there's already a field `{}`", earlier.text),
                    )
                    .with_label(earlier.span, "first declared here"));
                }
                let (ty, _) = check_type(&mut cx, &binder.ty)?;
                for (k, n) in binder.names.iter().enumerate() {
                    let ty = self.finish(&ty.shift(&self.globals, k, 0)?, cx.level())?;
                    let value = cx.eval(&ty)?;
                    if *interface {
                        self.check_interface_field(d, group_interfaces, n, &value)?;
                    }
                    fields.push((name(n), ty, binder.ty.span()));
                    cx.bind(&n.text, value);
                }
            }
            core_ctors.push(kernel::CtorDecl {
                name: name(&ctor.name),
                fields,
                result: Vec::new(),
                implicit: Vec::new(),
            });
        }
        Ok(core_ctors)
    }

    /// After a data type is admitted: registering builtins (in the prelude),
    /// and making its constructors' names refer to them.
    fn after_data(&mut self, decl: &Decl, d: DataId) -> Result<()> {
        let Decl::Data {
            name: data_name,
            ctors,
            ..
        } = decl
        else {
            unreachable!()
        };
        let data_key = self.declaration_key(data_name)?;
        for (c, ctor) in ctors.iter().enumerate() {
            let key = Self::member_key(&data_key, &ctor.name.text);
            self.scope
                .insert(&key, Global::Ctor(d, c), ctor.name.span, true);
        }
        if self.loading_prelude {
            self.bind_builtin_data(d)?;
        }
        if self.globals.data(d).record {
            let interface = matches!(
                decl,
                Decl::Data {
                    interface: true,
                    ..
                }
            );
            self.after_record(d, interface)?;
        } else {
            self.unnoted(|e| {
                e.derive_data_eq(d)?;
                e.derive_data_show(d)?;
                e.derive_data_ord(d)
            })?;
        }
        Ok(())
    }

    /// A definition on its own (one an ability generates): its signature,
    /// then its body.
    fn definition(&mut self, signature: &Decl, equations: &[Decl]) -> Result<()> {
        let Decl::Signature { name: def_name, .. } = signature else {
            unreachable!()
        };
        let id = self.signature(signature)?;
        // Registered before the body is elaborated, so it can refer to itself.
        // If the body fails, the definition stays declared but failed, so
        // later uses don't cascade into "unknown name" errors.
        let key = self.declaration_key(def_name)?;
        self.scope
            .insert(&key, Global::Def(id), def_name.span, false);
        self.clear_metas();
        self.module.phase = Phase::Body;
        self.local_helpers.clear();
        self.preadmitted.borrow_mut().clear();
        let (body, mut members) = self.lifted_body(id, def_name, equations)?;
        members.insert(0, (id, body));
        kernel::define_group(&mut self.globals, &members).map_err(|d| self.explain_lifted(d))?;
        self.bind_local_helpers()?;
        self.after_definition(signature, id)
    }

    /// Once their owner is final, its local definitions can be named from
    /// outside: `sumTo.go` (docs/proposals/syntax-conveniences.md §3.6).
    fn bind_local_helpers(&mut self) -> Result<()> {
        for (key, id, span) in std::mem::take(&mut self.local_helpers) {
            if let Some((_, other)) = self.scope.get(&key) {
                return Err(error(
                    "E-DUPLICATE",
                    span,
                    format!(
                        "`{}` is the name of a local definition and of a declaration",
                        scope::display(&key)
                    ),
                )
                .with_label(other, "the declaration is here"));
            }
            self.scope.insert(&key, Global::Def(id), span, false);
            self.helper_keys.insert(key);
        }
        Ok(())
    }

    /// A definition's body, with the `match`es in it lifted
    /// (docs/proposals/syntax-conveniences.md §2.2): those that are in a
    /// cycle with the definition are returned, to be admitted with it.
    fn lifted_body(
        &mut self,
        id: DefId,
        def_name: &ast::Name,
        equations: &[Decl],
    ) -> Result<(Term, Vec<(DefId, Term)>)> {
        let key = self.declaration_key(def_name)?;
        self.with_local_retries(&key, def_name, |e| {
            let term = e.body_term(id, def_name, equations)?;
            let joined = e.lift(&key, true)?;
            Ok((e.finish(&term, 0)?, joined))
        })
    }

    /// Runs `attempt`, the elaboration of the body of the declaration `key`
    /// (named `owner` in messages); if it fails, admits the local
    /// definitions it elaborated that can be, and tries again with them
    /// final (`local.rs`), until it succeeds or no more can be.
    fn with_local_retries<T>(
        &mut self,
        key: &str,
        owner: &ast::Name,
        mut attempt: impl FnMut(&mut Self) -> Result<T>,
    ) -> Result<T> {
        loop {
            self.clear_metas();
            *self.owner.borrow_mut() = vec![key.to_string()];
            self.local_keys.borrow_mut().clear();
            let result = attempt(self);
            self.owner.borrow_mut().clear();
            let d = match result {
                Ok(found) => return Ok(found),
                Err(d) if undo::fatal(&d) => return Err(d),
                Err(d) => d,
            };
            let before = self.preadmitted.borrow().len();
            match self.preadmit(key) {
                Ok((true, _)) if self.preadmitted.borrow().len() > before => {}
                Ok((_, waiting)) => return Err(local::unfinished(d, &waiting, owner)),
                Err(e) if undo::fatal(&e) => return Err(e),
                Err(_) => return Err(d),
            }
        }
    }

    /// A group of definitions that may call each other (or one definition),
    /// given as module items: every signature, then every body, then the
    /// kernel admits them together, or none of them
    /// (docs/proposals/mutual-recursion.md §5.3). The diagnostics, each with
    /// the item it's about.
    /// A recursive group whose members are all `Partial` is translated
    /// instead (`partial.rs`); one mixing partial and total members is
    /// refused.
    fn group(
        &mut self,
        members: &[(usize, &Decl, &[Decl])],
        recursive: bool,
    ) -> Vec<(usize, Diagnostic)> {
        // Recursion on a measure (`decreasing.rs`).
        if members.iter().any(|(_, s, _)| {
            matches!(
                s,
                Decl::Signature {
                    decreasing: Some(_),
                    ..
                }
            )
        }) {
            return self.decreasing_group(members);
        }
        let mut out = Vec::new();
        let mut ids = Vec::new();
        for &(item, signature, _) in members {
            self.module.item = Some(item);
            let result = self.signature(signature);
            out.extend(self.warnings.drain(..).map(|w| (item, w)));
            out.extend(self.lambda_warnings.take().into_iter().map(|w| (item, w)));
            match result {
                Ok(id) => ids.push(id),
                Err(d) => out.push((item, d)),
            }
        }
        if ids.len() < members.len() {
            return out;
        }
        // `Delay` and its constants: signatures without equations in the
        // prelude, which the kernel admits as primitives.
        if let [(item, Decl::Signature { name: n, .. }, [])] = members
            && self.loading_prelude
            && let Some(prim) = Primitive::named(&n.text)
            && let Ok(key) = self.declaration_key(n)
        {
            self.scope.insert(&key, Global::Def(ids[0]), n.span, false);
            match stitchwort_core::partial::define_primitive(&mut self.globals, ids[0], prim) {
                Ok(()) => {
                    registry::bind_def(&mut self.globals, ids[0]);
                }
                Err(d) => out.push((*item, d)),
            }
            return out;
        }
        // Every member can be referred to now, by its signature. None has a
        // body until the kernel admits them all, so none unfolds while the
        // others are checked.
        for (&(_, signature, _), id) in members.iter().zip(&ids) {
            if let Decl::Signature { name: n, .. } = signature
                && let Ok(key) = self.declaration_key(n)
            {
                self.scope.insert(&key, Global::Def(*id), n.span, false);
            }
        }
        if recursive {
            let partial = match members
                .iter()
                .zip(&ids)
                .map(|(&(_, _, equations), id)| self.partial_member(*id, equations))
                .collect::<Result<Vec<bool>>>()
            {
                Ok(partial) => partial,
                Err(d) => {
                    out.push((members[0].0, d));
                    return out;
                }
            };
            if partial.iter().all(|p| *p) {
                out.extend(self.partial_group(members, &ids));
                return out;
            }
            if partial.iter().any(|p| *p) {
                out.push((members[0].0, self.mixed_partial(members, &ids, &partial)));
                return out;
            }
        }
        let mut bodies = Vec::new();
        let mut helpers = Vec::new();
        self.local_helpers.clear();
        self.preadmitted.borrow_mut().clear();
        for (&(item, signature, equations), id) in members.iter().zip(&ids) {
            let Decl::Signature { name: def_name, .. } = signature else {
                unreachable!()
            };
            self.module.item = Some(item);
            self.module.phase = Phase::Body;
            self.clear_metas();
            self.branch_errors.take();
            match self.lifted_body(*id, def_name, equations) {
                Ok((body, joined)) => {
                    bodies.push((*id, body));
                    helpers.extend(joined);
                }
                Err(d) => {
                    out.push((item, d));
                    // The other bad branches of the case it failed in.
                    let mut seen: Vec<Span> = Vec::new();
                    for d in self.branch_errors.take() {
                        let at = d.labels.first().map(|l| l.span);
                        let repeated = at.is_some_and(|at| seen.contains(&at))
                            || out.iter().any(|(_, o)| {
                                o.code == d.code
                                    && o.message == d.message
                                    && o.labels.first().map(|l| l.span) == at
                            });
                        if !repeated {
                            seen.extend(at);
                            out.push((item, d));
                        }
                    }
                }
            }
            out.extend(self.lambda_warnings.take().into_iter().map(|w| (item, w)));
        }
        if bodies.len() < members.len() {
            return out;
        }
        self.module.item = Some(members[0].0);
        bodies.extend(helpers);
        if let Err(d) = kernel::define_group(&mut self.globals, &bodies) {
            let d = self.explain_lifted(d);
            out.push((members[0].0, d));
            return out;
        }
        if let Err(d) = self.bind_local_helpers() {
            out.push((members[0].0, d));
        }
        for (&(item, signature, _), id) in members.iter().zip(&ids) {
            self.module.item = Some(item);
            if let Err(d) = self.after_definition(signature, *id) {
                out.push((item, d));
            }
        }
        out
    }

    /// Elaborates a definition's signature and declares it to the kernel,
    /// without making its name refer to it.
    fn signature(&mut self, signature: &Decl) -> Result<DefId> {
        let Decl::Signature {
            name: def_name,
            ty,
            theorem,
            export,
            synonym: _,
            instance,
            decreasing: _,
            span,
        } = signature
        else {
            unreachable!()
        };
        let key = self.check_new_name(def_name)?;
        self.clear_metas();
        self.module.phase = Phase::Signature;

        let auto = autobind::auto_bound(self, ty)?;
        // A name that would have been a type variable, but is the name of
        // something in this module.
        let mut notes = Vec::new();
        for used in &auto.shadowing {
            let scope::Resolved::Found { span: defined, .. } = self.resolve(&used.text) else {
                continue;
            };
            let note = format!(
                "to make `{0}` a type variable instead, bind it explicitly: start the type with \
                 `[{0}: Type] ->`",
                used.text
            );
            self.warnings.push(
                Diagnostic::warning(
                    "W-MODULE-NAME",
                    format!(
                        "`{}` in this type is the declaration of that name in this module, not a \
                         type variable",
                        used.text
                    ),
                )
                .with_label(used.span, format!("this is the module's `{}`", used.text))
                .with_label(defined, format!("`{}` is defined here", used.text))
                .with_note(note.clone()),
            );
            notes.push(note);
        }
        let with_notes = |d: Diagnostic| notes.iter().fold(d, |d, n| d.with_note(n.clone()));
        *self.owner.borrow_mut() = vec![key.clone()];
        self.local_keys.borrow_mut().clear();
        let ty = (|| {
            let mut cx = Ctx::new(self, *span);
            let mut domains = Vec::new();
            for n in &auto.names {
                // The type of an implicitly bound variable is worked out from
                // how it's used (usually `Type`).
                cx.span = n.span;
                let dom = cx.fresh_meta();
                let value = cx.eval(&dom)?;
                domains.push(dom);
                cx.bind(&n.text, value);
            }
            cx.span = *span;
            cx.e.in_instance_signature.set(*instance);
            let checked = check_type(&mut cx, ty);
            cx.e.in_instance_signature.set(false);
            let (mut term, _) = checked?;
            for (n, dom) in auto.names.iter().zip(domains).rev() {
                term = Term::Pi(name(n), Icit::Implicit, Rc::new(dom), Rc::new(term));
            }
            Ok(term)
        })();
        self.owner.borrow_mut().clear();
        let ty = ty.map_err(|d| with_notes(autobind::explain(&auto, d)))?;
        // A `match` in the signature is admitted before it (§2.2): it can't
        // refer to the definition, which isn't declared yet.
        self.lift(&key, false).map_err(with_notes)?;
        // (The unfinished term is dropped here, not kept alive while the
        // kernel checks the finished one.)
        let ty = {
            let unfinished = ty;
            self.finish(&unfinished, 0).map_err(with_notes)?
        };
        self.check_redundant(&ty, def_name.span)?;
        let id = kernel::declare_def(
            &mut self.globals,
            &scope::display(&key).into(),
            &ty,
            *theorem,
            *export,
            *span,
        )
        .map_err(with_notes)?;
        if let Some(item) = self.module.item {
            self.module.def_items.insert(id, item);
        }
        // A dictionary keeps its name in what uses it (stage 1, item 13).
        if self.is_dictionary_type(&self.globals.def(id).ty.clone())? {
            kernel::mark_folded(&mut self.globals, id);
        }
        if *instance {
            self.register_instance(id, def_name)?;
        }
        Ok(id)
    }

    /// After a definition is admitted: registering natives (in the prelude)
    /// and an export's validators.
    fn after_definition(&mut self, signature: &Decl, id: DefId) -> Result<()> {
        let Decl::Signature {
            export, instance, ..
        } = signature
        else {
            unreachable!()
        };
        if *instance {
            self.validate_instance(id)?;
        }
        if self.loading_prelude {
            self.bind_builtin_def(id)?;
        }
        if *export {
            self.add_validators(id)?;
        }
        Ok(())
    }

    /// Binds the built-in data type the prelude's or a library file's final
    /// data type `d` is, if any, and tells the evaluator about it. Replaying
    /// a library file from the check cache binds through this too.
    pub(crate) fn bind_builtin_data(&mut self, d: DataId) -> Result<()> {
        match registry::bind_data(&mut self.globals, d) {
            Some(Builtin::Nat) => native::register_nat(&mut self.globals, d)?,
            Some(Builtin::Bool) => native::register_bool(&mut self.globals, d)?,
            Some(Builtin::Decidable) => native::register_decidable(&mut self.globals, d)?,
            // `Char` comes after `List`. If either isn't the declaration
            // the compact representation of text was written for, text
            // literals are constructors instead (and a test fails).
            Some(Builtin::Char) => {
                if let Some(list) = self.globals.registry.data(Builtin::List) {
                    chars::register(&mut self.globals, list, d);
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Binds the built-in definition the prelude's or a library file's
    /// final definition `id` is, if any, with its native implementation.
    /// Replaying a library file from the check cache binds through this too.
    pub(crate) fn bind_builtin_def(&mut self, id: DefId) -> Result<()> {
        match registry::bind_def(&mut self.globals, id) {
            Some(Builtin::NatNeq) => native::register_nat_neq(&mut self.globals, id)?,
            Some(b) => {
                if let Some(op) = Native::ALL.into_iter().find(|n| n.builtin() == b) {
                    native::register_native(&mut self.globals, id, op)?;
                }
            }
            None => {}
        }
        Ok(())
    }

    /// For each proof parameter of an export, a decision procedure that the
    /// extracted JS runs on its inputs (DESIGN.md §12). A proof parameter with
    /// no decision procedure can't be checked at runtime, so the export is
    /// refused.
    fn add_validators(&mut self, id: DefId) -> Result<()> {
        let Some(decidable) = self.globals.registry.data(Builtin::Decidable) else {
            return Ok(()); // no prelude
        };
        let def = self.globals.def(id);
        let (name, span) = (def.name.clone(), def.span);
        let tel = kernel::telescope(&self.globals, &def.ty_value, span)?;
        let mut found = Vec::new();
        for (i, (_, ty, erased)) in tel.params.iter().enumerate() {
            if !erased || kernel::is_type_former(&self.globals, i, ty)? {
                continue; // runtime data, or a type parameter (refused when exporting)
            }
            self.clear_metas();
            let mut cx = Ctx::from_parts(
                self,
                (0..i).map(Value::var).collect(),
                tel.params[..i].iter().map(|(_, t, _)| t.clone()).collect(),
                tel.params[..i].iter().map(|(x, _, _)| x.clone()).collect(),
                span,
            );
            let shown = cx.show(ty);
            let decision = auto::decide(&mut cx, ty, 0).map_err(|_| {
                Diagnostic::error("E-EXPORT", format!("`{name}` can't be exported"))
                    .with_label(
                        span,
                        format!("its precondition `{shown}` can't be checked at runtime"),
                    )
                    .with_note("an exported function's proof arguments need a decision procedure (an `instance` returning `Decidable …`)")
            })?;
            found.push((i, self.finish(&decision, i)?));
        }
        self.clear_metas();
        for (i, decision) in found {
            kernel::add_validator(&mut self.globals, id, i, decidable, &decision)?;
        }
        // Records crossing the boundary with proof fields need decision
        // procedures for those too (docs/proposals/records.md §11.3).
        let crossing: Vec<Value> = tel
            .params
            .iter()
            .filter(|(_, _, erased)| !erased)
            .map(|(_, ty, _)| ty.clone())
            .chain([tel.result.clone()])
            .collect();
        let mut seen = std::collections::HashSet::new();
        for ty in &crossing {
            self.record_validators(ty, &name, span, &mut seen)?;
        }
        Ok(())
    }

    /// A definition's body, finished: a lifted `match` in it is an error
    /// (`E-MATCH-MOTIVE`).
    fn body(&self, id: DefId, def_name: &ast::Name, equations: &[Decl]) -> Result<Term> {
        let term = self.body_term(id, def_name, equations)?;
        self.finish(&term, 0)
    }

    /// A definition's body, before metavariable solutions are substituted.
    fn body_term(&self, id: DefId, def_name: &ast::Name, equations: &[Decl]) -> Result<Term> {
        let g = &self.globals;
        let mut cx = Ctx::new(self, def_name.span);
        let written = Rc::new(g.def(id).ty.clone());
        self.body_in(
            &mut cx,
            g.def(id).ty_value.clone(),
            Some(written),
            def_name,
            equations,
        )
    }

    /// The body of a definition of type `ty` (with `written`, its type as
    /// written, in `cx`'s context), elaborated in `cx`: a top-level
    /// definition's in an empty context, a local one's where it's written.
    /// A term in `cx`'s context; `cx` is left as it was.
    pub(crate) fn body_in(
        &self,
        cx: &mut Ctx,
        ty: Value,
        written: Option<Rc<Term>>,
        def_name: &ast::Name,
        equations: &[Decl],
    ) -> Result<Term> {
        let mark = cx.mark();
        let span = cx.span;
        let goal = cx.goal.take();
        let result = self.body_in_parts(cx, ty, written, def_name, equations);
        cx.goal = goal;
        cx.reset(mark);
        cx.span = span;
        result
    }

    fn body_in_parts(
        &self,
        cx: &mut Ctx,
        ty: Value,
        written: Option<Rc<Term>>,
        def_name: &ast::Name,
        equations: &[Decl],
    ) -> Result<Term> {
        let g = &self.globals;
        // Arms under a `def` header: how many patterns are the header's
        // named parameters (docs/proposals/declaration-syntax.md §2.4).
        let header = match equations.first() {
            Some(Decl::Equation { arm, .. }) => *arm,
            _ => None,
        };
        let equations: Vec<(&Vec<Pattern>, Option<&Expr>, Span)> = equations
            .iter()
            .map(|eq| match eq {
                Decl::Equation {
                    patterns,
                    rhs,
                    span,
                    ..
                } => (patterns, rhs.as_ref(), *span),
                _ => unreachable!(),
            })
            .collect();
        let Some(&(first_patterns, first_rhs, first_span)) = equations.first() else {
            return Err(error(
                "E-MISSING-DEFINITION",
                def_name.span,
                format!("`{}` has no body", def_name.text),
            )
            .with_note(
                "give it a body after `:=`, or arms under its header; only the prelude's \
                 primitives are declared without one",
            ));
        };
        let arity = first_patterns.len();
        for &(patterns, _, span) in &equations {
            if patterns.len() != arity {
                let (form, h) = match header {
                    Some(h) => ("arm", h),
                    None => ("arm", 0),
                };
                return Err(error(
                    "E-ARITY",
                    span,
                    format!(
                        "this {form} has {} patterns, but the first one has {}",
                        patterns.len() - h,
                        arity - h
                    ),
                ));
            }
        }
        let span = first_span.to(equations.last().expect("non-empty").2);

        // Bind the parameters: implicit ones by their names in the signature,
        // explicit ones to be matched by the patterns. Implicit parameters after
        // the last pattern are bound too, so they can be used by name.
        cx.span = span;
        let mut lams: Vec<(Name, Icit)> = Vec::new();
        let mut columns = Vec::new();
        let mut column_types = Vec::new();
        let mut ty = ty;
        // The signature as written, alongside, for dot notation's namespaces.
        let mut written = written;
        let mut next_written = |cx: &mut Ctx| {
            let pi = written.take();
            if let Some(Term::Pi(_, _, dom, cod)) = pi.as_deref().map(Term::strip_loc) {
                cx.set_written(crate::dot::Written::Here(dom.clone()));
                written = Some(cod.clone());
            }
        };
        loop {
            match force(g, ty.clone())? {
                // Implicit and auto parameters are in scope by name, wherever
                // they are in the signature.
                Value::Pi(x, icit, dom, cod) if icit.is_implicit() => {
                    let var = Value::var(cx.level());
                    cx.bind(&x, (*dom).clone());
                    cx.set_kind(icit);
                    next_written(cx);
                    lams.push((x, icit));
                    ty = cod.apply(g, var)?;
                }
                Value::Pi(x, Icit::Explicit, dom, cod) if columns.len() < arity => {
                    let param = match &first_patterns[columns.len()] {
                        Pattern::Var(v) => name(v),
                        _ => x,
                    };
                    let var = Value::var(cx.level());
                    columns.push(cx.level());
                    column_types.push(Some((*dom).clone()));
                    cx.bind_hidden(param.clone(), (*dom).clone());
                    next_written(cx);
                    lams.push((param, Icit::Explicit));
                    ty = cod.apply(g, var)?;
                }
                _ => break,
            }
        }
        cx.goal = written.map(|w| (cx.level(), w));
        if let Some(h) = header {
            // Arms have exact arity: a pattern for every explicit argument
            // after the colon, counted up to the first thing that isn't a
            // function type (an ability row, say).
            let fewer = columns.len() == arity
                && matches!(force(g, ty.clone())?, Value::Pi(_, Icit::Explicit, ..));
            if columns.len() == h {
                return Err(error(
                    "E-ARITY",
                    first_span,
                    "arms need an argument after the colon to match; use `:=`",
                ));
            }
            if columns.len() < arity || fewer {
                let message = if fewer {
                    format!(
                        "this arm has {} pattern(s), but `{}` takes more arguments after the colon",
                        arity - h,
                        def_name.text
                    )
                } else if h > 0 {
                    // More patterns than arguments after the colon, and the
                    // header names parameters: the likely mistake is trying
                    // to match one of those (E-ARM-PARAMETER).
                    let named: Vec<&str> = first_patterns[..h]
                        .iter()
                        .filter_map(|p| match p {
                            Pattern::Var(n) => Some(n.text.as_str()),
                            _ => None,
                        })
                        .collect();
                    let first = named.first().copied().unwrap_or("x");
                    let list = named
                        .iter()
                        .map(|n| format!("`{n}`"))
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Err(error(
                        "E-ARM-PARAMETER",
                        first_span,
                        format!(
                            "named parameters can't be matched in arms: move {list} after the colon, \
                             or use `match {first} with`"
                        ),
                    )
                    .with_note(format!(
                        "`{}` takes {} argument(s) after the colon, but this arm has {} patterns",
                        def_name.text,
                        columns.len() - h,
                        arity - h
                    )));
                } else {
                    format!(
                        "`{}` takes {} argument(s) after the colon, but this arm has {} patterns",
                        def_name.text,
                        columns.len() - h,
                        arity - h
                    )
                };
                return Err(error("E-ARITY", first_span, message).with_note(
                    "an arm has a pattern for each explicit argument after the colon; to return \
                     a function, add the argument as a pattern, or write a lambda",
                ));
            }
        }
        if columns.len() < arity {
            return Err(error(
                "E-ARITY",
                first_span,
                format!(
                    "`{}` takes {} explicit argument(s), but this arm has {arity} patterns",
                    def_name.text,
                    columns.len()
                ),
            ));
        }

        let tree = if arity == 0 {
            if let Some(&(_, _, span)) = equations.get(1) {
                return Err(error(
                    "E-DUPLICATE",
                    span,
                    format!("`{}` is defined more than once", def_name.text),
                ));
            }
            Tree::Leaf {
                aliases: Vec::new(),
                written: Vec::new(),
                canon: Vec::new(),
                rhs: first_rhs,
                span: first_span,
            }
        } else {
            let rows: Vec<Row> = equations
                .iter()
                .map(|&(patterns, rhs, span)| Row {
                    // `()` with a right-hand side is the unit pattern; without
                    // one, it's absurd.
                    pats: patterns
                        .iter()
                        .map(|p| match p {
                            Pattern::Absurd(span) if rhs.is_some() => Cow::Owned(Pattern::Ctor(
                                ast::Name {
                                    text: UNIT_PATTERN.into(),
                                    span: *span,
                                },
                                Vec::new(),
                                *span,
                            )),
                            p => Cow::Borrowed(p),
                        })
                        .collect(),
                    aliases: Vec::new(),
                    written: written_names(patterns),
                    rhs,
                    span,
                })
                .collect();
            self.compile(&rows, cx.level(), &columns, &column_types, span)?
        };
        let mut term = families::warn_unreachable(cx, |cx| {
            let start = columns.first().copied().unwrap_or(cx.level());
            check_tree_from(cx, start, &tree, &ty)
        })?;
        for (x, icit) in lams.into_iter().rev() {
            term = Term::Lam(x, icit, Rc::new(term));
        }
        Ok(term)
    }

    /// Compiles equations into a case tree. `columns[j]` is the de Bruijn level
    /// of the value each row's `j`th pattern matches, and `types[j]` its type
    /// if known (a record pattern needs it); `depth` is the number of
    /// variables in scope.
    fn compile<'a>(
        &self,
        rows: &[Row<'a>],
        depth: usize,
        columns: &[usize],
        types: &[Option<Value>],
        span: Span,
    ) -> Result<Tree<'a>> {
        self.globals.budget.nesting(check::PASS)?;
        let first = &rows[0];
        if let Some(j) = first
            .pats
            .iter()
            .position(|p| matches!(**p, Pattern::Absurd(_)))
        {
            return Ok(Tree::Absurd {
                level: columns[j],
                span: first.pats[j].span(),
            });
        }
        let mut split = None;
        for (j, pattern) in first.pats.iter().enumerate() {
            // A column of numbers (with variables and `_`) is compared with
            // numbers. One with a `Zero` or `Succ` pattern is split into
            // those constructors, and numbers in it count down as it's split.
            // A column of `Int`s is split by sign first (see `pattern_ctor`).
            if matches!(**pattern, Pattern::Num(..))
                && !self.numbers_as_succ
                && !rows.iter().any(|r| matches!(*r.pats[j], Pattern::Ctor(..)))
                && self.number_kind(types[j].as_ref())? != NumberKind::Int
            {
                return self.compile_numbers(rows, depth, columns, types, j, span);
            }
            if let Some(ctor) = self.pattern_ctor(pattern, types[j].as_ref())? {
                split = Some((j, ctor.data));
                break;
            }
        }
        let Some((j, d)) = split else {
            // The first row matches whatever is left: it's the result.
            let mut aliases = first.aliases.clone();
            let mut canon = Vec::new();
            let proofs = self.char_proofs.borrow();
            for (pattern, level) in first.pats.iter().zip(columns) {
                if let Some(x) = pattern_var(pattern) {
                    aliases.push((&x.text, *level));
                }
                if let Pattern::Wildcard(s) = &**pattern
                    && proofs.contains(s)
                {
                    canon.push(*level);
                }
            }
            return Ok(Tree::Leaf {
                aliases,
                written: first.written.clone(),
                canon,
                rhs: first.rhs,
                span: first.span,
            });
        };

        let level = columns[j];
        let data = self.globals.data(d);
        if Some(d) == self.globals.registry.data(Builtin::Int) {
            self.int_coverage(rows, j, types[j].as_ref(), span)?;
        }
        let mut branches = Vec::new();
        for (c, ctor) in data.ctors.iter().enumerate() {
            let k = ctor.fields.len();
            // In this branch, column `j` is replaced by the constructor's
            // fields, which are bound at levels `depth..depth + k`.
            let branch_columns: Vec<usize> = columns[..j]
                .iter()
                .copied()
                .chain(depth..depth + k)
                .chain(columns[j + 1..].iter().copied())
                .collect();
            let branch_types: Vec<Option<Value>> = types[..j]
                .iter()
                .cloned()
                .chain(self.field_types(types[j].as_ref(), d, c, depth)?)
                .chain(types[j + 1..].iter().cloned())
                .collect();
            let mut names: Vec<Option<Name>> = vec![None; k];
            let mut branch_rows = Vec::new();
            for row in rows {
                let pattern = &row.pats[j];
                let mut aliases = row.aliases.clone();
                let fields: Vec<Pat> = match self.pattern_ctor(pattern, types[j].as_ref())? {
                    Some(CtorPattern {
                        data: d2,
                        ctor: c2,
                        args,
                        span: pattern_span,
                    }) => {
                        if d2 != d {
                            return Err(error(
                                "E-TYPE-MISMATCH",
                                pattern_span,
                                format!(
                                    "this pattern is {} `{}`, but other patterns here are `{}`",
                                    article(&self.globals.data(d2).name),
                                    self.globals.data(d2).name,
                                    data.name
                                ),
                            ));
                        }
                        if c2 != c {
                            continue;
                        }
                        let args = self.ctor_pattern_args(d, c, args, pattern_span)?;
                        for (f, arg) in args.iter().enumerate() {
                            if let Some(x) = pattern_var(arg) {
                                names[f].get_or_insert_with(|| name(x));
                            }
                        }
                        args
                    }
                    None => {
                        if let Some(x) = pattern_var(pattern) {
                            aliases.push((&x.text, level));
                        }
                        let wildcard = Pattern::Wildcard(pattern.span());
                        vec![Cow::Owned(wildcard); k]
                    }
                };
                let pats = row.pats[..j]
                    .iter()
                    .cloned()
                    .chain(fields)
                    .chain(row.pats[j + 1..].iter().cloned())
                    .collect();
                branch_rows.push(Row {
                    pats,
                    aliases,
                    written: row.written.clone(),
                    rhs: row.rhs,
                    span: row.span,
                });
            }
            let other_family = || -> Result<bool> {
                for (i, t) in types.iter().enumerate() {
                    if let Some(t) = t
                        && i != j
                        && let Value::Data(d2, _) = force(&self.globals, t.clone())?
                        && !self.globals.data(d2).indices.is_empty()
                    {
                        return Ok(true);
                    }
                }
                Ok(false)
            };
            if branch_rows.is_empty() && (!data.indices.is_empty() || other_family()?) {
                // It may be impossible: `check_tree` unifies, and decides
                // (docs/proposals/indexed-families.md §7.3). Without
                // indices, only if another column's type becomes empty in
                // this branch (`Fin n` with `n := Zero`): SW-181.
                let names = (ctor.fields.iter()).map(|(x, _)| x.clone()).collect();
                branches.push((
                    names,
                    Tree::Missing {
                        columns: branch_columns,
                        span,
                    },
                ));
                continue;
            }
            if branch_rows.is_empty() {
                let example = std::iter::once(ctor.name.to_string())
                    .chain(std::iter::repeat_n("_".to_string(), k))
                    .collect::<Vec<_>>()
                    .join(" ");
                return Err(error(
                    "E-NONEXHAUSTIVE",
                    span,
                    format!("missing case: no arm matches `{example}`"),
                ));
            }
            let body = self.compile(
                &branch_rows,
                depth + k,
                &branch_columns,
                &branch_types,
                span,
            )?;
            let names = names
                .into_iter()
                .zip(&ctor.fields)
                .map(|(n, (field, _))| n.unwrap_or_else(|| field.clone()))
                .collect();
            branches.push((names, body));
        }
        Ok(Tree::Case {
            level,
            data: d,
            branches,
            span,
        })
    }

    /// Compiles a split on column `j`, which holds numbers, variables and
    /// `_` (and maybe `()`), into a number case: one arm per number, keeping the rows that have
    /// that number or a variable there, in order, and a default keeping the
    /// rows with a variable. The same number in several rows is one arm.
    #[allow(clippy::too_many_arguments)]
    fn compile_numbers<'a>(
        &self,
        rows: &[Row<'a>],
        depth: usize,
        columns: &[usize],
        types: &[Option<Value>],
        j: usize,
        span: Span,
    ) -> Result<Tree<'a>> {
        // The rows with each number there, and the rest, by index.
        let mut by_key: BTreeMap<&BigUint, Vec<usize>> = BTreeMap::new();
        let mut others = Vec::new();
        for (i, row) in rows.iter().enumerate() {
            match &*row.pats[j] {
                Pattern::Num(n, _) => by_key.entry(n).or_default().push(i),
                Pattern::NegNum(_, s) => return Err(negative_nat(*s)),
                _ => others.push(i),
            }
        }
        if others.is_empty() {
            let chars = self.char_patterns.borrow();
            let as_chars: Option<Vec<String>> = by_key
                .values()
                .map(|rs| match &*rows[rs[0]].pats[j] {
                    Pattern::Num(_, s) => chars.get(s).map(|c| format!("'{}'", escape_char(*c))),
                    _ => None,
                })
                .collect();
            let (what, listed) = match as_chars {
                Some(items) => {
                    let n = items.len();
                    ("characters", list_numbers(items.into_iter(), n))
                }
                None => (
                    "numbers",
                    list_numbers(by_key.keys().map(|k| k.to_string()), by_key.len()),
                ),
            };
            return Err(error(
                "E-NONEXHAUSTIVE",
                span,
                format!("missing case: no arm matches {what} other than {listed}"),
            )
            .with_note("add an arm with a variable or `_` in that position"));
        }
        let mut arms = Vec::new();
        for (key, matching) in by_key {
            // In the order of the source.
            let mut indices: Vec<usize> =
                matching.into_iter().chain(others.iter().copied()).collect();
            indices.sort_unstable();
            let arm_rows: Vec<Row> = indices
                .into_iter()
                .map(|i| {
                    let mut row = rows[i].clone();
                    if let Pattern::Num(_, s) = &*row.pats[j] {
                        row.pats[j] = Cow::Owned(Pattern::Wildcard(*s));
                    }
                    row
                })
                .collect();
            let tree = self.compile(&arm_rows, depth, columns, types, span)?;
            arms.push((key.clone(), tree));
        }
        let default_rows: Vec<Row> = others.iter().map(|&i| rows[i].clone()).collect();
        let default = self.compile(&default_rows, depth, columns, types, span)?;
        Ok(Tree::NumCase {
            level: columns[j],
            arms,
            default: Box::new(default),
            span,
        })
    }

    /// The types of the fields of constructor `c` of `d`, bound at levels
    /// from `depth`, when the matched value's type `ty` is known.
    fn field_types(
        &self,
        ty: Option<&Value>,
        d: DataId,
        c: usize,
        depth: usize,
    ) -> Result<Vec<Option<Value>>> {
        let g = &self.globals;
        let fields = &g.data(d).ctors[c].fields;
        let params = match ty.map(|t| force(g, t.clone())).transpose()? {
            Some(Value::Data(d2, params)) if d2 == d => params,
            _ => return Ok(vec![None; fields.len()]),
        };
        let mut env = params;
        let mut out = Vec::new();
        for (f, (_, field_ty)) in fields.iter().enumerate() {
            out.push(Some(eval(g, &env, field_ty)?));
            env.push(Value::var(depth + f));
        }
        Ok(out)
    }

    /// The constructor `pattern` matches, if any, and its argument patterns.
    /// A number `n` is `Succ` of `n - 1`, or `OfNat n` where `ty` is `Int`;
    /// a record pattern is resolved by `ty`, the type of what it matches.
    fn pattern_ctor<'a>(
        &self,
        pattern: &Pat<'a>,
        ty: Option<&Value>,
    ) -> Result<Option<CtorPattern<'a>>> {
        match &**pattern {
            Pattern::Var(_) | Pattern::Wildcard(_) | Pattern::Absurd(_) => Ok(None),
            Pattern::Named(_, _, span) => Err(error(
                "E-ARITY",
                *span,
                "`[n := p]` only matches an implicit field, among a constructor's arguments",
            )),
            // A number pattern on an `Int` is `OfNat k` or `NegSucc (k - 1)`
            // around a number pattern on the `Nat` field (`-0` is `OfNat 0`).
            // A negative one on a type not known to be `Int` is one too, and
            // the split reports the mismatch.
            Pattern::NegNum(n, span) => match self.number_kind(ty)? {
                NumberKind::Nat => Err(negative_nat(*span)),
                _ => self.int_pattern(n, true, *span).map(Some),
            },
            Pattern::Num(n, span) if self.number_kind(ty)? == NumberKind::Int => {
                self.int_pattern(n, false, *span).map(Some)
            }
            Pattern::Record { fields, rest, span } => Ok(Some(match pattern {
                Cow::Borrowed(Pattern::Record { fields, .. }) => {
                    self.record_pattern(fields, *rest, *span, ty)?
                }
                _ => {
                    let found = self.record_pattern(fields, *rest, *span, ty)?;
                    CtorPattern {
                        args: found
                            .args
                            .into_iter()
                            .map(|a| Cow::Owned(a.into_owned()))
                            .collect(),
                        ..found
                    }
                }
            })),
            Pattern::Tuple(p, q, span) => {
                let (data, ctor) = self.builtin_ctor(Builtin::MkPair, *span)?;
                let args = match pattern {
                    Cow::Borrowed(Pattern::Tuple(p, q, _)) => {
                        vec![Cow::Borrowed(&**p), Cow::Borrowed(&**q)]
                    }
                    _ => vec![Cow::Owned((**p).clone()), Cow::Owned((**q).clone())],
                };
                Ok(Some(CtorPattern {
                    data,
                    ctor,
                    args,
                    span: *span,
                }))
            }
            Pattern::Nil(span) => {
                let (data, ctor) = self.builtin_ctor(Builtin::Nil, *span)?;
                Ok(Some(CtorPattern {
                    data,
                    ctor,
                    args: Vec::new(),
                    span: *span,
                }))
            }
            Pattern::Cons(p, q, span) => {
                let (data, ctor) = self.builtin_ctor(Builtin::Cons, *span)?;
                let args = match pattern {
                    Cow::Borrowed(Pattern::Cons(p, q, _)) => {
                        vec![Cow::Borrowed(&**p), Cow::Borrowed(&**q)]
                    }
                    _ => vec![Cow::Owned((**p).clone()), Cow::Owned((**q).clone())],
                };
                Ok(Some(CtorPattern {
                    data,
                    ctor,
                    args,
                    span: *span,
                }))
            }
            // `'L'` is `MkChar 76 _`.
            Pattern::Char(c, span) => {
                let (data, ctor) = self.builtin_ctor(Builtin::MkChar, *span)?;
                self.char_patterns.borrow_mut().insert(*span, *c);
                self.char_proofs.borrow_mut().insert(*span);
                Ok(Some(CtorPattern {
                    data,
                    ctor,
                    args: vec![
                        Cow::Owned(Pattern::Num(BigUint::from(u32::from(*c)), *span)),
                        Cow::Owned(Pattern::Wildcard(*span)),
                    ],
                    span: *span,
                }))
            }
            Pattern::Num(n, span) => {
                let (ctor, args) = if n.bits() == 0 {
                    (Builtin::Zero, Vec::new())
                } else {
                    let pred = Pattern::Num(n - 1u32, *span);
                    (Builtin::Succ, vec![Cow::Owned(pred)])
                };
                let (data, ctor) = self.builtin_ctor(ctor, *span)?;
                Ok(Some(CtorPattern {
                    data,
                    ctor,
                    args,
                    span: *span,
                }))
            }
            Pattern::Ctor(n, args, span) => {
                let (data, ctor) = if n.text == UNIT_PATTERN {
                    self.builtin_ctor(Builtin::UnitValue, n.span)?
                } else {
                    self.ctor_named(&n.text, n.span)?
                };
                let args = match pattern {
                    Cow::Borrowed(Pattern::Ctor(_, args, _)) => {
                        args.iter().map(Cow::Borrowed).collect()
                    }
                    _ => args.iter().cloned().map(Cow::Owned).collect(),
                };
                Ok(Some(CtorPattern {
                    data,
                    ctor,
                    args,
                    span: *span,
                }))
            }
        }
    }

    /// Whether `ty`, the type of a column, is the built-in `Nat` or `Int`
    /// (by registry identity, as `numbers::classify` decides).
    fn number_kind(&self, ty: Option<&Value>) -> Result<NumberKind> {
        let g = &self.globals;
        let Some(ty) = ty else {
            return Ok(NumberKind::Other);
        };
        Ok(match force(g, ty.clone())? {
            Value::Data(d, params) if params.is_empty() && Some(d) == g.builtins.nat => {
                NumberKind::Nat
            }
            Value::Data(d, params)
                if params.is_empty() && Some(d) == g.registry.data(Builtin::Int) =>
            {
                NumberKind::Int
            }
            _ => NumberKind::Other,
        })
    }

    /// The constructor pattern for the `Int` literal `k` or `-k`.
    fn int_pattern<'a>(&self, k: &BigUint, negative: bool, span: Span) -> Result<CtorPattern<'a>> {
        let (ctor, field) = if negative && k.bits() != 0 {
            (Builtin::NegSucc, k - 1u32)
        } else {
            (Builtin::OfNat, k.clone())
        };
        let (data, ctor) = self.builtin_ctor(ctor, span)?;
        Ok(CtorPattern {
            data,
            ctor,
            args: vec![Cow::Owned(Pattern::Num(field, span))],
            span,
        })
    }

    /// Before column `j` of `rows`, an `Int`, is split by sign: if a sign
    /// has no equation for the numbers other than those written (no
    /// variable, `_`, or `OfNat`/`NegSucc` around one), the match is
    /// incomplete, and the error names the numbers as integers rather than
    /// as the `Nat` fields the split leaves.
    fn int_coverage(&self, rows: &[Row], j: usize, ty: Option<&Value>, span: Span) -> Result<()> {
        if !rows
            .iter()
            .any(|r| matches!(*r.pats[j], Pattern::Num(..) | Pattern::NegNum(..)))
        {
            return Ok(());
        }
        let (Some((_, of_nat)), Some((_, neg_succ))) = (
            self.globals.registry.ctor(Builtin::OfNat),
            self.globals.registry.ctor(Builtin::NegSucc),
        ) else {
            return Ok(());
        };
        // The numbers written, as the `Nat` fields of `OfNat` and `NegSucc`,
        // and whether each sign has a row matching all its values.
        let mut keys: [BTreeSet<BigUint>; 2] = Default::default();
        let mut covered = [false, false];
        for row in rows {
            let Some(found) = self.pattern_ctor(&row.pats[j], ty)? else {
                covered = [true, true];
                continue;
            };
            let sign = if found.ctor == of_nat {
                0
            } else if found.ctor == neg_succ {
                1
            } else {
                // Some other type's constructor: the split reports it.
                return Ok(());
            };
            match found.args.first().map(|a| &**a) {
                Some(Pattern::Num(k, _)) => {
                    keys[sign].insert(k.clone());
                }
                _ => covered[sign] = true,
            }
        }
        let which = match covered {
            [false, false] => "numbers",
            [false, true] => "non-negative numbers",
            [true, false] => "negative numbers",
            [true, true] => return Ok(()),
        };
        let mut listed: Vec<String> = Vec::new();
        if !covered[1] {
            listed.extend(keys[1].iter().rev().map(|k| format!("-{}", k + 1u32)));
        }
        if !covered[0] {
            listed.extend(keys[0].iter().map(|k| k.to_string()));
        }
        let message = if listed.is_empty() {
            format!("missing case: no arm matches {which}")
        } else {
            let n = listed.len();
            format!(
                "missing case: no arm matches {which} other than {}",
                list_numbers(listed.into_iter(), n)
            )
        };
        Err(error("E-NONEXHAUSTIVE", span, message)
            .with_note("add an arm with a variable or `_` in that position"))
    }

    /// The prelude's constructor `b`, for a pattern the compiler writes.
    fn builtin_ctor(&self, b: Builtin, span: Span) -> Result<(DataId, usize)> {
        self.globals.registry.ctor(b).ok_or_else(|| {
            error(
                "E-UNKNOWN-NAME",
                span,
                format!("this needs the prelude's `{}`", b.name()),
            )
        })
    }

    fn ctor_named(&self, ctor: &str, span: Span) -> Result<(DataId, usize)> {
        let used = ast::Name {
            text: ctor.to_string(),
            span,
        };
        match self.resolve_exact(&used)? {
            (Global::Ctor(d, c), target, key) => {
                self.note_found(span, &key, Global::Ctor(d, c), target);
                Ok((d, c))
            }
            (Global::Unchecked(item), ..) => Err(self.unchecked(&used, item)),
            (Global::Failed, ..) => Err(module::failed_name(&used)),
            (Global::Pending(file, _), ..) => Err(self.unloaded(&used, file)),
            _ => Err(error(
                "E-NOT-A-CONSTRUCTOR",
                span,
                format!("`{ctor}` isn't a constructor"),
            )),
        }
    }
}

/// In an arm of a char pattern like `'a'`, the matched character is
/// `MkChar 97 p` for a proof variable `p : Char.isScalar 97 = True`, which
/// isn't the literal `'a'` (`MkChar 97 rfl`) by computation alone: the kernel
/// doesn't identify proofs. So where the goal or a hypothesis mentions a
/// proof in `proofs`, the arm is checked with `rfl` for it, and the result is
/// transported back with `J` along `Bool.uniqueEq _ _ rfl p : rfl = p`, the
/// hypotheses that mention `p` taken as arguments. Names whose values mention
/// `p` (the matched character itself) stand for their values with `rfl` in
/// the arm. The kernel checks the whole term, so a mistake here can only
/// reject a program. `body` checks the arm, told whether it's under a `J`.
fn canonical(
    cx: &mut Ctx,
    proofs: &[usize],
    goal: &Value,
    body: &mut dyn FnMut(&mut Ctx, &Value, bool) -> Result<Term>,
) -> Result<Term> {
    let Some((&p, rest)) = proofs.split_first() else {
        return body(cx, goal, false);
    };
    let g = cx.g();
    let base = cx.level();
    let own = |cx: &Ctx, l: usize| {
        cx.lets[l].is_none()
            && matches!(&cx.env[l], Value::Neutral(Head::Var(x), s) if *x == l && s.is_empty())
    };
    // `p : a = b` in `Bool`, where `a` computes to `b` (it's `True`).
    let (a, b) = match force(g, cx.types[p].clone())? {
        Value::Eq(ty, a, b)
            if own(cx, p)
                && matches!(force(g, (*ty).clone())?,
                    Value::Data(d, _) if g.registry.is_data(Builtin::Bool, d))
                && stitchwort_core::value::conv(g, base, &a, &b)? =>
        {
            (a, b)
        }
        _ => return canonical(cx, rest, goal, body),
    };
    let mentions = |t: &Term, l: usize| t.mentions(base - 1 - l);
    let types = (0..base)
        .map(|l| quote(g, base, &cx.types[l]))
        .collect::<std::result::Result<Vec<_>, _>>()?;
    let goal_t = quote(g, base, goal)?;
    // The hypotheses to take as arguments: those whose types mention `p`,
    // or one of them.
    let mut reverted: Vec<usize> = Vec::new();
    loop {
        let more: Vec<usize> = (0..base)
            .filter(|&l| l != p && !reverted.contains(&l) && own(cx, l))
            .filter(|&l| mentions(&types[l], p) || reverted.iter().any(|&h| mentions(&types[l], h)))
            .collect();
        if more.is_empty() {
            break;
        }
        reverted.extend(more);
    }
    reverted.sort_unstable();
    // Each type may mention only the hypotheses before it.
    let ordered = reverted
        .iter()
        .enumerate()
        .all(|(i, &h)| reverted[i..].iter().all(|&h2| !mentions(&types[h], h2)));
    if !ordered || (reverted.is_empty() && !mentions(&goal_t, p)) {
        return canonical(cx, rest, goal, body);
    }
    let k = reverted.len();
    // `σ`: what each variable becomes, `p` as `with` and the hypotheses as
    // new variables from `first`.
    let subst = |with: Value, first: usize| {
        let mut env: Vec<Value> = (0..base).map(Value::var).collect();
        env[p] = with;
        for (i, &h) in reverted.iter().enumerate() {
            env[h] = Value::var(first + i);
        }
        env
    };
    // The motive `r e => (h₁ : T₁[r]) -> … -> G[r]`, under `r` and `e` at
    // `base` and `base + 1`.
    let motive_env = subst(Value::var(base), base + 2);
    let mut motive = quote(g, base + 2 + k, &eval(g, &motive_env, &goal_t)?)?;
    for (i, &h) in reverted.iter().enumerate().rev() {
        let ty = quote(g, base + 2 + i, &eval(g, &motive_env, &types[h])?)?;
        motive = Term::Pi(
            cx.names[h].clone(),
            Icit::Explicit,
            Rc::new(ty),
            Rc::new(motive),
        );
    }
    let motive = Term::Lam(
        "r".into(),
        Icit::Explicit,
        Rc::new(Term::Lam("e".into(), Icit::Explicit, Rc::new(motive))),
    );
    // The arm, with `rfl` for `p` and new variables for the hypotheses.
    let mark = cx.mark();
    let refl_env = subst(Value::Refl, base);
    for &h in &reverted {
        let ty = eval(g, &refl_env, &types[h])?;
        cx.bind_hidden(cx.names[h].clone(), ty);
    }
    for (i, &h) in reverted.iter().enumerate() {
        cx.rebind(h, base + i);
    }
    let mut names = cx.scope_names();
    names.sort();
    names.dedup();
    for name in names {
        let Some(l) = cx.lookup(&name) else { continue };
        if l >= base || l == p || reverted.contains(&l) || own(cx, l) || cx.lets[l].is_some() {
            continue;
        }
        let value = quote(g, base, &cx.env[l])?;
        if mentions(&value, p) || reverted.iter().any(|&h| mentions(&value, h)) {
            let term = quote(g, base + k, &eval(g, &refl_env, &value)?)?;
            let ty = eval(g, &refl_env, &types[l])?;
            cx.bind_local(&name, term, ty);
        }
    }
    let arm_goal = eval(g, &refl_env, &goal_t)?;
    let result = canonical(cx, rest, &arm_goal, &mut |cx, goal, _| body(cx, goal, true));
    cx.reset(mark);
    let mut arm = result?;
    for &h in reverted.iter().rev() {
        arm = Term::Lam(cx.names[h].clone(), Icit::Explicit, Rc::new(arm));
    }
    // `Bool.uniqueEq a b rfl p : rfl = p`.
    let mut unique = Term::Def(check::builtin_def(cx, Builtin::BoolUniqueEq)?);
    for arg in [
        quote(g, base, &a)?,
        quote(g, base, &b)?,
        Term::Refl,
        Term::Var(base - 1 - p),
    ] {
        unique = Term::App(Rc::new(unique), Rc::new(arg), Icit::Explicit);
    }
    let mut term = Term::J(Rc::new(motive), Rc::new(arm), Rc::new(unique));
    for &h in &reverted {
        term = Term::App(
            Rc::new(term),
            Rc::new(Term::Var(base - 1 - h)),
            Icit::Explicit,
        );
    }
    Ok(term)
}

/// Checks a compiled pattern match against `goal`, refining the goal in each
/// branch (the kernel does the same when it re-checks the result).
/// The order of every variable in scope at a leaf, for the captures of a
/// helper lifted from the arm (D228): the variables bound before the case
/// tree, in the order they already had (so an enclosing arm's order is kept
/// and a header's parameters come first), then the variables the tree binds,
/// the ones the arm names in the order written and the rest by level.
fn written_order(cx: &Ctx, aliases: &[(&str, usize)], written: &[&str]) -> Vec<usize> {
    let start = cx.tree_start.min(cx.level());
    let rank = |l: usize| lift::rank(&cx.order, l);
    let mut order: Vec<usize> = (0..start).collect();
    order.sort_by_key(|&l| rank(l));
    for name in written {
        if let Some(&(_, level)) = aliases.iter().rev().find(|(x, _)| x == name)
            && level >= start
            && !order.contains(&level)
        {
            order.push(level);
        }
    }
    for level in start..cx.level() {
        if !order.contains(&level) {
            order.push(level);
        }
    }
    order
}

/// [`check_tree`] for a tree that binds only fields, from the current level.
fn check_tree_here(cx: &mut Ctx, tree: &Tree, goal: &Value) -> Result<Term> {
    let start = cx.level();
    check_tree_from(cx, start, tree, goal)
}

/// [`check_tree`] for a tree whose variables start at level `start`.
fn check_tree_from(cx: &mut Ctx, start: usize, tree: &Tree, goal: &Value) -> Result<Term> {
    let saved = std::mem::replace(&mut cx.tree_start, start);
    let result = check_tree(cx, tree, goal);
    cx.tree_start = saved;
    result
}

/// A branch of a case failed: keep its error and go on with the other
/// branches, which don't depend on it, so one run reports every bad branch.
/// Running out of resources stops everything instead.
fn branch_failed(cx: &Ctx, error: Diagnostic, failed: &mut Vec<Diagnostic>) -> Result<()> {
    if error.code == "E-RESOURCE" || cx.g().budget.exhausted().is_some() {
        return Err(error);
    }
    failed.push(error);
    Ok(())
}

/// Fails with the first failed branch's error, leaving the others (those not
/// already reported at the same place) for the definition to report after it
/// (`Elaborator::branch_errors`).
fn report_failed_branches(cx: &Ctx, failed: Vec<Diagnostic>) -> Result<()> {
    let mut failed = failed.into_iter();
    let Some(first) = failed.next() else {
        return Ok(());
    };
    cx.e.branch_errors.borrow_mut().extend(failed);
    Err(first)
}

fn check_tree(cx: &mut Ctx, tree: &Tree, goal: &Value) -> Result<Term> {
    cx.g().budget.nesting(check::PASS)?;
    match tree {
        Tree::Leaf {
            aliases,
            written,
            canon,
            rhs,
            span,
        } => {
            families::reached(cx, *span);
            let Some(rhs) = rhs else {
                return Err(error(
                    "E-ARITY",
                    *span,
                    "this arm needs `=> …`: only an arm with a `()` pattern can leave it out",
                ));
            };
            let mark = cx.mark();
            for (x, level) in aliases {
                cx.alias(x, *level);
            }
            let order = written_order(cx, aliases, written);
            let saved_order = std::mem::replace(&mut cx.order, order);
            let result = canonical(cx, canon, goal, &mut |cx, goal, wrapped| {
                // A `match` that's the whole right-hand side, on variables of
                // the equation, splits them further here
                // (docs/proposals/syntax-conveniences.md §4.3); not under
                // `canonical`'s `J`, as a case split must be at the top.
                let in_tree = match rhs {
                    Expr::Match { .. } if !wrapped => matching::in_tree(cx, rhs, goal),
                    _ => None,
                };
                in_tree.unwrap_or_else(|| check(cx, rhs, goal))
            });
            cx.reset(mark);
            cx.order = saved_order;
            result
        }
        Tree::Missing { columns, span } => Err(error(
            "E-NONEXHAUSTIVE",
            *span,
            format!("missing case ({} columns left)", columns.len()),
        )),
        // An indexed family whose every constructor conflicts here is empty
        // too (docs/proposals/indexed-families.md §7.3).
        Tree::Absurd { level, span }
            if let Some(term) = families::empty_case(cx, *level, Some(*span))? =>
        {
            Ok(Term::Loc(*span, Rc::new(term)))
        }
        Tree::Absurd { level, span } => match force(cx.g(), cx.types[*level].clone())? {
            Value::Data(d, _) if cx.g().data(d).ctors.is_empty() => Ok(Term::Loc(
                *span,
                Rc::new(Term::Case(cx.level() - 1 - level, d, Vec::new().into())),
            )),
            other => Err(error(
                "E-NOT-EMPTY",
                *span,
                format!(
                    "`{}` has values, so this argument can't be `()`",
                    cx.show(&other)
                ),
            )),
        },
        Tree::Case {
            level: x,
            data: d,
            branches,
            span,
        } => {
            let g = cx.g();
            let data = g.data(*d);
            let mut ty = force(g, cx.types[*x].clone())?;
            if let Value::Neutral(Head::Meta(_), _) = ty {
                // A variable of a type not yet known, matched by a
                // constructor: a pattern lambda's parameter checked before
                // the argument that fixes its type, as in `List.map ((a, b)
                // => …) ps` (docs/proposals/syntax-conveniences.md §5.5). Its
                // type is the constructor's, with parameters still unknown.
                let params = (0..data.params.len() + data.indices.len())
                    .map(|_| cx.eval(&cx.fresh_meta()))
                    .collect::<Result<Vec<_>>>()?;
                let known = Value::Data(*d, params);
                if cx.unify(&ty, &known)? {
                    ty = known;
                }
            }
            let params = match ty {
                Value::Data(d2, params) if d2 == *d => params,
                other => {
                    return Err(error(
                        "E-TYPE-MISMATCH",
                        *span,
                        format!(
                            "these patterns match a `{}`, but the argument has type `{}`",
                            data.name,
                            cx.show(&other)
                        ),
                    ));
                }
            };
            let goal_term = cx.quote(goal)?;
            if !data.indices.is_empty() {
                let term = families::check_case(cx, *x, *d, &params, branches, &goal_term, *span)?;
                return Ok(Term::Loc(*span, Rc::new(term)));
            }
            let mut out = Vec::new();
            let mut failed = Vec::new();
            for (c, ((names, subtree), ctor)) in branches.iter().zip(&data.ctors).enumerate() {
                let mark = cx.mark();
                let base = cx.level();
                let fields: Vec<Value> = (0..ctor.fields.len())
                    .map(|i| Value::var(base + i))
                    .collect();
                // Inside the branch, the matched variable *is* the constructor
                // value, so it's substituted into the goal and the whole
                // context (as the kernel does).
                let value = Value::Ctor(*d, c, fields.clone().into());
                let level = cx.level();
                let mut env = kernel::substitute(g, level, *x, &value, &cx.env)?;
                env[*x] = value.clone();
                let refined = kernel::substitute(g, level, *x, &value, &cx.types)?;
                let branch_goal =
                    kernel::substitute(g, level, *x, &value, &[eval(g, &cx.env, &goal_term)?])?
                        .pop()
                        .expect("one value in, one out");
                let saved_env = std::mem::replace(&mut cx.env, env);
                let saved_types = std::mem::replace(&mut cx.types, refined);
                let mut field_env = params.clone();
                for ((_, field_ty), (name, field)) in
                    ctor.fields.iter().zip(names.iter().zip(&fields))
                {
                    let ty = eval(g, &field_env, field_ty)?;
                    field_env.push(field.clone());
                    cx.bind_hidden(name.clone(), ty);
                }
                let result = match subtree {
                    // No arm covers this constructor: fine if it makes
                    // another column's type empty (`Fin n` with `n := Zero`).
                    Tree::Missing { columns, span } => (|| {
                        for &level in columns {
                            if let Some(term) = families::empty_case(cx, level, None)? {
                                return Ok(term);
                            }
                        }
                        let example = std::iter::once(ctor.name.to_string())
                            .chain(std::iter::repeat_n("_".to_string(), ctor.fields.len()))
                            .collect::<Vec<_>>()
                            .join(" ");
                        Err(error(
                            "E-NONEXHAUSTIVE",
                            *span,
                            format!("missing case: no arm matches `{example}`"),
                        ))
                    })(),
                    _ => check_tree(cx, subtree, &branch_goal),
                };
                cx.reset(mark);
                cx.env = saved_env;
                cx.types = saved_types;
                match result {
                    Ok(body) => out.push(Branch {
                        names: names.clone(),
                        body: Some(Rc::new(body)),
                    }),
                    Err(e) => branch_failed(cx, e, &mut failed)?,
                }
            }
            report_failed_branches(cx, failed)?;
            Ok(Term::Loc(
                *span,
                Rc::new(Term::Case(cx.level() - 1 - x, *d, out.into())),
            ))
        }
        Tree::NumCase {
            level: x,
            arms,
            default,
            span,
        } => {
            let g = cx.g();
            let nat = g.builtins.nat;
            match force(g, cx.types[*x].clone())? {
                Value::Data(d, params) if Some(d) == nat && params.is_empty() => {}
                other => {
                    return Err(error(
                        "E-TYPE-MISMATCH",
                        *span,
                        format!(
                            "these patterns match a `Nat`, but the argument has type `{}`",
                            cx.show(&other)
                        ),
                    ));
                }
            }
            let goal_term = cx.quote(goal)?;
            let mut out = Vec::new();
            let mut failed = Vec::new();
            for (key, subtree) in arms {
                // In this arm, the matched variable *is* the number, so it's
                // substituted into the goal and the whole context (as the
                // kernel does).
                let value = Value::Nat(Rc::new(key.clone()));
                let level = cx.level();
                let mut env = kernel::substitute(g, level, *x, &value, &cx.env)?;
                env[*x] = value.clone();
                let refined = kernel::substitute(g, level, *x, &value, &cx.types)?;
                let arm_goal =
                    kernel::substitute(g, level, *x, &value, &[eval(g, &cx.env, &goal_term)?])?
                        .pop()
                        .expect("one value in, one out");
                let saved_env = std::mem::replace(&mut cx.env, env);
                let saved_types = std::mem::replace(&mut cx.types, refined);
                let result = check_tree(cx, subtree, &arm_goal);
                cx.env = saved_env;
                cx.types = saved_types;
                match result {
                    Ok(body) => out.push(NumArm {
                        value: Rc::new(key.clone()),
                        body: Rc::new(body),
                    }),
                    Err(e) => branch_failed(cx, e, &mut failed)?,
                }
            }
            // The default knows nothing new about the variable. If its type
            // mentions it, the programmer may have expected otherwise.
            let default = check_tree(cx, default, goal).map_err(|d| {
                let ix = cx.level() - 1 - x;
                let mentioned = |v: &Value| cx.quote(v).is_ok_and(|t| t.mentions(ix));
                let depends = mentioned(goal) || cx.types[*x + 1..].iter().any(mentioned);
                if depends && ["E-TYPE-MISMATCH", "E-NOT-EMPTY", "E-REFL"].contains(&d.code) {
                    let n = cx.show(&Value::var(*x));
                    d.with_note(format!(
                        "number patterns only test values: an arm with a variable or `_` \
                         where the others have numbers knows nothing about `{n}`, not even that \
                         it's a different number. To use the shape of `{n}`, match on `Zero` and \
                         `Succ` instead"
                    ))
                } else {
                    d
                }
            });
            let default = match default {
                Ok(default) => default,
                Err(e) => {
                    branch_failed(cx, e, &mut failed)?;
                    report_failed_branches(cx, failed)?;
                    unreachable!("a failed default leaves an error to report")
                }
            };
            report_failed_branches(cx, failed)?;
            Ok(Term::Loc(
                *span,
                Rc::new(Term::NumCase(
                    cx.level() - 1 - x,
                    out.into(),
                    Rc::new(default),
                )),
            ))
        }
    }
}

/// Whether a row in `expr` mentions ability `name`. Uses a work list: the
/// expression can nest more deeply than recursion could follow.
pub(crate) fn mentions_ability(expr: &ast::Expr, name: &str) -> bool {
    use ast::Expr;
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr {
            Expr::Effect(row, ty) => {
                let mentioned = row.abilities.iter().any(|a| {
                    let mut h = a;
                    while let Expr::App(f, _) = h {
                        h = f;
                    }
                    matches!(h, Expr::Var(v) if v.text == name)
                });
                if mentioned {
                    return true;
                }
                pending.push(ty);
            }
            Expr::App(a, b)
            | Expr::Arrow(a, b)
            | Expr::Binary(_, a, b)
            | Expr::Pipe(a, b)
            | Expr::Seq(a, b) => {
                pending.extend([&**a, &**b]);
            }
            Expr::Pi { dom, cod, .. } => pending.extend([&**dom, &**cod]),
            Expr::Lam(_, b, _) | Expr::Ann(b, _, _) | Expr::NamedArg(_, b, _) => pending.push(b),
            Expr::TypedLam(_, t, b, _) => pending.extend([&**t, &**b]),
            Expr::Tuple(a, b, _) => pending.extend([&**a, &**b]),
            Expr::List(items, _) => pending.extend(items),
            Expr::Record { base, fields, .. } => {
                pending.extend(base.as_deref());
                pending.extend(fields.iter().map(|(_, e)| e));
            }
            Expr::Field(e, _) => pending.push(e),
            Expr::Match {
                scrutinees, alts, ..
            } => {
                pending.extend(scrutinees.iter().map(|s| &s.expr));
                pending.extend(alts.iter().map(|a| &a.body));
            }
            _ => {}
        }
    }
    false
}
