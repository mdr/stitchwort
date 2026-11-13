use crate::Span;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    /// An open goal, `?`: what must go there, and the names in scope. Not
    /// an error, but a declaration with one is unfinished, so `check` still
    /// fails (docs/proposals/lsp-goal-holes.md).
    Goal,
}

/// A message attached to a span of source code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

/// A problem reported to the user. Every compiler phase reports errors this way.
///
/// The first label, if any, is the primary location of the problem.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub severity: Severity,
    /// Stable identifier such as `E-POSITIVITY`. Tests match on this rather than
    /// on the message, so a rejection only counts if it's for the right reason.
    pub code: &'static str,
    pub message: String,
    pub labels: Vec<Label>,
    pub notes: Vec<String>,
    /// What the code navigation index carries besides the text. One box for
    /// the three, which are rare, so that a `Result<_, Diagnostic>` (held in
    /// every frame of a recursive pass, and the debug build's frames are
    /// large) stays small (SW-1056).
    pub detail: Option<Box<Detail>>,
}

/// The index data of a [`Diagnostic`] (its `detail`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Detail {
    /// For a goal: its hypotheses and target, each printed apart, for the
    /// code navigation index (docs/proposals/code-navigation.md).
    pub goal: Option<GoalData>,
    /// A counterexample to the statement, when one of the notes says the
    /// statement is false: its bindings, for the index.
    pub counterexample: Option<Counterexample>,
    /// For `E-NONEXHAUSTIVE` on a constructor case: every case no arm
    /// matches, as patterns, for the index.
    pub missing: Option<MissingCases>,
    /// For `E-UNKNOWN-NAME` when an import would bring the name in: the
    /// import to add, for the editor's quick fix.
    pub import: Option<SuggestedImport>,
    /// For `E-TYPE-MISMATCH` where a test fact is expected and the term
    /// given proves one of its readings: where, and the fact. The
    /// declaration is checked again with the fact built there
    /// (docs/proposals/bool-as-proposition-building.md §2.2).
    pub build: Option<BuildSite>,
}

/// [`Detail::build`]: the term's span and the expected test fact, as
/// shown, so the retry builds only where the same fact is expected again.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BuildSite {
    pub span: Span,
    pub fact: String,
}

/// `import <path> (<item>)`: the import a diagnostic suggests.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuggestedImport {
    /// The namespace, in full (`Std`, `Std.List`).
    pub path: String,
    /// The name taken from it.
    pub item: String,
}

/// The cases a `match` leaves out (SW-1027): each a row of patterns, one
/// per scrutinee, separated by commas, that pastes as an arm's patterns
/// (`Tri _ _`, `Some _, True`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MissingCases {
    /// Every one of them, in the order of the constructors.
    pub patterns: Vec<String>,
    /// The same cases, for the editor's "add the missing arms": a field of
    /// a constructor that no arm looked at is `‹name›` (its declared
    /// name) where `patterns` has `_`, so the arm can bind a variable of
    /// that name. Parallel to `patterns`.
    pub fills: Vec<String>,
    /// Where each of `patterns` is in the case tree: the constructor taken
    /// at each split, so that the cases from several branches sort in the
    /// order of the constructors. Not shown.
    pub order: Vec<Vec<usize>>,
}

impl MissingCases {
    /// The most cases a diagnostic lists.
    pub const CAP: usize = 20;

    /// The ones listed: the first [`MissingCases::CAP`].
    pub fn shown(&self) -> &[String] {
        &self.patterns[..self.patterns.len().min(Self::CAP)]
    }

    /// How many are left out of the list.
    pub fn more(&self) -> usize {
        self.patterns.len().saturating_sub(Self::CAP)
    }
}

/// A goal as data: what its label shows, each part printed alone.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GoalData {
    pub hypotheses: Vec<Hypothesis>,
    /// What must be shown, as after `⊢`, computed as the checker sees it
    /// (a call that matches at once is replaced by what it steps to). The
    /// proof search and the lemma are made from this text; a reader is
    /// shown [`GoalData::written`] first.
    pub target: String,
    /// The target as written, with the values of the context put in and no
    /// call computed (`beats Rock Rock = False` where `target` is
    /// `False = False`); `None` when it prints the same as `target`
    /// (D3522).
    pub written: Option<String>,
    /// Whether the target is a proposition (a proof goal), if that was
    /// known when the hole was checked: `None` when its sort couldn't be
    /// told.
    pub prop: Option<bool>,
    /// The goal as a declaration of its own, to paste at the top level of
    /// the file (`theorem fGoal1 (n: Nat): n + 0 = n := ?`), when every
    /// name in it means there what it means at the goal.
    pub lemma: Option<String>,
}

impl GoalData {
    /// What a reader sees first: the target as written, else the target.
    pub fn shown(&self) -> &str {
        self.written.as_deref().unwrap_or(&self.target)
    }

    /// The computed form to show under [`GoalData::shown`], if it differs.
    pub fn computed(&self) -> Option<&str> {
        self.written.as_ref().map(|_| self.target.as_str())
    }
}

/// How many characters of a goal's `computes to` line are shown: the same
/// as a message's notes (D3522).
pub const COMPUTES_TO_LIMIT: usize = 240;

/// `computed` cut to [`COMPUTES_TO_LIMIT`] characters, ending in `…`.
pub fn cut_computed(computed: &str) -> String {
    if computed.chars().count() <= COMPUTES_TO_LIMIT {
        return computed.to_string();
    }
    let mut cut: String = computed.chars().take(COMPUTES_TO_LIMIT - 1).collect();
    cut.push('…');
    cut
}

/// One name in scope at a goal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hypothesis {
    pub name: String,
    pub ty: String,
    /// For a `let` of data, its value.
    pub value: Option<String>,
    /// The patterns that split it into its type's constructors, as they
    /// resolve where it is in scope; `None` unless its type is a data type
    /// without indices (not a proposition or a function).
    pub splits: Option<Vec<String>>,
}

/// A counterexample the search found, as the note shows it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counterexample {
    /// `"false"`: the statement is false (the verdict as
    /// `check --counterexamples` names it).
    pub verdict: &'static str,
    /// Each type parameter, and the type it was tried at (`Nat`).
    pub types: Vec<(String, String)>,
    /// Each input's name and value.
    pub bindings: Vec<(String, String)>,
}

impl Diagnostic {
    /// The index data, to set: made when first needed.
    pub fn detail_mut(&mut self) -> &mut Detail {
        self.detail.get_or_insert_with(Default::default)
    }

    pub fn goal_data(&self) -> Option<&GoalData> {
        self.detail.as_ref()?.goal.as_ref()
    }

    pub fn counterexample_data(&self) -> Option<&Counterexample> {
        self.detail.as_ref()?.counterexample.as_ref()
    }

    pub fn missing_data(&self) -> Option<&MissingCases> {
        self.detail.as_ref()?.missing.as_ref()
    }

    pub fn import_data(&self) -> Option<&SuggestedImport> {
        self.detail.as_ref()?.import.as_ref()
    }

    pub fn build_site(&self) -> Option<&BuildSite> {
        self.detail.as_ref()?.build.as_ref()
    }

    /// Records that the term at `at` builds the expected test fact from a
    /// proof of its reading.
    pub fn with_build(mut self, span: Span, fact: String) -> Self {
        self.detail_mut().build = Some(BuildSite { span, fact });
        self
    }

    /// The diagnostic without [`Detail::build`], which only the retry that
    /// builds reads: what is reported once that is done.
    pub fn without_build(mut self) -> Self {
        self.clear_build();
        self
    }

    /// Takes [`Detail::build`] off.
    pub fn clear_build(&mut self) {
        if let Some(detail) = self.detail.as_mut() {
            detail.build = None;
            if **detail == Detail::default() {
                self.detail = None;
            }
        }
    }

    /// Records the import that would fix this diagnostic.
    pub fn with_import(mut self, path: impl Into<String>, item: impl Into<String>) -> Self {
        self.detail_mut().import = Some(SuggestedImport {
            path: path.into(),
            item: item.into(),
        });
        self
    }

    pub fn error(code: &'static str, message: impl Into<String>) -> Self {
        Self::new(Severity::Error, code, message)
    }

    pub fn warning(code: &'static str, message: impl Into<String>) -> Self {
        Self::new(Severity::Warning, code, message)
    }

    pub fn goal(message: impl Into<String>) -> Self {
        Self::new(Severity::Goal, "GOAL", message)
    }

    fn new(severity: Severity, code: &'static str, message: impl Into<String>) -> Self {
        Diagnostic {
            severity,
            code,
            message: message.into(),
            labels: Vec::new(),
            notes: Vec::new(),
            detail: None,
        }
    }

    pub fn with_label(mut self, span: Span, message: impl Into<String>) -> Self {
        self.labels.push(Label {
            span,
            message: message.into(),
        });
        self
    }

    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    pub fn primary_span(&self) -> Option<Span> {
        self.labels.first().map(|label| label.span)
    }
}
