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
    /// For a goal: its hypotheses and target, each printed apart, for the
    /// code navigation index (docs/proposals/code-navigation.md).
    pub goal: Option<Box<GoalData>>,
    /// A counterexample to the statement, when one of the notes says the
    /// statement is false: its bindings, for the index.
    pub counterexample: Option<Box<Counterexample>>,
}

/// A goal as data: what its label shows, each part printed alone.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GoalData {
    pub hypotheses: Vec<Hypothesis>,
    /// What must be shown, as after `⊢`.
    pub target: String,
    /// The goal as a declaration of its own, to paste at the top level of
    /// the file (`theorem fGoal1 (n: Nat): n + 0 = n := ?`), when every
    /// name in it means there what it means at the goal.
    pub lemma: Option<String>,
}

/// One name in scope at a goal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hypothesis {
    pub name: String,
    pub ty: String,
    /// For a `let` of data, its value.
    pub value: Option<String>,
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
            goal: None,
            counterexample: None,
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
