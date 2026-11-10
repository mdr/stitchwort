//! Rename in the server (docs/proposals/refactoring.md, R3): `prepareRename`,
//! `rename`, and "rename anyway".
//!
//! The project is on the checker thread, so a rename is a job for it, sent
//! like an edit and answered from there ([`RenameJob`]); search threads and
//! the main thread go on meanwhile. The edits come from
//! [`stitchwort_driver::rename`] and are tried on the checked project
//! ([`LiveProject::trial`]). A clean rename keeps the checked state and
//! answers the `WorkspaceEdit`.
//!
//! With problems the rename is refused, the project put back, and the plan
//! remembered ([`Anyway`]). The error says what would break and carries
//! `data: {"renameAnyway": true}`. The edit can then be had by
//! `workspace/executeCommand` of `stitchwort.renameAnyway`, whose answer is
//! the `WorkspaceEdit`: a client that can't take requests from the server
//! (the playground's) applies it itself. A client that can show a message
//! with buttons (VS Code) is also sent `window/showMessageRequest`, and on
//! the button the server asks the client to apply the edit
//! (`workspace/applyEdit`), so that it needs no code of its own.
//!
//! Either way the declarations whose meaning changed get a warning that
//! stays until the file is edited to other text than the rename left. The new
//! errors are ordinary diagnostics.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

#[cfg(target_family = "wasm")]
use super::wasm::FileUrl as _;
use lsp_server::{ErrorCode, Notification, Request, RequestId, Response};
use lsp_types::{Position, Url};
use serde_json::{Value, json};
use stitchwort_driver::live::{Answers, Place, Problems, TrialOutcome};
use stitchwort_driver::rename::{RenameError, RenamePlan, Target};
use stitchwort_syntax::Severity;

use super::{Checker, Work, range};

/// The command that applies the rename the server last refused.
pub const RENAME_ANYWAY: &str = "stitchwort.renameAnyway";
/// The button of the message that offers it.
const BUTTON: &str = "Rename anyway";
/// Problems listed in an error before "and N more".
const LISTED: usize = 5;
/// The name tried to find where a name is, for `prepareRename`.
const PROBE: &str = "renamed_by_stitchwort";

/// A job for the checker thread: a request about renaming, or the client's
/// answer to the message offering "rename anyway".
pub(super) enum RenameJob {
    Prepare {
        id: RequestId,
        path: PathBuf,
        position: Position,
    },
    Rename {
        id: RequestId,
        path: PathBuf,
        position: Position,
        new_name: String,
        document_changes: bool,
    },
    /// `workspace/executeCommand` of [`RENAME_ANYWAY`].
    Anyway {
        id: RequestId,
        document_changes: bool,
    },
    /// The client's response to a request of the server's.
    Reply {
        id: RequestId,
        result: Option<Value>,
        document_changes: bool,
    },
}

impl RenameJob {
    pub(super) fn path(&self) -> Option<&Path> {
        match self {
            RenameJob::Prepare { path, .. } | RenameJob::Rename { path, .. } => Some(path),
            _ => None,
        }
    }
}

/// A rename refused for its problems, which can be applied anyway.
pub(super) struct Anyway {
    key: PathBuf,
    plan: RenamePlan,
    /// The edited files as they were: the plan is for these texts.
    base: BTreeMap<String, String>,
    /// The id of the message offering it, if one was sent.
    asked: Option<String>,
}

/// The warnings left on the declarations whose meaning a rename changed, by
/// file: the text of the file as the rename left it, and the places.
pub(super) type Warnings = BTreeMap<Url, (String, Vec<[u32; 4]>)>;

pub(super) struct Failure {
    code: ErrorCode,
    message: String,
    data: Option<Value>,
}

fn fail(message: impl Into<String>) -> Failure {
    Failure {
        code: ErrorCode::RequestFailed,
        message: message.into(),
        data: None,
    }
}

impl Checker {
    pub(super) fn rename_job(&mut self, job: RenameJob) {
        let id = match &job {
            RenameJob::Prepare { id, .. }
            | RenameJob::Rename { id, .. }
            | RenameJob::Anyway { id, .. }
            | RenameJob::Reply { id, .. } => id.clone(),
        };
        let ran = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.rename_run(job)));
        match ran {
            Ok(Some(result)) => {
                let response = match result {
                    Ok(value) => Response::new_ok(id, value),
                    Err(f) => Response {
                        id,
                        result: None,
                        error: Some(lsp_server::ResponseError {
                            code: f.code as i32,
                            message: f.message,
                            data: f.data,
                        }),
                    },
                };
                let _ = self.sender.send(response.into());
            }
            Ok(None) => {}
            Err(payload) => {
                // The request is answered; the checker restarts as for any
                // panic.
                let response = Response::new_err(
                    id,
                    ErrorCode::InternalError as i32,
                    format!(
                        "internal error in rename: {}",
                        super::panic_message(&*payload)
                    ),
                );
                let _ = self.sender.send(response.into());
                std::panic::resume_unwind(payload);
            }
        }
    }

    /// Does the job; its answer, or none if it is not a request.
    fn rename_run(&mut self, job: RenameJob) -> Option<Result<Value, Failure>> {
        match job {
            RenameJob::Prepare { path, position, .. } => Some(self.prepare(&path, position)),
            RenameJob::Rename {
                path,
                position,
                new_name,
                document_changes,
                ..
            } => Some(self.rename(&path, position, &new_name, document_changes)),
            RenameJob::Anyway {
                document_changes, ..
            } => Some(self.rename_anyway(document_changes)),
            RenameJob::Reply {
                id,
                result,
                document_changes,
            } => {
                self.offered_reply(&id, result.as_ref(), document_changes);
                None
            }
        }
    }

    /// The project folder and the relative path of `path`, if it can be
    /// renamed in, with the project fully checked.
    fn project_for(&mut self, path: &Path) -> Result<(PathBuf, String), Failure> {
        if let Some(why) = &self.stopped {
            return Err(fail(why.clone()));
        }
        if let Some(key) = self.quarantine_key(path) {
            return Err(fail(self.quarantined[&key].clone()));
        }
        let Some((key, relative)) = self.project_of(path) else {
            return Err(fail(
                "rename works on the files of a project; this file is checked on its own",
            ));
        };
        let Some(Work::Project(p)) = self.work.get(&key) else {
            return Err(fail("rename works on the files of a project"));
        };
        if p.live.pending() {
            return Err(fail(
                "the project is still being checked: try the rename again in a moment",
            ));
        }
        Ok((key, relative))
    }

    fn plan(
        &mut self,
        key: &Path,
        relative: &str,
        position: Position,
        new: &str,
    ) -> Result<RenamePlan, RenameError> {
        let Some(Work::Project(p)) = self.work.get_mut(key) else {
            unreachable!("project_for found it")
        };
        let target = Target::At {
            path: relative.to_string(),
            line: position.line,
            column: position.character,
        };
        p.live.rename_plan(&target, new)
    }

    /// The words of a refusal to plan, with a hint when errors hide names.
    fn plan_failure(&mut self, key: &Path, e: &RenameError) -> Failure {
        let mut message = e.describe();
        if matches!(
            e,
            RenameError::NoSuchName(_) | RenameError::NothingAt { .. }
        ) && let Some(Work::Project(p)) = self.work.get_mut(key)
            && p.live
                .answers()
                .values()
                .flat_map(|f| &f.diagnostics)
                .any(|d| d.severity == Severity::Error)
        {
            message.push_str(" (the project has errors, which can hide names)");
        }
        fail(message)
    }

    /// `textDocument/prepareRename`: the range and text of the name at
    /// `position`, if it can be renamed.
    fn prepare(&mut self, path: &Path, position: Position) -> Result<Value, Failure> {
        let (key, relative) = self.project_for(path)?;
        let plan = match self.plan(&key, &relative, position, PROBE) {
            Ok(plan) => plan,
            Err(e) => return Err(self.plan_failure(&key, &e)),
        };
        let at = (position.line, position.character);
        let place = Place::Program(relative.clone());
        // The edit that covers the position is the name written there.
        let covering = plan.edits.iter().find(|e| {
            e.place == place
                && e.range[0] == e.range[2]
                && (e.range[0], e.range[1]) <= at
                && at <= (e.range[2], e.range[3])
        });
        let Some(edit) = covering else {
            let e = RenameError::NothingAt {
                path: relative,
                line: position.line,
                column: position.character,
            };
            return Err(self.plan_failure(&key, &e));
        };
        let Some(Work::Project(p)) = self.work.get(&key) else {
            unreachable!("project_for found it")
        };
        let placeholder = p
            .live
            .text(&relative)
            .and_then(|text| text.split('\n').nth(edit.range[0] as usize))
            .map(|line| utf16_slice(line, edit.range[1], edit.range[3]))
            .unwrap_or_default();
        Ok(json!({ "range": range(edit.range), "placeholder": placeholder }))
    }

    /// `textDocument/rename`.
    fn rename(
        &mut self,
        path: &Path,
        position: Position,
        new: &str,
        document_changes: bool,
    ) -> Result<Value, Failure> {
        let (key, relative) = self.project_for(path)?;
        let plan = match self.plan(&key, &relative, position, new) {
            Ok(plan) => plan,
            Err(e) => return Err(self.plan_failure(&key, &e)),
        };
        self.try_plan(&key, plan, false, document_changes)
    }

    /// `workspace/executeCommand` of [`RENAME_ANYWAY`]: the edit of the
    /// rename last refused.
    fn rename_anyway(&mut self, document_changes: bool) -> Result<Value, Failure> {
        let Some(anyway) = self.anyway.take() else {
            return Err(fail(
                "there's no refused rename to apply: ask for the rename again",
            ));
        };
        let Some(Work::Project(p)) = self.work.get(&anyway.key) else {
            return Err(fail("the project is gone: ask for the rename again"));
        };
        let unchanged = !p.live.pending()
            && anyway
                .base
                .iter()
                .all(|(path, text)| p.live.text(path) == Some(text.as_str()));
        if !unchanged {
            return Err(fail(
                "the files changed since the rename was refused: ask for the rename again",
            ));
        }
        self.try_plan(&anyway.key, anyway.plan, true, document_changes)
    }

    /// Tries `plan` on the project, and either keeps it, answering the
    /// edit, or puts the project back and says what it would break.
    fn try_plan(
        &mut self,
        key: &Path,
        plan: RenamePlan,
        anyway: bool,
        document_changes: bool,
    ) -> Result<Value, Failure> {
        let Some(Work::Project(p)) = self.work.get_mut(key) else {
            unreachable!("project_for found it")
        };
        let doing = format!("renaming `{}` to `{}`", plan.old, plan.new);
        let mut base = BTreeMap::new();
        for edit in &plan.edits {
            if let Place::Program(path) = &edit.place
                && let Some(text) = p.live.text(path)
            {
                base.insert(path.clone(), text.to_string());
            }
        }
        let trial = match p.live.trial(&plan.edits, &plan.promise) {
            Ok(TrialOutcome::Checked(trial)) => trial,
            Ok(TrialOutcome::Refused(refusals)) => {
                let lines: Vec<String> = refusals.iter().map(|r| r.describe(&doing)).collect();
                return Err(fail(lines.join("\n")));
            }
            Err(_) => {
                return Err(Failure {
                    code: ErrorCode::ContentModified,
                    message: "the text changed during the rename: ask for it again".to_string(),
                    data: None,
                });
            }
        };
        let problems = trial.problems.clone();
        if !problems.is_empty() && !anyway {
            let _ = p.live.restore(trial);
            let message = refusal_message(&plan, &problems);
            let count = problems.diagnostics.len() + problems.changed.len();
            let asked = self.offer(&plan, count);
            self.anyway = Some(Anyway {
                key: key.to_path_buf(),
                plan,
                base,
                asked,
            });
            return Err(Failure {
                code: ErrorCode::RequestFailed,
                message,
                data: Some(json!({ "renameAnyway": true })),
            });
        }
        p.live.keep(trial);
        self.anyway = None;
        let answers = p.live.answers();
        let mut warned: BTreeMap<String, (String, Vec<[u32; 4]>)> = BTreeMap::new();
        for c in &problems.changed {
            if let (Some(path), Some(range)) = (&c.path, c.range)
                && let Some(text) = p.live.text(path)
            {
                warned
                    .entry(path.clone())
                    .or_insert_with(|| (text.to_string(), Vec::new()))
                    .1
                    .push(range);
            }
        }
        for (path, warning) in warned {
            if let Ok(uri) = Url::from_file_path(file_of(key, &path)) {
                self.warnings.insert(uri, warning);
            }
        }
        let edit = self.workspace_edit(key, &plan, document_changes);
        // The edit is what the answer carries; the checked state is what the
        // editor will have once it is applied.
        self.last = Some(key.to_path_buf());
        self.republish(key, answers);
        Ok(edit)
    }

    fn republish(&mut self, key: &Path, answers: Answers) {
        self.publish_as(key, true, answers, false);
    }

    /// The `WorkspaceEdit` for `plan`: `documentChanges` if the client takes
    /// them, else `changes`.
    fn workspace_edit(&self, key: &Path, plan: &RenamePlan, document_changes: bool) -> Value {
        let mut by_file: BTreeMap<&str, Vec<Value>> = BTreeMap::new();
        for e in &plan.edits {
            if let Place::Program(path) = &e.place {
                by_file
                    .entry(path)
                    .or_default()
                    .push(json!({ "range": range(e.range), "newText": e.new_text }));
            }
        }
        if document_changes {
            let changes: Vec<Value> = by_file
                .into_iter()
                .filter_map(|(path, edits)| {
                    let full = file_of(key, path);
                    let uri = Url::from_file_path(&full).ok()?;
                    Some(json!({
                        "textDocument": { "uri": uri, "version": self.versions.get(&full) },
                        "edits": edits,
                    }))
                })
                .collect();
            json!({ "documentChanges": changes })
        } else {
            let changes: serde_json::Map<String, Value> = by_file
                .into_iter()
                .filter_map(|(path, edits)| {
                    let uri = Url::from_file_path(file_of(key, path)).ok()?;
                    Some((uri.to_string(), Value::Array(edits)))
                })
                .collect();
            json!({ "changes": changes })
        }
    }

    /// Asks the client to offer "Rename anyway", if it can: the id of the
    /// request.
    fn offer(&mut self, plan: &RenamePlan, count: usize) -> Option<String> {
        if !self.options.offer_rename_anyway {
            return None;
        }
        self.requests += 1;
        let id = format!("stitchwort-{}", self.requests);
        let message = format!(
            "Renaming `{}` to `{}` would cause {count} {}. Rename anyway and fix them by hand?",
            plan.old,
            plan.new,
            if count == 1 { "problem" } else { "problems" }
        );
        let request = Request::new(
            RequestId::from(id.clone()),
            "window/showMessageRequest".to_string(),
            json!({
                "type": lsp_types::MessageType::WARNING,
                "message": message,
                "actions": [{ "title": BUTTON }],
            }),
        );
        let _ = self.sender.send(request.into());
        Some(id)
    }

    /// The client's answer to [`Checker::offer`]: on the button, applies the
    /// rename, through the client.
    fn offered_reply(&mut self, id: &RequestId, result: Option<&Value>, document_changes: bool) {
        let asked = self.anyway.as_ref().and_then(|a| a.asked.clone());
        let ours = asked.is_some_and(|asked| RequestId::from(asked) == *id);
        let pressed = result.and_then(|r| r.get("title")).and_then(Value::as_str) == Some(BUTTON);
        if !ours || !pressed {
            return;
        }
        match self.rename_anyway(document_changes) {
            Ok(edit) => {
                self.requests += 1;
                let request = Request::new(
                    RequestId::from(format!("stitchwort-{}", self.requests)),
                    "workspace/applyEdit".to_string(),
                    json!({ "label": BUTTON, "edit": edit }),
                );
                let _ = self.sender.send(request.into());
            }
            Err(f) => {
                let n = Notification::new(
                    "window/showMessage".to_string(),
                    json!({ "type": lsp_types::MessageType::ERROR, "message": f.message }),
                );
                let _ = self.sender.send(n.into());
            }
        }
    }

    /// Forgets the warnings of a file edited to other text than the rename
    /// left.
    pub(super) fn rename_warnings_stale(&mut self, path: &Path, text: &str) {
        if self.warnings.is_empty() {
            return;
        }
        if let Ok(uri) = Url::from_file_path(path)
            && self
                .warnings
                .get(&uri)
                .is_some_and(|(kept, _)| kept != text)
        {
            self.warnings.remove(&uri);
        }
    }
}

/// The warnings to show with the diagnostics of `uri`.
pub(super) fn warnings_for(warnings: &Warnings, uri: &Url) -> Vec<lsp_types::Diagnostic> {
    let Some((_, places)) = warnings.get(uri) else {
        return Vec::new();
    };
    places
        .iter()
        .map(|r| lsp_types::Diagnostic {
            range: range(*r),
            severity: Some(lsp_types::DiagnosticSeverity::WARNING),
            code: Some(lsp_types::NumberOrString::String(
                "rename-changed-meaning".to_string(),
            )),
            source: Some("stitchwort".to_string()),
            message: "meaning changed by rename: check this".to_string(),
            ..Default::default()
        })
        .collect()
}

/// The error for a rename with problems: at most [`LISTED`] of them.
fn refusal_message(plan: &RenamePlan, problems: &Problems) -> String {
    let lines = problems.describe("it");
    let count = lines.len();
    let mut message = format!(
        "Can't rename `{}` to `{}`: it would cause {count} {}.",
        plan.old,
        plan.new,
        if count == 1 { "problem" } else { "problems" }
    );
    for line in lines.iter().take(LISTED) {
        message.push_str("\n- ");
        message.push_str(line);
    }
    if count > LISTED {
        message.push_str(&format!("\n- and {} more", count - LISTED));
    }
    message.push_str("\nChoose \"Rename anyway\" to make the change and fix these by hand.");
    message
}

fn file_of(key: &Path, relative: &str) -> PathBuf {
    let mut full = key.to_path_buf();
    full.extend(relative.split('/'));
    full
}

/// The part of `line` between UTF-16 columns `from` and `to`.
fn utf16_slice(line: &str, from: u32, to: u32) -> String {
    let units: Vec<u16> = line.encode_utf16().collect();
    let (from, to) = (from as usize, (to as usize).min(units.len()));
    String::from_utf16_lossy(units.get(from..to).unwrap_or_default())
}
