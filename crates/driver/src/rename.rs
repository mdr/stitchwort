//! The edits of a rename (docs/proposals/refactoring.md §1.2, §3.1): given
//! what a checked project's navigation answers say, a target and a new name,
//! the text edits that rename it everywhere and the [`Promise`] to check them
//! against. [`LiveProject::trial`] then says what the edits would break.
//!
//! Covers locals, hypotheses, functions and theorems (R3). Fields,
//! constructors, types and namespaces have hashed names and more places to
//! edit (R7), and are refused with a message saying so.

use std::collections::BTreeMap;

use stitchwort_syntax::{SourceMap, Tok, keywords, lex};

use crate::live::{Answers, Edit, LiveProject, Loc, Place, Promise};
use crate::nav::Range;

/// What to rename.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Target {
    /// A declaration's full name (`Shop.step`).
    Name(String),
    /// What is written at a position of a project file: a declaration's
    /// name, a use of one, a local's binder or a use of it. Lines and
    /// columns count from 0, as LSP's do.
    At {
        path: String,
        line: u32,
        column: u32,
    },
}

/// A rename, ready to be checked.
#[derive(Clone, Debug)]
pub struct RenamePlan {
    /// The name as written, without its qualifier.
    pub old: String,
    pub new: String,
    /// The declaration's full name, or the local's name.
    pub name: String,
    /// `def`, `theorem` or `local`.
    pub kind: &'static str,
    /// Sorted by file, then position.
    pub edits: Vec<Edit>,
    pub promise: Promise,
}

/// Why there is no rename to check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RenameError {
    /// No declaration has this full name.
    NoSuchName(String),
    /// Nothing renamable is written at the position (or the file is not one
    /// of the project's).
    NothingAt {
        path: String,
        line: u32,
        column: u32,
    },
    /// The target is in the standard library, which is never changed here.
    Library(String),
    /// A kind of name not renamed yet (R7).
    Unsupported { name: String, kind: &'static str },
    /// Not an identifier a function, theorem or local can have.
    BadName { name: String, why: &'static str },
    /// The new name is the old one.
    SameName(String),
}

impl RenameError {
    pub fn describe(&self) -> String {
        match self {
            RenameError::NoSuchName(name) => {
                format!(
                    "there's no declaration `{name}` in the project; give its full name, or a position as `file:line:column`"
                )
            }
            RenameError::NothingAt { path, line, column } => format!(
                "there's no name to rename at {path}:{}:{}",
                line + 1,
                column + 1
            ),
            RenameError::Library(name) => {
                format!("`{name}` is in the standard library and can't be renamed here")
            }
            RenameError::Unsupported { name, kind } => format!(
                "can't rename `{name}` yet: renaming a {} is not supported (only locals, hypotheses, functions and theorems)",
                kind_word(kind)
            ),
            RenameError::BadName { name, why } => format!("`{name}` isn't a name for this: {why}"),
            RenameError::SameName(name) => format!("the new name is the old one, `{name}`"),
        }
    }
}

fn kind_word(kind: &str) -> &str {
    match kind {
        "record" | "data" => "type",
        "ctor" => "constructor",
        "field" => "field",
        "op" => "ability operation",
        other => other,
    }
}

/// Whether `name` can be the name of a local, function or theorem: one
/// lowercase identifier that isn't a keyword.
pub fn check_new_name(name: &str) -> Result<(), RenameError> {
    let bad = |why| {
        Err(RenameError::BadName {
            name: name.to_string(),
            why,
        })
    };
    if keywords().contains(&name) {
        return bad("it is a keyword");
    }
    if name.contains('.') {
        return bad("it has a dot: give the last component only");
    }
    let mut sources = SourceMap::new();
    let file = sources.add("name", name);
    match lex(file, name).as_deref() {
        Ok([one]) if matches!(&one.tok, Tok::Lower(w) if w == name) => Ok(()),
        Ok([one]) if matches!(one.tok, Tok::Upper(_)) => {
            bad("it starts with an uppercase letter, which is for types and constructors")
        }
        _ => bad("it is not a single identifier"),
    }
}

impl LiveProject {
    /// The rename of `target` to `new`, from the answers of the project as
    /// checked now (which the caller has finished checking).
    pub fn rename_plan(&mut self, target: &Target, new: &str) -> Result<RenamePlan, RenameError> {
        let answers = self.answers();
        plan_rename(
            &answers,
            &|path| self.text(path).map(str::to_string),
            target,
            new,
        )
    }
}

/// The edits renaming `target` to `new`. `text` gives a project file's text,
/// which the answers' ranges are from.
pub fn plan_rename(
    answers: &Answers,
    text: &dyn Fn(&str) -> Option<String>,
    target: &Target,
    new: &str,
) -> Result<RenamePlan, RenameError> {
    check_new_name(new)?;
    let (loc, name, kind) = resolve(answers, target)?;
    if matches!(loc.place, Place::Library(_)) {
        return Err(RenameError::Library(name));
    }
    if !matches!(kind, "def" | "theorem" | "local") {
        return Err(RenameError::Unsupported { name, kind });
    }
    let old = name.rsplit('.').next().unwrap_or(&name).to_string();
    if old == new {
        return Err(RenameError::SameName(old));
    }

    // Where the old name is written: its declaration, and every reference
    // to the same declaration (matched by where it is declared).
    let mut texts: BTreeMap<String, Option<String>> = BTreeMap::new();
    let mut slice_of = |path: &str, range: Range| -> Option<(Range, String)> {
        if range[0] != range[2] {
            return None;
        }
        let text = texts
            .entry(path.to_string())
            .or_insert_with(|| text(path))
            .as_deref()?;
        let line = text.split('\n').nth(range[0] as usize)?;
        let slice = utf16_slice(line, range[1], range[3])?;
        Some((range, slice.to_string()))
    };
    let mut edits = Vec::new();

    let generated_prefix = format!("{name}.");
    for (place, file) in answers {
        let Place::Program(path) = place else {
            continue;
        };
        let mut found: Vec<(Range, String)> = Vec::new();
        if *place == loc.place {
            found.extend(slice_of(path, loc.range));
        }
        for r in &file.refs {
            if r.target == loc {
                found.extend(slice_of(path, r.range));
            } else if kind != "local" && r.kind != "local" && r.name.starts_with(&generated_prefix)
            {
                // A generated declaration (`f.eq1`, `f.induct`) written
                // after its owner: the owner's component is edited.
                let rest = &r.name[generated_prefix.len()..];
                if let Some((range, slice)) = slice_of(path, r.range) {
                    let written = format!("{old}.{rest}");
                    if let Some(at) = ends_with_name(&slice, &written) {
                        let start = range[3] - utf16_len(&slice[at..]);
                        edits.push(edit_at(place, range[0], start, &old, new));
                    }
                }
            }
        }
        for (range, slice) in found {
            // SW-2627 will record the exact span of a name; until then a
            // site is edited only where the text there ends with the old
            // name, so an import alias or a renamed pun is left alone.
            if let Some(at) = ends_with_name(&slice, &old) {
                let start = range[3] - utf16_len(&slice[at..]);
                edits.push(edit_at(place, range[0], start, &old, new));
            }
        }
    }
    edits.sort_by(|a, b| (&a.place, a.range).cmp(&(&b.place, b.range)));
    edits.dedup();

    let mut renames = BTreeMap::new();
    if kind != "local" {
        let renamed = match name.rfind('.') {
            Some(dot) => format!("{}{new}", &name[..=dot]),
            None => new.to_string(),
        };
        renames.insert(name.clone(), renamed);
    }
    Ok(RenamePlan {
        old,
        new: new.to_string(),
        name,
        kind,
        edits,
        promise: Promise::SameMeaning { renames },
    })
}

fn edit_at(place: &Place, line: u32, start: u32, old: &str, new: &str) -> Edit {
    Edit {
        place: place.clone(),
        range: [line, start, line, start + utf16_len(old)],
        new_text: new.to_string(),
    }
}

fn utf16_len(s: &str) -> u32 {
    s.encode_utf16().count() as u32
}

/// The part of `line` between UTF-16 columns `from` and `to`.
fn utf16_slice(line: &str, from: u32, to: u32) -> Option<&str> {
    let mut column = 0;
    let (mut start, mut end) = (None, None);
    for (i, c) in line.char_indices() {
        if column == from {
            start = Some(i);
        }
        if column == to {
            end = Some(i);
        }
        column += c.len_utf16() as u32;
    }
    if column == from {
        start = Some(line.len());
    }
    if column == to {
        end = Some(line.len());
    }
    Some(&line[start?..end?])
}

/// Where in `slice` the name `word` starts, if the slice ends with it as a
/// whole name (not the end of a longer one).
fn ends_with_name(slice: &str, word: &str) -> Option<usize> {
    let at = slice.len().checked_sub(word.len())?;
    if !slice.is_char_boundary(at) || &slice[at..] != word {
        return None;
    }
    let before = slice[..at].chars().next_back();
    match before {
        Some(c) if c.is_alphanumeric() || c == '_' || c == '\'' => None,
        _ => Some(at),
    }
}

/// The declaration (or binder) `target` names: where it is declared, its
/// full name and kind.
fn resolve(answers: &Answers, target: &Target) -> Result<(Loc, String, &'static str), RenameError> {
    match target {
        Target::Name(name) => {
            for (place, file) in answers {
                if let Some(item) = file.outline.iter().find(|i| i.name == *name) {
                    return Ok((
                        Loc {
                            place: place.clone(),
                            range: item.range,
                        },
                        name.clone(),
                        item.kind,
                    ));
                }
            }
            // A name only the library declares.
            let in_library = (answers.values().flat_map(|f| &f.refs))
                .any(|r| r.name == *name && matches!(r.target.place, Place::Library(_)));
            if in_library {
                return Err(RenameError::Library(name.clone()));
            }
            Err(RenameError::NoSuchName(name.clone()))
        }
        Target::At { path, line, column } => {
            let nothing = || RenameError::NothingAt {
                path: path.clone(),
                line: *line,
                column: *column,
            };
            let place = Place::Program(path.clone());
            let file = answers.get(&place).ok_or_else(nothing)?;
            let at = (*line, *column);
            if let Some(item) = file
                .outline
                .iter()
                .find(|i| (i.range[0], i.range[1]) <= at && at < (i.range[2], i.range[3]))
            {
                let loc = Loc {
                    place,
                    range: item.range,
                };
                return Ok((loc, item.name.clone(), item.kind));
            }
            if let Some(r) = file.ref_at(*line, *column) {
                return Ok((r.target.clone(), r.name.clone(), r.kind));
            }
            if let Some(r) = file.binder_at(&place, *line, *column) {
                return Ok((r.target, r.name, r.kind));
            }
            Err(nothing())
        }
    }
}
