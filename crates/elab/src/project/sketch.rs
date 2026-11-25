//! What the project pre-pass reads of one file: its namespace line, the
//! names it declares, its imports and the qualified names it writes. A
//! namespace's edges and the names `import N (..)` brings follow from these
//! alone, so a file whose text hasn't changed needn't be parsed to find
//! them: the driver keeps a sketch by the text's hash (SW-4813).

use stitchwort_syntax::ast::{Decl, Module, Name};
use stitchwort_syntax::{FileId, Span};

use super::{grouped, written};
use crate::module::{Ref, decl_refs};

/// What [`FileSketch::things`] says a name is, by its number.
const THINGS: [&str; 3] = ["type", "ability", "definition"];

/// One import of a file.
#[derive(Clone, Debug)]
pub struct ImportSketch {
    /// The namespace, as written.
    pub path: Name,
    /// The names listed: each as in the namespace, and as this file calls
    /// it.
    pub items: Vec<(Name, String)>,
    /// `(..)`.
    pub everything: bool,
}

/// What the pre-pass reads of a file that parsed without errors.
#[derive(Clone, Debug)]
pub struct FileSketch {
    /// The file's namespace line, as `(namespace path, whole line's span)`.
    pub namespace: Option<(Name, Span)>,
    /// The names its declarations write, in order, leaving out the
    /// declarations that have none (tests, equations).
    pub names: Vec<String>,
    pub imports: Vec<ImportSketch>,
    /// The types, abilities and definitions it declares, each with what it
    /// is (`type`, `ability` or `definition`): what a namespace clash
    /// names.
    pub things: Vec<(Name, &'static str)>,
    /// The names its declarations write that contain a `.`, in the order
    /// the pre-pass reads them.
    pub refs: Vec<Name>,
    /// The keys its declarations put in scope that a doc link may name,
    /// without the namespace and its `.` ([`declared_in`]).
    pub declared: Vec<String>,
}

impl FileSketch {
    /// The sketch of a parsed file.
    pub fn of(module: &Module) -> FileSketch {
        let names = (module.decls.iter())
            .map(written)
            .filter(|text| !text.is_empty())
            .map(str::to_string)
            .collect();
        let imports = (module.imports.iter())
            .map(|i| ImportSketch {
                path: i.path.clone(),
                items: (i.items.iter())
                    .map(|item| (item.name.clone(), item.local().text.clone()))
                    .collect(),
                everything: i.everything.is_some(),
            })
            .collect();
        let things = (module.decls.iter())
            .filter_map(|decl| match decl {
                Decl::Data { name, .. } => Some((name.clone(), THINGS[0])),
                Decl::Ability { name, .. } => Some((name.clone(), THINGS[1])),
                Decl::Signature { name, .. } => Some((name.clone(), THINGS[2])),
                _ => None,
            })
            .collect();
        let mut refs = Vec::new();
        for (decl, equations) in grouped(&module.decls) {
            for (r, _) in decl_refs(decl, equations) {
                if let Ref::Name(n) = r
                    && n.text.contains('.')
                {
                    refs.push(n.clone());
                }
            }
        }
        FileSketch {
            namespace: module
                .namespace
                .as_ref()
                .map(|ns| (ns.path.clone(), ns.span)),
            names,
            imports,
            things,
            refs,
            declared: declared_in(module),
        }
    }

    /// The names `import N (..)` brings from a namespace of files with
    /// these sketches: those declared without a qualifier.
    pub fn direct_names(&self) -> impl Iterator<Item = &str> {
        self.names
            .iter()
            .map(String::as_str)
            .filter(|text| !text.contains('.'))
    }

    /// Appends the sketch to `out`, without the file's id.
    pub fn encode(&self, out: &mut Vec<u8>) {
        fn num(out: &mut Vec<u8>, n: usize) {
            out.extend_from_slice(&(n as u32).to_le_bytes());
        }
        fn text(out: &mut Vec<u8>, s: &str) {
            num(out, s.len());
            out.extend_from_slice(s.as_bytes());
        }
        fn span(out: &mut Vec<u8>, s: Span) {
            out.extend_from_slice(&s.start.to_le_bytes());
            out.extend_from_slice(&s.end.to_le_bytes());
        }
        fn name(out: &mut Vec<u8>, n: &Name) {
            text(out, &n.text);
            span(out, n.span);
        }
        match &self.namespace {
            None => out.push(0),
            Some((path, line)) => {
                out.push(1);
                name(out, path);
                span(out, *line);
            }
        }
        num(out, self.names.len());
        for n in &self.names {
            text(out, n);
        }
        num(out, self.imports.len());
        for i in &self.imports {
            name(out, &i.path);
            out.push(u8::from(i.everything));
            num(out, i.items.len());
            for (item, local) in &i.items {
                name(out, item);
                text(out, local);
            }
        }
        num(out, self.things.len());
        for (n, what) in &self.things {
            name(out, n);
            out.push(THINGS.iter().position(|w| w == what).unwrap_or(0) as u8);
        }
        num(out, self.refs.len());
        for r in &self.refs {
            name(out, r);
        }
        num(out, self.declared.len());
        for d in &self.declared {
            text(out, d);
        }
    }

    /// Reads a sketch [`Self::encode`] wrote, taking its bytes off the front
    /// of `bytes`, with every span in file `file`. `None` if the bytes
    /// aren't one.
    pub fn decode(bytes: &mut &[u8], file: FileId) -> Option<FileSketch> {
        struct Reader<'a, 'b>(&'b mut &'a [u8], FileId);
        impl<'a> Reader<'a, '_> {
            fn take(&mut self, n: usize) -> Option<&'a [u8]> {
                let (head, rest) = self.0.split_at_checked(n)?;
                *self.0 = rest;
                Some(head)
            }
            fn u32(&mut self) -> Option<u32> {
                Some(u32::from_le_bytes(self.take(4)?.try_into().ok()?))
            }
            fn count(&mut self) -> Option<usize> {
                let n = self.u32()? as usize;
                // Every counted thing takes a byte at least.
                (n <= self.0.len()).then_some(n)
            }
            fn text(&mut self) -> Option<String> {
                let n = self.u32()? as usize;
                String::from_utf8(self.take(n)?.to_vec()).ok()
            }
            fn span(&mut self) -> Option<Span> {
                let start = self.u32()?;
                let end = self.u32()?;
                Some(Span::new(self.1, start, end))
            }
            fn name(&mut self) -> Option<Name> {
                let text = self.text()?;
                Some(Name {
                    text,
                    span: self.span()?,
                })
            }
        }
        let mut r = Reader(bytes, file);
        let namespace = match r.take(1)?[0] {
            0 => None,
            1 => {
                let path = r.name()?;
                Some((path, r.span()?))
            }
            _ => return None,
        };
        let mut names = Vec::new();
        for _ in 0..r.count()? {
            names.push(r.text()?);
        }
        let mut imports = Vec::new();
        for _ in 0..r.count()? {
            let path = r.name()?;
            let everything = r.take(1)?[0] == 1;
            let mut items = Vec::new();
            for _ in 0..r.count()? {
                let item = r.name()?;
                items.push((item, r.text()?));
            }
            imports.push(ImportSketch {
                path,
                items,
                everything,
            });
        }
        let mut things = Vec::new();
        for _ in 0..r.count()? {
            let n = r.name()?;
            things.push((n, *THINGS.get(usize::from(r.take(1)?[0]))?));
        }
        let mut refs = Vec::new();
        for _ in 0..r.count()? {
            refs.push(r.name()?);
        }
        let mut declared = Vec::new();
        for _ in 0..r.count()? {
            declared.push(r.text()?);
        }
        Some(FileSketch {
            namespace,
            names,
            imports,
            things,
            refs,
            declared,
        })
    }
}

/// The keys the declarations of a file put in scope that a doc link may
/// name, as far as their syntax tells, each without the namespace and its
/// `.`: each declaration's own, its constructors, operations, interface
/// methods and generated `unfold` equation, and a record's fields. A
/// declaration written with a qualifier (`Rules.rule`, or a function for
/// another namespace's type) has the name as written, unless the qualifier
/// is an import's local name for something else (`import N (T as U)`),
/// whose keys are left out. A key may be missing (a local definition's,
/// `t.go`), never wrongly present, in a namespace that checks. Doc links
/// look a project namespace's keys up here, loaded or not, so that what
/// one resolves to never depends on what else a check loads (SW-4827).
pub fn declared_in(module: &Module) -> Vec<String> {
    let renamed: Vec<&str> = (module.imports.iter())
        .flat_map(|i| &i.items)
        .filter(|item| item.local().text != item.name.text)
        .map(|item| item.local().text.as_str())
        .collect();
    let mut out = Vec::new();
    for decl in &module.decls {
        let (Some(main), members) = crate::module::declared_names(decl) else {
            continue;
        };
        if let Some((first, _)) = main.text.split_once('.') {
            if !renamed.contains(&first) {
                out.push(main.text.clone());
            }
            continue;
        }
        for (member, _) in &members {
            if !member.text.starts_with('%') {
                out.push(format!("{}.{}", main.text, member.text));
            }
        }
        if let Decl::Data {
            ctors,
            record: true,
            ..
        } = decl
        {
            for field in ctors.iter().flat_map(|c| &c.fields) {
                out.push(format!("{}.{}", main.text, field.name.text));
            }
        }
        out.push(main.text.clone());
    }
    out
}
