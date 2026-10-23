//! Source maps for the generated module (docs/proposals/js-source-maps.md).
//!
//! Generation records, for each generated definition and each export's
//! wrapper, where in the module it starts and which `.sw` span it came from
//! ([`Mapper`]). [`to_json`] turns those into a standard version 3 source map.
//! The granularity is a definition: every line of its generated text maps to
//! the definition's name in the source, so a stack frame anywhere in its body
//! reports the definition's line. Code with no source (the runtime, codecs)
//! is left unmapped.

use std::collections::HashMap;
use std::fmt::Write;

use stitchwort_syntax::{FileId, SourceFile, SourceMap, Span};

/// One mapped position of the generated module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mapping {
    /// Zero-based line and column in the generated module.
    pub line: u32,
    pub column: u32,
    /// Where it came from, or `None` where unmapped code starts again.
    pub span: Option<Span>,
    /// The definition's Stitchwort name: where it's written is what the
    /// position is, and with `label`, it's in the map's `names` too.
    pub name: Option<String>,
    pub label: bool,
}

/// Collects [`Mapping`]s as the module is built, in order.
pub(crate) struct Mapper {
    /// How much of the module has been counted, and the line it ends on.
    counted: usize,
    line: u32,
    out: Vec<Mapping>,
}

impl Mapper {
    /// For a module whose text so far is `js`.
    pub(crate) fn new(js: &str) -> Self {
        let mut mapper = Mapper {
            counted: 0,
            line: 0,
            out: Vec::new(),
        };
        mapper.sync(js);
        mapper
    }

    fn sync(&mut self, js: &str) {
        let new = &js.as_bytes()[self.counted..];
        self.line += u32::try_from(new.iter().filter(|b| **b == b'\n').count())
            .expect("a module of under 4 billion lines");
        self.counted = js.len();
    }

    fn push(&mut self, line: u32, column: usize, span: Span, name: &str, label: bool) {
        self.out.push(Mapping {
            line,
            column: u32::try_from(column).expect("a short line"),
            span: Some(span),
            name: Some(name.to_string()),
            label,
        });
    }

    /// `text` is about to be appended to `js`: every line of it is from
    /// `span`, and its first identifier is `name`.
    pub(crate) fn chunk(&mut self, js: &str, text: &str, span: Span, name: &str) {
        self.sync(js);
        let mut named = false;
        for (i, line) in text.split('\n').enumerate() {
            if line.is_empty() {
                continue;
            }
            let at = self.line + u32::try_from(i).expect("a definition of under 4 billion lines");
            self.push(at, 0, span, name, false);
            // `const $Main$dfoo = …` or `function $$foo(…`: the name.
            if !named
                && (line.starts_with("const ") || line.starts_with("function "))
                && let Some(column) = line.find('$')
            {
                named = true;
                self.push(at, column, span, name, true);
            }
        }
    }

    /// What's appended next has no source.
    pub(crate) fn end(&mut self, js: &str) {
        self.sync(js);
        let line = self.line;
        if self
            .out
            .last()
            .is_some_and(|m| m.span.is_some() && m.line < line)
        {
            self.out.push(Mapping {
                line,
                column: 0,
                span: None,
                name: None,
                label: false,
            });
        }
    }

    pub(crate) fn finish(self) -> Vec<Mapping> {
        self.out
    }
}

/// The source map for `js_file`, version 3, as JSON. `source_path` says how
/// the map refers to a source file, and whether its text is in the map too
/// (`sourcesContent`).
pub fn to_json(
    js_file: &str,
    mappings: &[Mapping],
    sources: &SourceMap,
    source_path: &dyn Fn(&SourceFile) -> (String, bool),
) -> String {
    let mut files: Vec<FileId> = Vec::new();
    let mut file_index: HashMap<FileId, i64> = HashMap::new();
    let mut names: Vec<&str> = Vec::new();
    let mut name_index: HashMap<&str, i64> = HashMap::new();
    let mut line_starts: HashMap<FileId, Vec<usize>> = HashMap::new();

    let mut out = String::new();
    let (mut gen_line, mut gen_col) = (0u32, 0i64);
    let (mut prev_file, mut prev_line, mut prev_col, mut prev_name) = (0i64, 0i64, 0i64, 0i64);
    let mut first_in_line = true;
    for m in mappings {
        while gen_line < m.line {
            out.push(';');
            gen_line += 1;
            gen_col = 0;
            first_in_line = true;
        }
        if !first_in_line {
            out.push(',');
        }
        first_in_line = false;
        vlq(&mut out, i64::from(m.column) - gen_col);
        gen_col = i64::from(m.column);
        let Some(span) = m.span else { continue };
        let file = *file_index.entry(span.file).or_insert_with(|| {
            files.push(span.file);
            i64::try_from(files.len() - 1).expect("few files")
        });
        let text = &sources.get(span.file).text;
        let starts = line_starts.entry(span.file).or_insert_with(|| {
            std::iter::once(0)
                .chain(text.match_indices('\n').map(|(i, _)| i + 1))
                .collect()
        });
        let offset = m
            .name
            .as_deref()
            .and_then(|n| name_offset(text, span, n))
            .unwrap_or(span.start as usize);
        let line = starts.partition_point(|s| *s <= offset) - 1;
        // Columns are in UTF-16 code units.
        let column = text[starts[line]..offset].encode_utf16().count();
        let (line, column) = (line as i64, column as i64);
        vlq(&mut out, file - prev_file);
        vlq(&mut out, line - prev_line);
        vlq(&mut out, column - prev_col);
        (prev_file, prev_line, prev_col) = (file, line, column);
        if let (true, Some(name)) = (m.label, &m.name) {
            let next = i64::try_from(names.len()).expect("few names");
            let index = *name_index.entry(name.as_str()).or_insert_with(|| {
                names.push(name.as_str());
                next
            });
            vlq(&mut out, index - prev_name);
            prev_name = index;
        }
    }

    let mut json = String::from("{\"version\":3,");
    let _ = write!(json, "\"file\":{},", json_string(js_file));
    let resolved: Vec<(String, bool)> =
        files.iter().map(|f| source_path(sources.get(*f))).collect();
    let paths: Vec<String> = resolved.iter().map(|(p, _)| json_string(p)).collect();
    let _ = write!(json, "\"sources\":[{}],", paths.join(","));
    if resolved.iter().any(|(_, with_text)| *with_text) {
        // `null` for a file the consumer can read itself.
        let texts: Vec<String> = files
            .iter()
            .zip(&resolved)
            .map(|(f, (_, with_text))| {
                if *with_text {
                    json_string(&sources.get(*f).text)
                } else {
                    "null".to_string()
                }
            })
            .collect();
        let _ = write!(json, "\"sourcesContent\":[{}],", texts.join(","));
    }
    let names: Vec<String> = names.iter().map(|n| json_string(n)).collect();
    let _ = write!(json, "\"names\":[{}],", names.join(","));
    let _ = write!(json, "\"mappings\":{}}}", json_string(&out));
    json
}

/// `text` as a JSON string (JS's `\u{..}` escapes aren't JSON's).
fn json_string(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Where in `span` the definition `name` is written: after `def`, else as a
/// word. Only the last component counts (`List.length` is written `length`).
fn name_offset(text: &str, span: Span, name: &str) -> Option<usize> {
    let short = name.rsplit('.').next().unwrap_or(name);
    let range = text.get(span.range())?;
    let part = |c: Option<char>| c.is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '\'');
    let word = |at: usize| {
        !part(range[..at].chars().next_back()) && !part(range[at + short.len()..].chars().next())
    };
    let found = range
        .match_indices(&format!("def {short}"))
        .map(|(i, _)| i + 4)
        .find(|at| word(*at))
        .or_else(|| {
            range
                .match_indices(short)
                .map(|(i, _)| i)
                .find(|at| word(*at))
        })?;
    Some(span.start as usize + found)
}

const BASE64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// Appends `value` as a base64 VLQ.
pub fn vlq(out: &mut String, value: i64) {
    let mut v = if value < 0 {
        ((-value) << 1) | 1
    } else {
        value << 1
    };
    loop {
        let mut digit = (v & 31) as usize;
        v >>= 5;
        if v > 0 {
            digit |= 32;
        }
        out.push(BASE64[digit] as char);
        if v == 0 {
            break;
        }
    }
}

/// A decoded segment: generated line and column, the source position
/// `(file, line, column)` if it has one, and the name index if it has one.
pub type Segment = (u32, i64, Option<(i64, i64, i64)>, Option<i64>);

/// Decodes a source map's `mappings`, for tests.
pub fn decode_mappings(mappings: &str) -> Vec<Segment> {
    let value = |c: u8| BASE64.iter().position(|b| *b == c).expect("base64") as i64;
    let mut out = Vec::new();
    let (mut file, mut line, mut col, mut name) = (0i64, 0i64, 0i64, 0i64);
    for (gen_line, text) in mappings.split(';').enumerate() {
        let mut gen_col = 0i64;
        for segment in text.split(',').filter(|s| !s.is_empty()) {
            let mut fields = Vec::new();
            let (mut acc, mut shift) = (0i64, 0);
            for c in segment.bytes() {
                let d = value(c);
                acc |= (d & 31) << shift;
                if d & 32 != 0 {
                    shift += 5;
                } else {
                    fields.push(if acc & 1 == 1 { -(acc >> 1) } else { acc >> 1 });
                    (acc, shift) = (0, 0);
                }
            }
            gen_col += fields[0];
            let source = (fields.len() >= 4).then(|| {
                file += fields[1];
                line += fields[2];
                col += fields[3];
                (file, line, col)
            });
            let named = (fields.len() == 5).then(|| {
                name += fields[4];
                name
            });
            out.push((
                u32::try_from(gen_line).expect("lines"),
                gen_col,
                source,
                named,
            ));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vlq_matches_the_specification() {
        let enc = |v| {
            let mut s = String::new();
            vlq(&mut s, v);
            s
        };
        assert_eq!(enc(0), "A");
        assert_eq!(enc(1), "C");
        assert_eq!(enc(-1), "D");
        assert_eq!(enc(16), "gB");
        assert_eq!(enc(-123), "3H");
    }

    #[test]
    fn decoding_reads_back_what_was_encoded() {
        let mut sources = SourceMap::new();
        let file = sources.add("a.sw", "x\n  def foo: Nat = 1\n");
        let at = |line, column, span, label| Mapping {
            line,
            column,
            span,
            name: Some("foo".into()),
            label,
        };
        let span = Some(Span::new(file, 2, 21));
        let mappings = vec![
            at(1, 0, span, false),
            at(1, 6, span, true),
            Mapping {
                line: 3,
                column: 0,
                span: None,
                name: None,
                label: false,
            },
        ];
        let json = to_json("a.js", &mappings, &sources, &|f| (f.name.clone(), false));
        assert!(json.contains("\"sources\":[\"a.sw\"]"), "{json}");
        assert!(json.contains("\"names\":[\"foo\"]"), "{json}");
        let text = json.split("\"mappings\":\"").nth(1).unwrap();
        let text = text.trim_end_matches("\"}");
        assert_eq!(
            decode_mappings(text),
            vec![
                (1, 0, Some((0, 1, 6)), None),
                (1, 6, Some((0, 1, 6)), Some(0)),
                (3, 0, None, None),
            ]
        );
    }
}
