//! Running a program's `main`, performing its `IO` operations for real
//! (docs/proposals/text-and-io.md, "`main` and `stitchwort run`").
//!
//! `main ()` evaluates to a `Comp` tree. The runner evaluates it only as far
//! as the next `Done` or `Call`; for a `Call`, it performs the operation,
//! applies the rest of the tree to the result, and repeats. The loop itself
//! doesn't grow the stack.
//!
//! This is the only place where `print` and `readLine` happen for real. The
//! type checker never calls it.

use std::fmt;
use std::io::{self, BufRead, Write};

use stitchwort_core::value::{apply, eval, force};
use stitchwort_core::{DataId, ResourceError, Term, Value, native};
use stitchwort_syntax::{Diagnostic, Span, parse_expression};

use crate::driver::Session;

/// What `main` must be. A pure `main : () -> ()` fits too: it's passed where
/// a function with more abilities is allowed, like any other argument.
pub const MAIN_TYPE: &str = "() -> {IO} ()";

/// A program's `main`, ready to run.
pub struct Main {
    /// `main ()`, as a computation in the row `{IO}`.
    term: Term,
    /// Where `main` is defined.
    pub span: Span,
}

/// Why a run stopped early.
#[derive(Debug)]
pub enum RunError {
    /// Evaluating the program ran out of resources.
    Resource(ResourceError),
    /// Reading standard input failed.
    Read(io::Error),
    /// Line `line` (counting from 1) of the input isn't valid UTF-8.
    InvalidUtf8 { line: usize },
    /// Writing or flushing standard output failed.
    Write(io::Error),
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RunError::Resource(e) => write!(f, "ran out of resources: {e}"),
            RunError::Read(e) => write!(f, "can't read standard input: {e}"),
            RunError::InvalidUtf8 { line } => {
                write!(f, "line {line} of standard input isn't valid UTF-8")
            }
            RunError::Write(e) => write!(f, "can't write standard output: {e}"),
        }
    }
}

impl RunError {
    /// The error to report: `E-RESOURCE`, pointing at `main`, or `E-IO`.
    pub fn diagnostic(&self, main: &Main) -> Diagnostic {
        match self {
            RunError::Resource(e) => {
                Diagnostic::from(*e).with_label(main.span, "while running this program")
            }
            _ => Diagnostic::error("E-IO", self.to_string()),
        }
    }
}

impl From<ResourceError> for RunError {
    fn from(e: ResourceError) -> RunError {
        RunError::Resource(e)
    }
}

/// `main ()`, checked against [`MAIN_TYPE`]. The lambda lets a pure `main`
/// through: calling a pure function from code in `{IO}` is allowed.
const MAIN_CALL: &str = "((\\u -> main ()) : () -> {IO} ()) ()";

impl Session {
    /// Finds the loaded program's `main`, and checks its type.
    pub fn main(&mut self) -> Result<Main, Diagnostic> {
        let g = &self.elab.globals;
        let Some(def) = g.defs.iter().rev().find(|d| &*d.name == "main") else {
            return Err(Diagnostic::error("E-NO-MAIN", "there's no `main` to run")
                .with_note(format!("define `main : {MAIN_TYPE}`")));
        };
        let (span, ty) = (def.span, self.elab.show(&def.ty_value));
        let file = self.sources.add("<main>", MAIN_CALL);
        let expr = parse_expression(file, MAIN_CALL)?;
        match self.elab.infer_expr(&expr) {
            Ok((term, _)) => Ok(Main { term, span }),
            Err(d) if d.code == "E-RESOURCE" => Err(d),
            Err(_) => Err(Diagnostic::error(
                "E-MAIN-TYPE",
                format!("`main` must have type `{MAIN_TYPE}`"),
            )
            .with_label(span, format!("this has type `{ty}`"))
            .with_note(
                "a pure `main : () -> ()` is allowed too; other abilities must be handled inside `main`",
            )),
        }
    }

    /// What `main` prints when it's run by the prelude's `simulate` with
    /// scripted input lines: the reference that [`Session::run_main`] is
    /// tested against. Its output is these payloads, each followed by LF.
    pub fn simulate(&mut self, input: &[&str]) -> Result<Vec<String>, Diagnostic> {
        self.main()?;
        let lines: Vec<String> = input
            .iter()
            .map(|line| {
                let escaped: String = line
                    .chars()
                    .map(|c| format!("\\u{{{:X}}}", u32::from(c)))
                    .collect();
                format!("\"{escaped}\"")
            })
            .collect();
        let source = format!(
            "fst (simulate [{}] ((\\u -> main ()) : {MAIN_TYPE}))",
            lines.join(", ")
        );
        let file = self.sources.add("<simulate>", &source);
        let expr = parse_expression(file, &source)?;
        let (term, _) = self.elab.infer_expr(&expr)?;
        let g = &self.elab.globals;
        let s = Shapes::new(self);
        let _op = g.budget.operation(self.elab.limits);
        let run = || -> Result<Vec<String>, ResourceError> {
            let mut printed = Vec::new();
            let mut list = force(g, eval(g, &[], &term)?)?;
            while let Value::Ctor(_, 1, cell) = list {
                printed.push(s.text_to_string(self, &cell[0])?);
                list = force(g, cell[1].clone())?;
            }
            Ok(printed)
        };
        run().map_err(Diagnostic::from)
    }

    /// Runs `main`, reading lines from `input` and printing to `output`, and
    /// flushes `output` at the end. Evaluating each step between operations
    /// is one operation, with its own resource limits.
    ///
    /// The contract for reading: input is UTF-8; a trailing LF, and a CR just
    /// before it, are removed; an empty line is `Just ""`; `Nothing` comes
    /// only once nothing remains. Output is flushed before every read. Each
    /// `print` writes its payload, then LF.
    pub fn run_main(
        &self,
        main: &Main,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<(), RunError> {
        let result = self.run_loop(main, input, output);
        match result {
            Ok(()) => output.flush().map_err(RunError::Write),
            Err(e) => {
                // What was printed before the error still appears. The first
                // error is the one reported.
                let _ = output.flush();
                Err(e)
            }
        }
    }

    fn run_loop(
        &self,
        main: &Main,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<(), RunError> {
        let g = &self.elab.globals;
        let s = Shapes::new(self);
        let mut lines = 0;
        let mut comp = {
            let _op = g.budget.operation(self.elab.limits);
            force(g, eval(g, &[], &main.term)?)?
        };
        loop {
            let (o, rest) = match comp {
                Value::Ctor(d, c, _) if d == s.comp && c == s.done => return Ok(()),
                Value::Ctor(d, c, fields) if d == s.comp && c == s.call => {
                    (fields[0].clone(), fields[1].clone())
                }
                _ => unreachable!("`main ()` is a computation"),
            };
            let reply = {
                let _op = g.budget.operation(self.elab.limits);
                // `{IO}` is `Plus IO NoOp`, so every operation is `L` of an
                // `IO` operation.
                let Value::Ctor(_, _, fields) = force(g, o)? else {
                    unreachable!("an operation in `{{IO}}`")
                };
                match force(g, fields[0].clone())? {
                    Value::Ctor(d, c, payload) if d == s.io && c == s.print => {
                        let text = s.text_to_string(self, &payload[0])?;
                        output
                            .write_all(text.as_bytes())
                            .and_then(|()| output.write_all(b"\n"))
                            .map_err(RunError::Write)?;
                        s.unit()
                    }
                    Value::Ctor(d, c, _) if d == s.io && c == s.read_line => {
                        output.flush().map_err(RunError::Write)?;
                        match read_line(input, &mut lines)? {
                            Some(line) => s.just(s.text(&line)),
                            None => s.nothing(),
                        }
                    }
                    _ => unreachable!("an `IO` operation"),
                }
            };
            let _op = g.budget.operation(self.elab.limits);
            comp = force(g, apply(g, rest, reply)?)?;
        }
    }
}

/// The next line of input without its line ending, or `None` at the end.
/// `lines` counts the lines read so far.
fn read_line(input: &mut impl BufRead, lines: &mut usize) -> Result<Option<String>, RunError> {
    let mut bytes = Vec::new();
    if input
        .read_until(b'\n', &mut bytes)
        .map_err(RunError::Read)?
        == 0
    {
        return Ok(None);
    }
    *lines += 1;
    if bytes.last() == Some(&b'\n') {
        bytes.pop();
        if bytes.last() == Some(&b'\r') {
            bytes.pop();
        }
    }
    String::from_utf8(bytes)
        .map(Some)
        .map_err(|_| RunError::InvalidUtf8 { line: *lines })
}

/// The prelude's types that `IO` operations and their results are built
/// from, and their constructors.
struct Shapes {
    comp: DataId,
    done: usize,
    call: usize,
    io: DataId,
    print: usize,
    read_line: usize,
    unit: DataId,
    maybe: DataId,
    text: DataId,
    list: DataId,
    char: DataId,
}

impl Shapes {
    fn new(session: &Session) -> Shapes {
        let g = &session.elab.globals;
        let data = |name: &str| g.find_data(name).expect("the prelude declares it");
        let ctor = |d: DataId, name: &str| {
            g.data(d)
                .ctors
                .iter()
                .position(|c| &*c.name == name)
                .expect("the prelude declares it")
        };
        let (comp, io) = (data("Comp"), data("IO"));
        Shapes {
            comp,
            done: ctor(comp, "Done"),
            call: ctor(comp, "Call"),
            io,
            print: ctor(io, "IO.print"),
            read_line: ctor(io, "IO.readLine"),
            unit: data("UnitType"),
            maybe: data("Maybe"),
            text: data("Text"),
            list: data("List"),
            char: data("Char"),
        }
    }

    fn unit(&self) -> Value {
        Value::Ctor(self.unit, 0, Vec::new().into())
    }

    // `Maybe` is `Nothing | Just a`, and `List` is `Nil | Cons a (List a)`.

    fn nothing(&self) -> Value {
        Value::Ctor(self.maybe, 0, Vec::new().into())
    }

    fn just(&self, value: Value) -> Value {
        Value::Ctor(self.maybe, 1, [value].into())
    }

    /// `MkText` of the line's characters, each `MkChar code rfl`.
    fn text(&self, line: &str) -> Value {
        let mut list = Value::Ctor(self.list, 0, Vec::new().into());
        for c in line.chars().rev() {
            let code = native::nat_value(u32::from(c).into());
            let c = Value::Ctor(self.char, 0, [code, Value::Refl].into());
            list = Value::Ctor(self.list, 1, [c, list].into());
        }
        Value::Ctor(self.text, 0, [list].into())
    }

    /// A `Text` value's characters. A checked program's text is always made
    /// of scalar values.
    fn text_to_string(&self, session: &Session, value: &Value) -> Result<String, ResourceError> {
        let g = &session.elab.globals;
        let Value::Ctor(d, 0, fields) = force(g, value.clone())? else {
            unreachable!("a `Text` value")
        };
        debug_assert_eq!(d, self.text);
        let mut out = String::new();
        let mut list = force(g, fields[0].clone())?;
        while let Value::Ctor(_, 1, cell) = list {
            let Value::Ctor(_, 0, c) = force(g, cell[0].clone())? else {
                unreachable!("a `Char` value")
            };
            let code = native::as_nat(g, &c[0])?
                .and_then(|n| u32::try_from(n).ok())
                .and_then(char::from_u32)
                .expect("a `Char` holds a scalar value");
            out.push(code);
            list = force(g, cell[1].clone())?;
        }
        Ok(out)
    }
}
