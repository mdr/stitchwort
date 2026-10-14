//! Runs source files through the compiler pipeline.

use stitchwort_elab::{Elaborator, PRELUDE};
use stitchwort_syntax::{Diagnostic, FileId, SourceMap, parse_module};

/// A compiler session: the prelude plus whatever has been loaded since.
pub struct Session {
    pub sources: SourceMap,
    pub elab: Elaborator,
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

impl Session {
    pub fn new() -> Self {
        let mut session = Session {
            sources: SourceMap::new(),
            elab: Elaborator::new(),
        };
        if let Err(diagnostics) = session.load("<prelude>", PRELUDE) {
            panic!("internal error: the prelude doesn't check: {diagnostics:#?}");
        }
        session
    }

    /// Parses, elaborates and checks a file, and checks that its exports can
    /// cross the JS boundary.
    pub fn load(&mut self, name: &str, text: &str) -> Result<FileId, Vec<Diagnostic>> {
        let file = self.sources.add(name, text);
        let module = parse_module(file, text)?;
        let first_new_def = self.elab.globals.defs.len();
        let mut diagnostics = self.elab.elaborate_module(&module);
        if diagnostics.is_empty() {
            for id in first_new_def..self.elab.globals.defs.len() {
                let id = stitchwort_core::DefId(id);
                if self.elab.globals.def(id).export
                    && let Err(d) = stitchwort_js::exportable(&self.elab.globals, id)
                {
                    diagnostics.push(d);
                }
            }
        }
        if diagnostics.is_empty() {
            Ok(file)
        } else {
            Err(diagnostics)
        }
    }
}
