//! Projects on the command line (docs/proposals/multi-file.md §7, §12).

use std::path::Path;

/// The repository's own folder isn't a project, so running `stitchwort`
/// anywhere in it, an example included, never finds an accidental one
/// (§4.3).
#[test]
fn the_repository_root_is_not_a_project() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../stitchwort.yaml");
    assert!(!root.exists(), "{} must not exist", root.display());
}
