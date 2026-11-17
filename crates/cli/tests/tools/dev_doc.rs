//! `stitchwort dev doc`: each declaration's layout document and printed
//! text in the line form the self-hosted formatter's engine harness reads
//! (`task fmt:twin STAGE=engine`).

use std::process::{Command, Stdio};

fn dev_doc(name: &str, source: &str) -> std::process::Output {
    let dir =
        std::env::temp_dir().join(format!("stitchwort-dev-doc-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("make a folder");
    let file = dir.join("input.sw");
    std::fs::write(&file, source).expect("write the input");
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["dev", "doc"])
        .arg(&file)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    std::fs::remove_dir_all(&dir).ok();
    output
}

#[test]
fn a_declaration_is_written_as_its_text_and_its_document() {
    let output = dev_doc("one", "def x: Nat := 1\n");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let out = String::from_utf8(output.stdout).unwrap();
    let expected = "decl 1\nsize 27\ntext def x: Nat := 1\nConcat 4\nIdGroup 1\nConcat 4\nConcat 3\nText def\nText  \nText x\n";
    assert!(out.starts_with(expected), "{out}");
    // The text before `:=` is a line of its own; a space is a text of one.
    assert!(out.contains("\nText  \n"), "{out}");
    assert!(out.contains("\nIfBroken 1\n"), "{out}");
}

#[test]
fn a_comment_is_a_line_suffix_and_line_breaks_in_text_are_escaped() {
    let source = "def f: Text := \"\"\"\n  a\\\\b\n  c\n  \"\"\" -- tail\n";
    let output = dev_doc("escapes", source);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let out = String::from_utf8(output.stdout).unwrap();
    assert!(out.contains("\nLineSuffix -- tail\n"), "{out}");
    let text = out.lines().nth(2).unwrap();
    assert!(text.starts_with("text def f: Text :="), "{out}");
    assert!(text.contains("\\n") && text.contains("a\\\\\\\\b"), "{out}");
    // Every document line is a node: none starts inside a text's line break.
    assert!(
        out.lines()
            .skip(3)
            .all(|line| line.chars().next().is_some_and(|c| c.is_ascii_uppercase())),
        "{out}"
    );
}

#[test]
fn a_file_that_does_not_lex_is_refused_on_standard_error() {
    let output = dev_doc("refused", "def x := \"unterminated\n");
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).starts_with("error: "));
}
