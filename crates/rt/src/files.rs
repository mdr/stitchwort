//! The host side of `Files` (std/Files/Files.sw): its four operations on the
//! real disk, over `std::fs`, with the host's errors mapped onto
//! `FileError`'s kinds. Shared by every runner that performs `Files`, as
//! [`crate::host`] is for `IO`, so they reply alike: the runners only turn
//! these answers into values (docs/proposals/file-io-and-text.md §2.3).
//!
//! The answers are those of `Files.simulate`'s disk wherever the host can
//! agree with it: a folder's size is 0, a listing is sorted by name in
//! `Text.compare`'s order (Rust's `str` order: by scalar value), and a write
//! never creates a folder. Symbolic links are followed.

use std::fs;
use std::io::{self, Write as _};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// What a path is: `FileKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    File,
    Folder,
    Other,
}

/// Why an operation failed: `FileError`'s kinds, without the path, which
/// the runner puts back from the operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Failure {
    NotFound,
    NotPermitted,
    NotAFile,
    NotAFolder,
    NotText,
    /// The host's own words.
    Other(String),
}

/// A `Path` value as a host path: its parts as `Path.normal` takes them
/// (each split again at `/`, with empty parts and `.` dropped, `..` kept),
/// joined with `/`, after `/` if it is absolute; the starting folder (`.`)
/// if none is left. `Files.simulate`'s disk reads a path through the same
/// `Path.normal`, so a path built by hand means the same to both.
pub fn host_path(parts: &[String], absolute: bool) -> PathBuf {
    let joined = parts
        .iter()
        .flat_map(|part| part.split('/'))
        .filter(|part| !part.is_empty() && *part != ".")
        .collect::<Vec<_>>()
        .join("/");
    match (absolute, joined.is_empty()) {
        (true, _) => PathBuf::from(format!("/{joined}")),
        (false, true) => PathBuf::from("."),
        (false, false) => PathBuf::from(joined),
    }
}

fn failure(e: &io::Error) -> Failure {
    use io::ErrorKind as K;
    match e.kind() {
        K::NotFound => Failure::NotFound,
        K::PermissionDenied | K::ReadOnlyFilesystem => Failure::NotPermitted,
        K::IsADirectory => Failure::NotAFile,
        K::NotADirectory => Failure::NotAFolder,
        _ => Failure::Other(e.to_string()),
    }
}

fn kind_of(metadata: &fs::Metadata) -> Kind {
    if metadata.is_file() {
        Kind::File
    } else if metadata.is_dir() {
        Kind::Folder
    } else {
        Kind::Other
    }
}

/// `Files.read`: the whole file, as UTF-8. The checked bytes are returned
/// as they were read: a runner's `Text::from` takes an ASCII file's `String`
/// as its buffer with no copy.
pub fn read(path: &Path) -> Result<String, Failure> {
    let bytes = fs::read(path).map_err(|e| match failure(&e) {
        // Opening a folder succeeds on some hosts and reading it fails.
        Failure::Other(_) if path.is_dir() => Failure::NotAFile,
        other => other,
    })?;
    String::from_utf8(bytes).map_err(|_| Failure::NotText)
}

/// A number for each temporary file this process makes, so that two writes
/// at once never share one.
static TEMPORARY: AtomicU64 = AtomicU64::new(0);

/// `Files.write`: replaces the file whole, or creates it. The text goes to a
/// temporary file beside the target, which is then renamed over it, so the
/// target is never left half written: it has its old contents or the new
/// ones. An existing file must be writable, and keeps its permissions (not
/// its other hard links or its owner); the temporary file is never readable
/// more widely than the file will be. A link is written through to the file
/// it points at, even one that doesn't exist yet. Something that isn't a
/// regular file (a device or a pipe) is written in place: replacing it
/// whole means nothing.
pub fn write(path: &Path, text: &str) -> Result<(), Failure> {
    let target = resolve_link(path);
    let existing = match fs::metadata(&target) {
        Ok(m) if m.is_dir() => return Err(Failure::NotAFile),
        Ok(m) if !m.is_file() => {
            return fs::OpenOptions::new()
                .write(true)
                .truncate(true)
                .open(&target)
                .and_then(|mut file| file.write_all(text.as_bytes()))
                .map_err(|e| failure(&e));
        }
        Ok(m) => {
            // Renaming needs only the folder's permission: ask the system
            // whether the file itself may be written, as `>` would.
            fs::OpenOptions::new()
                .write(true)
                .open(&target)
                .map_err(|e| failure(&e))?;
            Some(m.permissions())
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => None,
        Err(e) => return Err(failure(&e)),
    };
    let Some(name) = target.file_name() else {
        // `..` or the root: a folder.
        return Err(Failure::NotAFile);
    };
    let number = TEMPORARY.fetch_add(1, Ordering::Relaxed);
    let name = name.to_string_lossy();
    // A long name would make the temporary one too long for the system.
    let temporary = target.with_file_name(if name.len() > 200 {
        format!(".sw-{}-{number}.tmp", std::process::id())
    } else {
        format!(".{name}.{}-{number}.tmp", std::process::id())
    });
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    if existing.is_some() {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options.open(&temporary).map_err(|e| failure(&e))?;
    let written = (|| {
        if let Some(permissions) = existing {
            file.set_permissions(permissions)?;
        }
        file.write_all(text.as_bytes())?;
        file.sync_all()?;
        fs::rename(&temporary, &target)
    })();
    written.map_err(|e| {
        let _ = fs::remove_file(&temporary);
        failure(&e)
    })
}

/// Where a write to `path` goes: the file a link points at, or `path`
/// itself. A link to a file that doesn't exist yet resolves to that file's
/// path, beside the link, so the write creates it and the link survives.
fn resolve_link(path: &Path) -> PathBuf {
    match fs::symlink_metadata(path) {
        Ok(m) if m.file_type().is_symlink() => {
            fs::canonicalize(path).unwrap_or_else(|_| match fs::read_link(path) {
                Ok(to) => path.parent().unwrap_or(Path::new(".")).join(to),
                Err(_) => path.to_path_buf(),
            })
        }
        _ => path.to_path_buf(),
    }
}

/// `Files.list`: the folder's entries, sorted by name. A name that isn't
/// UTF-8 is given with each bad sequence replaced by U+FFFD; a link is
/// listed as what it points at, or `Other` if that is missing.
pub fn list(path: &Path) -> Result<Vec<(String, Kind)>, Failure> {
    let mut entries = Vec::new();
    for entry in fs::read_dir(path).map_err(|e| failure(&e))? {
        let entry = entry.map_err(|e| failure(&e))?;
        let kind = fs::metadata(entry.path()).map_or(Kind::Other, |m| kind_of(&m));
        entries.push((entry.file_name().to_string_lossy().into_owned(), kind));
    }
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(entries)
}

/// `Files.info`: what is at the path, and its size in bytes (0 for a
/// folder, whose size on the host means nothing portable).
pub fn info(path: &Path) -> Result<(Kind, u64), Failure> {
    let metadata = fs::metadata(path).map_err(|e| failure(&e))?;
    let kind = kind_of(&metadata);
    let size = if kind == Kind::Folder {
        0
    } else {
        metadata.len()
    };
    Ok((kind, size))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A fresh, empty folder under the system's temporary folder.
    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "stitchwort-files-{name}-{}-{}",
            std::process::id(),
            TEMPORARY.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn host_files_each_operation_and_error() {
        let dir = scratch("ops");
        let file = dir.join("a.txt");
        assert_eq!(read(&file), Err(Failure::NotFound));
        assert_eq!(info(&file), Err(Failure::NotFound));
        assert_eq!(list(&file), Err(Failure::NotFound));
        assert_eq!(
            write(&dir.join("missing/a.txt"), "x"),
            Err(Failure::NotFound)
        );
        write(&file, "héllo").unwrap();
        assert_eq!(read(&file).as_deref(), Ok("héllo"));
        assert_eq!(info(&file), Ok((Kind::File, 6)));
        assert_eq!(info(&dir), Ok((Kind::Folder, 0)));
        // A folder where a file is wanted, and a file where a folder is.
        assert_eq!(read(&dir), Err(Failure::NotAFile));
        assert_eq!(write(&dir, "x"), Err(Failure::NotAFile));
        assert_eq!(list(&file), Err(Failure::NotAFolder));
        assert_eq!(read(&file.join("b")), Err(Failure::NotAFolder));
        assert_eq!(write(&file.join("b"), "x"), Err(Failure::NotAFolder));
        fs::write(dir.join("bad.txt"), [0x66, 0xff, 0x6f]).unwrap();
        assert_eq!(read(&dir.join("bad.txt")), Err(Failure::NotText));
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn host_files_listing_is_sorted_and_leaves_no_temporary() {
        let dir = scratch("list");
        for name in ["b", "a", "Z", "é", "c.txt"] {
            write(&dir.join(name), name).unwrap();
        }
        fs::create_dir(dir.join("d")).unwrap();
        write(&dir.join("b"), "again").unwrap();
        let names: Vec<_> = list(&dir).unwrap();
        assert_eq!(
            names,
            [
                ("Z".to_string(), Kind::File),
                ("a".to_string(), Kind::File),
                ("b".to_string(), Kind::File),
                ("c.txt".to_string(), Kind::File),
                ("d".to_string(), Kind::Folder),
                ("é".to_string(), Kind::File),
            ]
        );
        assert_eq!(read(&dir.join("b")).as_deref(), Ok("again"));
        fs::remove_dir_all(&dir).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn host_files_not_permitted_and_permissions_kept() {
        use std::os::unix::fs::PermissionsExt;
        let dir = scratch("perm");
        let file = dir.join("secret.txt");
        write(&file, "x").unwrap();
        fs::set_permissions(&file, fs::Permissions::from_mode(0o640)).unwrap();
        write(&file, "y").unwrap();
        let mode = fs::metadata(&file).unwrap().permissions().mode() & 0o777;
        assert_eq!(mode, 0o640);
        // A file that may not be written isn't replaced, whatever its folder
        // allows.
        fs::set_permissions(&file, fs::Permissions::from_mode(0o444)).unwrap();
        if fs::OpenOptions::new().write(true).open(&file).is_err() {
            assert_eq!(write(&file, "z"), Err(Failure::NotPermitted));
            assert_eq!(read(&file).as_deref(), Ok("y"));
        }
        // Running as root, nothing is refused: there's nothing to test.
        fs::set_permissions(&file, fs::Permissions::from_mode(0o000)).unwrap();
        if fs::read(&file).is_err() {
            assert_eq!(read(&file), Err(Failure::NotPermitted));
            let locked = dir.join("locked");
            fs::create_dir(&locked).unwrap();
            fs::set_permissions(&locked, fs::Permissions::from_mode(0o500)).unwrap();
            assert_eq!(write(&locked.join("a"), "x"), Err(Failure::NotPermitted));
            fs::set_permissions(&locked, fs::Permissions::from_mode(0o700)).unwrap();
        }
        fs::set_permissions(&file, fs::Permissions::from_mode(0o600)).unwrap();
        fs::remove_dir_all(&dir).unwrap();
    }

    /// A pipe is written in place, not replaced; a link to a missing file
    /// creates the file and stays a link.
    #[cfg(unix)]
    #[test]
    fn host_files_pipes_and_dangling_links_survive_a_write() {
        let dir = scratch("special");
        let pipe = dir.join("pipe");
        assert!(
            std::process::Command::new("mkfifo")
                .arg(&pipe)
                .status()
                .unwrap()
                .success()
        );
        let reader = {
            let pipe = pipe.clone();
            std::thread::spawn(move || fs::read_to_string(pipe).unwrap())
        };
        write(&pipe, "through").unwrap();
        assert_eq!(reader.join().unwrap(), "through");
        assert!(!fs::symlink_metadata(&pipe).unwrap().is_file());
        let link = dir.join("link");
        std::os::unix::fs::symlink("target.txt", &link).unwrap();
        write(&link, "made").unwrap();
        assert!(
            fs::symlink_metadata(&link)
                .unwrap()
                .file_type()
                .is_symlink()
        );
        assert_eq!(read(&dir.join("target.txt")).as_deref(), Ok("made"));
        fs::remove_dir_all(&dir).unwrap();
    }

    /// A private file stays private across a write, and a name too long to
    /// lengthen still writes (through a short temporary name).
    #[cfg(unix)]
    #[test]
    fn host_files_private_and_long_names() {
        use std::os::unix::fs::PermissionsExt;
        let dir = scratch("private");
        let file = dir.join("token");
        write(&file, "old").unwrap();
        fs::set_permissions(&file, fs::Permissions::from_mode(0o600)).unwrap();
        write(&file, "new").unwrap();
        assert_eq!(
            fs::metadata(&file).unwrap().permissions().mode() & 0o777,
            0o600
        );
        let long = dir.join("n".repeat(250));
        write(&long, "long").unwrap();
        assert_eq!(read(&long).as_deref(), Ok("long"));
        fs::remove_dir_all(&dir).unwrap();
    }

    /// A write that fails partway leaves the target as it was: here the
    /// temporary file can't be made, as a folder already has its name.
    #[test]
    fn host_files_failed_write_leaves_the_target_whole() {
        let dir = scratch("atomic");
        let file = dir.join("a.txt");
        write(&file, "old").unwrap();
        let next = TEMPORARY.load(Ordering::Relaxed);
        let blocker = dir.join(format!(".a.txt.{}-{next}.tmp", std::process::id()));
        fs::create_dir(&blocker).unwrap();
        assert!(write(&file, "new").is_err());
        assert_eq!(read(&file).as_deref(), Ok("old"));
        fs::remove_dir_all(&dir).unwrap();
    }
}
