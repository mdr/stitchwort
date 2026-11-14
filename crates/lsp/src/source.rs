//! Where the server reads files and projects: the disk natively ([`Disk`]),
//! the page's memory in the playground ([`Memory`]). Every read of a file
//! the editor hasn't opened goes through a [`Source`].

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::{Arc, RwLock};

use stitchwort_driver::project::{
    Config, DiskFiles, Entry, EntryKind, Files, find_project, parse_config, project_sources,
};
use stitchwort_elab::project::IncludeFiles;
use stitchwort_syntax::{Diagnostic, SourceMap};

/// A project as the checker keeps it: what [`Source::project`] reads.
pub struct ProjectFiles {
    /// The text of `stitchwort.yaml`, which keys the check cache.
    pub config: Option<String>,
    /// The source folders, normalised as `Config::sources` has them.
    pub sources: Vec<String>,
    /// Every source file: (path within the project, text).
    pub files: BTreeMap<String, String>,
}

/// The files and projects the server can read. Shared with the proof
/// searches' threads, so `Send` and `Sync`; what it hands out (`files`)
/// is made on the thread that uses it.
pub trait Source: Send + Sync {
    /// The text of the file at `path`, if it can be read.
    fn read(&self, path: &Path) -> Option<String>;

    /// The project folder that holds `folder`: it or the nearest folder
    /// above it that is a project's.
    fn find_project(&self, folder: &Path) -> Option<PathBuf>;

    /// The project in folder `dir`, or `None` (with the reason logged) if
    /// it can't be read.
    fn project(&self, dir: &Path) -> Option<ProjectFiles>;

    /// The source folders of the project in `dir`, reading only its
    /// configuration, or `None` (with the reason logged) if that can't be
    /// read.
    fn sources(&self, dir: &Path) -> Option<Vec<String>>;

    /// The files in folder `dir`, by path within it: for `include`, and for
    /// a search to read a project again.
    fn files(&self, dir: &Path) -> Box<dyn Files>;

    /// The check cache of the project in `dir`, made if it isn't there.
    fn project_cache(&self, dir: &Path) -> Option<PathBuf>;

    /// The check cache in folder `dir`, for a file on its own: only if it
    /// is there already.
    fn file_cache(&self, dir: &Path) -> Option<PathBuf>;
}

/// Whether `relative` (a path within a project) is a `.sw` file in one of
/// its source folders. The one rule for what a project's sources are.
pub fn sources_hold(sources: &[String], relative: &str) -> bool {
    relative.ends_with(".sw")
        && sources.iter().any(|s| {
            let s = s.trim_end_matches('/');
            s.is_empty() || relative.strip_prefix(s).is_some_and(|r| r.starts_with('/'))
        })
}

/// The disk, as `stitchwort lsp` reads it.
pub struct Disk;

impl Source for Disk {
    fn read(&self, path: &Path) -> Option<String> {
        std::fs::read_to_string(path).ok()
    }

    fn find_project(&self, folder: &Path) -> Option<PathBuf> {
        find_project(folder)
    }

    fn project(&self, dir: &Path) -> Option<ProjectFiles> {
        let name = dir
            .file_name()
            .map_or("project".to_string(), |n| n.to_string_lossy().into_owned());
        let files = DiskFiles {
            root: dir.to_path_buf(),
        };
        let mut sources = SourceMap::new();
        let found = match project_sources(&files, &name, &mut sources) {
            Ok(found) => found,
            Err(errors) => {
                for e in errors {
                    eprintln!("stitchwort lsp: {}: {}", dir.display(), e.message);
                }
                return None;
            }
        };
        let config_text = std::fs::read_to_string(dir.join("stitchwort.yaml")).ok();
        let config = config_text.as_deref().and_then(|text| {
            let id = sources.add("stitchwort.yaml", text);
            parse_config(id, "stitchwort.yaml", text).ok()
        })?;
        Some(ProjectFiles {
            config: config_text,
            sources: config.sources,
            files: found.into_iter().collect(),
        })
    }

    fn sources(&self, dir: &Path) -> Option<Vec<String>> {
        let text = std::fs::read_to_string(dir.join("stitchwort.yaml")).ok()?;
        let mut sources = SourceMap::new();
        let id = sources.add("stitchwort.yaml", &text);
        match parse_config(id, "stitchwort.yaml", &text) {
            Ok(config) => Some(config.sources),
            Err(e) => {
                eprintln!("stitchwort lsp: {}: {}", dir.display(), e.message);
                None
            }
        }
    }

    fn files(&self, dir: &Path) -> Box<dyn Files> {
        Box::new(DiskFiles {
            root: dir.to_path_buf(),
        })
    }

    /// `.stitchwort/cache` in the project folder, as the command line uses.
    fn project_cache(&self, dir: &Path) -> Option<PathBuf> {
        let stitchwort = dir.join(".stitchwort");
        if !stitchwort.exists() && std::fs::create_dir_all(&stitchwort).is_ok() {
            let _ = std::fs::write(stitchwort.join(".gitignore"), "*\n");
        }
        Some(stitchwort.join("cache"))
    }

    fn file_cache(&self, dir: &Path) -> Option<PathBuf> {
        Some(dir.join(".stitchwort").join("cache")).filter(|dir| dir.is_dir())
    }
}

/// Projects held in memory: the playground's (the AoC project, the
/// roguelike), at made-up folders such as `/playground/aoc`. Their
/// configuration comes parsed. With no cache folder, the server keeps an
/// in-memory check cache for their namespaces (`LayeredStore`).
#[derive(Default)]
pub struct Memory {
    projects: RwLock<Vec<MemoryProject>>,
    /// A check cache folder shared by every project and file, if any: for
    /// tests, which replay the library from a cache of their own.
    cache: Option<PathBuf>,
}

/// One project of a [`Memory`].
#[derive(Clone)]
pub struct MemoryProject {
    /// Its folder (`/playground/aoc`).
    pub root: PathBuf,
    /// The source folders (`["src"]`), as `stitchwort.yaml` would list them.
    pub sources: Vec<String>,
    /// Every file, by path within the project: the sources and the files
    /// `include` reads.
    pub files: Arc<BTreeMap<String, String>>,
}

impl Memory {
    /// A source whose projects and files check through the cache in
    /// `cache`, instead of having none.
    pub fn with_cache(cache: PathBuf) -> Self {
        Memory {
            projects: RwLock::default(),
            cache: Some(cache),
        }
    }

    /// Adds a project, or replaces the one at the same folder.
    pub fn add(&self, project: MemoryProject) {
        let mut projects = self.projects.write().unwrap_or_else(|e| e.into_inner());
        projects.retain(|p| p.root != project.root);
        projects.push(project);
    }

    /// Gives the file `path` of the project in `root` this text, when the
    /// page has changed it behind the server's back (a rename that edited a
    /// file the editor hasn't opened). No such project or file: nothing.
    pub fn set_file(&self, root: &Path, path: &str, text: String) {
        let mut projects = self.projects.write().unwrap_or_else(|e| e.into_inner());
        if let Some(project) = projects.iter_mut().find(|p| p.root == root) {
            let mut files = (*project.files).clone();
            if let Some(old) = files.get_mut(path) {
                *old = text;
                project.files = Arc::new(files);
            }
        }
    }

    /// The project holding `path`, and `path` within it.
    fn locate(&self, path: &Path) -> Option<(MemoryProject, String)> {
        let projects = self.projects.read().unwrap_or_else(|e| e.into_inner());
        projects.iter().find_map(|p| {
            let rest = path.strip_prefix(&p.root).ok()?;
            let parts: Option<Vec<&str>> = rest.iter().map(|c| c.to_str()).collect();
            Some((p.clone(), parts?.join("/")))
        })
    }
}

impl MemoryProject {
    fn config(&self) -> Config {
        Config {
            sources: self.sources.clone(),
            allowed_axioms: None,
            open_goals: Default::default(),
        }
    }

    /// The YAML the project would have on disk: what keys a check cache.
    fn config_text(&self) -> String {
        format!("sources: [{}]", self.sources.join(", "))
    }
}

impl Source for Memory {
    fn read(&self, path: &Path) -> Option<String> {
        let (project, relative) = self.locate(path)?;
        project.files.get(&relative).cloned()
    }

    fn find_project(&self, folder: &Path) -> Option<PathBuf> {
        self.locate(folder).map(|(p, _)| p.root)
    }

    fn project(&self, dir: &Path) -> Option<ProjectFiles> {
        let (project, relative) = self.locate(dir)?;
        if !relative.is_empty() {
            return None;
        }
        let files = (project.files.iter())
            .filter(|(path, _)| sources_hold(&project.sources, path))
            .map(|(path, text)| (path.clone(), text.clone()))
            .collect();
        Some(ProjectFiles {
            config: Some(project.config_text()),
            sources: project.sources.clone(),
            files,
        })
    }

    fn sources(&self, dir: &Path) -> Option<Vec<String>> {
        let (project, relative) = self.locate(dir)?;
        relative.is_empty().then_some(project.sources)
    }

    fn files(&self, dir: &Path) -> Box<dyn Files> {
        match self.locate(dir) {
            Some((project, relative)) if relative.is_empty() => Box::new(MemoryFiles {
                config: project.config(),
                config_text: project.config_text(),
                files: project.files,
            }),
            // A folder within a project, or none: files on their own here
            // are only ever the editor's, so `include` finds nothing.
            _ => Box::new(MemoryFiles {
                config: Config {
                    sources: Vec::new(),
                    allowed_axioms: None,
                    open_goals: Default::default(),
                },
                config_text: String::new(),
                files: Arc::default(),
            }),
        }
    }

    fn project_cache(&self, _: &Path) -> Option<PathBuf> {
        self.cache.clone()
    }

    fn file_cache(&self, _: &Path) -> Option<PathBuf> {
        self.cache.clone()
    }
}

/// A [`MemoryProject`]'s files, with its configuration parsed already.
#[derive(Clone)]
struct MemoryFiles {
    config: Config,
    config_text: String,
    files: Arc<BTreeMap<String, String>>,
}

impl Files for MemoryFiles {
    fn entries(&self, dir: &str) -> std::io::Result<Vec<Entry>> {
        let prefix = if dir.is_empty() {
            String::new()
        } else {
            format!("{dir}/")
        };
        let mut found: BTreeMap<&str, EntryKind> = BTreeMap::new();
        for path in self.files.keys() {
            if let Some(rest) = path.strip_prefix(&prefix) {
                match rest.split_once('/') {
                    Some((name, _)) => found.insert(name, EntryKind::Dir),
                    None => found.insert(rest, EntryKind::File),
                };
            }
        }
        if found.is_empty() && !dir.is_empty() {
            return Err(std::io::ErrorKind::NotFound.into());
        }
        Ok(found
            .into_iter()
            .map(|(name, kind)| Entry {
                name: name.to_string(),
                kind,
            })
            .collect())
    }

    fn read(&self, path: &str) -> std::io::Result<String> {
        if path == "stitchwort.yaml" {
            return Ok(self.config_text.clone());
        }
        self.files
            .get(path)
            .cloned()
            .ok_or_else(|| std::io::ErrorKind::NotFound.into())
    }

    fn include_files(&self) -> Option<Rc<dyn IncludeFiles>> {
        Some(Rc::new(self.clone()))
    }

    fn config(
        &self,
        text: &str,
        display: &str,
        sources: &mut SourceMap,
    ) -> Result<Config, Diagnostic> {
        sources.add(display, text);
        Ok(self.config.clone())
    }
}

impl IncludeFiles for MemoryFiles {
    fn read(&self, path: &str) -> std::io::Result<String> {
        Files::read(self, path)
    }
}
