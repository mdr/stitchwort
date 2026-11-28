#!/usr/bin/env python3
"""Tests for web/bundle-projects.sh. Run: python3 dev/bundle-projects_test.py

Runs the bundler into a temporary folder and checks its manifests against the
folders it wrote, with no WebAssembly build and no browser.
"""
import json
import os
import shutil
import subprocess
import tempfile
import unittest

here = os.path.dirname(os.path.abspath(__file__))
root = os.path.dirname(here)
script = os.path.join(root, "web", "bundle-projects.sh")

# The project folders the script bundles, and where their sources live.
PROJECTS = {"aoc": "aoc", "rogue": "games/rogue", "sf": "sf", "book": "book"}


def files_under(folder, suffix):
    """The relative paths of the files under FOLDER whose names end in SUFFIX, sorted."""
    found = []
    for dirpath, _, names in os.walk(folder):
        for name in names:
            if name.endswith(suffix):
                path = os.path.relpath(os.path.join(dirpath, name), folder)
                found.append(path.replace(os.sep, "/"))
    return sorted(found)


class T(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = tempfile.mkdtemp(prefix="bundle-projects-")
        cls.addClassCleanup(shutil.rmtree, cls.out, ignore_errors=True)
        subprocess.run(["bash", script, root, cls.out], cwd=root, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        cls.projects_dir = os.path.join(cls.out, "projects")
        cls.manifests = {}
        for name in os.listdir(cls.projects_dir):
            with open(os.path.join(cls.projects_dir, name, "manifest.json")) as f:
                cls.manifests[name] = json.load(f)
        # sf/ and book/ are optional: the script skips a folder without a config.
        cls.expected = {name for name, folder in PROJECTS.items()
                        if os.path.isfile(os.path.join(root, folder, "stitchwort.yaml"))}

    def folder(self, name):
        return os.path.join(self.projects_dir, name)

    def test_writes_the_projects_the_repo_has(self):
        self.assertEqual(set(self.manifests), self.expected)
        self.assertIn("aoc", self.manifests)
        self.assertIn("rogue", self.manifests)
        for name, manifest in self.manifests.items():
            self.assertEqual(manifest["name"], name)
            title = manifest.get("title")
            self.assertIsInstance(title, str)
            self.assertTrue(title.strip(), f"{name}: the manifest has no title")

    def test_files_are_non_empty_sorted_unique_and_present(self):
        for name, manifest in self.manifests.items():
            files = manifest["files"]
            self.assertIsInstance(files, list, name)
            self.assertTrue(files, f"{name}: the manifest lists no files")
            self.assertEqual(files, sorted(set(files)), f"{name}: files are not sorted and unique")
            for path in files:
                self.assertTrue(path.endswith(".sw"), f"{name}: {path} is not a .sw file")
                self.assertTrue(os.path.isfile(os.path.join(self.folder(name), path)),
                                f"{name}: {path} is listed but was not copied")

    def test_every_sw_file_in_a_project_is_listed(self):
        for name, manifest in self.manifests.items():
            self.assertEqual(files_under(self.folder(name), ".sw"), manifest["files"],
                             f"{name}: the manifest's files differ from the .sw files copied")

    def test_data_lists_every_text_file(self):
        for name, manifest in self.manifests.items():
            data = manifest["data"]
            self.assertIsInstance(data, list, name)
            self.assertEqual(data, sorted(set(data)), f"{name}: data is not sorted and unique")
            for path in data:
                self.assertTrue(path.endswith(".txt"), f"{name}: {path} is not a .txt file")
                self.assertTrue(os.path.isfile(os.path.join(self.folder(name), path)),
                                f"{name}: {path} is listed as data but was not copied")
            self.assertEqual(files_under(self.folder(name), ".txt"), data,
                             f"{name}: the manifest's data differs from the .txt files copied")
        self.assertTrue(self.manifests["aoc"]["data"], "aoc: the puzzle inputs and examples are missing")

    def test_every_entry_names_files_that_exist(self):
        for name, manifest in self.manifests.items():
            entries = manifest["days"]
            self.assertTrue(entries, f"{name}: the manifest has no entries")
            files = set(manifest["files"])
            data = set(manifest["data"])
            for entry in entries:
                self.assertTrue(entry.get("title"), f"{name}: an entry has no title")
                opened = entry.get("open")
                self.assertTrue(opened, f"{name}: {entry['title']} names no file to open")
                self.assertIn(opened, files, f"{name}: {entry['title']} opens {opened}, which is not listed")
                self.assertTrue(os.path.isfile(os.path.join(self.folder(name), opened)),
                                f"{name}: {entry['title']} opens {opened}, which was not copied")
                if "main" in entry:
                    self.assertEqual(entry["main"], entry["namespaces"][0] + ".main")
                for item in entry.get("inputs", []):
                    self.assertIn(item["path"], data,
                                  f"{name}: {entry['title']} names input {item['path']}, which is not listed")
                    self.assertTrue(os.path.isfile(os.path.join(self.folder(name), item["path"])),
                                    f"{name}: {entry['title']} names input {item['path']}, which was not copied")

    def test_chapter_projects_are_marked_not_to_run(self):
        for name in ("sf", "book"):
            if name not in self.manifests:
                continue
            manifest = self.manifests[name]
            self.assertIs(manifest.get("noRun"), True)
            self.assertIn(manifest.get("openGoals"), ("warn", "fail"))
            for entry in manifest["days"]:
                self.assertNotIn("main", entry)
        for name in ("aoc", "rogue"):
            manifest = self.manifests[name]
            self.assertNotIn("noRun", manifest)
            self.assertNotIn("openGoals", manifest)
            for entry in manifest["days"]:
                self.assertIn("main", entry)


if __name__ == "__main__":
    unittest.main()
