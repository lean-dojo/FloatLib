"""Checks for declaration exports and source links during local edits."""

import contextlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location(
    "export_atlas", Path(__file__).with_name("export_atlas.py"))
atlas = importlib.util.module_from_spec(spec)
spec.loader.exec_module(atlas)


class ExportTests(unittest.TestCase):
    def test_modified_and_untracked_paths_keep_their_first_character(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def git(*args):
                subprocess.run(["git", "-C", directory, *args], check=True,
                               capture_output=True, text=True)
            git("init")
            git("config", "user.email", "site-test@example.invalid")
            git("config", "user.name", "Site test")
            (root / "FloatLib").mkdir()
            source = root / "FloatLib" / "Core.lean"
            source.write_text("def original := 1\n")
            git("add", ".")
            git("commit", "-m", "fixture")
            source.write_text("def renamed := 1\n")
            (root / "FloatLib" / "New File.lean").write_text("def added := 2\n")
            (root / "FloatLib.lean").write_text("import FloatLib.Core\n")
            with patch.object(atlas, "ROOT", root):
                self.assertEqual(atlas.dirty_files(), {
                    "FloatLib/Core.lean", "FloatLib/New File.lean", "FloatLib.lean",
                })
                git("mv", "FloatLib/Core.lean", "FloatLib/Renamed.lean")
                self.assertEqual(atlas.dirty_files(), {
                    "FloatLib/Renamed.lean", "FloatLib/New File.lean", "FloatLib.lean",
                })

    def test_uncommitted_source_path_has_no_github_url(self):
        self.assertEqual(atlas.node_url("revision", "FloatLib/New.lean", 1, 1,
                                       "def n := 1", {"FloatLib/New.lean"}, set()), "")

    def test_skip_lean_rejects_exports_with_outdated_declarations(self):
        phases = [{"id": "example", "nodes": [{"name": "FloatLib.example"}]}]
        with tempfile.TemporaryDirectory() as directory:
            raw = Path(directory) / "nodes.raw.json"
            raw.write_text(json.dumps({"nodes": [{"name": "FloatLib.removedExample"}]}))
            output = io.StringIO()
            with patch.object(atlas, "load_phases", return_value=phases), \
                    contextlib.redirect_stderr(output), self.assertRaises(SystemExit):
                atlas.build(raw, Path(directory) / "nodes.json")
            self.assertIn("without --skip-lean", output.getvalue())


if __name__ == "__main__":
    unittest.main()
