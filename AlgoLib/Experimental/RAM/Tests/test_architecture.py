"""Try to cross architectural boundaries in isolated copies of the current tree."""
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from architecture import load_model, validate_architecture

ROOT = Path(__file__).resolve().parents[1]


class ArchitectureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="ram-architecture-")
        cls.repo = Path(cls.temp.name) / "repo"
        # Include ordinary AlgoLib modules: boundaries must survive external bridges.
        shutil.copytree(ROOT.parents[1], cls.repo / "AlgoLib",
                        ignore=shutil.ignore_patterns("__pycache__"))
        shutil.copy2(ROOT.parents[2] / "AlgoLib.lean", cls.repo / "AlgoLib.lean")
        cls.root = cls.repo / "AlgoLib/Experimental/RAM"
        cls.metadata = cls.root / "docs/modules.json"
        cls.original = cls.metadata.read_text()

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def tearDown(self):
        self.metadata.write_text(self.original)

    def change(self, path, text):
        original = path.read_text() if path.exists() else None
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

        def restore():
            if original is None:
                path.unlink()
            else:
                path.write_text(original)
        self.addCleanup(restore)

    def module(self, relative, source, *, register=True):
        self.change(self.root / relative, source + "\n/-! # Architecture regression fixture -/\n")
        if register:
            records = json.loads(self.metadata.read_text())
            records["modules"][relative] = {
                "entrypoint": False, "layer": relative.split("/")[0], "status": "internal"}
            self.metadata.write_text(json.dumps(records))

    def check(self):
        validate_architecture(load_model(self.root))

    def test_baseline(self):
        self.check()

    def test_new_logical_module_inherits_policy(self):
        self.module("Language/Fresh.lean", "  import AlgoLib.Experimental.RAM.Compiler")
        with self.assertRaisesRegex(ValueError, "Fresh.lean: forbidden dependency"):
            self.check()

    def test_new_library_module_inherits_policy(self):
        self.module("Library/Fresh.lean", "import AlgoLib.Experimental.RAM.Machine")
        with self.assertRaisesRegex(ValueError, "Fresh.lean: forbidden dependency"):
            self.check()

    def test_import_comments_cannot_hide_edge(self):
        self.module("Language/Fresh.lean", "import /- outer /- inner -/ -/\n AlgoLib.Experimental.RAM.Compiler")
        with self.assertRaisesRegex(ValueError, "Fresh.lean: forbidden dependency"):
            self.check()

    def test_local_bridge_cannot_hide_backend(self):
        self.change(self.repo / "AlgoLib/Bridge.lean", "import AlgoLib.Experimental.RAM.Compiler\n")
        self.module("Language/Fresh.lean", "import AlgoLib.Bridge")
        with self.assertRaisesRegex(ValueError, "Fresh.lean: forbidden dependency on Compiler.lean"):
            self.check()

    def test_root_ram_umbrella_cannot_hide_backend(self):
        self.module("Language/Fresh.lean", "import AlgoLib.Experimental.RAM")
        with self.assertRaisesRegex(ValueError, "Fresh.lean: forbidden dependency"):
            self.check()

    def test_example_entrypoint_is_not_a_core_dependency(self):
        self.module("Compiler/Fresh.lean", "import AlgoLib.Experimental.RAM.Examples")
        with self.assertRaisesRegex(ValueError, "Fresh.lean: forbidden dependency on Examples.lean"):
            self.check()

    def test_new_valid_module_needs_no_allowlist(self):
        self.module("Language/Fresh.lean", "import AlgoLib.Experimental.RAM.Language.Program")
        self.check()

    def test_documentation_import_is_not_a_dependency(self):
        self.module("Language/Fresh.lean", "/-!\nimport AlgoLib.Experimental.RAM.Compiler\n-/\ndef x := 0")
        self.check()

    def test_missing_registration(self):
        self.module("Language/Fresh.lean", "", register=False)
        with self.assertRaisesRegex(ValueError, "module metadata mismatch"):
            self.check()

    def test_missing_import_target(self):
        self.module("Language/Fresh.lean", "import AlgoLib.Experimental.RAM.Language.DoesNotExist")
        with self.assertRaisesRegex(ValueError, "missing RAM module"):
            self.check()

    def test_cyclic_import(self):
        self.module("Language/Fresh.lean", "import AlgoLib.Experimental.RAM.Language.Fresh")
        with self.assertRaisesRegex(ValueError, "cyclic local imports"):
            self.check()

    def test_policy_must_cover_all_layers(self):
        path = self.root / "docs/architecture.json"
        policy = json.loads(path.read_text())
        del policy["allowed_imports"]["Library"]
        self.change(path, json.dumps(policy))
        with self.assertRaisesRegex(ValueError, "must cover every layer"):
            self.check()

    def test_logical_purity_remains_transitive(self):
        path = self.root / "docs/architecture.json"
        policy = json.loads(path.read_text())
        # Broadening a direct-edge rule does not remove the logical-layer fence.
        policy["allowed_imports"]["Language"].append("Compiler")
        self.change(path, json.dumps(policy))
        self.module("Language/Fresh.lean", "import AlgoLib.Experimental.RAM.Compiler")
        with self.assertRaisesRegex(ValueError, "logical layer depends on backend"):
            self.check()


if __name__ == "__main__":
    unittest.main()
