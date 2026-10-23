"""Exercise navigation metadata rejection without touching the working tree."""
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    with tempfile.TemporaryDirectory(prefix="ram-navigation-") as temp:
        repo = Path(temp) / "repo"
        copy = repo / "AlgoLib/Experimental/RAM"
        shutil.copytree(ROOT, copy, ignore=shutil.ignore_patterns("__pycache__"))
        shutil.copy2(ROOT.with_suffix(".lean"), copy.with_suffix(".lean"))
        for relative in ("README.md", ".github/CONTRIBUTING.md", ".github/CODEOWNERS",
                         ".github/PULL_REQUEST_TEMPLATE.md", "vendor/README.md"):
            target = repo / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT.parents[2] / relative, target)
        command = [sys.executable, str(copy / "Tests/generate_navigation.py"), "--check"]

        def check(success, diagnostic="", *, checker=command):
            result = subprocess.run(checker, capture_output=True, text=True)
            assert (result.returncode == 0) == success, result.stdout + result.stderr
            if diagnostic:
                assert diagnostic in result.stderr, result.stderr

        def rejects(path, change, diagnostic, *, checker=command):
            original = path.read_text()
            try:
                path.write_text(change(original))
                check(False, diagnostic, checker=checker)
            finally:
                path.write_text(original)

        check(True)
        def missing(text):
            data = json.loads(text)
            data["modules"].pop("Language.lean")
            return json.dumps(data)
        rejects(copy / "docs/modules.json", missing, "module metadata mismatch")
        def wrong_layer(text):
            data = json.loads(text)
            data["modules"]["Language.lean"]["layer"] = "Historical"
            return json.dumps(data)
        rejects(copy / "docs/modules.json", wrong_layer, "metadata does not match physical layer")
        def wrong_export(text):
            data = json.loads(text)
            data[0]["original"] += "Typo"
            return json.dumps(data)
        rejects(copy / "docs/public-exports.json", wrong_export, "public export metadata disagrees with source")
        rejects(copy / "Language/README.md", lambda text: text.replace("Module index (generated)",
                "Obsolete index"), "stale generated navigation")
        check(True)

        navigation = [sys.executable, str(copy / "Tests/check_navigation.py")]
        check(True, checker=navigation)
        # Entry pages may reference unrelated files outside this isolated RAM tree.
        entry = repo / "README.md"
        original = entry.read_text()
        try:
            entry.write_text(original + "\n[Unrelated](unrelated-missing.md)\n"
                             "[External](https://example.invalid/AlgoLib/Experimental/RAM/missing.md)\n")
            check(True, checker=navigation)
            rejects(entry, lambda text: text +
                    "\n[RAM guide](AlgoLib/Experimental/RAM/docs/missing-entry-guide.md)\n",
                    "missing-entry-guide.md", checker=navigation)
        finally:
            entry.write_text(original)
        for relative in (".github/CONTRIBUTING.md", ".github/PULL_REQUEST_TEMPLATE.md", "vendor/README.md"):
            rejects(repo / relative, lambda text: text +
                    "\n[RAM guide](../AlgoLib/Experimental/RAM/docs/missing-entry-guide.md)\n",
                    "missing-entry-guide.md", checker=navigation)
        check(True, checker=navigation)
    print("Navigation rejection tests: missing metadata, wrong ownership/export, stale index, "
          "and broken repository RAM links rejected")


if __name__ == "__main__":
    main()
