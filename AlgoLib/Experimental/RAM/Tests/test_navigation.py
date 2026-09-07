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
        copy = Path(temp) / "RAM"
        shutil.copytree(ROOT, copy, ignore=shutil.ignore_patterns("*.pdf", "*.pptx", "__pycache__"))
        command = [sys.executable, str(copy / "Tests/generate_navigation.py"), "--check"]

        def check(success, diagnostic=""):
            result = subprocess.run(command, capture_output=True, text=True)
            assert (result.returncode == 0) == success, result.stdout + result.stderr
            if diagnostic:
                assert diagnostic in result.stderr, result.stderr

        def rejects(relative, change, diagnostic):
            path = copy / relative
            original = path.read_text()
            try:
                path.write_text(change(original))
                check(False, diagnostic)
            finally:
                path.write_text(original)

        check(True)
        def missing(text):
            data = json.loads(text)
            data["modules"].pop("Language.lean")
            return json.dumps(data)
        rejects("docs/modules.json", missing, "module metadata mismatch")
        def wrong_layer(text):
            data = json.loads(text)
            data["modules"]["Language.lean"]["layer"] = "Historical"
            return json.dumps(data)
        rejects("docs/modules.json", wrong_layer, "metadata does not match physical layer")
        def wrong_export(text):
            data = json.loads(text)
            data[0]["original"] += "Typo"
            return json.dumps(data)
        rejects("docs/public-exports.json", wrong_export, "public export metadata disagrees with source")
        rejects("Language/README.md", lambda text: text.replace("Module index (generated)",
                "Obsolete index"), "stale generated navigation")
        check(True)
    print("Navigation rejection tests: missing metadata, wrong ownership/export, and stale index rejected")


if __name__ == "__main__":
    main()
