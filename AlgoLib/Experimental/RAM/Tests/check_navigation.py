"""Check canonical module homes, guide links, and documented RAM imports.

This catches navigation regressions after module moves. It does not replace Lean
checking or claim that arbitrary code snippets in prose are executable programs.
"""
from pathlib import Path
import json
import re
from urllib.parse import unquote

root = Path(__file__).resolve().parents[1]
repo = root.parents[2]


def check_document(path: Path, *, ram_only: bool = False):
    """Check local links and RAM imports, optionally limiting links to RAM targets."""
    text = path.read_text()
    for target in re.findall(r"\]\(([^\s)]+)\)", text):
        target = target.split("#")[0]
        if not target or ":" in target or target.startswith("/"):
            continue
        destination = (path.parent / unquote(target)).resolve()
        if ram_only and not (destination.is_relative_to(root) or
                             destination == root.with_suffix(".lean")):
            continue
        assert destination.exists(), (path, "broken link", target)
    for module in re.findall(r"^import (AlgoLib\.Experimental\.RAM\S*)", text, re.M):
        assert (repo / (module.replace(".", "/") + ".lean")).is_file(), (
            path, "nonexistent documented import", module)


allowed = {"Language", "Verification", "Library", "Implementations", "Compiler",
           "Machine", "Examples", "Historical", "Research", "Tests", "docs"}
assert {p.name for p in root.iterdir() if p.is_dir()} <= allowed
for layer in allowed - {"docs"}:
    assert (root / layer / "README.md").is_file(), (layer, "missing entry page")
for old, new in json.loads((root / "docs/module-migration.json").read_text()).items():
    assert not (root / old).exists(), (old, "retired module still exists")
    assert (root / new).is_file(), (new, "missing migrated module")
for path in root.rglob("*.md"):
    check_document(path)
# Repository entry pages introduce RAM without making their unrelated links part
# of this checker. Resolve targets relative to each page before selecting RAM links.
for relative in ("README.md", ".github/CONTRIBUTING.md", ".github/PULL_REQUEST_TEMPLATE.md", "vendor/README.md"):
    check_document(repo / relative, ram_only=True)
for example in (root / "Examples").iterdir():
    if example.is_dir():
        page = example / "README.md"
        assert page.is_file(), (example, "missing example entry page")
        for module in example.glob("*.lean"):
            assert f"]({module.name})" in page.read_text(), (
                module, "example module not linked from entry page")
print("Navigation: canonical modules, repository/layer/example entry pages, links and imports OK")
