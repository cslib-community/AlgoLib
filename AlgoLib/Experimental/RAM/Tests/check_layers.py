"""Run architecture, algorithm-role, ownership, conformance and navigation checks.

Run from any directory with Python 3.10+. Lean separately checks semantics and
costs. See docs/ARCHITECTURE-POLICY.md for the scope of these regression rules.
"""
import os
from pathlib import Path
import subprocess
import sys

from algorithm_roles import validate_algorithms
from architecture import load_model, validate_architecture


def main():
    root = Path(__file__).resolve().parents[1]
    model = load_model(root)
    validate_architecture(model)
    algorithms = validate_algorithms(root, model.records, model.edges)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    checks = (
        ("test_lean_imports.py",),
        ("test_architecture.py",),
        ("test_algorithm_roles.py",),
        ("check_reviewers.py", "--check"),
        ("test_reviewers.py",),
        ("Conformance/generate.py", "--check"),
        ("Conformance/generate_signed.py", "--check"),
        ("generate_navigation.py", "--check"),
        ("check_navigation.py",),
        ("test_navigation.py",),
    )
    for script, *arguments in checks:
        subprocess.run([sys.executable, str(root / "Tests" / script), *arguments], check=True, env=env)
    print(f"Checked {len(model.records)} documented modules and "
          f"{len(algorithms['algorithms'])} maintained algorithms: architecture and ownership OK")


if __name__ == "__main__":
    try:
        main()
    except ValueError as error:
        sys.exit(f"Architecture: {error}")
