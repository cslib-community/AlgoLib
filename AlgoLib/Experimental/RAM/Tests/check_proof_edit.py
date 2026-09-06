"""Measure a proof-only edit and assert reuse of the generated API and RAM backend.

Builds dependencies, checks a successful edit and a deliberately failing proof edit,
then restores and rebuilds the original file even if either check fails.
Do not run concurrently with other builds or edits of SortingProofs.lean.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
BASE = "AlgoLib.Experimental.RAM.Prototype.Composition."
OUT = ROOT / ".lake/build/ram-proof-edit"
LAKE = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")


def artifact(module: str) -> Path:
    return ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")


def fingerprint(path: Path) -> dict:
    return {"mtime_ns": path.stat().st_mtime_ns,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def build(label: str, *, expect_success: bool = True) -> float:
    start = time.perf_counter()
    with (OUT / (label + ".log")).open("w") as log:
        result = subprocess.run([LAKE, "build", BASE + "SortingExecution"], cwd=ROOT,
                                stdout=log, stderr=subprocess.STDOUT, timeout=600)
    if (result.returncode == 0) != expect_success:
        raise RuntimeError(f"Unexpected build result for {label}: {result.returncode}")
    if not expect_success:
        diagnostic = (OUT / (label + ".log")).read_text()
        if "deliberate proof-edit regression" not in diagnostic:
            raise RuntimeError("Build failed for a reason other than the deliberate proof edit")
    return time.perf_counter() - start


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    build("prepare")
    proof = ROOT / (BASE.replace(".", "/") + "SortingProofs.lean")
    original = proof.read_bytes()
    watched = {name: artifact(BASE + name)
               for name in ("SortingProgram", "SortingSpec", "SortingBackend", "SortingProofs")}
    before = {name: fingerprint(path) for name, path in watched.items()}
    report = {"measurement": "proof-only source edit followed by executable rebuild",
              "before": before}
    try:
        marker = b"simp [Prefix]"
        if original.count(marker) != 1:
            raise RuntimeError("Expected a unique initialization proof to edit")
        proof.write_bytes(original.replace(marker, b"simpa [Prefix]", 1))
        report["seconds"] = build("edited-proof")
        after = {name: fingerprint(path) for name, path in watched.items()}
        report["after"] = after
        report["api_reused"] = before["SortingSpec"] == after["SortingSpec"]
        report["backend_reused"] = before["SortingBackend"] == after["SortingBackend"]
        report["proof_rechecked"] = before["SortingProofs"] != after["SortingProofs"]
        proof.write_bytes(original.replace(marker, b'fail "deliberate proof-edit regression"', 1))
        report["failing_edit_seconds"] = build("failing-proof", expect_success=False)
        report["failing_api_reused"] = before["SortingSpec"] == fingerprint(watched["SortingSpec"])
        report["failing_backend_reused"] = before["SortingBackend"] == fingerprint(watched["SortingBackend"])
        report["passed"] = all(report[key] for key in
                               ("api_reused", "backend_reused", "proof_rechecked",
                                "failing_api_reused", "failing_backend_reused"))
    finally:
        proof.write_bytes(original)
        report["restore_seconds"] = build("restored-proof")
        (OUT / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if not report["passed"]:
        raise SystemExit("Proof-edit reuse regression: inspect " + str(OUT / "report.json"))
    print(f"PASS: proof edit and executable rebuild {report['seconds']:.2f}s; "
          f"failing proof edit {report['failing_edit_seconds']:.2f}s; "
          "specification and backend artifacts unchanged in both cases")


if __name__ == "__main__":
    main()
