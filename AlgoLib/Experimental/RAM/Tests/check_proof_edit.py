"""Measure a proof-only edit and assert reuse of the generated API and RAM backend.

Builds dependencies, adds a harmless comment to the proof module, rebuilds the
executable, then restores and rebuilds the original file even if the check fails.
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


def build(label: str) -> float:
    start = time.perf_counter()
    with (OUT / (label + ".log")).open("w") as log:
        subprocess.run([LAKE, "build", BASE + "SortingExecution"], cwd=ROOT,
                       stdout=log, stderr=subprocess.STDOUT, check=True, timeout=600)
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
        proof.write_bytes(original + b"\n-- Proof-edit build-cache regression.\n")
        report["seconds"] = build("edited-proof")
        after = {name: fingerprint(path) for name, path in watched.items()}
        report["after"] = after
        report["api_reused"] = before["SortingSpec"] == after["SortingSpec"]
        report["backend_reused"] = before["SortingBackend"] == after["SortingBackend"]
        report["proof_rechecked"] = before["SortingProofs"] != after["SortingProofs"]
        report["passed"] = all(report[key] for key in
                               ("api_reused", "backend_reused", "proof_rechecked"))
    finally:
        proof.write_bytes(original)
        report["restore_seconds"] = build("restored-proof")
        (OUT / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if not report["passed"]:
        raise SystemExit("Proof-edit reuse regression: inspect " + str(OUT / "report.json"))
    print(f"PASS: proof edit and executable rebuild {report['seconds']:.2f}s; "
          "specification and backend artifacts unchanged")


if __name__ == "__main__":
    main()
