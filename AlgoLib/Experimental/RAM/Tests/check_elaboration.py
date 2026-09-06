"""Re-elaborate representative clients and assemblies against checked time budgets.

Unlike `lake build` on an unchanged checkout, `lake env lean FILE` actually checks
FILE every run. Imports are built first, outside the timed interval. The generated Lake setup preserves project options. Single-thread
Lean elaboration/type-checking profiles accompany the JSON report for diagnosis. No compiler result or proof is trusted by this measurement script.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import platform
import shutil
import signal
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
CONFIG = Path(__file__).with_name("performance") / "budgets.json"


def run_logged(command: list[str], log: Path, timeout: float | None = None):
    """Bound the entire compiler process group, retaining diagnostics on failure."""
    start = time.perf_counter()
    with log.open("w") as output:
        process = subprocess.Popen(command, cwd=ROOT, stdout=output,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=timeout)
            status = "ok" if code == 0 else "compiler_error"
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            code, status = None, "timeout"
    return {"seconds": time.perf_counter() - start, "status": status,
            "returncode": code, "log": str(log)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runs", type=int, default=1)
    parser.add_argument("--case", action="append", dest="names")
    parser.add_argument("--budget-scale", type=float, default=1.0,
                        help="Explicit hardware adjustment, recorded in the report")
    parser.add_argument("--output", type=Path, default=ROOT / ".lake/build/ram-elaboration")
    args = parser.parse_args()
    if args.runs < 1 or not 0 < args.budget_scale < float("inf"):
        parser.error("runs and budget-scale must be positive and finite")
    cases = json.loads(CONFIG.read_text())["cases"]
    if args.names:
        unknown = set(args.names) - {case["name"] for case in cases}
        if unknown:
            parser.error(f"unknown cases: {sorted(unknown)}")
        cases = [case for case in cases if case["name"] in args.names]
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    report = {"schema": 1, "platform": platform.platform(),
              "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
              "budget_scale": args.budget_scale, "runs": args.runs,
              "measurement": "single-thread fresh module check with warm dependencies",
              "options_source": "Lake-generated module setup",
              "cases": []}
    report["revision"] = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    report["dirty"] = bool(subprocess.check_output(
        ["git", "status", "--porcelain"], cwd=ROOT, text=True).strip())
    print("Preparing checked dependencies (not timed)...", flush=True)
    preparation = run_logged([lake, "build", *[c["module"] for c in cases]],
                             output / "prepare.log", timeout=1800)
    report["preparation"] = preparation
    failed = preparation["status"] != "ok"
    if not failed:
        for case in cases:
            budget = case["seconds"] * args.budget_scale
            samples = []
            setup = ROOT / ".lake/build/ir" / (case["module"].replace(".", "/") + ".setup.json")
            for i in range(args.runs):
                print(f"Checking {case['name']} ({i + 1}/{args.runs})...", flush=True)
                samples.append(run_logged(
                    [lake, "env", "lean", "-j1", "--profile", f"--setup={setup}",
                     case["module"].replace(".", "/") + ".lean"],
                    output / f"{case['name']}-{i + 1}.log", timeout=budget))
                if samples[-1]["status"] != "ok":
                    break
            median = statistics.median(s["seconds"] for s in samples)
            passed = all(s["status"] == "ok" for s in samples) and median <= budget
            failed |= not passed
            report["cases"].append({**case, "budget_seconds": budget,
                                    "median_seconds": median, "passed": passed,
                                    "samples": samples})
            print(f"  {'PASS' if passed else 'FAIL'}: {median:.2f}s / {budget:.2f}s", flush=True)
    report["passed"] = not failed
    target = output / "report.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Report: {target}", flush=True)
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
