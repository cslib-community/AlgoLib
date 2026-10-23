"""Validate algorithm boundaries from docs/algorithms.json.

These are architectural regression checks, not semantic or privacy proofs. The
import graph enforces backend independence; the small source-name checks retain
existing safeguards against broad proof searches and known private layout names.
Kernel-checked refinement and ownership theorems remain the semantic evidence.
"""
import json
from pathlib import Path, PurePosixPath
import re

from lean_imports import strip_comments


ROLES = frozenset({"program", "obligations", "proofs", "facts", "client",
                   "backend", "storage", "execution", "inputs"})
REQUIRED_ROLES = frozenset({"program", "obligations", "proofs", "backend", "execution"})
LOGICAL_ROLES = frozenset({"program", "obligations", "proofs", "facts", "client"})
BACKEND_LAYERS = frozenset({"Implementations", "Compiler", "Machine"})
PRIVATE_LAYOUT_NAMES = (
    "QueueRing.", "QueueStacksImplementation.", "BufferImplementation.",
    "GraphCursorImplementation.footprint", "GraphCursorImplementation.cells",
    "GraphCursorImplementation.no_register",
)
PROOF_SEARCH_TACTICS = ("all_goals", "paper_solve", "paper_vc", "contract_solve")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def dependencies(module: str, edges: dict[str, list[str]]) -> set[str]:
    """Return transitive imports, including indirect imports through helpers."""
    seen, pending = set(), list(edges[module])
    while pending:
        target = pending.pop()
        if target not in seen:
            seen.add(target)
            pending.extend(edges[target])
    return seen


def _path(root: Path, value, description: str, suffix: str) -> str:
    require(isinstance(value, str) and bool(value), f"{description}: expected a relative path")
    path = PurePosixPath(value)
    require(not path.is_absolute() and ".." not in path.parts and
            str(path) == value and path.suffix == suffix,
            f"{description}: invalid RAM-relative {suffix} path: {value}")
    require((root / value).is_file(), f"{description}: missing file: {value}")
    return value


def _module(root: Path, value, records: dict, description: str, layer: str) -> str:
    module = _path(root, value, description, ".lean")
    require(module in records, f"{description}: module is absent from docs/modules.json: {module}")
    require(records[module]["layer"] == layer and module.startswith(layer + "/"),
            f"{description}: expected a {layer} module: {module}")
    return module


def validate_algorithms(root: Path, records: dict, edges: dict[str, list[str]]) -> dict:
    """Validate and return the algorithm manifest; paths are RAM-relative.

    ``records`` is the modules object in docs/modules.json. ``edges`` contains
    every local RAM import, keyed by the same relative .lean paths. The caller
    checks general layer rules and cycles; this check adds algorithm-role rules.
    """
    manifest = json.loads((root / "docs/algorithms.json").read_text())
    require(isinstance(manifest, dict) and
            set(manifest) == {"schema", "algorithms", "fixtures"} and
            manifest["schema"] == 1, "algorithm metadata: expected schema 1")
    require(isinstance(manifest["algorithms"], dict) and bool(manifest["algorithms"]),
            "algorithm metadata: expected a nonempty algorithms registry")
    require(isinstance(manifest["fixtures"], dict), "algorithm metadata: expected fixture mapping")
    require(set(edges) == set(records), "algorithm metadata: import graph and module inventory disagree")
    for module, targets in edges.items():
        require(all(target in edges for target in targets), f"{module}: import graph has an unknown target")

    assignments = {}
    for name, algorithm in manifest["algorithms"].items():
        require(re.fullmatch(r"[a-z][a-z0-9-]*", name) is not None,
                f"invalid algorithm identity: {name}")
        require(isinstance(algorithm, dict) and
                set(algorithm) == {"review_area", "entrypoint", "roles", "tests"},
                f"{name}: expected review_area, entrypoint, roles, and tests")
        require(isinstance(algorithm["review_area"], str) and bool(algorithm["review_area"]),
                f"{name}: missing review area")
        _path(root, algorithm["entrypoint"], f"{name} entrypoint", ".md")
        roles = algorithm["roles"]
        require(isinstance(roles, dict) and set(roles) == ROLES,
                f"{name}: role fields must be {', '.join(sorted(ROLES))}")
        for role, paths in roles.items():
            require(isinstance(paths, list), f"{name}/{role}: expected a list of modules")
            require(bool(paths) or role not in REQUIRED_ROLES, f"{name}: required role is empty: {role}")
            for path in paths:
                module = _module(root, path, records, f"{name}/{role}", "Examples")
                require(module not in assignments, f"algorithm module has multiple roles: {module}")
                assignments[module] = (name, role)
        require(isinstance(algorithm["tests"], list) and bool(algorithm["tests"]),
                f"{name}: at least one execution regression test is required")
        tests = [_module(root, path, records, f"{name} test", "Tests")
                 for path in algorithm["tests"]]
        require(len(tests) == len(set(tests)), f"{name}: duplicate regression test")
        covered = set()
        for test in tests:
            reached = dependencies(test, edges).intersection(roles["execution"])
            require(bool(reached), f"{name}: test does not import registered execution: {test}")
            covered.update(reached)
        require(covered == set(roles["execution"]), f"{name}: execution module has no importing test")

    for path, fixture in manifest["fixtures"].items():
        module = _module(root, path, records, "fixture", "Examples")
        require(module not in assignments, f"algorithm module is also classified as a fixture: {module}")
        require(isinstance(fixture, dict) and set(fixture) == {"kind", "review_area", "reason"},
                f"{module}: fixture needs kind, review_area, and reason")
        require(fixture["kind"] in {"logical", "integration"}, f"{module}: unknown fixture kind")
        require(isinstance(fixture["review_area"], str) and bool(fixture["review_area"]),
                f"{module}: fixture has no review area")
        require(isinstance(fixture["reason"], str) and bool(fixture["reason"].strip()),
                f"{module}: fixture classification needs an explicit reason")

    expected = {path for path, record in records.items()
                if record["layer"] == "Examples" and path != "Examples.lean"}
    assigned = set(assignments) | set(manifest["fixtures"])
    require(expected == assigned,
            f"algorithm role coverage mismatch: unclassified={sorted(expected - assigned)}, "
            f"unexpected={sorted(assigned - expected)}")
    proof_modules = {path for path, (_, role) in assignments.items()
                     if role in {"proofs", "obligations"}}
    backend_modules = {path for path, (_, role) in assignments.items()
                       if role in {"backend", "storage", "execution", "inputs"}}
    integration_fixtures = {path for path, fixture in manifest["fixtures"].items()
                            if fixture["kind"] == "integration"}

    for module in sorted(assigned):
        reached = dependencies(module, edges)
        role = assignments.get(module, (None, None))[1]
        logical_fixture = module in manifest["fixtures"] and manifest["fixtures"][module]["kind"] == "logical"
        if role in LOGICAL_ROLES or logical_fixture:
            forbidden = sorted(target for target in reached if
                               records[target]["layer"] in BACKEND_LAYERS or
                               target in backend_modules or target in integration_fixtures)
            require(not forbidden, f"{module}: logical algorithm module imports backend-dependent module: {forbidden}")
        if role in {"backend", "storage"}:
            forbidden = sorted(reached.intersection(proof_modules))
            require(not forbidden,
                    f"{module}: backend/storage imports algorithm proofs or obligations: {forbidden}")
        source = strip_comments((root / module).read_text())
        if role in {"proofs", "client"}:
            for tactic in PROOF_SEARCH_TACTICS:
                require(not re.search(r"\b" + tactic + r"\b", source),
                        f"{module}: algorithm proof bypasses the named-block interface: {tactic}")
        if role in {"storage", "execution"}:
            for name in PRIVATE_LAYOUT_NAMES:
                require(name not in source, f"{module}: assembly opens private layout: {name}")
    return manifest
