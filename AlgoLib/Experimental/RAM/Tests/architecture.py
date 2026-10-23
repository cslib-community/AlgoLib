"""Read the project import graph and enforce the RAM architecture policy.

Module status/ownership and allowed dependencies are data, not opt-in Python lists.
External packages remain Lean's responsibility. Repository-local bridges are followed
so importing a backend through an unrelated AlgoLib module cannot hide a violation.
These checks protect engineering boundaries; they are not semantic soundness proofs.
"""
from dataclasses import dataclass
import json
from pathlib import Path
import re

from lean_imports import read_imports, strip_comments

PREFIX = "AlgoLib.Experimental.RAM."
LAYERS = {"Language", "Verification", "Library", "Implementations", "Compiler",
          "Machine", "Examples", "Historical", "Research", "Tests"}
SUPPORTED = LAYERS - {"Historical", "Research", "Tests"}
BACKENDS = {"Implementations", "Compiler", "Machine"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def closure(edges, start):
    seen, pending = set(), list(edges[start])
    while pending:
        node = pending.pop()
        if node not in seen:
            seen.add(node)
            pending.extend(edges[node])
    return seen


@dataclass
class Model:
    root: Path
    records: dict
    # RAM-relative paths; edges also include imports reached through local bridges.
    edges: dict


def load_model(root: Path) -> Model:
    root = root.resolve()
    repo = root.parents[2]
    records = json.loads((root / "docs/modules.json").read_text())["modules"]
    actual = {str(p.relative_to(root)) for p in root.rglob("*.lean")}
    require(actual == set(records),
            f"module metadata mismatch: unregistered={sorted(actual - set(records))}, "
            f"missing={sorted(set(records) - actual)}")
    for path, record in records.items():
        physical = path.split("/")[0] if "/" in path else Path(path).stem
        require(record["layer"] in LAYERS and record["layer"] == physical,
                f"{path}: metadata does not match physical layer")
        require(record["status"] in {"public", "internal", "compatibility", "historical", "research", "test"},
                f"{path}: unknown module status")
        expected = {"Historical": "historical", "Research": "research", "Tests": "test"}
        if physical in expected:
            require(record["status"] == expected[physical], f"{path}: inconsistent module status")
        if record["entrypoint"]:
            require(physical in SUPPORTED and path == physical + ".lean" and record["status"] == "public",
                    f"{path}: invalid public entry point")
        require("/-!" in (root / path).read_text(), f"{path}: missing module documentation")
    for layer in SUPPORTED:
        require([p for p, r in records.items() if r["layer"] == layer and r["entrypoint"]]
                == [layer + ".lean"], f"{layer}: requires one canonical public entry")

    names = {PREFIX + p[:-5].replace("/", "."): p for p in records}
    project_edges, active = {}, []

    def visit(module):
        require(module not in active, f"cyclic local imports: {' -> '.join(active + [module])}")
        if module in project_edges:
            return
        path = repo / (module.replace(".", "/") + ".lean")
        active.append(module)
        imports = read_imports(path)
        local = []
        for dependency in imports:
            target = repo / (dependency.replace(".", "/") + ".lean")
            if dependency.startswith(PREFIX):
                require(dependency in names, f"{path}: missing RAM module {dependency}")
            if target.is_file():
                local.append(dependency)
                visit(dependency)
        project_edges[module] = local
        active.pop()

    for module in names:
        visit(module)

    def nearest_ram(module):
        seen, found, pending = set(), set(), list(project_edges[module])
        while pending:
            target = pending.pop()
            if target in names:
                found.add(names[target])
            elif target not in seen:
                seen.add(target)
                pending.extend(project_edges[target])
        return sorted(found)

    return Model(root, records, {path: nearest_ram(name) for name, path in names.items()})


def validate_architecture(model: Model):
    root, records, edges = model.root, model.records, model.edges
    policy = json.loads((root / "docs/architecture.json").read_text())
    require(policy.get("schema") == 1, "unsupported architecture policy schema")
    fields = {"schema", "allowed_imports", "backend_free_layers", "additional_logical_roots",
              "no_verification_roots", "isolated_modules", "native_only_roots"}
    require(set(policy) == fields, "architecture policy has missing or unknown fields")
    allowed = policy["allowed_imports"]
    require(set(allowed) == LAYERS, "dependency policy must cover every layer")
    for layer, targets in allowed.items():
        require(isinstance(targets, list) and len(targets) == len(set(targets))
                and set(targets) <= LAYERS, f"{layer}: invalid allowed dependencies")
    pure_layers = policy["backend_free_layers"]
    require(isinstance(pure_layers, list) and set(pure_layers) == {"Language", "Verification", "Library"}
            and len(pure_layers) == 3, "logical layers must remain backend-free by default")
    for field in ("additional_logical_roots", "no_verification_roots", "isolated_modules", "native_only_roots"):
        for path, reason in policy[field].items():
            require(path in records, f"{field}: unknown module {path}")
            require(isinstance(reason, str) and bool(reason.strip()), f"{field}: {path} needs a reason")

    transitive = {path: closure(edges, path) for path in records}
    for path, record in records.items():
        layer = record["layer"]
        for dependency in edges[path]:
            require(records[dependency]["layer"] in allowed[layer],
                    f"{path}: forbidden dependency on {dependency} ({layer} boundary)")
        if layer in SUPPORTED:
            for dependency in transitive[path]:
                require(records[dependency]["layer"] not in {"Historical", "Research", "Tests"},
                        f"{path}: supported module depends on history/research/tests: {dependency}")
        if layer in pure_layers or path in policy["additional_logical_roots"]:
            for dependency in transitive[path]:
                require(records[dependency]["layer"] not in BACKENDS,
                        f"{path}: logical layer depends on backend {dependency}")
        code = strip_comments((root / path).read_text())
        if layer in {"Language", "Verification", "Examples", "Research"}:
            require(not re.search(r"\bChecked\.(?:Exec|Code|run)\b", code),
                    f"{path}: supported interface references the retired Nat execution target")
        for obsolete in ("named_proof_blocks", "namedTree", "ProofViews", "ProofInputViews",
                         "#paper_goals", "#legacy_named_goals"):
            require(obsolete not in code, f"{path}: removed proof API {obsolete}")
        if path.startswith("Compiler/Native/"):
            for retired in ("Historical/NatCompiler/Compiler.lean", "Historical/NatMachine/Runner.lean"):
                require(retired not in transitive[path], f"{path}: loads a retired compiler/runner")
    for path in policy["no_verification_roots"]:
        require(not any(records[d]["layer"] == "Verification" for d in transitive[path]),
                f"{path}: mathematical contracts depend on verification machinery")
    for path in policy["isolated_modules"]:
        require(not edges[path], f"{path}: isolated module depends on the RAM stack")
    for path in policy["native_only_roots"]:
        for dependency in transitive[path]:
            require(not dependency.startswith(("Implementations/Natural/", "Compiler/Assembly/Natural/",
                                               "Compiler/Native/Natural.lean")),
                    f"{path}: native assembly loads a natural implementation adapter: {dependency}")
    return policy
