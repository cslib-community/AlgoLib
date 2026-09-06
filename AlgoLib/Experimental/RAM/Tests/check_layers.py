"""Check the public/backend boundary and local module DAG after reorganizations.

Run from any directory with Python 3. No Lean installation is needed for this
structural check; the Lean test modules separately check semantics and costs.
"""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
prefix = "AlgoLib.Experimental.RAM."
modules = {
    prefix + str(p.relative_to(root).with_suffix("")).replace("/", "."): p
    for p in root.rglob("*.lean")
}
edges = {}
for module, path in modules.items():
    text = path.read_text()
    imports = re.findall(r"^import (\S+)", text, re.MULTILINE)
    local = [i for i in imports if i.startswith(prefix)]
    for dependency in local:
        assert dependency in modules, (path, "missing module", dependency)
    layer = path.relative_to(root).parts[0]
    if layer in ("Programs", "Authoring", "Library", "Backend", "Machine", "Specification"):
        assert not any(i.startswith(prefix + "Prototype.") for i in local), (
            path, "production layer depends on the isolated prototype"
        )
    if layer == "Prototype" and path.stem in ("Observation", "Interpretation", "Verification", "LoomObservation", "Mutable", "Frontend", "Procedures",
            "MultipleArrays", "VelvetSemantics", "VelvetWP", "Nondeterministic",
            "NondeterministicRunner", "ExecutableTranslation", "ExecutionBridge"):
        assert not any(
            i.startswith(prefix + blocked + ".")
            for i in local for blocked in ("Programs", "Legacy", "Library")
        ), (path, "generic prototype infrastructure depends on an algorithm library/demo")
        assert not any(
            i == prefix + "Prototype." + blocked
            for i in local for blocked in ("InsertionSort", "BFS", "Graph", "GraphTests", "Tests", "Axioms",
                "MultipleArrayTests", "VelvetArrayTranslation", "VelvetTranslationTests",
                "RecursiveTranslation", "ArraySubstitution", "SortingAlgorithm", "ZeroAlgorithm")
        ), (path, "generic prototype infrastructure depends on a domain adapter or demo/tests")
    if layer == "Programs":
        assert not any(
            i.startswith(prefix + blocked + ".")
            for i in local for blocked in ("Backend", "Machine", "Legacy")
        ), (path, "public algorithm imports an implementation layer")
    if layer in ("Authoring", "Library", "Backend", "Machine", "Specification"):
        assert not any(
            i.startswith(prefix + blocked + ".")
            for i in local for blocked in ("Programs", "Legacy")
        ), (path, "reusable layer depends on an algorithm/demo")
    assert re.search(r"/-!", text), (path, "missing module documentation")
    edges[module] = local

# These modules form the complete source-language / Loom reasoning layer.
# Enforce the boundary transitively, including frontend and actual algorithm proofs.
pure_modules = {prefix + name for name in (
    "Authoring.Semantics", "Authoring.Syntax", "Authoring.Contracts",
    "Authoring.Mutable", "Authoring.MultipleArrays", "Authoring.ArrayFacts", "Prototype.Observation",
    "Prototype.LogicalInterpretation", "Prototype.LogicalVerification",
    "Prototype.LoomObservation", "Prototype.Procedures", "Prototype.LogicalFrontend",
    "Prototype.SortingFacts", "Prototype.SortingAlgorithm", "Prototype.ZeroAlgorithm",
    "Tests.CreditLogic",
)}
for module in pure_modules:
    assert all(i in pure_modules for i in edges[module]), (
        modules[module], "logical language/proof layer imports a backend-dependent module"
    )

active, done = set(), set()
def visit(module):
    assert module not in active, (module, "cyclic local imports")
    if module in done:
        return
    active.add(module)
    for dependency in edges[module]:
        visit(dependency)
    active.remove(module)
    done.add(module)

for module in modules:
    visit(module)
print(f"Checked {len(modules)} documented modules: boundaries and import DAG OK")
