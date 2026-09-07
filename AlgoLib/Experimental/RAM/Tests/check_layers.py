"""Check the public/backend boundary and local module DAG after reorganizations.

Run from any directory with Python 3. No Lean installation is needed for this
structural check; the Lean test modules separately check semantics and costs.
"""
from pathlib import Path
import os
import re
import subprocess
import sys

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
    if layer.endswith(".lean"):
        layer = path.stem
    if layer in {"Language", "Verification", "Library", "Implementations", "Compiler", "Machine"}:
        assert not any(i.startswith(prefix + blocked + ".") for i in local
                       for blocked in ("Examples", "Tests", "Research")), (
            path, "reusable layer imports an example, test, or research fixture")
    assert re.search(r"/-!", text), (path, "missing module documentation")
    edges[module] = local

# These modules form the complete source-language / Loom reasoning layer.
# Enforce the boundary transitively, including frontend and actual algorithm proofs.
pure_modules = {prefix + name for name in (
    "Language", "Verification", "Library", "Library.Graph.GraphBridge", "Language.Model.NatArithmetic",
    "Language.Model.Semantics", "Language.Model.Syntax", "Language.Model.Contracts",
    "Language.Model.Mutable", "Language.Model.MultipleArrays", "Language.Model.ArrayFacts", "Verification.Semantics.Observation",
    "Verification.Semantics.LogicalInterpretation", "Verification.Semantics.LogicalVerification",
    "Verification.Semantics.LoomObservation", "Verification.Semantics.Procedures", "Language.Frontend", "Historical.Prototype.LegacyArrayFrontend",
    "Language.Expressions", "Examples.Composition.MixedAlgorithms",
    "Examples.InsertionSort.MinimumCaller",
    "Examples.BFS.Facts", "Library.GraphCursor",
    "Library.Queue", "Examples.Composition.QueueAlgorithms",
    "Library.QueueStacks", "Library.Stack",
    "Library.Graph.Graph", "Library.Graph.Traversal",
    "Library.SortingFacts", "Historical.Prototype.SortingAlgorithm", "Historical.Prototype.ZeroAlgorithm",
    "Tests.CreditLogic",
    "Language.Owned", "Language.Program", "Verification.Loom",
    "Library.Buffer", "Examples.Composition.BufferClient",
    "Historical.Adapters.CreditCompatibility", "Language.Contracts", "Verification.SourceMetadata", "Verification.Plan", "Verification.Algorithm",
    "Language.Elaboration", "Examples.Composition.BufferAlgorithms",
    "Verification.ProofGoals", "Verification.NamedProofs", "Verification.GeneratedObligations",
    "Verification.ObligationExplorer",
    "Examples.InsertionSort.Program", "Examples.InsertionSort.Obligations", "Examples.InsertionSort.Proofs",
    "Examples.BFS.Program", "Examples.BFS.Obligations", "Examples.BFS.Proofs",
    "Language.Elaboration.Syntax", "Language.Elaboration.Resources",
    "Language.Elaboration.Expressions", "Language.Elaboration.Statements",
    "Language.Elaboration.Method",
)}
for module in pure_modules:
    assert all(i in pure_modules for i in edges[module]), (
        modules[module], "logical language/proof layer imports a backend-dependent module"
    )

# The public frontend must never silently regain the historical array dispatcher.
def dependencies(module, seen=None):
    seen = set() if seen is None else seen
    for dependency in edges[module]:
        if dependency not in seen:
            seen.add(dependency)
            dependencies(dependency, seen)
    return seen

assert prefix + "Historical.Prototype.LegacyArrayFrontend" not in dependencies(
    prefix + "Language.Frontend"
), "public frontend imports the legacy array adapter"

# Assembly may use public permission/initialization contracts, never queue internals.
# This deliberately checks source references as well as the import graph: implementation
# modules remain transitive dependencies of any executable.
for name in ("Storage", "Execution"):
    path = root / "Examples" / "BFS" / f"{name}.lean"
    text = path.read_text()
    for private_name in ("QueueRing.", "QueueStacksImplementation.", "BufferImplementation.",
                         "GraphCursorImplementation.footprint", "GraphCursorImplementation.cells",
                         "GraphCursorImplementation.no_register"):
        assert private_name not in text, (path, "assembly opens private layout", private_name)

# The teaching examples must retain source-level proof blocks, not broad VC goal searches.
for name in ("InsertionSort/MinimumCaller", "InsertionSort/Proofs", "BFS/Proofs"):
    path = root / "Examples" / f"{name}.lean"
    text = path.read_text()
    for legacy_tactic in ("all_goals", "paper_solve", "paper_vc", "contract_solve"):
        assert not re.search(r"\b" + legacy_tactic + r"\b", text), (
            path, "algorithm proof bypasses the named-block interface", legacy_tactic
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

# Contracts and mathematical operations must not import proof plans or elaboration.
for entry in ("Language.Contracts", "Language.Expressions",
              "Implementations.Contracts.ResourceRefinement", "Compiler.Assembly.Native.Linking"):
    assert not any(n.startswith(prefix + "Verification.") for n in dependencies(prefix + entry)), (
        entry, "mathematical contracts depend on verification machinery")
assert not edges[prefix + "Verification.SourceMetadata"], "source metadata imports the RAM stack"

# Supported layers, including maintained implementation views, must not load history.
for module, path in modules.items():
    layer = path.relative_to(root).parts[0].removesuffix(".lean")
    if layer in {"Language", "Verification", "Library", "Implementations", "Compiler", "Machine", "Examples"}:
        assert not any(n.startswith(prefix + banned + ".") for n in dependencies(module)
                       for banned in ("Historical", "Research")), (path, "supported module depends on history/research")

# Standard commands and native execution must not load compatibility representations.
# Test the transitive graph, not just the spelling of direct imports.
for entry in ("Compiler.Assembly", "Compiler.Assembly.Native.Execution",
              "Examples.InsertionSort.Backend"):
    for dependency in dependencies(prefix + entry):
        assert not any(dependency.startswith(prefix + forbidden) for forbidden in (
            "Implementations.Natural.", "Compiler.Assembly.Natural.", "Compiler.Native.Natural"
        )), (entry, "native assembly loads a natural implementation adapter", dependency)
for entry in ("Compiler.Assembly.Tactics", "Compiler.Assembly.Result"):
    assert not edges[prefix + entry], (entry, "shared assembly utility depends on the RAM stack")

# A proof-only edit must not invalidate the costly sorting backend certificate.
assert prefix + "Examples.InsertionSort.Proofs" not in dependencies(
    prefix + "Examples.InsertionSort.Backend"
), "sorting backend imports algorithm proofs"
assert prefix + "Examples.InsertionSort.Obligations" not in dependencies(
    prefix + "Examples.InsertionSort.Backend"
), "sorting backend imports obligation generation"

# The generated API is the only supported named-obligation engine.
removed = ("named_proof_blocks", "namedTree", "ProofViews", "ProofInputViews", "#paper_goals", "#legacy_named_goals")
for path in root.rglob("*.lean"):
    text = path.read_text()
    for obsolete in removed:
        assert obsolete not in text, (path, "removed proof API", obsolete)

# Regeneration is cheap and independent of Lean's cached artifacts.
subprocess.run([sys.executable, str(root / "Tests/Conformance/generate.py"), "--check"],
               check=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
subprocess.run([sys.executable, str(root / "Tests/Conformance/generate_signed.py"), "--check"],
               check=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))

# Supported interfaces must not leak the retired target back into execution
# witnesses. Historical instruction references belong in Backend/Machine/Tests.
for module, path in modules.items():
    if path.relative_to(root).parts[0] in {"Language", "Verification", "Examples", "Research"}:
        assert not re.search(r"\bChecked\.(?:Exec|Code|run)\b", path.read_text()), (
            path, "supported interface references the retired Nat execution target"
        )
    if "Compiler/Native/" in path.as_posix():
        for retired in ("Historical.NatCompiler.Compiler", "Historical.NatMachine.Runner"):
            assert prefix + retired not in dependencies(module), (
                path, "native compiler transitively imports a retired compiler/runner", retired
            )

subprocess.run([sys.executable, str(root / "Tests/generate_navigation.py"), "--check"], check=True)
subprocess.run([sys.executable, str(root / "Tests/check_navigation.py")], check=True)
subprocess.run([sys.executable, str(root / "Tests/test_navigation.py")], check=True)
print(f"Checked {len(modules)} documented modules: boundaries and import DAG OK")
