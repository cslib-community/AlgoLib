"""Check role-based boundaries on disposable, newly named algorithm fixtures.

No working-tree Lean files are edited and no Lean build is needed. These tests
ensure that a third algorithm inherits the same rules as sorting and BFS.
"""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from algorithm_roles import ROLES, validate_algorithms


class AlgorithmRoleTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="ram-algorithm-roles-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "docs").mkdir()
        self.records, self.edges = {}, {}
        self.manifest = {"schema": 1, "algorithms": {}, "fixtures": {}}
        self.module("Language/Program.lean")
        self.module("Compiler/Compile.lean")
        self.module("Implementations/Queue.lean")
        self.add_algorithm("fresh-example", "Fresh")

    def module(self, path, imports=(), source="/-! Fixture. -/\n"):
        file = self.root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(source)
        self.records[path] = {"layer": path.split("/")[0], "status": "internal", "entrypoint": False}
        self.edges[path] = list(imports)
        return path

    def add_algorithm(self, name, directory):
        prefix = f"Examples/{directory}/"
        roles = {role: [] for role in sorted(ROLES)}
        for role, filename in (("program", "Program"), ("obligations", "Obligations"),
                               ("proofs", "Proofs"), ("backend", "Backend"),
                               ("storage", "Storage"), ("execution", "Execution"),
                               ("client", "Client"), ("inputs", "Inputs")):
            roles[role] = [self.module(prefix + filename + ".lean")]
        self.edges[roles["program"][0]] = ["Language/Program.lean"]
        self.edges[roles["obligations"][0]] = roles["program"].copy()
        self.edges[roles["proofs"][0]] = roles["obligations"].copy()
        self.edges[roles["client"][0]] = roles["proofs"].copy()
        self.edges[roles["backend"][0]] = roles["program"] + ["Compiler/Compile.lean"]
        self.edges[roles["storage"][0]] = roles["backend"] + ["Implementations/Queue.lean"]
        self.edges[roles["execution"][0]] = roles["client"] + roles["storage"]
        # Host input encoding is explicitly permitted to use an implementation.
        self.edges[roles["inputs"][0]] = ["Implementations/Queue.lean"]
        test = self.module(f"Tests/{directory}.lean", roles["execution"])
        entrypoint = prefix + "README.md"
        (self.root / entrypoint).write_text("# Example\n")
        self.manifest["algorithms"][name] = {
            "review_area": "algorithms", "entrypoint": entrypoint,
            "roles": roles, "tests": [test],
        }
        return roles

    @property
    def algorithm(self):
        return self.manifest["algorithms"]["fresh-example"]

    @property
    def roles(self):
        return self.algorithm["roles"]

    def validate(self):
        (self.root / "docs/algorithms.json").write_text(json.dumps(self.manifest))
        return validate_algorithms(self.root, self.records, self.edges)

    def reject(self, diagnostic):
        with self.assertRaisesRegex(ValueError, diagnostic):
            self.validate()

    def test_new_algorithm_is_accepted(self):
        self.assertEqual(self.validate(), self.manifest)

    def test_every_example_needs_a_role(self):
        self.module("Examples/Fresh/Forgotten.lean")
        self.reject("role coverage mismatch.*Forgotten")

    def test_duplicate_role_is_rejected(self):
        self.roles["facts"] = self.roles["program"].copy()
        self.reject("multiple roles")

    def test_unknown_role_is_rejected(self):
        self.roles["proof"] = self.roles.pop("proofs")
        self.reject("role fields")

    def test_required_role_cannot_be_empty(self):
        self.roles["backend"] = []
        self.reject("required role is empty: backend")

    def test_metadata_requires_an_existing_entrypoint(self):
        self.algorithm["entrypoint"] = "Examples/Fresh/Missing.md"
        self.reject("entrypoint: missing file")

    def test_metadata_rejects_paths_outside_ram(self):
        self.algorithm["entrypoint"] = "../README.md"
        self.reject("invalid RAM-relative")

    def test_metadata_requires_an_existing_module(self):
        self.roles["facts"] = ["Examples/Fresh/Missing.lean"]
        self.reject("missing file")

    def test_required_test_must_exercise_registered_execution(self):
        self.edges["Tests/Fresh.lean"] = self.roles["program"].copy()
        self.reject("test does not import registered execution")

    def test_empty_test_list_is_rejected(self):
        self.algorithm["tests"] = []
        self.reject("execution regression test is required")

    def test_each_execution_module_needs_coverage(self):
        self.roles["execution"].append(self.module("Examples/Fresh/OtherExecution.lean"))
        self.reject("execution module has no importing test")

    def test_backend_cannot_import_proof_through_a_helper(self):
        helper = self.module("Compiler/Helper.lean", self.roles["proofs"])
        self.edges[self.roles["backend"][0]].append(helper)
        self.reject("backend/storage imports algorithm proofs or obligations")

    def test_storage_cannot_import_obligations(self):
        self.edges[self.roles["storage"][0]].extend(self.roles["obligations"])
        self.reject("backend/storage imports algorithm proofs or obligations")

    def test_other_algorithm_proofs_cannot_leak_into_backend(self):
        other = self.add_algorithm("second-example", "Second")
        self.edges[self.roles["backend"][0]].extend(other["proofs"])
        self.reject("backend/storage imports algorithm proofs or obligations")

    def test_logical_roles_cannot_import_backend_through_helper(self):
        helper = self.module("Library/Helper.lean", ["Compiler/Compile.lean"])
        for role in ("program", "obligations", "proofs", "client"):
            with self.subTest(role=role):
                path = self.roles[role][0]
                before = self.edges[path].copy()
                self.edges[path].append(helper)
                self.reject("logical algorithm module imports backend-dependent")
                self.edges[path] = before

    def test_named_proof_interface_applies_to_new_proofs_and_clients(self):
        for role in ("proofs", "client"):
            for tactic in ("all_goals", "paper_solve", "paper_vc", "contract_solve"):
                with self.subTest(role=role, tactic=tactic):
                    path = self.root / self.roles[role][0]
                    path.write_text("example : True := by\n  " + tactic + "\n")
                    self.reject("bypasses the named-block interface")
                    path.write_text("/-! Fixture. -/\n")

    def test_layout_guard_applies_to_new_storage_and_execution(self):
        for role in ("storage", "execution"):
            with self.subTest(role=role):
                path = self.root / self.roles[role][0]
                path.write_text("def leaked := QueueRing.cells\n")
                self.reject("assembly opens private layout")
                path.write_text("/-! Fixture. -/\n")

    def test_comments_do_not_trigger_source_guards(self):
        (self.root / self.roles["proofs"][0]).write_text(
            "/-! Avoid all_goals and /- paper_solve -/ contract_solve. -/\n"
            "-- paper_vc\nexample : True := by trivial\n")
        (self.root / self.roles["execution"][0]).write_text(
            "-- QueueRing.cells must remain private.\n/- GraphCursorImplementation.footprint -/\n")
        self.validate()

    def test_known_public_graph_contracts_remain_allowed(self):
        (self.root / self.roles["storage"][0]).write_text(
            "#check GraphCursorImplementation.extent\n#check GraphCursorImplementation.region\n")
        self.validate()

    def add_fixture(self, kind="logical", imports=()):
        path = self.module("Examples/Composition/Small.lean", imports,
                           "example : True := by contract_solve []\n")
        self.manifest["fixtures"][path] = {
            "kind": kind, "review_area": "algorithms",
            "reason": "Internal contract-composition regression fixture.",
        }
        return path

    def test_explicit_logical_fixture_may_use_internal_tactics(self):
        self.add_fixture()
        self.validate()

    def test_logical_fixture_remains_backend_independent(self):
        self.add_fixture(imports=["Implementations/Queue.lean"])
        self.reject("logical algorithm module imports backend-dependent")

    def test_integration_fixture_may_link_implementations(self):
        self.add_fixture(kind="integration", imports=["Implementations/Queue.lean"])
        self.validate()

    def test_fixture_needs_an_explicit_reason(self):
        path = self.add_fixture()
        self.manifest["fixtures"][path]["reason"] = " "
        self.reject("explicit reason")

    def test_module_cannot_be_both_algorithm_and_fixture(self):
        fixture = self.add_fixture()
        self.manifest["fixtures"][self.roles["program"][0]] = copy.deepcopy(self.manifest["fixtures"][fixture])
        self.reject("also classified as a fixture")


if __name__ == "__main__":
    unittest.main()
