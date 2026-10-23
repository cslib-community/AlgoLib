"""Exercise review-policy failures in an isolated synthetic repository."""
from copy import deepcopy
from pathlib import Path
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("ram_reviewers", HERE / "check_reviewers.py")
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)


class ReviewerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="ram-reviewers-")
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.data = json.loads((review.REPO / review.REGISTRY).read_text())
        for patterns in review.REQUIRED_PATHS.values():
            for pattern in patterns:
                path = self.repo / pattern.lstrip("/")
                if pattern.endswith("/"):
                    path.mkdir(parents=True, exist_ok=True)
                elif pattern != "/" + review.CODEOWNERS:
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("isolated fixture\n")
        self.registry = self.repo / review.REGISTRY
        self.owners = self.repo / review.CODEOWNERS
        self.algorithms = self.repo / review.ALGORITHMS
        self.algorithms.write_text(json.dumps({
            "algorithms": {"example": {"review_area": "algorithms", "roles": {
                "program": ["Examples/Example/Program.lean"],
                "proofs": ["Examples/Example/Proofs.lean"],
            }}},
            "fixtures": {"Examples/Example.lean": {"review_area": "algorithms"}},
        }))
        self.save()
        review.check(self.repo, write=True)

    def save(self):
        self.registry.write_text(json.dumps(self.data, indent=2) + "\n")

    def rejects(self, diagnostic):
        self.save()
        with self.assertRaisesRegex(ValueError, diagnostic):
            review.check(self.repo)

    def test_valid_and_deterministic(self):
        original = self.owners.read_bytes()
        review.check(self.repo)
        review.check(self.repo, write=True)
        self.assertEqual(original, self.owners.read_bytes())
        # JSON map/list order does not change generated area/path ordering.
        self.data["areas"] = dict(reversed(list(self.data["areas"].items())))
        for area in self.data["areas"].values():
            area["paths"].reverse()
        self.save()
        review.check(self.repo)

    def test_area_routing_and_fallback(self):
        for area, layer in review.LAYER_AREAS.items():
            self.assertEqual(review.area_for_path(self.data, f"{review.RAM}{layer}/New.lean"), area)
            self.assertEqual(review.area_for_path(self.data, f"{review.RAM}{layer}.lean"), area)
        for path in ("Historical/New.lean", "Research/New.lean"):
            self.assertEqual(review.area_for_path(self.data, review.RAM + path), "experiments")
        for path in ("Unclassified.lean", "Tests/New.py", "docs/new.md"):
            self.assertEqual(review.area_for_path(self.data, review.RAM + path), "infrastructure")
        for path in (".github/workflows/new.yml", "vendor/loom/New.lean", "vendor/velvet/New.lean"):
            self.assertEqual(review.area_for_path(self.data, path), "infrastructure")
        self.assertIsNone(review.area_for_path(self.data, "AlgoLib/Unrelated.lean"))
        self.assertIsNone(review.area_for_path(self.data, "AlgoLib/Experimental/RAMish/New.lean"))

    def test_preserve_unrelated_rules(self):
        prefix = "# Existing ownership\n/other/ @other-owner\n"
        suffix = "\n# Keep this trailing comment.\n"
        self.owners.write_text(prefix + self.owners.read_text() + suffix)
        self.data["areas"]["machine"]["primary"] = ["@machine-reviewer"]
        self.save()
        review.check(self.repo, write=True)
        self.assertTrue(self.owners.read_text().startswith(prefix))
        self.assertTrue(self.owners.read_text().endswith(suffix))
        self.assertIn("/AlgoLib/Experimental/RAM/Machine/ @machine-reviewer", self.owners.read_text())
        review.check(self.repo)

    def test_existing_file_without_markers(self):
        original = "# Existing owner\n/other/ @other-owner"
        self.owners.write_text(original)
        review.check(self.repo, write=True)
        self.assertTrue(self.owners.read_text().startswith(original + "\n" + review.BEGIN))

    def test_unknown_or_missing_area(self):
        self.data["areas"]["typo"] = self.data["areas"].pop("frontend")
        self.rejects("exactly cover")

    def test_empty_primary(self):
        self.data["areas"]["frontend"]["primary"] = []
        self.rejects("primary reviewer must not be empty")

    def test_invalid_reviewer(self):
        initial = deepcopy(self.data)
        for value in ("sorrachai", "@bad name", "@-bad", "@bad--name", "@bad/", "@a\n/b", None):
            with self.subTest(value=value):
                self.data = deepcopy(initial)
                self.data["areas"]["frontend"]["primary"] = [value]
                self.rejects("invalid reviewer")

    def test_duplicate_primary_case_insensitive(self):
        self.data["areas"]["frontend"]["primary"] = ["@sorrachai", "@Sorrachai"]
        self.rejects("duplicate reviewer")

    def test_duplicate_backup(self):
        self.data["areas"]["frontend"]["backup"] = ["@backup", "@backup"]
        self.rejects("duplicate reviewer")

    def test_primary_is_not_its_own_backup(self):
        self.data["areas"]["frontend"]["backup"] = ["@Sorrachai"]
        self.rejects("backup must be distinct")

    def test_distinct_backup_and_team(self):
        self.data["areas"]["frontend"]["backup"] = ["@example-org/ram-reviewers"]
        self.save()
        review.check(self.repo, write=True)
        self.assertIn("@sorrachai @example-org/ram-reviewers", self.owners.read_text())
        review.check(self.repo)

    def test_empty_responsibility(self):
        self.data["areas"]["frontend"]["responsibility"] = "  "
        self.rejects("responsibility must not be empty")

    def test_missing_path(self):
        self.data["areas"]["frontend"]["paths"].pop()
        self.rejects("ownership path coverage mismatch")

    def test_extra_path_cannot_expand_scope(self):
        self.data["areas"]["frontend"]["paths"].append("/**")
        self.rejects("ownership path coverage mismatch")

    def test_duplicate_path(self):
        self.data["areas"]["frontend"]["paths"] *= 2
        self.rejects("duplicate path")

    def test_wrong_path_area(self):
        self.data["areas"]["frontend"]["paths"], self.data["areas"]["library"]["paths"] = (
            self.data["areas"]["library"]["paths"], self.data["areas"]["frontend"]["paths"])
        self.rejects("ownership path coverage mismatch")

    def test_missing_target(self):
        (self.repo / "lean-toolchain").unlink()
        self.rejects("ownership target does not exist")

    def test_missing_fallback(self):
        self.data["fallback_paths"] = []
        self.rejects("subtree fallback")

    def test_duplicate_json_key(self):
        self.registry.write_text(self.registry.read_text().replace(
            '"schema_version": 1,', '"schema_version": 1, "schema_version": 1,'))
        with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
            review.check(self.repo)

    def test_unknown_algorithm_review_area(self):
        initial = json.loads(self.algorithms.read_text())
        for section in ("algorithms", "fixtures"):
            with self.subTest(section=section):
                data = deepcopy(initial)
                next(iter(data[section].values()))["review_area"] = "missing-area"
                self.algorithms.write_text(json.dumps(data))
                with self.assertRaisesRegex(ValueError, "unknown review_area"):
                    review.check(self.repo)

    def test_known_but_wrong_review_area(self):
        initial = json.loads(self.algorithms.read_text())
        for section in ("algorithms", "fixtures"):
            with self.subTest(section=section):
                data = deepcopy(initial)
                next(iter(data[section].values()))["review_area"] = "machine"
                self.algorithms.write_text(json.dumps(data))
                with self.assertRaisesRegex(ValueError, "disagrees with CODEOWNERS area"):
                    review.check(self.repo)

    def test_every_algorithm_role_file_matches_routing(self):
        data = json.loads(self.algorithms.read_text())
        data["algorithms"]["example"]["roles"]["proofs"].append("Machine/Unrelated.lean")
        self.algorithms.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "CODEOWNERS area 'machine' for Machine/Unrelated.lean"):
            review.check(self.repo)

    def test_fixture_path_matches_routing(self):
        data = json.loads(self.algorithms.read_text())
        data["fixtures"] = {"Machine/Example.lean": {"review_area": "algorithms"}}
        self.algorithms.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "CODEOWNERS area 'machine' for Machine/Example.lean"):
            review.check(self.repo)

    def test_stale_file_is_read_only_by_default(self):
        self.owners.write_text(self.owners.read_text().replace("@sorrachai", "@someone-else", 1))
        original = self.owners.read_bytes()
        for flag in ([], ["--check"]):
            result = subprocess.run([sys.executable, str(HERE / "check_reviewers.py"),
                                     "--repo", str(self.repo), *flag], capture_output=True, text=True)
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertIn("stale CODEOWNERS", result.stderr)
            self.assertEqual(self.owners.read_bytes(), original)
        result = subprocess.run([sys.executable, str(HERE / "check_reviewers.py"),
                                 "--repo", str(self.repo), "--write"], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        review.check(self.repo)

    def test_broken_markers(self):
        self.owners.write_text(self.owners.read_text().replace(review.END, ""))
        with self.assertRaisesRegex(ValueError, "markers must occur exactly once"):
            review.check(self.repo, write=True)

    def test_later_rules_cannot_shadow(self):
        self.owners.write_text(self.owners.read_text() + "*.lean @someone-else\n")
        with self.assertRaisesRegex(ValueError, "could shadow RAM routing"):
            review.check(self.repo, write=True)


if __name__ == "__main__":
    unittest.main()
