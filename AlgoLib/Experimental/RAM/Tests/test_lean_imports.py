"""Regression checks for dependency scanning; optional --check-lean compares Lean.

Run with Python alone for all lexical/rejection tests. With --check-lean, three
temporary headers are also compared to the pinned compiler's --deps output.
This does not build the project or edit the checkout.
"""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from lean_imports import ImportParseError, parse_imports, read_imports, strip_comments

ROOT = Path(__file__).resolve().parents[1]
CHECK_LEAN = "--check-lean" in sys.argv
if CHECK_LEAN:
    sys.argv.remove("--check-lean")


class ImportTests(unittest.TestCase):
    def test_indentation_and_leading_comment(self):
        self.assertEqual(parse_imports("/- license -/\n  import AlgoLib.Experimental.RAM.Machine\n"),
                         ["AlgoLib.Experimental.RAM.Machine"])

    def test_tokens_can_span_lines_and_nested_comments(self):
        text = """/- outer /- import Hidden -/ still outer -/
module
prelude
public /- comment -/
meta
import -- rest of line
Lean.Parser.Module.Syntax
import /- one /- two -/ three -/ all
Lean.Parser.Basic
"""
        self.assertEqual(parse_imports(text), ["Lean.Parser.Module.Syntax", "Lean.Parser.Basic"])

    def test_repeated_imports_on_one_line(self):
        self.assertEqual(parse_imports("import Init import Lean\n#check Nat\n"), ["Init", "Lean"])

    def test_import_comments_and_duplicates(self):
        self.assertEqual(parse_imports("-- import Hidden\nimport Init /- import Hidden -/\nimport Init\n"),
                         ["Init", "Init"])

    def test_supported_module_identifiers(self):
        self.assertEqual(parse_imports("import Foo.Bar'\nimport _Root.Thing_2!\nimport A.B?\n"),
                         ["Foo.Bar'", "_Root.Thing_2!", "A.B?"])

    def test_body_strings_and_quotations_are_not_imports(self):
        text = '''import Init
def text := "import Hidden"
def raw := r#"import Hidden.Raw"#
def quoted := `(command| import Hidden.Quotation)
'''
        self.assertEqual(parse_imports(text), ["Init"])

    def test_doc_comments_end_header(self):
        self.assertEqual(parse_imports("import Init\n/-! import Hidden -/\nnamespace Example\n"), ["Init"])
        self.assertEqual(parse_imports('/-- module docs --/\ndef s := "import Hidden"\n'), [])

    def test_body_modifiers_are_not_import_modifiers(self):
        self.assertEqual(parse_imports("module\npublic section\n"), [])
        self.assertEqual(parse_imports("module\nimport Init\npublic meta def f := 1\n"), ["Init"])

    def test_empty_and_prelude_headers(self):
        for text in ("", "-- comment\n", "prelude\n", "module\nprelude\n"):
            with self.subTest(text=text):
                self.assertEqual(parse_imports(text), [])

    def test_bad_header_forms_fail_with_location(self):
        cases = {
            "import": "module name",
            "import\nimport Init": "module name",
            "import Foo.": "partial names",
            "import Foo..Bar": "module name",
            "import Foo, Bar": "one module per import",
            "import Foo Bar": "one module per import",
            'import "Foo"': "module name",
            "import «Foo»": "escaped/Unicode",
            "import Foo.«Bar»": "escaped/Unicode",
            "import Δ": "escaped/Unicode",
            "private import Init": "unsupported import modifiers",
            "module\nmeta public import Init": "unsupported import modifiers",
            "module\npublic public import Init": "unsupported import modifiers",
            "module\nimport all": "module name",
            "public import Init": "require a leading module",
            "meta import Init": "require a leading module",
            "import all Init": "require a leading module",
            "module\npublic import all Init": "public import all is invalid",
            "module\nprelude\nprelude": "may occur only once",
            "import Init\nmodule": "must precede all imports",
            "\timport Init": "tabs are not permitted",
            "import /- unfinished": "unterminated block comment",
            'import "unfinished': "unterminated string literal",
            "import «unfinished": "unterminated escaped identifier",
        }
        for text, diagnostic in cases.items():
            with self.subTest(text=text):
                with self.assertRaisesRegex(ImportParseError, diagnostic) as error:
                    parse_imports(text, "fixture.lean")
                self.assertRegex(str(error.exception), r"^fixture\.lean:\d+:\d+:")

    def test_read_imports_includes_path_in_errors(self):
        with tempfile.TemporaryDirectory(prefix="ram-imports-") as temporary:
            path = Path(temporary) / "Fixture.lean"
            path.write_text("  import Init\n")
            self.assertEqual(read_imports(path), ["Init"])
            path.write_text("import Foo, Bar\n")
            with self.assertRaises(ImportParseError) as error:
                read_imports(path)
            self.assertIn(str(path), str(error.exception))

    def test_existing_ram_sources_are_supported(self):
        for path in ROOT.rglob("*.lean"):
            with self.subTest(path=path.relative_to(ROOT)):
                read_imports(path)
                strip_comments(path.read_text(), str(path))

    @unittest.skipUnless(CHECK_LEAN, "pass --check-lean for the pinned compiler comparison")
    def test_matches_pinned_lean_dependencies(self):
        lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
        headers = (
            "  import Lean.Parser.Module.Syntax\nimport Lean.Parser.Basic\n",
            "import Lean.Parser.Module.Syntax import Lean.Parser.Basic\n",
            "module\nprelude\npublic /- outer /- nested -/ -/ meta\n"
            "import\nLean.Parser.Module.Syntax\nimport all Lean.Parser.Basic\n",
        )
        with tempfile.TemporaryDirectory(prefix="ram-lean-header-") as temporary:
            for index, text in enumerate(headers):
                with self.subTest(header=index):
                    path = Path(temporary) / f"Header{index}.lean"
                    path.write_text(text)
                    result = subprocess.run([lake, "env", "lean", "--deps", str(path)],
                                            cwd=ROOT.parents[2], capture_output=True, text=True,
                                            timeout=30)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    actual = {line.split("/lib/lean/", 1)[1].removesuffix(".olean").replace("/", ".")
                              for line in result.stdout.splitlines() if "/lib/lean/" in line}
                    expected = set(parse_imports(text))
                    if "prelude" not in text:
                        expected.add("Init")
                    self.assertEqual(actual, expected, result.stdout)


class CommentTests(unittest.TestCase):
    def test_comments_are_blank_and_offsets_preserved(self):
        text = "def a := 1 -- import Hidden\n/- outer\n/- inner -/ tail -/\ndef b := 2\n"
        stripped = strip_comments(text)
        self.assertEqual(len(stripped), len(text))
        self.assertEqual([i for i, c in enumerate(stripped) if c == "\n"],
                         [i for i, c in enumerate(text) if c == "\n"])
        self.assertNotIn("Hidden", stripped)
        self.assertNotIn("inner", stripped)
        self.assertEqual(stripped.index("def b"), text.index("def b"))

    def test_normal_strings_characters_and_escaped_names_are_preserved(self):
        text = r'''def s := "-- /- text -/ \" quote"
def ch := '"'
def «/- name --» := 1
'''
        self.assertEqual(strip_comments(text), text)

    def test_raw_strings_are_preserved(self):
        text = 'def s := r##"a " /- raw -- text "##\ndef t := r"-- raw"\n'
        self.assertEqual(strip_comments(text), text)
        # An identifier ending in r is not a raw-string prefix.
        text = r'''def s := renderer"\" /- literal -/"'''
        self.assertEqual(strip_comments(text), text)

    def test_interpolation_comments_and_nested_strings(self):
        text = 'def s := s!"value { /- hidden -/ "-- visible" } /- visible -/"\n'
        stripped = strip_comments(text)
        self.assertNotIn("hidden", stripped)
        self.assertIn('"-- visible"', stripped)
        self.assertIn("/- visible -/", stripped)
        self.assertEqual(len(stripped), len(text))

    def test_unterminated_lexical_forms_fail(self):
        for text in ("/- unfinished", '"unfinished', 'r##"unfinished', "«unfinished"):
            with self.subTest(text=text):
                with self.assertRaisesRegex(ImportParseError, "unterminated"):
                    strip_comments(text)


if __name__ == "__main__":
    unittest.main()
