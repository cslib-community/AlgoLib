"""Generate inventories and import diagrams from checked module metadata.

Module ownership/status lives in docs/modules.json. Summaries come from Lean module
headings. Explanatory README prose outside marked sections remains handwritten.
Use --check in CI; omit it to regenerate after intentional metadata/source changes.
"""
from pathlib import Path
import argparse
import collections
import json
import re

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "AlgoLib.Experimental.RAM."
BEGIN = "<!-- BEGIN GENERATED MODULE INDEX -->"
END = "<!-- END GENERATED MODULE INDEX -->"
LAYERS = ("Language", "Verification", "Library", "Implementations", "Compiler", "Machine", "Examples",
          "Historical", "Research", "Tests")


def generate():
    records = json.loads((ROOT / "docs/modules.json").read_text())["modules"]
    actual = {str(p.relative_to(ROOT)) for p in ROOT.rglob("*.lean")}
    assert actual == set(records), ("module metadata mismatch", actual - set(records), set(records) - actual)
    modules = {PREFIX + path[:-5].replace("/", "."): path for path in records}
    summaries, imports = {}, {}
    for path, record in records.items():
        assert record["layer"] in LAYERS, (path, "unknown layer")
        physical = Path(path).parts[0] if "/" in path else Path(path).stem
        assert record["layer"] == physical, (path, "metadata does not match physical layer")
        assert record["status"] in {"public", "internal", "compatibility", "historical", "research", "test"}
        if record["entrypoint"]:
            assert record["layer"] in LAYERS[:7] and path == record["layer"] + ".lean"
            assert record["status"] == "public", (path, "entry point must be public")
        expected_status = {"Historical": "historical", "Research": "research", "Tests": "test"}
        if record["layer"] in expected_status:
            assert record["status"] == expected_status[record["layer"]], (path, "inconsistent module status")
        text = (ROOT / path).read_text()
        block = re.search(r"/-!(.*?)-/", text, re.S)
        assert block, (path, "missing module documentation")
        heading = re.search(r"^# ([^\n]+)", block[1], re.M)
        summary = heading[1] if heading else block[1].strip().splitlines()[0]
        summaries[path] = summary.replace("|", "\\|")
        imports[path] = [modules[m] for m in re.findall(r"^import (\S+)", text, re.M) if m in modules]
    results = {}
    for layer in LAYERS:
        paths = [p for p, r in records.items() if r["layer"] == layer]
        entry = [p for p in paths if records[p]["entrypoint"]]
        if layer not in {"Historical", "Research", "Tests"}:
            assert entry == [layer + ".lean"], (layer, "requires one canonical public entry")
        lines = [BEGIN, "", "## Module index (generated)", "",
                 "Status and ownership come from `docs/modules.json`; summaries come from module docstrings.", ""]
        if entry:
            lines += [f"**Preferred import:** `AlgoLib.Experimental.RAM.{layer}`.", ""]
        lines += ["| Module | Status | Responsibility |", "| --- | --- | --- |"]
        for path in sorted(paths):
            target = "../" + path if "/" not in path else path[len(layer) + 1:]
            label = Path(path).stem if "/" not in path else path[len(layer) + 1:]
            lines += [f"| [{label}]({target}) | {records[path]['status']} | {summaries[path]} |"]
        lines += ["", END]
        readme = ROOT / layer / "README.md"
        text = readme.read_text()
        block = "\n".join(lines)
        if BEGIN in text:
            assert text.count(BEGIN) == text.count(END) == 1
            text = re.sub(re.escape(BEGIN) + r".*?" + re.escape(END), lambda _: block, text, flags=re.S)
        else:
            text = text.rstrip() + "\n\n" + block + "\n"
        results[readme] = text
    counts = collections.Counter()
    for source, deps in imports.items():
        for target in deps:
            a, b = records[source]["layer"], records[target]["layer"]
            if a != b: counts[a, b] += 1
    lines = ["# Dependency map (generated)", "", "Arrows mean **imports**, labelled with the number of direct module imports.",
             "Aggregation can show cycles between layers (for example frontend convenience imports);",
             "the actual module graph is checked to be acyclic. This is a dependency map, not an execution pipeline.", "", "```mermaid", "flowchart LR"]
    lines += [f'  {a} -->|"{n}"| {b}' for (a,b),n in sorted(counts.items())]
    lines += ["```", "", "## Public entries", "", "| Import | Direct dependencies |", "| --- | --- |"]
    for path,record in records.items():
        if record["entrypoint"]:
            links=", ".join(f"[{d}](../{d})" for d in imports[path])
            lines += [f"| [{record['layer']}](../{path}) | {links} |"]
    lines += ["", "## Complete module imports", "", "| Module | Direct local imports |", "| --- | --- |"]
    for path in sorted(records):
        links=", ".join(f"[{d}](../{d})" for d in imports[path]) or "None"
        lines += [f"| [{path}](../{path}) | {links} |"]
    results[ROOT / "docs/DEPENDENCIES.md"]="\n".join(lines)+"\n"
    exports=json.loads((ROOT / "docs/public-exports.json").read_text())
    actual_exports = set()
    for path, record in records.items():
        if record["entrypoint"]:
            for namespace, source, names in re.findall(
                r"namespace (\S+)\nexport (\S+) \(([^)]*)\)", (ROOT / path).read_text()):
                for name in names.split():
                    actual_exports.add((namespace + "." + name, source + "." + name, record["layer"]))
    declared_exports = {(x["name"], x["original"], x["entry"]) for x in exports}
    assert actual_exports == declared_exports, ("public export metadata disagrees with source",
                                               actual_exports ^ declared_exports)
    lines=["# Public names (generated)", "", "Preferred names resolve to the same declarations as their compatibility spellings.",
           "This is a staged alias migration; implementation declaration namespaces have not been renamed.",
           "See [the evolution policy](PUBLIC-API.md).", "", "| Preferred name | Compatibility spelling | Import |", "| --- | --- | --- |"]
    for item in exports:
        entry=ROOT/(item['entry']+'.lean')
        assert entry.exists()
        lines += [f"| `{item['name'].removeprefix(PREFIX)}` | `{item['original'].removeprefix(PREFIX)}` | `{PREFIX}{item['entry']}` |"]
    results[ROOT/'docs/PUBLIC-NAMES.md']='\n'.join(lines)+'\n'
    return results


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    for path,text in generate().items():
        if args.check:
            assert path.exists() and path.read_text()==text, (path,'stale generated navigation; run generate_navigation.py')
        else:path.write_text(text)
    print('Generated navigation: metadata, inventories, public names and import diagrams OK')

if __name__=='__main__':main()
