"""Validate RAM review roles and generate/check their managed CODEOWNERS section.

The default and --check are read-only; --write updates only the managed section.
Patterns are deliberately restricted to rooted exact files and directory prefixes,
so coverage does not depend on an approximation of GitHub's wildcard semantics.
This is repository policy validation, not proof evidence or a permissions audit.
"""
from pathlib import Path
import argparse
import json
import re
import sys

REPO = Path(__file__).resolve().parents[4]
REGISTRY = "AlgoLib/Experimental/RAM/docs/reviewers.json"
ALGORITHMS = "AlgoLib/Experimental/RAM/docs/algorithms.json"
CODEOWNERS = ".github/CODEOWNERS"
RAM = "/AlgoLib/Experimental/RAM/"
BEGIN = "# BEGIN RAM REVIEW OWNERS (generated)"
END = "# END RAM REVIEW OWNERS (generated)"
LAYER_AREAS = {
    "frontend": "Language", "verification": "Verification", "library": "Library",
    "implementations": "Implementations", "compiler": "Compiler", "machine": "Machine",
    "algorithms": "Examples",
}
AREA_ORDER = (*LAYER_AREAS, "infrastructure", "experiments")
REQUIRED_PATHS = {
    area: {f"{RAM}{layer}.lean", f"{RAM}{layer}/"}
    for area, layer in LAYER_AREAS.items()
}
REQUIRED_PATHS.update({
    "infrastructure": {
        f"{RAM}Tests/", f"{RAM}docs/", f"{RAM}README.md", RAM.rstrip("/") + ".lean",
        "/AlgoLib.lean", "/.github/CODEOWNERS", "/.github/PULL_REQUEST_TEMPLATE.md",
        "/.github/CONTRIBUTING.md", "/.github/workflows/", "/README.md",
        "/lean-toolchain", "/lakefile.toml", "/lake-manifest.json", "/vendor/README.md",
        "/vendor/loom/", "/vendor/velvet/",
    },
    "experiments": {f"{RAM}Historical/", f"{RAM}Research/"},
})
LOGIN = r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,37}[A-Za-z0-9])?"
REVIEWER = re.compile(rf"@({LOGIN})(?:/[A-Za-z0-9][A-Za-z0-9_-]*)?\Z")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def reviewers(value, label, *, required=False):
    require(isinstance(value, list), f"{label}: expected a reviewer list")
    require(not required or bool(value), f"{label}: primary reviewer must not be empty")
    seen = set()
    for reviewer in value:
        match = REVIEWER.fullmatch(reviewer) if isinstance(reviewer, str) else None
        require(match is not None and "--" not in match.group(1),
                f"{label}: invalid reviewer {reviewer!r}; use @login or @org/team")
        identity = reviewer.casefold()
        require(identity not in seen, f"{label}: duplicate reviewer {reviewer}")
        seen.add(identity)
    return seen


def load_registry(repo):
    data = json.loads((repo / REGISTRY).read_text(), object_pairs_hook=unique_object)
    require(isinstance(data, dict) and set(data) ==
            {"schema_version", "fallback_area", "fallback_paths", "areas"},
            "reviewer registry fields do not match schema")
    require(type(data["schema_version"]) is int and data["schema_version"] == 1,
            "unsupported reviewer schema version")
    require(data["fallback_area"] == "infrastructure" and data["fallback_paths"] == [RAM],
            "RAM subtree fallback must route to infrastructure")
    require(isinstance(data["areas"], dict) and set(data["areas"]) == set(AREA_ORDER),
            "review areas must exactly cover the nine registered areas")
    all_paths = set()
    for area in AREA_ORDER:
        record = data["areas"][area]
        require(isinstance(record, dict) and set(record) ==
                {"primary", "backup", "responsibility", "paths"}, f"{area}: invalid fields")
        primary = reviewers(record["primary"], f"{area}.primary", required=True)
        backup = reviewers(record["backup"], f"{area}.backup")
        require(not primary & backup, f"{area}: backup must be distinct from primary")
        require(isinstance(record["responsibility"], str) and
                bool(record["responsibility"].strip()), f"{area}: responsibility must not be empty")
        paths = record["paths"]
        require(isinstance(paths, list) and all(isinstance(path, str) for path in paths),
                f"{area}: paths must be a list of strings")
        require(len(paths) == len(set(paths)), f"{area}: duplicate path")
        require(not all_paths.intersection(paths), f"{area}: path assigned to multiple areas")
        all_paths.update(paths)
        require(set(paths) == REQUIRED_PATHS[area],
                f"{area}: ownership path coverage mismatch; "
                f"missing={sorted(REQUIRED_PATHS[area] - set(paths))}, "
                f"unexpected={sorted(set(paths) - REQUIRED_PATHS[area])}")
        for pattern in paths:
            target = repo / pattern.lstrip("/")
            # --write may create CODEOWNERS, which owns its own future edits.
            if pattern == "/" + CODEOWNERS and not target.exists():
                continue
            exists = target.is_dir() if pattern.endswith("/") else target.is_file()
            require(exists, f"{area}: ownership target does not exist: {pattern}")
    return data


def rules(data):
    """Return the same ordered exact/prefix rules used in the generated file."""
    for pattern in data["fallback_paths"]:
        yield pattern, data["fallback_area"]
    for area in AREA_ORDER:
        for pattern in sorted(data["areas"][area]["paths"]):
            yield pattern, area


def area_for_path(data, path):
    """Resolve a repository-relative path with last-match CODEOWNERS semantics."""
    path = "/" + path.lstrip("/")
    found = None
    for pattern, area in rules(data):
        if (pattern.endswith("/") and path.startswith(pattern)) or path == pattern:
            found = area
    return found


def validate_algorithm_areas(repo, data):
    """Match review-area references to routing; the role checker owns the schema."""
    manifest = json.loads((repo / ALGORITHMS).read_text(), object_pairs_hook=unique_object)
    require(isinstance(manifest, dict), "algorithm registry must be an object")
    for section in ("algorithms", "fixtures"):
        records = manifest.get(section)
        require(isinstance(records, dict), f"algorithm registry: missing {section} map")
        for identity, record in records.items():
            area = record.get("review_area") if isinstance(record, dict) else None
            require(isinstance(area, str) and area in data["areas"],
                    f"{section}.{identity}: unknown review_area {area!r}")
            if section == "algorithms":
                roles = record.get("roles")
                require(isinstance(roles, dict), f"algorithms.{identity}: missing roles map")
                paths = []
                for role, files in roles.items():
                    require(isinstance(files, list) and all(isinstance(path, str) for path in files),
                            f"algorithms.{identity}.{role}: expected a list of role files")
                    paths.extend(files)
            else:
                paths = [identity]
            for path in paths:
                require(path and not any(part in ("", ".", "..") for part in path.split("/")),
                        f"{section}.{identity}: noncanonical RAM-relative path {path!r}")
                routed = area_for_path(data, RAM + path)
                require(routed == area,
                        f"{section}.{identity}: review_area {area!r} disagrees with "
                        f"CODEOWNERS area {routed!r} for {path}")


def managed_section(data):
    lines = [BEGIN, f"# Source: {REGISTRY}",
             "# Regenerate: python3 AlgoLib/Experimental/RAM/Tests/check_reviewers.py --write",
             "# Fallback first; more specific area rules follow (last matching rule wins)."]
    previous = None
    for pattern, area in rules(data):
        if area != previous:
            lines.extend(["", f"# {area}"])
            previous = area
        record = data["areas"][area]
        owners = " ".join(record["primary"] + record["backup"])
        lines.append(f"{pattern} {owners}")
    lines.extend([END, ""])
    return "\n".join(lines)


def replace_section(existing, generated):
    """Preserve unrelated ownership rules and comments byte-for-byte."""
    if BEGIN not in existing and END not in existing:
        return existing + ("\n" if existing and not existing.endswith("\n") else "") + generated
    require(existing.count(BEGIN) == 1 and existing.count(END) == 1,
            "CODEOWNERS managed markers must occur exactly once")
    start = existing.index(BEGIN)
    finish = existing.index(END) + len(END)
    require(start == 0 or existing[start - 1] == "\n", "invalid CODEOWNERS begin marker")
    require(finish > start and (finish == len(existing) or existing[finish] == "\n"),
            "invalid CODEOWNERS end marker")
    if finish < len(existing):
        finish += 1
    suffix = existing[finish:]
    require(all(not line.strip() or line.lstrip().startswith("#") for line in suffix.splitlines()),
            "CODEOWNERS ownership rules after managed section could shadow RAM routing; "
            "place unrelated rules before it")
    return existing[:start] + generated + suffix


def check(repo, *, write=False):
    data = load_registry(repo)
    validate_algorithm_areas(repo, data)
    target = repo / CODEOWNERS
    existing = target.read_text() if target.exists() else ""
    expected = replace_section(existing, managed_section(data))
    if write:
        if existing != expected:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(expected)
    else:
        require(existing == expected,
                "stale CODEOWNERS managed section; run check_reviewers.py --write")
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="read-only validation (default)")
    mode.add_argument("--write", action="store_true", help="regenerate the managed CODEOWNERS section")
    parser.add_argument("--repo", type=Path, default=REPO, help=argparse.SUPPRESS)
    args = parser.parse_args()
    try:
        check(args.repo, write=args.write)
    except (ValueError, OSError) as error:
        print(f"Reviewer ownership: {error}", file=sys.stderr)
        return 1
    print("Reviewer ownership: nine areas, exact scope, reviewer roles, and CODEOWNERS OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
