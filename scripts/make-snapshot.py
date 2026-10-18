#!/usr/bin/env python3
"""Generate a Palomar-style snapshot for ONE result from the multi-result repository.

Usage:
    scripts/make-snapshot.py RESULT --out DIR [--repo ROOT] [--json-name NAME] [--force]

RESULT is the Lean-side suffix, e.g. `Lambda` or `Chi3`.  The script expects, in the repository:
    Challenge<RESULT>.lean   Solution<RESULT>.lean
    comparator-<result>.json formalization-<result>.yaml        (<result> = RESULT lowercased,
                                                                 or --json-name)
and produces a self-contained project tree in DIR:
    Challenge.lean           (Challenge<RESULT>.lean, module names renamed)
    Solution.lean            (Solution<RESULT>.lean, module names renamed)
    comparator.json          (comparator-<result>.json, challenge_module/solution_module renamed)
    formalization.yaml       (formalization-<result>.yaml, `module:` entries renamed)
    lakefile.toml  lean-toolchain  lake-manifest.json  LICENSE  NOTICE
    <the import closure of Solution.lean inside the repository, copied verbatim>
    scripts/check-lean-sources.py

Only files in the import closure of the Solution are copied, so unrelated results, the
`CatalanParity` library and templates never reach a snapshot.  This script only GENERATES; it
neither builds nor submits anything, and it refuses to write into a non-empty DIR unless
--force is given.  Palomar rules respected by construction: `module` headers are checked by the
bundled check-lean-sources.py, which is copied along.
"""
import argparse
import json
import re
import shutil
import sys
from pathlib import Path

IMPORT_RE = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.«»']+)", re.M)

# Library declarations (lakefile) needed when a top-level source directory is copied.
LIB_BY_ROOT = {
    "OAI": ("VendoredOAI", ['globs = ["OAI.+"]']),
    "PrimeNumberTheoremAnd": ("VendoredPNT", ['globs = ["PrimeNumberTheoremAnd.+"]']),
    "CatalanMeasure": ("CatalanMeasure", ['roots = ["CatalanMeasure"]', 'globs = ["CatalanMeasure.+"]']),
    "CatalanLambda": ("CatalanLambda", ['roots = ["CatalanLambda"]', 'globs = ["CatalanLambda", "CatalanLambda.+"]']),
    "CatalanCore": ("CatalanCore", ['roots = ["CatalanCore"]', 'globs = ["CatalanCore.+"]']),
    "CatalanFrames": ("CatalanFrames", ['roots = ["CatalanFrames"]', 'globs = ["CatalanFrames.+"]']),
}


def module_file(repo: Path, module: str) -> Path | None:
    path = repo.joinpath(*module.split(".")).with_suffix(".lean")
    return path if path.is_file() else None


def import_closure(repo: Path, start: list[Path]) -> list[Path]:
    """Repository-local files reachable from `start` through import statements."""
    seen: dict[Path, None] = {}
    todo = list(start)
    while todo:
        path = todo.pop()
        if path in seen:
            continue
        seen[path] = None
        for module in IMPORT_RE.findall(path.read_text(encoding="utf-8")):
            local = module_file(repo, module)
            if local is not None:
                todo.append(local)
    return list(seen)


def rename_modules(text: str, result: str) -> str:
    text = re.sub(rf"\bChallenge{result}\b", "Challenge", text)
    return re.sub(rf"\bSolution{result}\b", "Solution", text)


def lakefile_text(repo: Path, roots: set[str], result: str) -> str:
    source = (repo / "lakefile.toml").read_text(encoding="utf-8")
    header = source.split("[[lean_lib]]", 1)[0]
    header = re.sub(r"defaultTargets\s*=\s*\[[^\]]*\]", 'defaultTargets = ["Challenge", "Solution"]', header)
    header = re.sub(r'(?m)^name\s*=\s*"[^"]*"', f'name = "Catalan{result}"', header, count=1)
    blocks = [header.rstrip() + "\n"]
    for root in sorted(roots):
        if root in LIB_BY_ROOT:
            name, lines = LIB_BY_ROOT[root]
            blocks.append("[[lean_lib]]\nname = \"%s\"\n%s\n" % (name, "\n".join(lines)))
    for name in ("Challenge", "Solution"):
        blocks.append(f'[[lean_lib]]\nname = "{name}"\nroots = ["{name}"]\n')
    return "\n".join(blocks)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("result", help="Lean-side suffix, e.g. Lambda or Chi3")
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--json-name", help="suffix of comparator-X.json / formalization-X.yaml (default: lowercased RESULT)")
    parser.add_argument("--force", action="store_true", help="allow a non-empty output directory")
    args = parser.parse_args()

    repo, out, result = args.repo.resolve(), args.out.resolve(), args.result
    short = args.json_name or result.lower()
    sources = {
        "Challenge.lean": repo / f"Challenge{result}.lean",
        "Solution.lean": repo / f"Solution{result}.lean",
        "comparator.json": repo / f"comparator-{short}.json",
        "formalization.yaml": repo / f"formalization-{short}.yaml",
    }
    missing = [str(p) for p in sources.values() if not p.is_file()]
    if missing:
        print("missing inputs:\n  " + "\n  ".join(missing), file=sys.stderr)
        return 2
    if out.exists() and any(out.iterdir()) and not args.force:
        print(f"{out} is not empty (use --force)", file=sys.stderr)
        return 2
    out.mkdir(parents=True, exist_ok=True)

    # Challenge / Solution with module names renamed.
    for target in ("Challenge.lean", "Solution.lean"):
        text = sources[target].read_text(encoding="utf-8")
        (out / target).write_text(rename_modules(text, result), encoding="utf-8", newline="")
    yaml_text = rename_modules(sources["formalization.yaml"].read_text(encoding="utf-8"), result)
    (out / "formalization.yaml").write_text(yaml_text, encoding="utf-8", newline="")

    # comparator.json at the root: module names become Challenge/Solution.
    config = json.loads(sources["comparator.json"].read_text(encoding="utf-8"))
    config["challenge_module"] = "Challenge"
    config["solution_module"] = "Solution"
    (out / "comparator.json").write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8", newline="")

    # Import closure of the Solution (and Challenge), copied verbatim.
    closure = import_closure(repo, [sources["Challenge.lean"], sources["Solution.lean"]])
    roots: set[str] = set()
    for path in closure:
        relative = path.relative_to(repo)
        if relative.name in (sources["Challenge.lean"].name, sources["Solution.lean"].name):
            continue
        roots.add(relative.parts[0])
        destination = out / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)

    # Project files.
    (out / "lakefile.toml").write_text(lakefile_text(repo, roots, result), encoding="utf-8", newline="")
    for name in ("lean-toolchain", "lake-manifest.json", "LICENSE", "NOTICE"):
        if (repo / name).is_file():
            shutil.copyfile(repo / name, out / name)
    (out / "scripts").mkdir(exist_ok=True)
    shutil.copyfile(repo / "scripts" / "check-lean-sources.py", out / "scripts" / "check-lean-sources.py")

    print(f"snapshot for {result}: {len(closure)} Lean files in the import closure -> {out}")
    print("top-level roots copied: " + ", ".join(sorted(roots)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
