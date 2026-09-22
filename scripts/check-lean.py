#!/usr/bin/env python3
"""Build all Lean targets, run the three assumption audits, and record the checked inputs.

Inputs: the project sources and the local build mirror named by QUADRATURE_BUILD_ROOT. Output:
the --output JSON record, evidence/lean-quality.json by default, with logs in a temporary
directory.
Requires scripts/run-local.sh and a Lake toolchain. After `lake build` it drives
scripts/Audit.lean, scripts/AuditClight.lean, and scripts/AuditCSourceWrapper.lean, and it fails
if a project source module is missing from the audit or an input changes during the run.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def output(command: list[str], directory: Path) -> str:
    return subprocess.check_output(command, cwd=directory, text=True).strip()


def source_hashes(root: Path) -> dict[str, str]:
    # These are bounded source trees, never dependency or build directories.
    # Avoid requiring repository Git metadata in an extracted source archive.
    sources = {"Quadrature.lean"}
    for directory in ("Quadrature", "vendor/clean", "scripts"):
        sources.update(
            str(path.relative_to(root))
            for path in (root / directory).rglob("*.lean")
            if path.is_file()
        )
    sources.update(
        str(path.relative_to(root))
        for path in (root / "Quadrature").rglob("*.c")
        if path.is_file()
    )
    sources.update({
        "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        "scripts/run-local.sh", "scripts/check-lean.py",
    })
    return {name: digest(root / name) for name in sorted(sources)}


def audited_project_modules(project_log: str, sources: dict[str, str]) -> list[str]:
    """Require every project source module to occur in Lean's imported environment."""
    match = re.search(r"^Project modules: (\[.*\])$", project_log, flags=re.MULTILINE)
    if match is None:
        raise SystemExit("Missing project-module inventory in the Lean audit.")
    modules = json.loads(match[1])
    if not isinstance(modules, list) or not all(isinstance(name, str) for name in modules):
        raise SystemExit("Invalid project-module inventory in the Lean audit.")
    expected = {
        name.removesuffix(".lean").replace("/", ".")
        for name in sources
        if name == "Quadrature.lean" or name.startswith("Quadrature/") and name.endswith(".lean")
    }
    missing = expected - set(modules)
    unexpected = set(modules) - expected
    if missing or unexpected:
        details = []
        if missing:
            details.append("Source modules omitted from the audit: " + ", ".join(sorted(missing)))
        if unexpected:
            details.append("Audited modules without source files: " + ", ".join(sorted(unexpected)))
        raise SystemExit("\n".join(details))
    return sorted(expected)


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=root / "evidence/lean-quality.json")
    args = parser.parse_args()
    build = Path(os.environ.get(
        "QUADRATURE_BUILD_ROOT", "/mnt/build/robert/leanquadrature/LeanQuadrature"
    )).resolve()
    before = source_hashes(root)
    logs = Path(tempfile.mkdtemp(prefix="leanquadrature-quality-", dir="/tmp"))
    helper = str(root / "scripts/run-local.sh")
    commands = {
        "build": ["lake", "build"],
        "project-audit": ["lake", "env", "lean", "-DwarningAsError=true", "scripts/Audit.lean"],
        "clight-audit": ["lake", "env", "lean", "-DwarningAsError=true",
                         "scripts/AuditClight.lean"],
        "source-wrapper-audit": ["lake", "env", "lean", "-DwarningAsError=true",
                                 "scripts/AuditCSourceWrapper.lean"],
    }
    checks = {}
    for name, command in commands.items():
        log = logs / f"{name}.log"
        print(f"Checking {name}; log: {log}", flush=True)
        with log.open("w") as stream:
            result = subprocess.run(
                [helper, *command], cwd=root, stdout=stream, stderr=subprocess.STDOUT
            )
        if result.returncode:
            print(log.read_text()[-10000:])
            raise SystemExit(f"{name} failed with exit code {result.returncode}; see {log}")
        checks[name] = {
            "command": ["scripts/run-local.sh", *command],
            "exit_code": result.returncode,
            "log": str(log),
            "log_sha256": digest(log),
        }
    after = source_hashes(root)
    if before != after:
        raise SystemExit("Lean or C sources or build configuration changed during checking; rerun.")
    project_log = (logs / "project-audit.log").read_text()
    clight_log = (logs / "clight-audit.log").read_text()
    modules = audited_project_modules(project_log, after)
    counts = {}
    for key, pattern, text in [
        ("audited_project_theorem_count", r"Audited (\d+) Quadrature theorems", project_log),
        ("audited_private_project_theorem_count",
         r"Included (\d+) private project theorems", project_log),
        ("audited_clight_theorem_count", r"Audited (\d+) Clight theorems", clight_log),
    ]:
        match = re.search(pattern, text)
        if match is None:
            raise SystemExit(f"Missing audit result: {key}")
        counts[key] = int(match[1])
    manifest = json.loads((root / "lake-manifest.json").read_text())
    dependencies = {}
    for package in manifest["packages"]:
        if package["type"] != "git":
            continue
        # Lake quotes names such as «doc-gen4» in JSON, but not on disk.
        name = package["name"].removeprefix("«").removesuffix("»")
        checkout = build / ".lake/packages" / name
        revision = output(["git", "rev-parse", "HEAD"], checkout)
        status = output(["git", "status", "--porcelain", "--untracked-files=normal"], checkout)
        if revision != package["rev"] or status:
            raise SystemExit(f"Dependency is modified or not pinned: {name}")
        dependencies[name] = {"revision": revision, "clean": True}
    retained_logs = args.output.parent / f"{args.output.stem}-logs"
    retained_logs.mkdir(parents=True, exist_ok=True)
    for name, check in checks.items():
        target = retained_logs / f"{name}.txt"
        shutil.copyfile(logs / f"{name}.log", target)
        resolved = target.resolve()
        check["retained_log"] = (
            str(resolved.relative_to(root)) if resolved.is_relative_to(root) else str(resolved)
        )
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "Full Lean build and transitive project/private/CLean assumption audit",
        "lean_version": output([helper, "lake", "env", "lean", "--version"], root),
        "build_directory": str(build),
        "checks": checks,
        **counts,
        "audited_project_modules": modules,
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "warnings_are_errors": ["Quadrature", "CCLib", "Clightdefs"],
        "source_and_configuration_sha256": after,
        "dependency_checkouts": dependencies,
        "scope": [
            "Incremental Lake build of every default target under the pinned toolchain.",
            "Public and private theorems are selected by their defining module.",
            "Every project source module must be imported by Quadrature.",
            "All project-module theorems are audited, in any namespace.",
            "All CCLib-module theorems imported by CCLib are audited, in any namespace.",
            "Separate inspection of the original and internal-cosine wrapper assumptions.",
            "The C replacement is a Lake input dependency and is checked against its Lean source.",
            "Generated declarations contribute to theorem counts.",
            "No fresh upstream VST or Rocq compilation build is claimed.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Evidence: {args.output}\nProject theorems: {counts['audited_project_theorem_count']}"
          f"\nCLean theorems: {counts['audited_clight_theorem_count']}")


if __name__ == "__main__":
    main()
