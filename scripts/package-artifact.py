#!/usr/bin/env python3
"""Package the project sources, including uncommitted work, as a tarball with a SHA-256 manifest.

Inputs: the git working tree, tracked and untracked files alike, minus EXCLUDED_PARTS and
EXCLUDED_SUFFIXES. Output: --output, dist/LeanQuadrature-paper.tar.gz by default, plus a
.sha256 sidecar file.
Requires git on PATH and a repository checkout.
"""

import argparse
import datetime
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile


DIRECTORIES = {"Quadrature", "compcert", "docs", "evidence", "paper", "scripts", "vendor"}
ROOT_FILES = {
    ".gitattributes", ".gitignore", "CONTRIBUTING.md", "LICENSE", "README.md",
    "Quadrature.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
}
EXCLUDED_PARTS = {".git", ".lake", ".build", "__pycache__", "dist"}
EXCLUDED_SUFFIXES = {".pyc", ".pyo", ".olean", ".ilean", ".aux", ".log", ".out"}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(root: Path, *arguments: str) -> bytes:
    return subprocess.check_output(["git", *arguments], cwd=root)


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=root / "dist" / "LeanQuadrature-paper.tar.gz")
    args = parser.parse_args()
    if not (root / "paper" / "main.pdf").is_file():
        raise SystemExit("Build paper/main.pdf first: python3 scripts/build-paper.py")
    names = set(git(root, "ls-files", "-c", "-o", "--exclude-standard", "-z")
                .decode().strip("\0").split("\0"))
    names.add("paper/main.pdf")  # Always include the compiled paper in the source archive.
    files = {}
    for name in sorted(names):
        relative = Path(name)
        if not name or relative.is_absolute() or ".." in relative.parts:
            continue
        if name not in ROOT_FILES and relative.parts[0] not in DIRECTORIES:
            continue
        if EXCLUDED_PARTS.intersection(relative.parts) or relative.suffix in EXCLUDED_SUFFIXES:
            continue
        source = root / relative
        if source.is_symlink():
            raise SystemExit(f"Refusing to package a symlink: {name}")
        if not source.exists():  # A deleted tracked file is absent from this snapshot.
            continue
        if not source.is_file():
            raise SystemExit(f"Not a regular source file: {name}")
        data = source.read_bytes()
        files[name] = (data, 0o755 if source.stat().st_mode & 0o111 else 0o644)
    status = git(root, "status", "--porcelain=v1", "--untracked-files=all").decode()
    created = datetime.datetime.now(datetime.timezone.utc).isoformat()
    manifest = {
        "format": 1,
        "created_at": created,
        "git_head": git(root, "rev-parse", "HEAD").decode().strip(),
        "includes_working_tree_changes": bool(status.strip()),
        "git_status": status.splitlines(),
        "scope": "Project source snapshot plus compiled paper; dependencies and build caches excluded.",
        "files": {name: {"sha256": digest(data), "bytes": len(data), "mode": oct(mode)}
                  for name, (data, mode) in files.items()},
    }
    files["ARTIFACT-MANIFEST.json"] = (
        (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode(), 0o644)
    epoch = int(datetime.datetime(2026, 9, 20, tzinfo=datetime.timezone.utc).timestamp())
    output = args.output.resolve()
    if output == root or output.is_relative_to(root) and output.parts[len(root.parts)] != "dist":
        raise SystemExit("Place repository-local archives under dist/.")
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("wb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=epoch) as compressed:
            with tarfile.open(fileobj=compressed, mode="w") as archive:
                for name, (data, mode) in sorted(files.items()):
                    info = tarfile.TarInfo("LeanQuadrature/" + name)
                    info.size, info.mode, info.mtime = len(data), mode, epoch
                    info.uid = info.gid = 0
                    info.uname = info.gname = ""
                    archive.addfile(info, io.BytesIO(data))
    # Check the emitted archive against its embedded manifest, not just the input list.
    with tarfile.open(output, "r:gz") as archive:
        embedded = json.load(archive.extractfile("LeanQuadrature/ARTIFACT-MANIFEST.json"))
        if len(archive.getmembers()) != len(embedded["files"]) + 1:
            raise SystemExit("Archive member count does not match its manifest.")
        for name, expected in embedded["files"].items():
            member = archive.getmember("LeanQuadrature/" + name)
            if not member.isfile() or member.mode != int(expected["mode"], 8):
                raise SystemExit(f"Unexpected archive member type or mode: {name}")
            actual = archive.extractfile(member).read()
            if digest(actual) != expected["sha256"] or len(actual) != expected["bytes"]:
                raise SystemExit(f"Archive content does not match manifest: {name}")
    checksum = digest(output.read_bytes())
    output.with_name(output.name + ".sha256").write_text(f"{checksum}  {output.name}\n")
    print(f"Archive: {output}\nFiles: {len(manifest['files'])}\nSHA-256: {checksum}")


if __name__ == "__main__":
    main()
