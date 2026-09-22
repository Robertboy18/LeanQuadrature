"""Pinned upstream sources shared by the independent quadrature checks.

Inputs: SOURCES maps each file name to its raw URL at REVISION (simple_cfem) or LAPROOF_REVISION
(LAProof) and its SHA-256. Output: read_source returns the file bytes after checking that hash.
Requires network access, unless a directory holding already downloaded copies is given.
"""

import hashlib
from pathlib import Path
import urllib.request


REVISION = "e79a28dba247db9f934289bcf4e4debd5eebc884"
LAPROOF_REVISION = "4286f63f456e47ea9da25d9474ca7f3e20523784"

_CFEM = f"https://raw.githubusercontent.com/VeriNum/simple_cfem/{REVISION}"
_LAPROOF = f"https://raw.githubusercontent.com/VeriNum/LAProof/{LAPROOF_REVISION}"

SOURCES = {
    "quadrules.c": (
        f"{_CFEM}/src/quadrules.c",
        "fb774551d772092f9ecba6dca51952ec9baaf4c3cdc27962f65d69818b2aeb91",
    ),
    "quadrules.h": (
        f"{_CFEM}/src/quadrules.h",
        "d71440c24db6b5a5509848d6828ccaeb18b7853f2e238860afc24a13b39df112",
    ),
    "quadmodel.v": (
        f"{_CFEM}/proof/quadmodel.v",
        "ba025818e6e14f12bffbe7eb786af8cf13d2f1dc7948088adb5dcda20245edd0",
    ),
    "quadmodel_accuracy.v": (
        f"{_CFEM}/proof/quadmodel_accuracy.v",
        "bf23cfaf171e423c39f5d0004e4d056e1b7bed812bdf3a106d2ecfc350d19b4d",
    ),
    "laproof-common.v": (
        f"{_LAPROOF}/accuracy_proofs/common.v",
        "4eb465d3694740e09e8da29f91332292309db6336407f079aef8e04bf8f9ec35",
    ),
}


def read_source(name: str, directory: Path | None = None) -> bytes:
    """Read a named source, rejecting changed local files and changed downloads."""
    url, expected = SOURCES[name]
    if directory is None:
        with urllib.request.urlopen(url, timeout=60) as response:
            content = response.read()
    else:
        content = (directory / name).read_bytes()
    actual = hashlib.sha256(content).hexdigest()
    if actual != expected:
        raise RuntimeError(f"Upstream SHA-256 mismatch for {name}: {actual}")
    return content
