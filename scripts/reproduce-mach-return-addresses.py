#!/usr/bin/env python3
"""Check the concrete return-address tables against the pinned assembly generator in Rocq.

Inputs: --work-dir, the evidence records of the rtl-preallocation, ltl, linear, and mach imports,
and evidence/assembly-certificate.json. Output: the --output JSON record (the retained run is
evidence/mach-return-addresses.json).
Requires the proof build recorded in evidence/mach-import.json and Docker with the pinned Coq
image. The script loads reproduce-mach-import.py by path for BASE and UPSTREAM, and
scripts/import-mach-return-addresses.py as the importer. The Lean table must reproduce
Quadrature/Compiler/Mach/ImportedReturnAddresses.lean byte for byte.
"""

import argparse
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


REPO = Path(__file__).resolve().parents[1]


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


MACH = load_module("mach_reproduction", REPO / "scripts/reproduce-mach-import.py")
BASE = MACH.BASE


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    work = args.work_dir.resolve()
    if work == Path("/efs") or Path("/efs") in work.parents:
        raise ValueError("use local storage for compilation")
    work.mkdir(parents=True, exist_ok=True)
    dependency_paths = {
        name: REPO / "evidence" / (name + ".json")
        for name in ["rtl-preallocation-import", "ltl-import", "linear-import", "mach-import"]
    }
    dependencies = {
        name: json.loads(path.read_text()) for name, path in dependency_paths.items()
    }
    mach = dependencies["mach-import"]
    proof = Path(mach["proof_build"])
    assembly_path = REPO / "evidence/assembly-certificate.json"
    assembly = json.loads(assembly_path.read_text())
    if assembly["compcert_base_revision"] != BASE.REVISION:
        raise ValueError("unexpected CompCert revision")
    if assembly["container_image"] != BASE.IMAGE:
        raise ValueError("unexpected Rocq image")
    for name, digest in assembly["configured_source_sha256"].items():
        BASE.check_hash(proof / "compiler" / name, digest)
    for name, digest in assembly["project_proof_sha256"].items():
        BASE.check_hash(proof / "proof" / name, digest)
        if name not in BASE.GENERATED_CERTIFICATES:
            BASE.check_hash(REPO / "compcert" / name, digest)
    BASE.check_hash(proof / "proof/quadrules.v", assembly["clight_source_sha256"])
    for name, digest in MACH.UPSTREAM.items():
        BASE.check_hash(proof / "compiler" / name, digest)
    dependency_aliases = {
        "preallocation": "rtl-preallocation-import",
        "ltl": "ltl-import", "linear": "linear-import",
    }
    for name, record in dependencies.items():
        if record["assembly_evidence_sha256"] != BASE.digest(assembly_path):
            raise ValueError(f"{name} uses a different compiler build")
        for tool, digest in record["tool_source_sha256"].items():
            BASE.check_hash(REPO / tool, digest)
        for alias, dependency in dependency_aliases.items():
            expected = record.get("dependency_evidence_sha256", {}).get(
                alias, record.get(alias + "_evidence_sha256")
            )
            if expected is not None and expected != BASE.digest(dependency_paths[dependency]):
                raise ValueError(f"{name} has stale {alias} evidence")
        source = Path(record["work_dir"])
        if source.resolve() == work:
            raise ValueError("the work directory must differ from dependency directories")
        for artifact, digest in record["artifacts_sha256"].items():
            BASE.check_hash(source / artifact, digest)
            if artifact.endswith((".v", ".vo")):
                shutil.copy2(source / artifact, work / artifact)
    files = ["ExportMachReturnAddresses.v", "MachReturnAddressTable.v"]
    for name in files:
        shutil.copy2(REPO / "compcert" / name, work / name)
    (work / "RunMachAddressExport.v").write_text(
        "From Coq Require Import String.\n"
        "From CminorImport Require Import ImportedMach ExportMachReturnAddresses.\n"
        "Definition exported n := program_addresses (ImportedMach.imported_program n).\n"
        "Set Printing Width 1000000.\n"
        + "\n".join(f'Redirect "addresses{n}" Eval vm_compute in exported {n}.'
                    for n in range(1, 11)) + "\n"
    )
    docker = [
        "docker", "run", "--rm", "--network", "none", "--user", f"{os.getuid()}:{os.getgid()}",
        "-v", f"{proof}/compiler:/compcert:ro", "-v", f"{proof}/proof:/proof:ro",
        "-v", f"{proof}/export:/export:ro", "-v", f"{work}:/work:rw", "-w", "/work",
        "--entrypoint", "/home/coq/.opam/4.13.1+flambda/bin/coqc", BASE.IMAGE,
    ]
    flags = []
    for directory in ["lib", "common", "x86_64", "x86", "backend", "cfrontend",
                      "driver", "cparser"]:
        flags += ["-R", "/compcert/" + directory, "compcert." + directory]
    flags += [
        "-R", "/compcert/flocq", "Flocq", "-R", "/compcert/MenhirLib", "MenhirLib",
        "-R", "/export", "compcert.export", "-Q", "/proof", "QuadratureC",
        "-Q", "/work", "CminorImport", "-output-directory", "/work",
    ]

    def compile_file(name):
        result = subprocess.run(docker + flags + [name], text=True, capture_output=True)
        (work / (name + ".log")).write_text(result.stdout + result.stderr)
        result.check_returncode()
        print(f"Checked {name}", flush=True)
        return result.stdout

    compile_file("ExportMachReturnAddresses.v")
    generic_audit = compile_file("MachReturnAddressTable.v")
    if generic_audit.count("Closed under the global context") != 3:
        raise ValueError("the three generic theorems must have no axioms")
    compile_file("RunMachAddressExport.v")
    importer = load_module("address_import", REPO / "scripts/import-mach-return-addresses.py")
    inventory = importer.generate(
        work, work / "ImportedReturnAddresses.lean", work / "ImportedMachAddresses.v"
    )
    lean_path = REPO / "Quadrature/Compiler/Mach/ImportedReturnAddresses.lean"
    BASE.check_hash(work / "ImportedReturnAddresses.lean", BASE.digest(lean_path))
    audit = compile_file("ImportedMachAddresses.v")
    axioms = set(re.findall(r"^([A-Za-z_][A-Za-z0-9_.]*)\s*:", audit, re.MULTILINE))
    axioms.discard("Axioms")
    if axioms != BASE.EXPECTED_AXIOMS:
        raise ValueError(f"unexpected table certificate assumptions: {sorted(axioms)}")
    stems = ["ExportMachReturnAddresses", "MachReturnAddressTable",
             "RunMachAddressExport", "ImportedMachAddresses"]
    artifacts = [
        name + suffix for name in stems for suffix in [".v", ".v.log", ".vo"]
    ] + ["ImportedReturnAddresses.lean"]
    tools = [
        "scripts/import-mach-return-addresses.py",
        "scripts/reproduce-mach-return-addresses.py",
        "compcert/ExportMachReturnAddresses.v", "compcert/MachReturnAddressTable.v",
    ]
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "Concrete return-address table checked against the pinned Asmgen relation",
        "compcert_base_revision": BASE.REVISION,
        "container_image": BASE.IMAGE,
        "proof_build": str(proof), "work_dir": str(work),
        "assembly_evidence_sha256": BASE.digest(assembly_path),
        "dependency_evidence_sha256": {
            name: BASE.digest(path) for name, path in dependency_paths.items()
        },
        "dependency_artifacts_sha256": {
            name: record["artifacts_sha256"] for name, record in dependencies.items()
        },
        "dependency_work_dirs": {
            name: record["work_dir"] for name, record in dependencies.items()
        },
        "tool_source_sha256": {name: BASE.digest(REPO / name) for name in tools},
        "upstream_source_sha256": MACH.UPSTREAM,
        "lean_import_sha256": BASE.digest(lean_path),
        "rocq_generic_theorems_closed": True,
        "rocq_certificate_axioms": sorted(axioms),
        "rocq_all_entries_valid": True,
        "rocq_all_static_calls_covered": True,
        "rocq_table_equivalent_to_assembly_relation_at_calls": True,
        "rocq_certificate_theorem": "ImportedMachAddresses.table_lookup_iff",
        "lean_table_reproduced_exactly": True,
        "lean_assembly_relation_correspondence_proved": False,
        "lean_rocq_interpretation_proved": False,
        "offset_unit": "formal Asm instructions, not native machine-code bytes",
        "trust_boundary": (
            "Rocq proves that the reconstructed table exactly represents its assembly "
            "return-address relation at the imported programs' call sites. The Lean "
            "rendering is reproducible, but no interpretation between the kernels or "
            "between the Lean table and native assembly is supplied by this certificate."
        ),
        **inventory,
        "artifacts_sha256": {name: BASE.digest(work / name) for name in artifacts},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Wrote {args.output}", flush=True)


if __name__ == "__main__":
    main()
