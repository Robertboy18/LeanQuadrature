#!/usr/bin/env python3
"""Reproduce the LTL import, after register allocation, from the checked configured CompCert build.

Inputs: --proof-build, --work-dir, --assembly-evidence, --preallocation-evidence. Output: the
--output JSON record (the retained run is evidence/ltl-import.json).
Requires the configured proof build, the preallocation import record, and Docker with the pinned
Coq image. The script loads reproduce-cminor-import.py by path as BASE and scripts/import-ltl.py
as the importer. The reconstructed Rocq AST is checked against the actual compiler computation,
and the Lean syntax must reproduce Quadrature/Compiler/LTL/Imported.lean byte for byte.
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


BASE = load_module("cminor_reproduction", REPO / "scripts/reproduce-cminor-import.py")
UPSTREAM = {
    "backend/LTL.v": "a40bff70372f0adcc82017a275bc7a54b16b9b76451621eb17581fcd835f45ad",
    "backend/Locations.v": "650cb788322b82a9d08c60a58f605cd93f73fb4faac92e526f4f960f8093e2b5",
    "x86/Machregs.v": "e012fb3000a6da6670f7320771332ced5d81e2feafd94dc177375e8044071cb6",
    "x86/Conventions1.v": "80495e4830a02aa5ff094549691b681286bebc7fabfe04076a0a6c197d25be8e",
    "x86_64/Archi.v": "6f6eaad80236ff892021318efcecffb957f2ee36bb6e763c6eda8217bc5205de",
    "backend/Allocation.v": "2f08c3e3c2c2d470b2a116a349bb8d4eac39f447be5dfdabc111b49ff3b464ec",
    "driver/Compiler.v": "f2828c5fea036927a9e57e9074b6ff1359393fc6faef3322968987f6ad9a2534",
    "driver/Compopts.v": "ac48681209a684458594376f5a53b4a7facf874349ab237bcb0d6e1814832172",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof-build", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--assembly-evidence", type=Path,
                        default=REPO / "evidence/assembly-certificate.json")
    parser.add_argument("--preallocation-evidence", type=Path,
                        default=REPO / "evidence/rtl-preallocation-import.json")
    args = parser.parse_args()
    proof, work = args.proof_build.resolve(), args.work_dir.resolve()
    if work == Path("/efs") or Path("/efs") in work.parents:
        raise ValueError("use local storage for compilation")
    work.mkdir(parents=True, exist_ok=True)
    certificate = json.loads(args.assembly_evidence.read_text())
    if certificate["compcert_base_revision"] != BASE.REVISION:
        raise ValueError("unexpected CompCert revision")
    if certificate["container_image"] != BASE.IMAGE:
        raise ValueError("unexpected Rocq image")
    for name, expected in certificate["configured_source_sha256"].items():
        BASE.check_hash(proof / "compiler" / name, expected)
    for name, expected in certificate["project_proof_sha256"].items():
        BASE.check_hash(proof / "proof" / name, expected)
        if name not in BASE.GENERATED_CERTIFICATES:
            BASE.check_hash(REPO / "compcert" / name, expected)
    BASE.check_hash(proof / "proof/quadrules.v", certificate["clight_source_sha256"])
    for name, expected in UPSTREAM.items():
        BASE.check_hash(proof / "compiler" / name, expected)
    previous = json.loads(args.preallocation_evidence.read_text())
    if previous["assembly_evidence_sha256"] != BASE.digest(args.assembly_evidence):
        raise ValueError("allocation input certificate belongs to a different compiler build")
    for name, expected in previous["tool_source_sha256"].items():
        BASE.check_hash(REPO / name, expected)
    previous_work = Path(previous["work_dir"])
    for name, expected in previous["artifacts_sha256"].items():
        BASE.check_hash(previous_work / name, expected)
        if name.endswith((".v", ".vo")):
            shutil.copy2(previous_work / name, work / name)
    for name in ["ExportLTL.v", "EqualityLTL.v", "LTLAfterAllocation.v"]:
        shutil.copy2(REPO / "compcert" / name, work / name)
    (work / "RunLTLExport.v").write_text(
        "From Coq Require Import String.\n"
        "From compcert Require Import Allocation Errors.\n"
        "From CminorImport Require Import ImportedPreallocation ExportLTL.\n"
        "Local Transparent Allocation.regalloc Allocation.choose_allocation\n"
        "  Allocation.allocation_candidates.\n"
        "Definition allocated n :=\n"
        "  Allocation.transf_program (ImportedPreallocation.imported_program n).\n"
        "Definition exported n := match allocated n with\n"
        ' | OK p => ExportLTL.program p | Error _ => "ERROR"%string end.\n'
        "Set Printing Width 1000000.\n"
        + "\n".join(f'Redirect "order{n}" Eval vm_compute in exported {n}.'
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

    def compile_file(filename):
        result = subprocess.run(docker + flags + [filename], text=True, capture_output=True)
        (work / (filename + ".log")).write_text(result.stdout + result.stderr)
        result.check_returncode()
        print(f"Checked {filename}", flush=True)
        # Print Assumptions is on stdout; diagnostics on stderr are retained in the log.
        return result.stdout

    for name in ["ExportLTL.v", "EqualityLTL.v", "LTLAfterAllocation.v", "RunLTLExport.v"]:
        compile_file(name)
    importer = load_module("ltl_import", REPO / "scripts/import-ltl.py")
    generated = importer.generate(work, work / "Imported.lean", work / "ImportedLTL.v")
    BASE.check_hash(work / "Imported.lean", BASE.digest(REPO / "Quadrature/Compiler/LTL/Imported.lean"))
    audit = compile_file("ImportedLTL.v")
    axioms = set(re.findall(r"^([A-Za-z_][A-Za-z0-9_.]*)\s*:", audit, re.MULTILINE))
    axioms.discard("Axioms")
    if axioms != BASE.EXPECTED_AXIOMS | {"Axioms.proof_irr"}:
        raise ValueError(f"unexpected certificate assumptions: {sorted(axioms)}")
    artifacts = [
        name + suffix
        for name in ["ExportLTL", "EqualityLTL", "LTLAfterAllocation", "RunLTLExport", "ImportedLTL"]
        for suffix in [".v", ".v.log", ".vo"]
    ] + ["Imported.lean"]
    tools = [
        "scripts/reproduce-cminor-import.py", "scripts/reproduce-ltl-import.py",
        "scripts/import-cminor.py", "scripts/import-cminorsel.py", "scripts/import-ltl.py",
        "compcert/ExportLTL.v", "compcert/EqualityLTL.v", "compcert/LTLAfterAllocation.v",
    ]
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "Concrete LTL syntax checked at the configured register-allocation output",
        "compcert_base_revision": BASE.REVISION,
        "configured_compcert": True,
        "container_image": BASE.IMAGE,
        "assembly_evidence_sha256": BASE.digest(args.assembly_evidence),
        "preallocation_evidence_sha256": BASE.digest(args.preallocation_evidence),
        "preallocation_artifacts_sha256": previous["artifacts_sha256"],
        "preallocation_work_dir": str(previous_work),
        "tool_source_sha256": {name: BASE.digest(REPO / name) for name in tools},
        "upstream_source_sha256": UPSTREAM,
        "lean_import_sha256": BASE.digest(REPO / "Quadrature/Compiler/LTL/Imported.lean"),
        "proof_build": str(proof),
        "work_dir": str(work),
        "configured_sources_checked": len(certificate["configured_source_sha256"]),
        "project_sources_checked": len(certificate["project_proof_sha256"]),
        "rocq_ast_equality_kernel_checked": True,
        "rocq_certificate_theorem": "ImportedLTL.imported_program_is_compiler_output",
        "rocq_certificate_axioms": sorted(axioms),
        "rocq_actual_pipeline_split_checked": True,
        "rocq_compiler_consumes_imported_program_checked": True,
        "pipeline_certificate": "ImportedLTL.compiler_uses_imported_program",
        "configuration_note": "The existing configured allocator chooses among 22 stored function candidates and validates each selection; the compiler configuration is unchanged.",
        "lean_syntax_reproduced_exactly": True,
        "lean_general_register_allocation_proved": False,
        "lean_rocq_encoding_correspondence_proved": False,
        "floatlib_flocq_correspondence_proved": False,
        "trust_boundary": (
            "Rocq checks equality of its reconstructed AST and the compiler computation, "
            "including constants with different validity proofs. Lean checks the separately "
            "rendered syntax and its adapted execution semantics. The renderers and the "
            "interpretation between these systems remain unproved."
        ),
        **generated,
        "artifacts_sha256": {name: BASE.digest(work / name) for name in artifacts},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Wrote {args.output}", flush=True)


if __name__ == "__main__":
    main()
