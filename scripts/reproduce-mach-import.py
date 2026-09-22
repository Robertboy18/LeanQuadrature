#!/usr/bin/env python3
"""Reproduce the Mach import, after stack layout, from the checked configured CompCert build.

Inputs: --proof-build, --work-dir, --assembly-evidence, --ltl-evidence, --preallocation-evidence,
--linear-evidence. Output: the --output JSON record (the retained run is evidence/mach-import.json).
Requires the configured proof build, the earlier import records, and Docker with the pinned Coq
image. The script loads reproduce-cminor-import.py by path as BASE and scripts/import-mach.py as
the importer. UPSTREAM lists the backend source hashes that reproduce-mach-return-addresses.py and
reproduce-asm-import.py reuse. The reconstructed Rocq AST is checked against the actual compiler
computation, and the Lean syntax must reproduce Quadrature/Compiler/Mach/Imported.lean byte for byte.
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
    "backend/Mach.v": "6490ee941a7892a90c5c241d7799d3a046d9e829fae63182e9c773d9c4fb45db",
    "backend/Stacking.v": "9a20c2d04c4e5287510b9c13b49e8c936761468d5ff69fdee46ae3db188ce666",
    "backend/Bounds.v": "dee68d14fc48b060535503b1f34123bead416e2a186d4e707fe05759a88fb335",
    "x86/Stacklayout.v": "9a40f7a4c54f879d079e3c108b2faa2b7f69d4d6ee7a0dc122d6d492471d9b40",
    "backend/Linear.v": "9ab166d6c4eb3afd264e0193420a7698d38a7202768fd4a465d0c869e67c54c8",
    "backend/Locations.v": "650cb788322b82a9d08c60a58f605cd93f73fb4faac92e526f4f960f8093e2b5",
    "x86/Machregs.v": "e012fb3000a6da6670f7320771332ced5d81e2feafd94dc177375e8044071cb6",
    "x86/Conventions1.v": "80495e4830a02aa5ff094549691b681286bebc7fabfe04076a0a6c197d25be8e",
    "x86_64/Archi.v": "6f6eaad80236ff892021318efcecffb957f2ee36bb6e763c6eda8217bc5205de",
    "x86/Asmgen.v": "158957f76f7f0c04c99547bbab87e203d5227c81cf1818de8e35d4c4fd8e8e92",
    "x86/Asmgenproof.v": "3fd12d37e53a15ae7bb9210eeb6e6163bbb006ecd80c946303801afc5bba90d4",
    "backend/Asmgenproof0.v": "ce401b20dbf86e691973ef66ce41974293a4370cb729027aae62afa1c429c7f0",
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
    parser.add_argument("--ltl-evidence", type=Path,
                        default=REPO / "evidence/ltl-import.json")
    parser.add_argument("--preallocation-evidence", type=Path,
                        default=REPO / "evidence/rtl-preallocation-import.json")
    parser.add_argument("--linear-evidence", type=Path,
                        default=REPO / "evidence/linear-import.json")
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
    dependency_paths = {
        "preallocation": args.preallocation_evidence,
        "ltl": args.ltl_evidence,
        "linear": args.linear_evidence,
    }
    dependency_records = {
        name: json.loads(path.read_text()) for name, path in dependency_paths.items()
    }
    for name, record in dependency_records.items():
        if record["assembly_evidence_sha256"] != BASE.digest(args.assembly_evidence):
            raise ValueError(f"{name} input belongs to a different compiler build")
        for tool, expected in record["tool_source_sha256"].items():
            BASE.check_hash(REPO / tool, expected)
        for dependency, path in dependency_paths.items():
            key = dependency + "_evidence_sha256"
            if key in record and record[key] != BASE.digest(path):
                raise ValueError(f"{name} refers to different {dependency} dependencies")
        dependency_work = Path(record["work_dir"])
        for artifact, expected in record["artifacts_sha256"].items():
            BASE.check_hash(dependency_work / artifact, expected)
            if artifact.endswith((".v", ".vo")):
                shutil.copy2(dependency_work / artifact, work / artifact)
    for name in ["ExportMach.v", "EqualityMach.v", "MachAfterStacking.v", "MachReturnAddresses.v"]:
        shutil.copy2(REPO / "compcert" / name, work / name)
    (work / "RunMachExport.v").write_text(
        "From Coq Require Import String.\n"
        "From compcert Require Import Stacking Errors.\n"
        "From CminorImport Require Import ImportedLinear ExportMach MachAfterStacking.\n"
        "Definition compiled_mach n := Stacking.transf_program (ImportedLinear.imported_program n).\n"
        "Definition exported n := match compiled_mach n with\n"
        ' | OK p => ExportMach.program p | Error _ => "ERROR"%string end.\n'
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

    for name in ["ExportMach.v", "EqualityMach.v", "MachAfterStacking.v",
                 "MachReturnAddresses.v", "RunMachExport.v"]:
        compile_file(name)
    importer = load_module("mach_import", REPO / "scripts/import-mach.py")
    generated = importer.generate(work, work / "Imported.lean", work / "ImportedMach.v")
    BASE.check_hash(work / "Imported.lean", BASE.digest(REPO / "Quadrature/Compiler/Mach/Imported.lean"))
    audit = compile_file("ImportedMach.v")
    axioms = set(re.findall(r"^([A-Za-z_][A-Za-z0-9_.]*)\s*:", audit, re.MULTILINE))
    axioms.discard("Axioms")
    if axioms != BASE.EXPECTED_AXIOMS | {"Axioms.proof_irr"}:
        raise ValueError(f"unexpected certificate assumptions: {sorted(axioms)}")
    artifacts = [
        name + suffix
        for name in ["ExportMach", "EqualityMach", "MachAfterStacking", "MachReturnAddresses",
                     "RunMachExport", "ImportedMach"]
        for suffix in [".v", ".v.log", ".vo"]
    ] + ["Imported.lean"]
    tools = [
        "scripts/reproduce-cminor-import.py", "scripts/reproduce-mach-import.py",
        "scripts/import-cminor.py", "scripts/import-cminorsel.py", "scripts/import-ltl.py",
        "scripts/import-mach.py",
        "compcert/ExportMach.v", "compcert/EqualityMach.v", "compcert/MachAfterStacking.v",
        "compcert/MachReturnAddresses.v",
    ]
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "Concrete Mach syntax checked after stack-frame layout in the configured compiler",
        "compcert_base_revision": BASE.REVISION,
        "configured_compcert": True,
        "container_image": BASE.IMAGE,
        "assembly_evidence_sha256": BASE.digest(args.assembly_evidence),
        "dependency_evidence_sha256": {
            name: BASE.digest(path) for name, path in dependency_paths.items()
        },
        "dependency_artifacts_sha256": {
            name: record["artifacts_sha256"] for name, record in dependency_records.items()
        },
        "dependency_work_dirs": {
            name: record["work_dir"] for name, record in dependency_records.items()
        },
        "tool_source_sha256": {name: BASE.digest(REPO / name) for name in tools},
        "upstream_source_sha256": UPSTREAM,
        "lean_import_sha256": BASE.digest(REPO / "Quadrature/Compiler/Mach/Imported.lean"),
        "proof_build": str(proof),
        "work_dir": str(work),
        "configured_sources_checked": len(certificate["configured_source_sha256"]),
        "project_sources_checked": len(certificate["project_proof_sha256"]),
        "rocq_ast_equality_kernel_checked": True,
        "rocq_certificate_theorem": "ImportedMach.imported_program_is_compiler_output",
        "rocq_certificate_axioms": sorted(axioms),
        "rocq_actual_pipeline_split_checked": True,
        "rocq_compiler_consumes_imported_program_checked": True,
        "pipeline_certificate": "ImportedMach.compiler_uses_imported_program",
        "rocq_every_internal_call_return_address_checked": True,
        "rocq_return_address_certificate": "ImportedMach.imported_call_return_addresses",
        "return_address_scope": (
            "For each call continuation in every internal function of all ten programs, "
            "the executable predictor succeeds and its offset is the unique value allowed "
            "by Asmgenproof0.return_address_offset. The offset counts formal Asm instructions; "
            "this is not a native machine-code byte-address certificate or a Lean theorem."
        ),
        "configuration_note": "The existing configured compiler lays out each stack frame, inserts callee-save stores and loads, and translates abstract slots into byte offsets. No compiler configuration was changed.",
        "lean_syntax_reproduced_exactly": True,
        "lean_general_stacking_proved": False,
        "lean_mach_execution_correctness_proved": False,
        "lean_mach_return_address_correspondence_proved": False,
        "lean_rocq_encoding_correspondence_proved": False,
        "floatlib_flocq_correspondence_proved": False,
        "trust_boundary": (
            "Rocq checks equality of its reconstructed AST and the compiler computation, "
            "including constants with different validity proofs. Lean typechecks the separately "
            "rendered syntax. Mach execution correctness is not established by this import. "
            "The renderers and the interpretation between these systems remain unproved."
        ),
        **generated,
        "artifacts_sha256": {name: BASE.digest(work / name) for name in artifacts},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Wrote {args.output}", flush=True)


if __name__ == "__main__":
    main()
