#!/usr/bin/env python3
"""Reproduce the Linear import, before stack layout, from the checked configured CompCert build.

Inputs: --proof-build, --work-dir, --assembly-evidence, --ltl-evidence, --preallocation-evidence.
Output: the --output JSON record (the retained run is evidence/linear-import.json).
Requires the configured proof build, the earlier import records, and Docker with the pinned Coq
image. The script loads reproduce-cminor-import.py by path as BASE and scripts/import-linear.py
as the importer. The reconstructed Rocq AST is checked against the actual compiler computation,
and the Lean syntax must reproduce Quadrature/Compiler/Linear/Imported.lean byte for byte.
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
    "backend/Linear.v": "9ab166d6c4eb3afd264e0193420a7698d38a7202768fd4a465d0c869e67c54c8",
    "backend/Linearize.v": "f60b3d63a9c9bf954bbc8336fb7a0eff1b3f52c70f9b84c8be15559a8fda30ce",
    "backend/Tunneling.v": "e0396cd237d6ac317986f14cce8084ff44702f17cddf7b47a48c783680eae93d",
    "backend/CleanupLabels.v": "6f8a753cf63f6cb3cb2de72f3ced7a883c615d41cd68d37bf4b0248a5dd3fe8c",
    "backend/Debugvar.v": "e4f40eb1a46cddad3e958bf1a3bf4fb4e2b2accc8ad14067b7e4fa95537d66b1",
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
    parser.add_argument("--ltl-evidence", type=Path,
                        default=REPO / "evidence/ltl-import.json")
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
    previous = json.loads(args.ltl_evidence.read_text())
    if previous["assembly_evidence_sha256"] != BASE.digest(args.assembly_evidence):
        raise ValueError("LTL input certificate belongs to a different compiler build")
    for name, expected in previous["tool_source_sha256"].items():
        BASE.check_hash(REPO / name, expected)
    dependencies = json.loads(args.preallocation_evidence.read_text())
    if previous["preallocation_evidence_sha256"] != BASE.digest(args.preallocation_evidence):
        raise ValueError("LTL certificate refers to different preallocation dependencies")
    if dependencies["assembly_evidence_sha256"] != BASE.digest(args.assembly_evidence):
        raise ValueError("preallocation dependencies belong to a different compiler build")
    for name, expected in dependencies["tool_source_sha256"].items():
        BASE.check_hash(REPO / name, expected)
    dependency_work = Path(dependencies["work_dir"])
    for name, expected in dependencies["artifacts_sha256"].items():
        BASE.check_hash(dependency_work / name, expected)
        if name.endswith((".v", ".vo")):
            shutil.copy2(dependency_work / name, work / name)
    previous_work = Path(previous["work_dir"])
    for name, expected in previous["artifacts_sha256"].items():
        BASE.check_hash(previous_work / name, expected)
        if name.endswith((".v", ".vo")):
            shutil.copy2(previous_work / name, work / name)
    for name in ["ExportLinear.v", "EqualityLinear.v", "LinearBeforeStacking.v"]:
        shutil.copy2(REPO / "compcert" / name, work / name)
    (work / "RunLinearExport.v").write_text(
        "From Coq Require Import String.\n"
        "From compcert Require Import Linearize Errors.\n"
        "From CminorImport Require Import ImportedLTL ExportLinear LinearBeforeStacking.\n"
        "Local Transparent Linearize.enumerate_aux.\n"
        "Definition compiled_linear n := linear_prefix (ImportedLTL.imported_program n).\n"
        "Definition exported n := match compiled_linear n with\n"
        ' | OK p => ExportLinear.program p | Error _ => "ERROR"%string end.\n'
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

    for name in ["ExportLinear.v", "EqualityLinear.v", "LinearBeforeStacking.v", "RunLinearExport.v"]:
        compile_file(name)
    importer = load_module("linear_import", REPO / "scripts/import-linear.py")
    generated = importer.generate(work, work / "Imported.lean", work / "ImportedLinear.v")
    BASE.check_hash(work / "Imported.lean", BASE.digest(REPO / "Quadrature/Compiler/Linear/Imported.lean"))
    audit = compile_file("ImportedLinear.v")
    axioms = set(re.findall(r"^([A-Za-z_][A-Za-z0-9_.]*)\s*:", audit, re.MULTILINE))
    axioms.discard("Axioms")
    if axioms != BASE.EXPECTED_AXIOMS | {"Axioms.proof_irr"}:
        raise ValueError(f"unexpected certificate assumptions: {sorted(axioms)}")
    artifacts = [
        name + suffix
        for name in ["ExportLinear", "EqualityLinear", "LinearBeforeStacking", "RunLinearExport", "ImportedLinear"]
        for suffix in [".v", ".v.log", ".vo"]
    ] + ["Imported.lean"]
    tools = [
        "scripts/reproduce-cminor-import.py", "scripts/reproduce-linear-import.py",
        "scripts/import-cminor.py", "scripts/import-cminorsel.py", "scripts/import-ltl.py",
        "scripts/import-linear.py",
        "compcert/ExportLinear.v", "compcert/EqualityLinear.v", "compcert/LinearBeforeStacking.v",
    ]
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "Concrete Linear syntax checked before stack-frame layout in the configured compiler",
        "compcert_base_revision": BASE.REVISION,
        "configured_compcert": True,
        "container_image": BASE.IMAGE,
        "assembly_evidence_sha256": BASE.digest(args.assembly_evidence),
        "ltl_evidence_sha256": BASE.digest(args.ltl_evidence),
        "preallocation_evidence_sha256": BASE.digest(args.preallocation_evidence),
        "preallocation_artifacts_sha256": dependencies["artifacts_sha256"],
        "preallocation_work_dir": str(dependency_work),
        "ltl_artifacts_sha256": previous["artifacts_sha256"],
        "ltl_work_dir": str(previous_work),
        "tool_source_sha256": {name: BASE.digest(REPO / name) for name in tools},
        "upstream_source_sha256": UPSTREAM,
        "lean_import_sha256": BASE.digest(REPO / "Quadrature/Compiler/Linear/Imported.lean"),
        "proof_build": str(proof),
        "work_dir": str(work),
        "configured_sources_checked": len(certificate["configured_source_sha256"]),
        "project_sources_checked": len(certificate["project_proof_sha256"]),
        "rocq_ast_equality_kernel_checked": True,
        "rocq_certificate_theorem": "ImportedLinear.imported_program_is_compiler_output",
        "rocq_certificate_axioms": sorted(axioms),
        "rocq_actual_pipeline_split_checked": True,
        "rocq_compiler_consumes_imported_program_checked": True,
        "pipeline_certificate": "ImportedLinear.compiler_uses_imported_program",
        "configuration_note": "The existing configured compiler tunnels branches, linearizes the graph with its checked concrete enumeration, and removes unused labels. Debug information is disabled; no compiler configuration was changed.",
        "lean_syntax_reproduced_exactly": True,
        "lean_general_linearization_proved": False,
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
