#!/usr/bin/env python3
"""Reproduce the Cminor import from the checked configured CompCert build.

Inputs: the --proof-build made by check-configured-compcert.py, --work-dir, and
--assembly-evidence (evidence/assembly-certificate.json by default). Output: the --output JSON
record (the retained run is evidence/cminor-import.json).
Requires that configured proof build and Docker with the pinned Coq image.
The script checks the source hashes, computes ten exports, regenerates the Lean syntax without
overwriting Quadrature/Compiler/Cminor/Imported.lean, and checks the Rocq AST certificate. The later
reproduce-*.py stages load this module by path for IMAGE, REVISION, EXPECTED_AXIOMS, and the
hash helpers. Lean execution and accuracy proofs are checked separately by `lake build`.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


REPO = Path(__file__).resolve().parents[1]
IMAGE = "coqorg/coq@sha256:18ebf3da56e60e3ddfd7d4e51f4c53d10241a129f34e93dacbc71562dd43c57a"
REVISION = "7b1f02b09954b9b916eb2a91d283c9b5355bf172"
CMINOR_SOURCE_SHA256 = {
    "backend/Cminor.v": "736f1865f540d83299d10517584c0030538ce418a29b45cc0a77f60b69171176",
    "common/Values.v": "da172d4ac0ae9524c545a8bb0ef3b3253e2d4fb49e5919b4dee2cbd38333fddc",
    "common/Switch.v": "5dea3883ef7bfdb8a3c4299a91ca9b73f2cedf1a0ac66c1fea62026a98decce2",
    "common/AST.v": "058ade1ff1d409c5d556e3e7f5b6048492615036771886cfa121dc2dfdcde4c7",
}
EXPECTED_AXIOMS = {
    "ClassicalDedekindReals.sig_not_dec",
    "ClassicalDedekindReals.sig_forall_dec",
    "FunctionalExtensionality.functional_extensionality_dep",
    "Classical_Prop.classic",
}
GENERATED_CERTIFICATES = {
    "CertifiedPolynomial.v", "CertifiedExternal.v",
    "CertifiedPolynomialRules.v", "CertifiedStoredPolynomial.v",
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_hash(path, expected):
    if digest(path) != expected:
        raise ValueError(f"source hash mismatch: {path}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof-build", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--assembly-evidence", type=Path,
                        default=REPO / "evidence/assembly-certificate.json")
    args = parser.parse_args()
    proof = args.proof_build.resolve()
    work = args.work_dir.resolve()
    if work == Path("/efs") or Path("/efs") in work.parents:
        raise ValueError("use local storage for compilation")
    work.mkdir(parents=True, exist_ok=True)
    certificate = json.loads(args.assembly_evidence.read_text())
    if certificate["compcert_base_revision"] != REVISION:
        raise ValueError("unexpected CompCert revision")
    if certificate["container_image"] != IMAGE:
        raise ValueError("unexpected Rocq image")
    for name, expected in certificate["configured_source_sha256"].items():
        check_hash(proof / "compiler" / name, expected)
    for name, expected in certificate["project_proof_sha256"].items():
        check_hash(proof / "proof" / name, expected)
        if name not in GENERATED_CERTIFICATES:
            check_hash(REPO / "compcert" / name, expected)
    check_hash(proof / "proof/quadrules.v", certificate["clight_source_sha256"])
    # Pin the definitions used by the Lean Cminor adaptation as well as the configured passes.
    for name, expected in CMINOR_SOURCE_SHA256.items():
        check_hash(proof / "compiler" / name, expected)
    shutil.copy2(REPO / "compcert/ExportCminor.v", work / "ExportCminor.v")
    (work / "RunExport.v").write_text(
        "From Coq Require Import String.\n"
        "From QuadratureC Require Import StoredPolynomialCompilation.\n"
        "From CminorImport Require Import ExportCminor.\n"
        "From compcert Require Import Errors.\n"
        "Definition exported n :=\n"
        "  match StoredPolynomialCompilation.second_translation n with\n"
        '  | OK p => ExportCminor.program p | Error _ => "ERROR"%string end.\n'
        "Set Printing Width 1000000.\n"
        + "\n".join(f'Redirect "order{n}" Eval vm_compute in exported {n}.'
                    for n in range(1, 11)) + "\n"
    )
    docker = [
        "docker", "run", "--rm", "--network", "none", "--user", f"{os.getuid()}:{os.getgid()}",
        "-v", f"{proof}/compiler:/compcert:ro", "-v", f"{proof}/proof:/proof:ro",
        "-v", f"{proof}/export:/export:ro", "-v", f"{work}:/work:rw", "-w", "/work",
        "--entrypoint", "/home/coq/.opam/4.13.1+flambda/bin/coqc", IMAGE,
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
        return result.stdout + result.stderr

    compile_file("ExportCminor.v")
    compile_file("RunExport.v")
    spec = importlib.util.spec_from_file_location(
        "cminor_import", REPO / "scripts/import-cminor.py"
    )
    importer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(importer)
    generated = importer.generate(work, work / "Imported.lean", work / "ImportedCminor.v")
    check_hash(work / "Imported.lean", digest(REPO / "Quadrature/Compiler/Cminor/Imported.lean"))
    audit = compile_file("ImportedCminor.v")
    axioms = set(re.findall(r"^([A-Za-z_][A-Za-z0-9_.]*)\s*:", audit, re.MULTILINE))
    axioms.discard("Axioms")
    if axioms != EXPECTED_AXIOMS:
        raise ValueError(f"unexpected certificate assumptions: {sorted(axioms)}")
    artifacts = [
        "ExportCminor.v", "RunExport.v", "ImportedCminor.v", "Imported.lean",
        "ExportCminor.v.log", "RunExport.v.log", "ImportedCminor.v.log",
        "ExportCminor.vo", "RunExport.vo", "ImportedCminor.vo",
    ]
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "Concrete Cminor syntax imported into Lean and checked against the Rocq compiler",
        "compcert_base_revision": REVISION,
        "semantics_source_sha256": CMINOR_SOURCE_SHA256,
        "configured_compcert": True,
        "container_image": IMAGE,
        "assembly_evidence_sha256": digest(args.assembly_evidence),
        "reproduction_script_sha256": digest(Path(__file__)),
        "importer_sha256": digest(REPO / "scripts/import-cminor.py"),
        "serializer_sha256": digest(REPO / "compcert/ExportCminor.v"),
        "lean_import_sha256": digest(REPO / "Quadrature/Compiler/Cminor/Imported.lean"),
        "proof_build": str(proof),
        "work_dir": str(work),
        "configured_sources_checked": len(certificate["configured_source_sha256"]),
        "project_sources_checked": len(certificate["project_proof_sha256"]),
        "rocq_ast_equality_kernel_checked": True,
        "rocq_certificate_theorem": "ImportedCminor.imported_program_is_compiler_output",
        "rocq_certificate_axioms": sorted(axioms),
        "lean_syntax_reproduced_exactly": True,
        "lean_compiler_simulation_proved": False,
        "lean_rocq_encoding_correspondence_proved": False,
        "floatlib_flocq_correspondence_proved": False,
        "trust_boundary": (
            "Rocq checks the reconstructed Rocq AST against the actual compiler computation. "
            "Lean separately checks its rendered AST under the FloatLib-adapted semantics. "
            "The renderers and the interpretation between these systems are not proved."
        ),
        **generated,
        "artifacts_sha256": {name: digest(work / name) for name in artifacts},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Wrote {args.output}", flush=True)


if __name__ == "__main__":
    main()
