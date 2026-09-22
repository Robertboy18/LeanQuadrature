#!/usr/bin/env python3
"""Reproduce the instruction-selection import from the checked configured CompCert build.

Inputs: --proof-build, --work-dir, --assembly-evidence. Output: the --output JSON record (the
retained run is evidence/cminorsel-import.json).
Requires the configured proof build and Docker with the pinned Coq image. The script loads
reproduce-cminor-import.py by path as BASE and scripts/import-cminorsel.py as the importer. The
reconstructed Rocq AST is checked against the actual compiler computation, and the Lean syntax
must reproduce Quadrature/Compiler/CminorSel/Imported.lean byte for byte.
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
    "backend/CminorSel.v": "b9d33bbb4c86656a38e693e0f9486347bbf4066fa779bd758412ab6f6478d183",
    "x86/Op.v": "6c306df6525a56609a4776e9661e196cb1c9b71b9b8121563f9aa2b9ca3f0ff5",
    "x86/SelectLong.v": "3f31a5f965e95482599d4a9541006fbe475230c813dfb0ac008f3ac8aa2e69ec",
    "common/Values.v": "da172d4ac0ae9524c545a8bb0ef3b3253e2d4fb49e5919b4dee2cbd38333fddc",
    "lib/Integers.v": "c0eec9e99de86765f62a2cd13902f62908f7c5fb199f5bc713c9fcb5e8924a02",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof-build", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--assembly-evidence", type=Path,
                        default=REPO / "evidence/assembly-certificate.json")
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
    for name in ["ExportCminor.v", "ExportCminorSel.v", "EqualityCminorSel.v"]:
        shutil.copy2(REPO / "compcert" / name, work / name)
    (work / "RunExport.v").write_text(
        "From Coq Require Import String.\n"
        "From QuadratureC Require Import StoredPolynomialCompilation.\n"
        "From CminorImport Require Import ExportCminorSel.\n"
        "From compcert Require Import Errors Selection SelectOp Compopts.\n"
        "Local Transparent SelectOp.symbol_is_relocatable Compopts.optim_for_size\n"
        "  Selection.compile_switch Selection.if_conversion_heuristic.\n"
        "Definition selected n := match StoredPolynomialCompilation.second_translation n with\n"
        " | OK p => Selection.sel_program p | Error e => Error e end.\n"
        "Definition exported n := match selected n with\n"
        ' | OK p => ExportCminorSel.program p | Error _ => "ERROR"%string end.\n'
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
        return result.stdout + result.stderr

    for name in ["ExportCminor.v", "ExportCminorSel.v", "EqualityCminorSel.v", "RunExport.v"]:
        compile_file(name)
    importer = load_module("cminorsel_import", REPO / "scripts/import-cminorsel.py")
    generated = importer.generate(work, work / "Imported.lean", work / "ImportedCminorSel.v")
    BASE.check_hash(work / "Imported.lean", BASE.digest(REPO / "Quadrature/Compiler/CminorSel/Imported.lean"))
    audit = compile_file("ImportedCminorSel.v")
    axioms = set(re.findall(r"^([A-Za-z_][A-Za-z0-9_.]*)\s*:", audit, re.MULTILINE))
    axioms.discard("Axioms")
    if axioms != BASE.EXPECTED_AXIOMS:
        raise ValueError(f"unexpected certificate assumptions: {sorted(axioms)}")
    artifacts = [
        name + suffix
        for name in ["ExportCminor", "ExportCminorSel", "EqualityCminorSel",
                     "RunExport", "ImportedCminorSel"]
        for suffix in [".v", ".v.log", ".vo"]
    ] + ["Imported.lean"]
    tools = [
        "scripts/reproduce-cminor-import.py", "scripts/reproduce-cminorsel-import.py",
        "scripts/import-cminor.py", "scripts/import-cminorsel.py",
        "compcert/ExportCminor.v", "compcert/ExportCminorSel.v",
        "compcert/EqualityCminorSel.v",
    ]
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "Concrete CminorSel syntax checked against configured instruction selection",
        "compcert_base_revision": BASE.REVISION,
        "configured_compcert": True,
        "container_image": BASE.IMAGE,
        "assembly_evidence_sha256": BASE.digest(args.assembly_evidence),
        "tool_source_sha256": {name: BASE.digest(REPO / name) for name in tools},
        "upstream_source_sha256": UPSTREAM,
        "lean_import_sha256": BASE.digest(REPO / "Quadrature/Compiler/CminorSel/Imported.lean"),
        "proof_build": str(proof),
        "work_dir": str(work),
        "configured_sources_checked": len(certificate["configured_source_sha256"]),
        "project_sources_checked": len(certificate["project_proof_sha256"]),
        "rocq_ast_equality_kernel_checked": True,
        "rocq_certificate_theorem": "ImportedCminorSel.imported_program_is_compiler_output",
        "rocq_certificate_axioms": sorted(axioms),
        "lean_syntax_reproduced_exactly": True,
        "lean_complete_selection_pass_proved": False,
        "lean_rocq_encoding_correspondence_proved": False,
        "floatlib_flocq_correspondence_proved": False,
        "trust_boundary": (
            "Rocq checks equality of its reconstructed AST and the compiler computation, "
            "including constants with different validity proofs. Lean checks the separately "
            "rendered syntax and its own expression semantics. The renderers and the "
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
