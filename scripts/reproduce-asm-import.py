#!/usr/bin/env python3
"""Reproduce the formal assembly import from the checked configured CompCert build.

Inputs: --work-dir, the optional --update-lean-import flag, the evidence records of the four
earlier stages (the rtl-preallocation, ltl, linear, and mach imports), and
evidence/assembly-certificate.json. Output: the --output JSON record (the retained run is
evidence/asm-import.json).
Requires the proof build recorded in evidence/mach-import.json and Docker with the pinned Coq
image. UPSTREAM extends the UPSTREAM hashes of reproduce-mach-import.py with x86/Asm.v from
generate-asm-syntax.py, and reproduce-mach-import.py in turn takes its image, revision, expected
axioms, and hash helpers from reproduce-cminor-import.py. scripts/import-asm.py is the importer.
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
SYNTAX = load_module("asm_syntax", REPO / "scripts/generate-asm-syntax.py")
UPSTREAM = {**MACH.UPSTREAM, "x86/Asm.v": SYNTAX.SOURCE_SHA256}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--update-lean-import", action="store_true",
                        help="explicitly replace the checked-in assembly AST during development")
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
    proof = Path(dependencies["mach-import"]["proof_build"])
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
    for name, digest in UPSTREAM.items():
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
    syntax_inventory = SYNTAX.generate(proof / "compiler/x86/Asm.v", work / "syntax")
    for name in syntax_inventory["generated_files"]:
        BASE.check_hash(work / "syntax" / name, BASE.digest(REPO / name))
    files = ["ExportAsm.v", "EqualityAsm.v"]
    for name in files:
        shutil.copy2(REPO / "compcert" / name, work / name)
    (work / "RunAsmExport.v").write_text(
        "From Coq Require Import String.\n"
        "From compcert Require Import Asmgen Errors.\n"
        "From CminorImport Require Import ImportedMach ExportAsm.\n"
        "Definition compiled_asm n := Asmgen.transf_program (ImportedMach.imported_program n).\n"
        "Definition exported n := match compiled_asm n with\n"
        ' | OK p => ExportAsm.program p | Error _ => "ERROR"%string end.\n'
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

    def compile_file(name):
        result = subprocess.run(docker + flags + [name], text=True, capture_output=True)
        log = result.stdout + result.stderr
        (work / (name + ".log")).write_text(log)
        if result.returncode:
            print(log, flush=True)
        result.check_returncode()
        print(f"Checked {name}", flush=True)
        return log

    def audit_axioms(log):
        axioms = set(re.findall(r"^([A-Za-z_][A-Za-z0-9_.]*)\s*:", log, re.MULTILINE))
        axioms.discard("Axioms")
        allowed = BASE.EXPECTED_AXIOMS | {"Axioms.proof_irr"}
        if not axioms <= allowed:
            raise ValueError(f"unapproved assembly certificate assumptions: {sorted(axioms)}")
        return sorted(axioms)

    compile_file("ExportAsm.v")
    equality_audit = compile_file("EqualityAsm.v")
    equality_axioms = audit_axioms(equality_audit)
    if equality_axioms or equality_audit.count("Closed under the global context") != 1:
        raise ValueError("the generic equality theorem must have no axioms")
    compile_file("RunAsmExport.v")
    importer = load_module("asm_import", REPO / "scripts/import-asm.py")
    inventory = importer.generate(work, work / "Imported.lean", work / "ImportedAsm.v")
    lean_path = REPO / "Quadrature/Compiler/Asm/Imported.lean"
    if args.update_lean_import:
        shutil.copy2(work / "Imported.lean", lean_path)
    BASE.check_hash(work / "Imported.lean", BASE.digest(lean_path))
    certificate_axioms = audit_axioms(compile_file("ImportedAsm.v"))
    if set(certificate_axioms) != BASE.EXPECTED_AXIOMS | {"Axioms.proof_irr"}:
        raise ValueError("the concrete assembly certificate has unexpected assumptions")
    stems = ["ExportAsm", "EqualityAsm", "RunAsmExport", "ImportedAsm"]
    artifacts = [
        name + suffix for name in stems for suffix in [".v", ".v.log", ".vo"]
    ] + ["Imported.lean"] + ["syntax/" + name for name in syntax_inventory["generated_files"]]
    tools = [
        "scripts/import-cminor.py", "scripts/import-asm.py", "scripts/asm-schema.json",
        "scripts/generate-asm-syntax.py", "scripts/reproduce-asm-import.py",
        "compcert/ExportAsm.v", "compcert/EqualityAsm.v",
    ]
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "Complete formal assembly syntax checked against the pinned Asmgen output",
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
        "upstream_source_sha256": UPSTREAM,
        "lean_import_sha256": BASE.digest(lean_path),
        "lean_syntax_sha256": BASE.digest(REPO / "Quadrature/Compiler/Asm/Syntax.lean"),
        "instruction_vocabulary_constructor_count":
            syntax_inventory["instruction_constructor_count"],
        "rocq_equality_axioms": equality_axioms,
        "rocq_certificate_axioms": certificate_axioms,
        "rocq_exact_asmgen_output_proved": True,
        "rocq_remaining_compiler_output_proved": True,
        "lean_syntax_and_import_reproduced_exactly": True,
        "lean_execution_proved": False,
        "lean_return_address_assembly_correspondence_proved": False,
        "lean_rocq_interpretation_proved": False,
        "source_c_and_linked_executable_correspondence_proved": False,
        "offset_unit": "formal Asm instructions, not native machine-code bytes",
        "trust_boundary": (
            "Rocq checks its reconstructed assembly AST against Asmgen and the actual "
            "remaining compiler pipeline. The complete Lean syntax and program rendering "
            "reproduce exactly. This certificate does not prove their interpretation "
            "between kernels, Lean assembly execution, or a linked executable."
        ),
        **inventory,
        "artifacts_sha256": {name: BASE.digest(work / name) for name in artifacts},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Wrote {args.output}", flush=True)


if __name__ == "__main__":
    main()
