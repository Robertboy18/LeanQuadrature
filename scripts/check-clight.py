#!/usr/bin/env python3
"""Check the Clight example proof, both lowering passes, and the conditional backend transfer.

Inputs: --compcert-root, --work-dir, and an optional --clight-source (otherwise the pinned
quadrules.v is downloaded and hash-checked). Output: the --output JSON record (the retained run
is evidence/clight-proof.json) and check.log in the work directory.
Requires a built unmodified CompCert 3.17 x86_64 tree at COMPCERT_REVISION, built with Coq 8.20,
and Docker with the pinned Coq image. The CompCert tree is mounted read-only.
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
import urllib.request


COMPCERT_REVISION = "7b1f02b09954b9b916eb2a91d283c9b5355bf172"
UPSTREAM_REVISION = "e79a28dba247db9f934289bcf4e4debd5eebc884"
CLIGHT_SHA256 = "7b19b9f1095cb7a36316633af3b959f79a1745be0b0e6c36103a1a38c000a1f7"
IMAGE = "coqorg/coq@sha256:18ebf3da56e60e3ddfd7d4e51f4c53d10241a129f34e93dacbc71562dd43c57a"
COQC = "/home/coq/.opam/4.13.1+flambda/bin/coqc"
ALLOWED_ASSUMPTIONS = {
    "Axioms.proof_irr",
    "ClassicalDedekindReals.sig_not_dec",
    "ClassicalDedekindReals.sig_forall_dec",
    "FunctionalExtensionality.functional_extensionality_dep",
    "Classical_Prop.classic",
    "Eqdep.Eq_rect_eq.eq_rect_eq",
    "external_functions_sem",
    "external_functions_properties",
    "inline_assembly_sem",
    "inline_assembly_properties",
}
COMPILER_PARAMETERS = {
    "Archi.win64",
    "SelectOp.symbol_is_relocatable",
    "Inlining.inlining_info",
    "Inlining.inlining_analysis",
    "Inlining.should_inline",
    "Allocation.regalloc",
    "RTLgen.more_likely",
    "Selection.compile_switch",
    "Selection.if_conversion_heuristic",
    "Linearize.enumerate_aux",
    "Compiler.print_Cminor",
    "Compiler.print_RTL",
    "Compiler.print_LTL",
    "Compiler.print_Mach",
    *{
        f"Compopts.{name}" for name in [
            "va_strict", "propagate_float_constants", "generate_float_constants",
            "optim_tailcalls", "optim_redundancy", "optim_for_size",
            "optim_constprop", "optim_CSE", "debug",
        ]
    },
}
ASSUMPTION_ALIASES = {
    "functional_extensionality_dep": "FunctionalExtensionality.functional_extensionality_dep",
    **{f"Events.{name}": name for name in [
        "external_functions_sem", "external_functions_properties",
        "inline_assembly_sem", "inline_assembly_properties",
    ]},
    **{
        name.split(".", 1)[1]: name
        for name in COMPILER_PARAMETERS
        if name.startswith(("Compopts.", "Compiler."))
    },
}


def run(command, **kwargs):
    return subprocess.run(
        command, check=True, text=True, capture_output=True, **kwargs
    ).stdout.strip()


def sha256(content):
    return hashlib.sha256(content).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compcert-root", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--clight-source", type=Path,
                        help="Use a previously downloaded pinned quadrules.v.")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    root = args.compcert_root.resolve(strict=True)
    work = args.work_dir.resolve()
    if work.is_relative_to(root) or work.is_relative_to(repo):
        raise ValueError("The build directory must be outside both source trees.")
    revision = run(["git", "-C", str(root), "rev-parse", "HEAD"])
    if revision != COMPCERT_REVISION:
        raise ValueError(f"Unexpected CompCert revision: {revision}")
    run(["git", "-C", str(root), "diff", "--exit-code", "HEAD", "--", "*.v"])
    required = ["cfrontend/ClightBigstep.vo", "cfrontend/Cshmgenproof.vo",
                "cfrontend/Cminorgenproof.vo", "driver/Compiler.vo",
                "x86_64/Archi.vo"]
    for name in required:
        if not (root / name).is_file():
            raise ValueError(f"Required compiled CompCert dependency missing: {name}")

    if args.clight_source:
        source = args.clight_source.read_bytes()
    else:
        url = (
            "https://raw.githubusercontent.com/VeriNum/simple_cfem/"
            f"{UPSTREAM_REVISION}/proof/C/quadrules.v"
        )
        with urllib.request.urlopen(url, timeout=60) as response:
            source = response.read()
    if sha256(source) != CLIGHT_SHA256:
        raise ValueError("The Clight source does not match the pinned artifact.")

    proof_dir, export_dir = work / "proof", work / "export"
    proof_dir.mkdir(parents=True, exist_ok=True)
    export_dir.mkdir(parents=True, exist_ok=True)
    (proof_dir / "quadrules.v").write_bytes(source)
    for name in ["Ctypesdefs.v", "Clightdefs.v"]:
        shutil.copyfile(root / "export" / name, export_dir / name)
    proof_names = [
        "ClightExample.v", "ClightRules.v", "ClightDeterminism.v",
        "ClightSafety.v", "CsharpminorExample.v", "CminorExample.v",
        "ClightLibrary.v", "AnnotatedBehavior.v", "ClightApplication.v",
        "CminorApplication.v", "CompilerBackend.v", "AsmApplication.v",
        "ValueAccuracy.v", "ExampleIntegral.v", "ApplicationAccuracy.v",
        "InternalCosine.v", "PolynomialApplication.v", "PolynomialCompilation.v",
    ]
    for name in proof_names:
        proof = (repo / "compcert" / name).read_text()
        if re.search(r"\b(?:Admitted|admit|Axiom|Axioms|Parameter|Parameters|Abort)\b", proof):
            raise ValueError("Unproved project declarations are not permitted.")
        (proof_dir / name).write_text(proof)

    common = [
        "docker", "run", "--rm", "--network", "none",
        "--user", f"{os.getuid()}:{os.getgid()}",
        "-v", f"{root}:/compcert:ro", "-v", f"{work}:/work",
        "--entrypoint", COQC, IMAGE,
    ]
    coq_version = run(common + ["--version"])
    load_path = []
    for name in ["lib", "common", "x86_64", "x86", "backend",
                 "cfrontend", "driver", "cparser"]:
        load_path += ["-R", f"/compcert/{name}", f"compcert.{name}"]
    load_path += [
        "-R", "/compcert/flocq", "Flocq",
        "-R", "/compcert/MenhirLib", "MenhirLib",
        "-R", "/work/export", "compcert.export",
        "-Q", "/work/proof", "QuadratureC",
    ]
    logs = []
    for name in ["export/Ctypesdefs.v", "export/Clightdefs.v",
                 "proof/quadrules.v"] + [f"proof/{name}" for name in proof_names]:
        print(f"Checking {name}", flush=True)
        result = subprocess.run(
            common + load_path + [f"/work/{name}"],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        (work / (Path(name).name + ".log")).write_text(result.stdout)
        logs.append(f"Checking {name}\n{result.stdout}")
        if result.returncode:
            print(result.stdout)
            raise subprocess.CalledProcessError(result.returncode, result.args)

    log = "\n".join(logs)
    (work / "check.log").write_text(log)
    assumptions = set()
    for section in log.split("Axioms:\n")[1:]:
        assumptions.update(re.findall(r"^([A-Za-z_][A-Za-z0-9_.']*)[ \t]*:", section, re.M))
    assumptions.discard("Axioms")
    assumptions = {ASSUMPTION_ALIASES.get(name, name) for name in assumptions}
    if not assumptions or assumptions - (ALLOWED_ASSUMPTIONS | COMPILER_PARAMETERS):
        raise ValueError(f"Unexpected or missing assumption audit: {sorted(assumptions)}")
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "Rocq quadrature accuracy through concrete Cminor lowering and conditional assembly transfer, with explicit callback or cosine contracts",
        "compcert_revision": revision,
        "compcert_target": "x86_64",
        "pinned_ast_metadata_target": "aarch64-apple; interpreted here under x86_64 CompCert semantics",
        "coq_version": coq_version,
        "container_image": IMAGE,
        "container_image_id": run(
            ["docker", "image", "inspect", "--format", "{{.Id}}", IMAGE]
        ),
        "upstream_revision": UPSTREAM_REVISION,
        "clight_source_sha256": CLIGHT_SHA256,
        "proof_sha256": sha256((proof_dir / "ClightExample.v").read_bytes()),
        "project_proof_sha256": {
            name: sha256((proof_dir / name).read_bytes()) for name in proof_names
        },
        "check_log_sha256": sha256(log.encode()),
        "assumptions": sorted(assumptions),
        "logical_and_external_semantics_assumptions": sorted(
            assumptions & ALLOWED_ASSUMPTIONS
        ),
        "upstream_computational_parameters": sorted(assumptions & COMPILER_PARAMETERS),
        "result_bits": "3fead02c771c35ed",
        "clight_small_step_execution_proved": True,
        "clight_library_call_total_correctness_proved": True,
        "clight_reachable_state_safety_proved": True,
        "clight_unique_return_proved": True,
        "clight_all_executions_finite_proved": True,
        "cshmgen_translation_success_proved": True,
        "cshmgen_execution_transfer_proved": True,
        "cminorgen_translation_success_proved": True,
        "cminorgen_execution_transfer_proved": True,
        "application_clight_entry_proved": True,
        "application_clight_terminating_behavior_proved": True,
        "application_cminor_forward_simulation_proved": True,
        "application_cminor_terminating_behavior_proved": True,
        "application_result_observation": "Event_annot quadrature-result [EVfloat 0x3fead02c771c35ed]; exit status zero",
        "application_entry_origin": "authored normalized Clight AST appended to the pinned library definitions",
        "application_c_wrapper_parsing_proved": False,
        "application_clight_all_behaviors_proved": True,
        "application_cminor_all_behaviors_proved": True,
        "application_all_behaviors_proved": True,
        "cminor_backend_forward_simulation_under_success_proved": True,
        "application_assembly_all_behaviors_under_success_proved": True,
        "real_integral_identity_proved_in_rocq": True,
        "concrete_result_accuracy_proved_in_rocq": True,
        "application_clight_integral_accuracy_proved": True,
        "application_cminor_integral_accuracy_proved": True,
        "application_assembly_integral_accuracy_under_success_proved": True,
        "corrected_absolute_error_bound": "356/100000",
        "draft_absolute_error_bound_refuted": "224/100000",
        "numerical_target": "Riemann integral of (1/2)*(1-x)*cos(x) on [-1,1]",
        "concrete_numerical_certificate_imports_lean_theorem": False,
        "polynomial_cosine_coefficients_checked": True,
        "polynomial_cosine_two_input_execution_proved": True,
        "polynomial_application_clight_total_correctness_proved": True,
        "polynomial_application_cminor_total_correctness_proved": True,
        "polynomial_application_integral_accuracy_without_cosine_premises_proved": True,
        "polynomial_application_assembly_accuracy_under_success_proved": True,
        "polynomial_application_external_cosine_premises": False,
        "polynomial_application_variant": "replace only the external cosine declaration by a degree-14 binary64 Horner polynomial; preserve all other library definitions and tables",
        "application_concrete_backend_success_proved": False,
        "application_concrete_assembly_artifact_checked": False,
        "backend_success_premise": "Compiler.transf_cminor_program CminorApplication.cminor_program = OK assembly_program",
        "backend_abi": "Archi.win64 remains an abstract CompCert parameter",
        "callback_parametric_rule_orders": [1, 2, 3, 4],
        "callback_contract": "valid function pointer; callback execution at each stored node with empty trace and unchanged initialized memory",
        "compiler_transfer_proved": False,
        "external_cosine_implementation_proved": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Proof checked; assumptions are printed in {work / 'check.log'}")


if __name__ == "__main__":
    main()
