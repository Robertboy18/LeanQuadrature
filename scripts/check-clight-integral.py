#!/usr/bin/env python3
"""Rebuild and audit the Rocq integral-accuracy theorems for the Clight and Cminor rules.

Inputs: --compcert-root, --clight-source, --mathcomp-root, --coquelicot-root, and an empty
--work-dir. Output: the --output JSON record (the retained run is evidence/clight-integral.json).
Requires a built unmodified CompCert 3.17 x86_64 tree, MathComp and Coquelicot checkouts at the
pinned DEPENDENCIES revisions, Docker with the pinned Coq image, and check-clight-roundoff.py,
which this script runs first. The analytic proofs and both lowering passes are then built in
one proof directory.
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
import sys


DEPENDENCIES = {
    "mathcomp": {
        "revision": "f7528eb05b49bca45fb07e274021a8c4a3200efb",
        "version": "1.19.0",
        "upstream": "https://github.com/math-comp/math-comp.git",
    },
    "coquelicot": {
        "revision": "594b782cef83a8ae214c44152c72dcb80f88d93c",
        "version": "3.4.2",
        "upstream": "https://gitlab.inria.fr/coquelicot/coquelicot.git",
    },
}
PROOFS = [
    "PolynomialAccuracy", "TaylorAccuracy", "HermiteRolle", "RealPolynomials",
    "HermiteInterpolation", "HermiteRemainder", "SharpAccuracy", "ClightIntegralAccuracy",
    "CsharpminorExample", "CminorExample", "SilentTermination", "CminorSafety",
    "CminorIntegralAccuracy",
]
AUDITED = [
    "PolynomialAccuracy.GaussianPolynomialAccuracy.ideal_value_plus",
    "PolynomialAccuracy.GaussianPolynomialAccuracy.ideal_value_scal",
    "PolynomialAccuracy.GaussianPolynomialAccuracy.ideal_value_uniform_error",
    "PolynomialAccuracy.GaussianPolynomialAccuracy.power_integrable",
    "PolynomialAccuracy.GaussianPolynomialAccuracy.power_integral",
    "PolynomialAccuracy.GaussianPolynomialAccuracy.ideal_power_integral",
    "PolynomialAccuracy.GaussianPolynomialAccuracy.polynomial_integrable",
    "PolynomialAccuracy.GaussianPolynomialAccuracy.real_integral_plus",
    "PolynomialAccuracy.GaussianPolynomialAccuracy.real_integral_minus",
    "PolynomialAccuracy.GaussianPolynomialAccuracy.real_integral_scal",
    "PolynomialAccuracy.GaussianPolynomialAccuracy.ideal_polynomial_integral",
    "PolynomialAccuracy.GaussianPolynomialAccuracy.polynomial_comparison",
    "TaylorAccuracy.GaussianTaylorAccuracy.real_derive_ext",
    "TaylorAccuracy.GaussianTaylorAccuracy.factorial_positive",
    "TaylorAccuracy.GaussianTaylorAccuracy.scaled_power_derivative",
    "TaylorAccuracy.GaussianTaylorAccuracy.moving_taylor_derivative",
    "TaylorAccuracy.GaussianTaylorAccuracy.moving_taylor_at_target",
    "TaylorAccuracy.GaussianTaylorAccuracy.taylor_segment",
    "TaylorAccuracy.GaussianTaylorAccuracy.moving_taylor_center_zero",
    "TaylorAccuracy.GaussianTaylorAccuracy.abs_power_le_one",
    "TaylorAccuracy.GaussianTaylorAccuracy.centered_taylor_error",
    "TaylorAccuracy.GaussianTaylorAccuracy.derivative_integrable",
    "TaylorAccuracy.GaussianTaylorAccuracy.ideal_rule_taylor_accuracy",
    "HermiteRolle.HermiteRolle.derivative_zeros_above",
    "HermiteRolle.HermiteRolle.repeated_rolle",
    "HermiteRolle.HermiteRolle.repeated_rolle_Derive_n",
    "HermiteRolle.HermiteRolle.derivative_zeros_retained",
    "HermiteRolle.HermiteRolle.insert_point_permutation",
    "HermiteRolle.HermiteRolle.insert_point_sorted",
    "HermiteRolle.HermiteRolle.filter_permutation",
    "HermiteRolle.HermiteRolle.filter_all",
    "HermiteRolle.HermiteRolle.double_zeros_rolle",
    "RealPolynomials.RealPolynomials.eval_add",
    "RealPolynomials.RealPolynomials.eval_scale",
    "RealPolynomials.RealPolynomials.eval_linear_mul",
    "RealPolynomials.RealPolynomials.length_add",
    "RealPolynomials.RealPolynomials.length_scale",
    "RealPolynomials.RealPolynomials.length_linear_mul",
    "RealPolynomials.RealPolynomials.length_derivative_aux",
    "RealPolynomials.RealPolynomials.length_derivative",
    "RealPolynomials.RealPolynomials.eval_derivative_aux_succ",
    "RealPolynomials.RealPolynomials.eval_derivative_cons",
    "RealPolynomials.RealPolynomials.eval_derivative",
    "RealPolynomials.RealPolynomials.eval_derivative_add",
    "RealPolynomials.RealPolynomials.eval_derivative_linear_mul",
    "RealPolynomials.RealPolynomials.eval_iter_derivative",
    "RealPolynomials.RealPolynomials.eval_smooth",
    "RealPolynomials.RealPolynomials.length_iter_derivative",
    "RealPolynomials.RealPolynomials.eval_high_derivative",
    "RealPolynomials.RealPolynomials.nth_nil",
    "RealPolynomials.RealPolynomials.coefficient_add",
    "RealPolynomials.RealPolynomials.coefficient_scale",
    "RealPolynomials.RealPolynomials.coefficient_linear_mul",
    "RealPolynomials.RealPolynomials.coefficient_derivative_aux",
    "RealPolynomials.RealPolynomials.coefficient_derivative",
    "RealPolynomials.RealPolynomials.coefficient_iter_derivative",
    "RealPolynomials.RealPolynomials.eval_top_derivative",
    "RealPolynomials.RealPolynomials.eval_integrable",
    "HermiteInterpolation.HermiteInterpolation.eval_nodal_square_cons",
    "HermiteInterpolation.HermiteInterpolation.derivative_nodal_square_cons",
    "HermiteInterpolation.HermiteInterpolation.length_nodal_square",
    "HermiteInterpolation.HermiteInterpolation.nodal_square_nonnegative",
    "HermiteInterpolation.HermiteInterpolation.nodal_square_positive",
    "HermiteInterpolation.HermiteInterpolation.nodal_square_zero",
    "HermiteInterpolation.HermiteInterpolation.nodal_square_monic",
    "HermiteInterpolation.HermiteInterpolation.nodal_square_top_derivative",
    "HermiteInterpolation.HermiteInterpolation.length_interpolate",
    "HermiteInterpolation.HermiteInterpolation.interpolate_matches",
    "HermiteRemainder.HermiteRemainder.sorted_nodes_nodup",
    "HermiteRemainder.HermiteRemainder.hermite_remainder",
    "HermiteRemainder.HermiteRemainder.hermite_remainder_bound",
    "SharpAccuracy.GaussianSharpAccuracy.ideal_nodes_length",
    "SharpAccuracy.GaussianSharpAccuracy.ideal_nodes_sorted",
    "SharpAccuracy.GaussianSharpAccuracy.ideal_nodes_interval",
    "SharpAccuracy.GaussianSharpAccuracy.ideal_node_member",
    "SharpAccuracy.GaussianSharpAccuracy.ideal_value_ext_nodes",
    "SharpAccuracy.GaussianSharpAccuracy.ideal_eval_integral",
    "SharpAccuracy.GaussianSharpAccuracy.ideal_interpolant_integral",
    "SharpAccuracy.GaussianSharpAccuracy.ideal_rule_nodal_accuracy",
    "SharpAccuracy.GaussianSharpAccuracy.nodal_square_formula",
    "SharpAccuracy.GaussianSharpAccuracy.nodal_square_polynomial",
    "SharpAccuracy.GaussianSharpAccuracy.polynomial_integral_coefficients",
    "SharpAccuracy.GaussianSharpAccuracy.nodal_square_integral",
    "SharpAccuracy.GaussianSharpAccuracy.factorial_real_succ",
    "SharpAccuracy.GaussianSharpAccuracy.sharp_constant_formula",
    "SharpAccuracy.GaussianSharpAccuracy.ideal_rule_sharp_accuracy",
    "ClightIntegralAccuracy.rule_value_integral_accuracy",
    "ClightIntegralAccuracy.integrate_rule_total_integral_accuracy",
    "ClightIntegralAccuracy.integrate_rule_all_returns_integral_accuracy",
    "CsharpminorExample.cshmgen_succeeds",
    "CsharpminorExample.program_translation",
    "CsharpminorExample.programs_match",
    "CsharpminorExample.compiled_program_initializes",
    "CsharpminorExample.transfer_steps",
    "CsharpminorExample.match_return_Kstop",
    "CsharpminorExample.transfer_library_call",
    "CsharpminorExample.entry_found",
    "CsharpminorExample.integrate_testfun_compiled_execution",
    "CsharpminorExample.integrate_found",
    "CsharpminorExample.integrate_rule_compiled_execution",
    "CminorExample.cminorgen_succeeds",
    "CminorExample.program_translation",
    "CminorExample.programs_match",
    "CminorExample.compiled_program_initializes",
    "CminorExample.transfer_steps",
    "CminorExample.match_float_return_Kstop",
    "CminorExample.transfer_library_call",
    "CminorExample.integrate_testfun_compiled_execution",
    "CminorExample.clight_function_valid_block",
    "CminorExample.integrate_rule_compiled_execution",
    "SilentTermination.SilentTermination.termination_step",
    "SilentTermination.SilentTermination.termination_prefix",
    "SilentTermination.SilentTermination.terminal_unique",
    "SilentTermination.SilentTermination.termination_accessible",
    "SilentTermination.SilentTermination.termination_safe",
    "CminorSafety.CminorTotalCorrectness.return_Kstop_nostep",
    "CminorSafety.CminorTotalCorrectness.silent_total_call_correct",
    "CminorSafety.CminorTotalCorrectness.integrate_rule_total_correct",
    "CminorIntegralAccuracy.integrate_rule_total_integral_accuracy",
    "CminorIntegralAccuracy.integrate_rule_all_returns_integral_accuracy",
]


def run(command):
    return subprocess.check_output(command, text=True, stderr=subprocess.STDOUT)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def logged(command, path):
    print(f"Checking {path.name}", flush=True)
    with path.open("w") as output:
        result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"Check failed: {path}\n{path.read_text()[-8000:]}")


def export_source(root, revision, destination):
    if run(["git", "-C", str(root), "rev-parse", "HEAD"]).strip() != revision:
        raise ValueError(f"Unexpected dependency revision: {root}")
    run(["git", "-C", str(root), "diff", "--exit-code", "HEAD", "--", "."])
    destination.mkdir(parents=True)
    with subprocess.Popen(
        ["git", "-C", str(root), "archive", "--format=tar", revision],
        stdout=subprocess.PIPE,
    ) as archive:
        unpack = subprocess.run(
            ["tar", "-xf", "-", "-C", str(destination)], stdin=archive.stdout
        )
        archive.stdout.close()
        if archive.wait() or unpack.returncode:
            raise RuntimeError(f"Could not export pinned sources: {root}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compcert-root", type=Path, required=True)
    parser.add_argument("--clight-source", type=Path, required=True)
    parser.add_argument("--mathcomp-root", type=Path, required=True)
    parser.add_argument("--coquelicot-root", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    work = args.work_dir.resolve()
    roots = {
        "mathcomp": args.mathcomp_root.resolve(strict=True),
        "coquelicot": args.coquelicot_root.resolve(strict=True),
    }
    compcert = args.compcert_root.resolve(strict=True)
    for source in [repo, compcert, *roots.values(), Path("/efs")]:
        if work.is_relative_to(source):
            raise ValueError("Use an empty local build directory outside the source trees.")
    if work.exists() and any(work.iterdir()):
        raise ValueError("The work directory must be empty.")
    work.mkdir(parents=True, exist_ok=True)

    baseline_path = repo / "scripts/check-clight.py"
    spec = importlib.util.spec_from_file_location("clight_checker", baseline_path)
    baseline = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(baseline)
    numerical_checker = repo / "scripts/check-clight-roundoff.py"
    numerical_work = work / "numerics"
    numerical_result = numerical_work / "result.json"
    subprocess.run(
        [sys.executable, str(numerical_checker),
         "--compcert-root", str(compcert),
         "--clight-source", str(args.clight_source.resolve()),
         "--work-dir", str(numerical_work), "--output", str(numerical_result)],
        check=True,
    )

    for name, root in roots.items():
        export_source(root, DEPENDENCIES[name]["revision"],
                      work / "dependencies" / name)

    common = [
        "docker", "run", "--rm", "--read-only", "--network", "none",
        "--user", f"{os.getuid()}:{os.getgid()}",
        "--tmpfs", "/tmp:rw,exec,size=256m",
        "-v", f"{compcert}:/compcert:ro", "-v", f"{work}:/work",
        "-e", f"COQBIN={Path(baseline.COQC).parent}/",
        "-e", "COQPATH=/work/dependencies/mathcomp",
    ]

    def container(command, directory="/work"):
        return (common + ["-w", directory, "--entrypoint", command[0],
                          baseline.IMAGE] + command[1:])

    build_logs = []
    builds = [
        ("mathcomp-build", ["make", "-j8", "seq.vo"],
         "/work/dependencies/mathcomp/mathcomp/ssreflect"),
        ("coquelicot-autoconf", ["autoconf"], "/work/dependencies/coquelicot"),
        ("coquelicot-configure", ["./configure"], "/work/dependencies/coquelicot"),
        ("coquelicot-build", ["./remake", "-j8"], "/work/dependencies/coquelicot"),
    ]
    for label, command, directory in builds:
        log = work / f"{label}.log"
        logged(container(command, directory), log)
        build_logs.append(log)

    proof_dir = numerical_work / "proof"
    for name in PROOFS:
        source = repo / "compcert" / f"{name}.v"
        if re.search(r"\b(Admitted|admit|Axioms?|Parameters?|Abort|native_compute)\b",
                     source.read_text()):
            raise ValueError(f"Unproved declarations or native computation: {source}")
        shutil.copyfile(source, proof_dir / source.name)
    audit_source = (
        "From QuadratureC Require Import " + " ".join(PROOFS) + ".\n" +
        "".join(f"Print Assumptions QuadratureC.{name}.\n" for name in AUDITED)
    )
    (proof_dir / "IntegralAudit.v").write_text(audit_source)
    load_path = [
        "-R", "/work/dependencies/mathcomp/mathcomp/ssreflect", "mathcomp.ssreflect",
        "-R", "/work/dependencies/coquelicot/theories", "Coquelicot",
    ]
    for name in ["lib", "common", "x86_64", "x86", "backend",
                 "cfrontend", "driver", "cparser"]:
        load_path += ["-R", f"/compcert/{name}", f"compcert.{name}"]
    load_path += [
        "-R", "/compcert/flocq", "Flocq",
        "-R", "/compcert/MenhirLib", "MenhirLib",
        "-R", "/work/numerics/export", "compcert.export",
        "-Q", "/work/numerics/proof", "QuadratureC",
    ]
    proof_logs = []
    for name in PROOFS + ["IntegralAudit"]:
        log = work / f"{name}.v.log"
        logged(container([baseline.COQC] + load_path +
                         [f"/work/numerics/proof/{name}.v"]), log)
        proof_logs.append(log)
    audit_log = proof_logs[-1].read_text()
    count = audit_log.count("Axioms:\n") + audit_log.count("Closed under the global context")
    if count != len(AUDITED):
        raise ValueError(f"Expected {len(AUDITED)} audits, found {count}.")
    assumptions = set()
    for section in audit_log.split("Axioms:\n")[1:]:
        assumptions.update(re.findall(
            r"^([A-Za-z_][A-Za-z0-9_.']*)[ \t]*:", section, re.M))
    assumptions = {baseline.ASSUMPTION_ALIASES.get(a, a) for a in assumptions}
    if not assumptions or assumptions - baseline.ALLOWED_ASSUMPTIONS:
        raise ValueError(f"Unexpected assumptions: {sorted(assumptions)}")

    numerical = json.loads(numerical_result.read_text())
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "Rocq integral accuracy and total correctness for all four Clight and Cminor rules",
        "numerical_evidence_sha256": digest(numerical_result),
        "numerical_evidence": numerical,
        "checker_sha256": digest(Path(__file__)),
        "dependencies": DEPENDENCIES,
        "dependency_build": {
            "fresh_source_exports": True,
            "mathcomp_target": "mathcomp/ssreflect/seq.vo and its dependency closure",
            "coquelicot_target": "complete library",
            "compatibility_note": (
                "MathComp 1.19.0 declares Coq <8.20~ in opam. This record certifies "
                "the required source subset's observed build on pinned Coq 8.20.1; "
                "it does not claim upstream support for that combination."
            ),
        },
        "project_sources_sha256": {
            f"compcert/{name}.v": digest(repo / "compcert" / f"{name}.v")
            for name in PROOFS
        },
        "checked_sources_sha256": {
            f"numerics/proof/{name}.v": digest(proof_dir / f"{name}.v")
            for name in PROOFS + ["IntegralAudit"]
        },
        "logs_sha256": {
            str(log.relative_to(work)): digest(log) for log in build_logs + proof_logs
        },
        "audited_theorems": AUDITED,
        "total_project_files": len(numerical["project_sources_sha256"]) + len(PROOFS),
        "total_assumption_audits": len(numerical["audited_theorems"]) + len(AUDITED),
        "axiom_dependencies": sorted(assumptions),
        "analytic_bound": "M*c_n, with c_1=1/3, c_2=1/135, c_3=1/15750, c_4=1/3472875",
        "lowering_passes": ["Cshmgen", "Cminorgen"],
        "lowering_success": "proved for the pinned artifact, with no success premise",
        "cminor_memory_relation": "Mem.inject from initial source memory to final target memory",
        "hypotheses": numerical["accuracy_hypotheses"] + [
            "ordinary real derivatives through order 2*n exist at all points of [-1,1]",
            "the first derivative is bounded by the stated Lipschitz constant",
            "the absolute 2*n-th derivative is bounded by the nonnegative M",
        ],
        "scope": [
            "the derivative hypotheses prove integrability",
            "the constructed Hermite interpolant matches values and first derivatives at arbitrary distinct sorted nodes",
            "repeated Rolle proves the pointwise 2*n-th derivative remainder on the closed interval",
            "exact nodal-square integrals give the sharp Gaussian constants for all four supported orders",
            "the highest derivative need not be continuous for the absolute error bound",
            "the conclusion concerns the actual pinned Clight loops under callback contracts",
            "the Cminor library calls have total correctness and the same integral budget",
            "every reachable Cminor state can step or is the unique prescribed return",
            "accessibility excludes infinite Cminor executions",
            "the general four-rule theorem stops at Cminor, before the remaining backend",
            "no checked Lean-to-Rocq semantic equivalence or linked executable claim",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"PASS: {record['total_project_files']} files, "
          f"{record['total_assumption_audits']} assumption audits; {args.output}")


if __name__ == "__main__":
    main()
