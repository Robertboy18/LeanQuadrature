#!/usr/bin/env python3
"""Check finite execution, signed results, and accuracy of the pinned Clight loops in Rocq.

Inputs: --compcert-root, --clight-source, --work-dir. Output: the --output JSON record (the
retained run is evidence/clight-roundoff.json) and one log per proof file in the work directory.
Requires a built unmodified CompCert 3.17 x86_64 tree and Docker with the pinned Coq image.
The fourteen PROOFS files are rebuilt from source in an empty local directory and their
numerical theorems are audited against the CompCert/Flocq assumption allowlist.
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


PROOFS = [
    "ClightExample", "ClightRules", "ClightDeterminism", "ClightSafety",
    "FiniteArithmetic", "FiniteRepresentation", "IntegerRounding", "FiniteInteger",
    "ClightRoundoff", "ClightRepresentation", "ClightInteger",
    "TableAccuracy", "CallbackAccuracy", "ClightAccuracy",
]
AUDITED = [
    "FiniteArithmetic.Binary64Roundoff.epsilon_nonnegative",
    "FiniteArithmetic.Binary64Roundoff.round_bounded",
    "FiniteArithmetic.Binary64Roundoff.round_no_overflow",
    "FiniteArithmetic.Binary64Roundoff.add_bounded",
    "FiniteArithmetic.Binary64Roundoff.mul_bounded",
    "FiniteArithmetic.Binary64Roundoff.product_mass_nonnegative",
    "FiniteArithmetic.Binary64Roundoff.integrate_bounded",
    "ClightRoundoff.rule_weight_finite",
    "ClightRoundoff.rule_terms_length",
    "ClightRoundoff.rule_terms_finite",
    "ClightRoundoff.rule_value_bounded",
    "ClightRoundoff.integrate_rule_numeric_correct",
    "ClightRoundoff.integrate_rule_all_returns_roundoff",
    "FiniteRepresentation.Binary64Representation.observe_injective",
    "FiniteRepresentation.Binary64Representation.addition_sign_compare",
    "FiniteRepresentation.Binary64Representation.observe_add",
    "FiniteRepresentation.Binary64Representation.observe_mul",
    "FiniteRepresentation.Binary64Representation.add_eq_iff",
    "FiniteRepresentation.Binary64Representation.mul_eq_iff",
    "FiniteRepresentation.Binary64Representation.observe_integrate_finite",
    "FiniteRepresentation.Binary64Representation.observe_integrate_bounded",
    "FiniteRepresentation.Binary64Representation.integrate_eq_iff",
    "ClightRepresentation.rule_value_observe",
    "ClightRepresentation.rule_value_eq_iff",
    "ClightRepresentation.integrate_rule_all_returns_observation",
    "IntegerRounding.IntegerRounding.nearest_even_quotient",
    "IntegerRounding.IntegerRounding.scale_denominator_positive",
    "IntegerRounding.IntegerRounding.scale_real",
    "IntegerRounding.IntegerRounding.digits_log2",
    "IntegerRounding.IntegerRounding.round_dyadic_real",
    "IntegerRounding.IntegerRounding.dyadic_real_zero",
    "IntegerRounding.IntegerRounding.dyadic_real_negative",
    "IntegerRounding.IntegerRounding.round_signed_real",
    "IntegerRounding.IntegerRounding.align_real",
    "IntegerRounding.IntegerRounding.add_real",
    "IntegerRounding.IntegerRounding.mul_real",
    "IntegerRounding.IntegerRounding.equal_iff_real",
    "FiniteInteger.Binary64Integer.exponent_compcert",
    "FiniteInteger.Binary64Integer.decode_real",
    "FiniteInteger.Binary64Integer.encode_real",
    "FiniteInteger.Binary64Integer.add_sign_real",
    "FiniteInteger.Binary64Integer.add_real",
    "FiniteInteger.Binary64Integer.mul_real",
    "FiniteInteger.Binary64Integer.represents_iff_observe",
    "FiniteInteger.Binary64Integer.add_represents",
    "FiniteInteger.Binary64Integer.mul_represents",
    "FiniteInteger.Binary64Integer.represents_unique",
    "FiniteInteger.Binary64Integer.add_eq_iff",
    "FiniteInteger.Binary64Integer.mul_eq_iff",
    "FiniteInteger.Binary64Integer.sum_real",
    "FiniteInteger.Binary64Integer.integrate_represents",
    "FiniteInteger.Binary64Integer.integrate_eq_iff",
    "ClightInteger.rule_value_integer",
    "ClightInteger.rule_value_integer_eq_iff",
    "ClightInteger.integrate_rule_all_returns_integer",
    "TableAccuracy.Binary64TableAccuracy.rule_node_real",
    "TableAccuracy.Binary64TableAccuracy.rule_weight_real",
    "TableAccuracy.Binary64TableAccuracy.two_node_spec",
    "TableAccuracy.Binary64TableAccuracy.three_node_spec",
    "TableAccuracy.Binary64TableAccuracy.four_radical_spec",
    "TableAccuracy.Binary64TableAccuracy.four_radical_bounds",
    "TableAccuracy.Binary64TableAccuracy.four_inner_spec",
    "TableAccuracy.Binary64TableAccuracy.four_outer_spec",
    "TableAccuracy.Binary64TableAccuracy.four_radical_tight",
    "TableAccuracy.Binary64TableAccuracy.rule_node_finite",
    "TableAccuracy.Binary64TableAccuracy.rule_node_interval",
    "TableAccuracy.Binary64TableAccuracy.ideal_node_interval",
    "TableAccuracy.Binary64TableAccuracy.rule_node_error",
    "TableAccuracy.Binary64TableAccuracy.rule_weight_error",
    "TableAccuracy.Binary64TableAccuracy.ideal_weight_positive",
    "TableAccuracy.Binary64TableAccuracy.ideal_weights_sum",
    "TableAccuracy.Binary64TableAccuracy.ideal_moment",
    "TableAccuracy.Binary64TableAccuracy.three_weight_exceeds_draft_tolerance",
    "CallbackAccuracy.Binary64CallbackAccuracy.sum_on_le",
    "CallbackAccuracy.Binary64CallbackAccuracy.sum_on_add",
    "CallbackAccuracy.Binary64CallbackAccuracy.sum_on_mul",
    "CallbackAccuracy.Binary64CallbackAccuracy.sum_on_const",
    "CallbackAccuracy.Binary64CallbackAccuracy.sum_on_abs_sub",
    "CallbackAccuracy.Binary64CallbackAccuracy.product_mass_as_sum",
    "CallbackAccuracy.Binary64CallbackAccuracy.exact_sum_as_sum",
    "CallbackAccuracy.Binary64CallbackAccuracy.lipschitz_of_derivative_bound",
    "CallbackAccuracy.Binary64CallbackAccuracy.stored_weight_mass",
    "CallbackAccuracy.Binary64CallbackAccuracy.callback_at_node",
    "CallbackAccuracy.Binary64CallbackAccuracy.callback_magnitude",
    "CallbackAccuracy.Binary64CallbackAccuracy.product_mass_bound",
    "CallbackAccuracy.Binary64CallbackAccuracy.weighted_sample_error",
    "CallbackAccuracy.Binary64CallbackAccuracy.samples_error",
    "CallbackAccuracy.Binary64CallbackAccuracy.rule_value_accuracy",
    "ClightAccuracy.integrate_rule_total_accuracy",
    "ClightAccuracy.integrate_rule_all_returns_accuracy",
]


def run(command):
    result = subprocess.run(
        command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT
    )
    if result.returncode:
        raise RuntimeError(f"{command[0]} failed:\n{result.stdout}")
    return result.stdout


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compcert-root", type=Path, required=True)
    parser.add_argument("--clight-source", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]

    # Reuse the pinned artifact identity and the existing CompCert assumption
    # names; compiler-choice parameters are not permitted in this check.
    baseline_path = repo / "scripts/check-clight.py"
    spec = importlib.util.spec_from_file_location("clight_checker", baseline_path)
    baseline = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(baseline)

    root = args.compcert_root.resolve(strict=True)
    work = args.work_dir.resolve()
    if (work.is_relative_to(root) or work.is_relative_to(repo) or
            work.is_relative_to("/efs")):
        raise ValueError("Use a local build directory outside both source trees.")
    if work.exists() and any(work.iterdir()):
        raise ValueError("The work directory must be empty.")
    if run(["git", "-C", str(root), "rev-parse", "HEAD"]).strip() != baseline.COMPCERT_REVISION:
        raise ValueError("Unexpected CompCert revision.")
    run(["git", "-C", str(root), "diff", "--exit-code", "HEAD", "--", "*.v"])
    for name in ["cfrontend/ClightBigstep.vo", "x86_64/Archi.vo", "lib/Floats.vo"]:
        if not (root / name).is_file():
            raise ValueError(f"Missing compiled dependency: {name}")
    if digest(args.clight_source) != baseline.CLIGHT_SHA256:
        raise ValueError("Unexpected Clight artifact.")

    proof_dir, export_dir = work / "proof", work / "export"
    proof_dir.mkdir(parents=True, exist_ok=True)
    export_dir.mkdir()
    shutil.copyfile(args.clight_source, proof_dir / "quadrules.v")
    for name in ["Ctypesdefs.v", "Clightdefs.v"]:
        shutil.copyfile(root / "export" / name, export_dir / name)
    for name in PROOFS:
        source = repo / "compcert" / f"{name}.v"
        if re.search(r"\b(Admitted|admit|Axioms?|Parameters?|Abort|native_compute)\b",
                     source.read_text()):
            raise ValueError(f"Unproved declarations or native computation: {source}")
        shutil.copyfile(source, proof_dir / source.name)

    audit_source = (
        "From QuadratureC Require Import FiniteArithmetic FiniteRepresentation "
        "IntegerRounding FiniteInteger ClightRoundoff ClightRepresentation "
        "ClightInteger TableAccuracy CallbackAccuracy "
        "ClightAccuracy.\n" +
        "".join(f"Print Assumptions QuadratureC.{name}.\n" for name in AUDITED)
    )
    (proof_dir / "RoundoffAudit.v").write_text(audit_source)
    common = [
        "docker", "run", "--rm", "--read-only", "--network", "none",
        "--user", f"{os.getuid()}:{os.getgid()}",
        "-v", f"{root}:/compcert:ro", "-v", f"{work}:/work",
        "--entrypoint", baseline.COQC, baseline.IMAGE,
    ]
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
    paths = ["export/Ctypesdefs.v", "export/Clightdefs.v", "proof/quadrules.v"]
    paths += [f"proof/{name}.v" for name in PROOFS]
    paths += ["proof/RoundoffAudit.v"]
    for name in paths:
        print(f"Checking {name}", flush=True)
        result = subprocess.run(
            common + load_path + [f"/work/{name}"],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        (work / f"{Path(name).name}.log").write_text(result.stdout)
        if result.returncode:
            raise RuntimeError(f"Rocq check failed: {name}\n{result.stdout}")

    audit_log = (work / "RoundoffAudit.v.log").read_text()
    audit_count = audit_log.count("Axioms:\n") + audit_log.count(
        "Closed under the global context"
    )
    if audit_count != len(AUDITED):
        raise ValueError(f"Expected {len(AUDITED)} assumption audits, got {audit_count}.")
    assumptions = set()
    for section in audit_log.split("Axioms:\n")[1:]:
        assumptions.update(re.findall(
            r"^([A-Za-z_][A-Za-z0-9_.']*)[ \t]*:", section, re.M
        ))
    assumptions = {baseline.ASSUMPTION_ALIASES.get(name, name) for name in assumptions}
    if not assumptions or assumptions - baseline.ALLOWED_ASSUMPTIONS:
        raise ValueError(f"Unexpected assumptions: {sorted(assumptions)}")

    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "Rocq finite execution, signed results, table certificates, and accuracy relative to the ideal four Clight rules",
        "compcert_revision": baseline.COMPCERT_REVISION,
        "compcert_target": "x86_64",
        "pinned_ast_metadata_target": "aarch64-apple; interpreted under x86_64 CompCert semantics",
        "clight_sha256": baseline.CLIGHT_SHA256,
        "coq_version": run(common + ["--version"]).strip(),
        "container_image": baseline.IMAGE,
        "container_image_id": run(
            ["docker", "image", "inspect", "--format", "{{.Id}}", baseline.IMAGE]
        ).strip(),
        "checker_sha256": digest(Path(__file__)),
        "baseline_checker_sha256": digest(baseline_path),
        "project_sources_sha256": {
            f"compcert/{name}.v": digest(repo / "compcert" / f"{name}.v")
            for name in PROOFS
        },
        "checked_sources_sha256": {name: digest(work / name) for name in paths},
        "logs_sha256": {
            f"{Path(name).name}.log": digest(work / f"{Path(name).name}.log")
            for name in paths
        },
        "audited_theorems": AUDITED,
        "axiom_dependencies": sorted(assumptions),
        "hypotheses": [
            "valid callback pointer and binary64 callback type",
            "silent memory-preserving callback execution at every stored node",
            "finite callback outputs",
            "radius at most the largest finite binary64 value",
            "sum of absolute exact stored products plus 2*n*epsilon(radius) at most radius",
        ],
        "accuracy_hypotheses": [
            "the same valid callback pointer, type, and silent memory-preserving execution contract",
            "at finite inputs x in [-1,1], callback(x) is finite and differs from g(real(x)) by at most error",
            "nonnegative callback error, integrand bound, and Lipschitz constant",
            "absolute value of g on [-1,1] at most bound",
            "g is Lipschitz on [-1,1] with the stated constant; a derivative-bound lemma supplies this condition",
            "radius at most the largest finite binary64 value",
            "(2+n*weight_tolerance)*(bound+error)+2*n*epsilon(radius) at most radius",
        ],
        "table_tolerances": {
            "node": "1/10000000000000000",
            "weight": "5/10000000000000000",
        },
        "scope": [
            "actual initialized C tables, orders 1 through 4",
            "CompCert floating-point semantics; no imported Lean proof",
            "real value and sign bit uniquely characterize each finite binary64 result",
            "separately rounded signed recurrence, including signed zero and underflow",
            "roundoff relative to exact stored products, not the real integral",
            "exact rational decodings, node and weight error bounds for the actual C initializers",
            "positive ideal weights, total mass two, and exact moments through degree 2*n-1",
            "refutation of the draft's absolute 2^(-53) tolerance for the three-point C weight",
            "callback, node, weight, and rounding errors composed relative to the ideal real rule",
            "the general analytic quadrature remainder is not included in the Rocq accuracy theorem",
            "no FloatLib-CompCert bitwise equivalence claim",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Checked {len(PROOFS)} project files and {len(AUDITED)} theorem audits.", flush=True)


if __name__ == "__main__":
    main()
