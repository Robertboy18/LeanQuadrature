#!/usr/bin/env python3
"""Rebuild the pinned upstream quadrature proofs in a prepared Rocq/VST environment."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

from upstream_sources import LAPROOF_REVISION, REVISION


REQUIRED_PACKAGES = {
    "coq": "9.0.1",
    "coq-compcert": "3.17",
    "coq-flocq": "4.2.2",
    "coq-interval": "4.11.4",
    "coq-mathcomp-ssreflect": "2.5.0",
    "coq-mathcomp-algebra": "2.5.0",
    "rocq-mathcomp-boot": "2.5.0",
    "coq-mathcomp-analysis": "1.15.0",
    "coq-mathcomp-reals-stdlib": "1.15.0",
    "coq-vst": "2.16",
    "coq-vst-lib": "2.15.1",
    "coq-vcfloat": "2.4.1",
}

QUERIES = [
    *(f"CFEM.C.verif_quadrules.body_{name}" for name in [
        "gauss_point", "gauss_weight", "gauss2d_npoint1d", "gauss2d_point",
        "gauss2d_weight", "hughes_point", "hughes_weight", "integrate", "integrate_testfun",
    ]),
    *(f"CFEM.C.spec_quadrules_highlevel.{name}" for name in [
        "sub_gauss_point", "sub_gauss_weight", "sub_integrate",
    ]),
    *(f"CFEM.quadmodel_accuracy.{name}" for name in [
        "integrate_model_err", "finite_integrate_model_aux", "gauss_pt_wt_limit_aux",
        "perturb_sum",
    ]),
    "CFEM.quadmodel_accuracy.Quadmodel_F64_accuracy.gauss_points_acc",
    "CFEM.quadmodel_accuracy.Quadmodel_F64_accuracy.gauss_weights_acc",
    *(f"CFEM.C.verif_quadrules.{name}" for name in [
        "testfun_fbound", "testfun_deriv_bound", "testfun_function_accuracy",
        "testfun_quadrature_error_bound",
    ]),
    "CFEM.quadrature.quadrature_error",
    "CFEM.quadrature.Rintegral_gt_0",
    "CFEM.quadrature.Legendre.quadrature_error_bound_is_bound",
    "CFEM.quadrature2.error_1_0_1",
    "CFEM.quadrature2.error_1_0_2",
    "CFEM.quadrature2.g_max_deriv",
    "CFEM.quadrature2.trigo_cos_e",
    "CFEM.quadrature2.trigo_sin_e",
]

REVIEW_LEMMAS = [
    "hughes_weight_identifier_mismatch",
    "gauss2d_weight_identifier_duplicated",
    "hughes_weight_identifier_missing",
    "semax_body_ignores_identifier",
    "hughes_weight_corrected_identifier",
    "body_hughes_weight_corrected_identifier",
    "three_point_initializer_model_mismatch",
]
QUERIES += [f"UpstreamReview.SpecAudit.{name}" for name in REVIEW_LEMMAS]
VST_BODY_DEFINITION = (
    "VST.floyd.SeparationLogicAsLogicSoundness.MainTheorem."
    "CSHL_MinimumLogic.CSHL_Defs.semax_body"
)
QUERIES.append(VST_BODY_DEFINITION)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def captured(args, cwd):
    return subprocess.check_output(args, cwd=cwd, text=True, stderr=subprocess.STDOUT)


def tracked_inputs(source):
    """Hash tracked sources in both pinned repositories, without walking build directories."""
    result = {}
    for root in [source, source / "LAProof"]:
        for name in captured(["git", "ls-files"], root).splitlines():
            path = root / name
            if path.is_file() and (
                path.suffix in {".v", ".c", ".h", ".opam"}
                or path.name.startswith("Makefile")
                or path.name in {"_CoqProject", "CoqMakefile.local"}
            ):
                result[str(path.relative_to(source))] = sha256(path)
    return result


def source_files(project):
    return [
        project.parent / line.strip()
        for line in project.read_text().splitlines()
        if line.strip().endswith(".v") and not line.lstrip().startswith("#")
    ]


def parse_assumptions(text):
    if text.strip() == "Closed under the global context":
        return []
    if "Axioms:" not in text:
        raise ValueError("Unrecognized Print Assumptions output")
    names = re.findall(r"(?m)^([^\s:]+)\s*:", text)
    names = [name for name in names if name != "Axioms"]
    if not names:
        raise ValueError("An axiom report contained no readable names")
    return names


def clight_metadata(text):
    """Read the generator's target without confusing it with the proof environment."""
    match = re.search(r"Module Info\.(.*?)End Info\.", text, re.DOTALL)
    if not match:
        raise ValueError("Clight output has no Info module")
    result = {}
    for name in ["version", "arch", "model", "abi", "bitsize", "big_endian"]:
        value = re.search(rf'\bDefinition {name}\s*:=\s*("[^"]*"|\w+)\.', match[1])
        if not value:
            raise ValueError(f"Clight output has no {name} metadata")
        result[name] = json.loads(value[1])
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=12)
    args = parser.parse_args()
    source = args.source_dir.resolve()
    work = args.work_dir.resolve()
    output = args.output.resolve()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if source == work or source in work.parents or work in source.parents:
        parser.error("--work-dir must be separate from the source checkout")
    logs = output.parent / f"{output.stem}-logs"
    if output.exists() or logs.exists():
        parser.error("Choose a new --output path to preserve earlier evidence and logs")
    work.mkdir(parents=True, exist_ok=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    logs.mkdir()
    record = {
        "status": "failed",
        "upstream_revision": REVISION,
        "laproof_revision": LAPROOF_REVISION,
        "required_packages": REQUIRED_PACKAGES,
        "commands": [],
        "scope": (
            "Original CFEM.C.verif_quadrules and its source dependency closure, "
            "using the committed Clight syntax. Successful compilation accepts the "
            "upstream admitted lemmas; their assumptions are reported separately."
        ),
    }
    started = time.monotonic()

    def run(command, name):
        log = logs / f"{name}.txt"
        with log.open("w") as stream:
            completed = subprocess.run(
                command, cwd=work, stdout=stream, stderr=subprocess.STDOUT, text=True,
            )
        record["commands"].append({
            "argv": command, "returncode": completed.returncode,
            "log": str(log.relative_to(output.parent)), "sha256": sha256(log),
        })
        if completed.returncode:
            raise RuntimeError(f"{name} failed; see {log}")
        return log

    try:
        for checkout, revision in [(source, REVISION), (source / "LAProof", LAPROOF_REVISION)]:
            if captured(["git", "rev-parse", "HEAD"], checkout).strip() != revision:
                raise RuntimeError(f"Unexpected revision in {checkout}")
            subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=checkout, check=True)
        record["inputs"] = tracked_inputs(source)
        driver = Path(__file__).resolve()
        template = driver.parent / "upstream" / "SpecAudit.v"
        record["review_sources"] = {
            driver.name: sha256(driver),
            "upstream_sources.py": sha256(driver.parent / "upstream_sources.py"),
            "upstream/SpecAudit.v": sha256(template),
        }
        installed = captured(
            ["opam", "list", "--installed", "--columns=name,version", "--color=never"], work,
        )
        packages = dict(
            line.split()[:2] for line in installed.splitlines()
            if line.strip() and not line.startswith("#") and len(line.split()) >= 2
        )
        record["installed_packages"] = packages
        for name, version in REQUIRED_PACKAGES.items():
            if packages.get(name) != version:
                raise RuntimeError(f"{name}: expected {version}, found {packages.get(name)}")
        run(["coqc", "--version"], "rocq-version")
        run(["opam", "switch", "export", str(logs / "environment.opam")], "opam-export")
        record["environment_sha256"] = sha256(logs / "environment.opam")
        (work / "target_probe.c").write_text("int probe(void) { return 0; }\n")
        run(
            ["clightgen", "-normalize", "-o", "TargetProbe.v", "target_probe.c"],
            "compiler-target",
        )
        shutil.copy2(work / "TargetProbe.v", logs / "TargetProbe.v")
        record["target_configuration"] = {
            "committed_clight": clight_metadata(
                (source / "proof" / "C" / "quadrules.v").read_text(),
            ),
            "installed_compcert": clight_metadata((work / "TargetProbe.v").read_text()),
            "probe_sha256": sha256(logs / "TargetProbe.v"),
            "scope": (
                "The original Clight syntax is checked under the installed CompCert "
                "configuration. This does not reproduce the original Apple toolchain."
            ),
        }

        project_sources = [
            *source_files(source / "LAProof" / "_CoqProject"),
            *source_files(source / "proof" / "_CoqProject"),
        ]
        # The broader FEM project lists generated C modules that are absent from
        # the checkout. The quadrature target only needs the existing closure.
        record["absent_project_sources"] = [
            str(path.relative_to(source)) for path in project_sources if not path.is_file()
        ]
        sources = [path for path in project_sources if path.is_file()]
        record["preexisting_compiled_modules"] = [
            str(path.relative_to(source)) for path in sources if path.with_suffix(".vo").exists()
        ]
        project = work / "ReviewProject"
        project.write_text(
            f'-Q "{source / "LAProof"}" LAProof\n-Q "{source / "proof"}" CFEM\n'
            "-arg -w -arg -notation-overridden,-notation-incompatible-prefix,"
            "-ambiguous-paths,-deprecated-from-Coq\n"
            + "".join(f'"{path}"\n' for path in sources)
        )
        record["project_sha256"] = sha256(project)
        shutil.copy2(project, logs / "ReviewProject")
        run(["coq_makefile", "-f", str(project), "-o", "ReviewMakefile"], "makefile")
        run(
            ["make", "-f", "ReviewMakefile", f"-j{args.jobs}",
             str(source / "proof" / "C" / "verif_quadrules.vo")],
            "original-build",
        )
        record["compiled_modules"] = {
            str(path.relative_to(source)): sha256(path.with_suffix(".vo"))
            for path in sources if path.with_suffix(".vo").exists()
        }

        flags = ["-Q", str(source / "LAProof"), "LAProof",
                 "-Q", str(source / "proof"), "CFEM", "-Q", str(work), "UpstreamReview"]
        shutil.copy2(template, work / "SpecAudit.v")
        run(["coqc", *flags, "SpecAudit.v"], "specification-checks")
        assumption_dir = work / "assumptions"
        assumption_dir.mkdir(exist_ok=True)
        queries = work / "Assumptions.v"
        queries.write_text(
            "From CFEM.C Require Import verif_quadrules.\n"
            "From UpstreamReview Require Import SpecAudit.\n"
            + "".join(
                f'Redirect "assumptions/{index:02d}" Print Assumptions {name}.\n'
                for index, name in enumerate(QUERIES)
            )
        )
        run(["coqc", *flags, "Assumptions.v"], "assumption-queries")
        record["assumptions"] = {}
        for index, name in enumerate(QUERIES):
            path = assumption_dir / f"{index:02d}.out"
            text = path.read_text()
            destination = logs / f"assumptions-{index:02d}.txt"
            destination.write_text(text)
            record["assumptions"][name] = {
                "axioms": parse_assumptions(text),
                "log": str(destination.relative_to(output.parent)),
                "sha256": sha256(destination),
            }
        record["review_assumption_checks"] = {}
        for name in REVIEW_LEMMAS:
            baseline = None
            if name == "semax_body_ignores_identifier":
                baseline = VST_BODY_DEFINITION
            elif name == "body_hughes_weight_corrected_identifier":
                baseline = "CFEM.C.verif_quadrules.body_hughes_weight"
            allowed = set(record["assumptions"][baseline]["axioms"]) if baseline else set()
            actual = set(record["assumptions"][f"UpstreamReview.SpecAudit.{name}"]["axioms"])
            unexpected = sorted(actual - allowed)
            record["review_assumption_checks"][name] = {
                "baseline": baseline, "unexpected_axioms": unexpected,
            }
            if unexpected:
                raise RuntimeError(f"The review lemma {name} adds axioms: {unexpected}")
        run(
            ["coqchk", *flags, "-norec", "CFEM.C.verif_quadrules",
             "-norec", "UpstreamReview.SpecAudit"],
            "kernel-recheck",
        )
        record["kernel_recheck_scope"] = (
            "coqchk -norec checks the upstream body-proof module and the review module. "
            "Their dependencies were compiled above or during the source package build."
        )
        c = (source / "proof" / "C" / "quadrules.v").read_text()
        proof = (source / "proof" / "C" / "verif_quadrules.v").read_text()
        functions = re.findall(r"(?m)^Definition f_(\w+)\s*:=", c)
        bodies = re.findall(r"(?m)^Lemma body_(\w+)\s*:", proof)
        record["body_proof_coverage"] = {
            "internal_functions": functions,
            "body_lemmas": bodies,
            "functions_without_body_lemma": sorted(set(functions) - set(bodies)),
        }
        if tracked_inputs(source) != record["inputs"]:
            raise RuntimeError("Upstream sources changed during the review")
        if {
            driver.name: sha256(driver),
            "upstream_sources.py": sha256(driver.parent / "upstream_sources.py"),
            "upstream/SpecAudit.v": sha256(template),
        } != record["review_sources"]:
            raise RuntimeError("Review sources changed during the run")
        record["status"] = "passed"
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as exc:
        record["error"] = str(exc)
    finally:
        record["elapsed_seconds"] = round(time.monotonic() - started, 3)
        output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Upstream VST review: {record['status']} ({output})")
    if record["status"] != "passed":
        raise SystemExit(record.get("error", "Review failed"))


if __name__ == "__main__":
    main()
