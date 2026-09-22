#!/usr/bin/env python3
"""Check the paired FloatLib and CompCert exceptional-value certificates in both kernels.

Inputs: --compcert-root, --work-dir. Output: the --output JSON record (the retained run is
evidence/exceptional-values.json) with lean.log and rocq.log in the work directory.
Requires the project's local Lean build through scripts/run-local.sh, a built unmodified
CompCert 3.17 x86_64 tree, and Docker with the pinned Coq image. Neither kernel imports the
other kernel's proof or semantics.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


COMPCERT_REVISION = "7b1f02b09954b9b916eb2a91d283c9b5355bf172"
FLOATLIB_REVISION = "393bea610296bf9a9ee5a479508c351edb65cc6d"
IMAGE = "coqorg/coq@sha256:18ebf3da56e60e3ddfd7d4e51f4c53d10241a129f34e93dacbc71562dd43c57a"
COQC = "/home/coq/.opam/4.13.1+flambda/bin/coqc"
ROCQ_ASSUMPTIONS = {
    "ClassicalDedekindReals.sig_not_dec",
    "ClassicalDedekindReals.sig_forall_dec",
    "FunctionalExtensionality.functional_extensionality_dep",
    "Classical_Prop.classic",
}
LEAN_AUDIT = """import Quadrature.Binary64.ExceptionalValues
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let expected := #[
    ``Quadrature.Binary64.ExceptionalValues.mixed_nan_add,
    ``Quadrature.Binary64.ExceptionalValues.mixed_nan_mul,
    ``Quadrature.Binary64.ExceptionalValues.opposite_infinities_add,
    ``Quadrature.Binary64.ExceptionalValues.infinity_zero_mul,
    ``Quadrature.Binary64.ExceptionalValues.zero_div_zero,
    ``Quadrature.Binary64.ExceptionalValues.finite_sub_nan]
  let mut checked : Nat := 0
  let mut requested : Nat := 0
  for (name, info) in env.constants do
    if name.toString.startsWith "Quadrature.Binary64.ExceptionalValues." then
      if info.isAxiom then
        throwError m!"Project axiom: {name}"
      if info.isTheorem then
        for axiomName in ← collectAxioms name do
          unless allowed.contains axiomName do
            throwError m!"Unexpected dependency: {name}: {axiomName}"
        checked := checked + 1
        if expected.contains name then
          requested := requested + 1
  unless requested == 6 do
    throwError m!"Expected six exceptional-value certificates, got {requested}"
  logInfo m!"Audited {checked} declarations, including all six requested certificates."
"""


def run(command, **kwargs):
    result = subprocess.run(
        command, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, **kwargs
    )
    if result.returncode:
        raise RuntimeError(f"{command[0]} failed:\n{result.stdout}")
    return result.stdout


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compcert-root", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    root = args.compcert_root.resolve(strict=True)
    work = args.work_dir.resolve()
    if (work.is_relative_to(root) or work.is_relative_to(repo) or
            work.is_relative_to("/efs")):
        raise ValueError("Use a local work directory outside both source trees.")
    if work.exists() and any(work.iterdir()):
        raise ValueError("The work directory must be empty.")
    work.mkdir(parents=True, exist_ok=True)

    if run(["git", "-C", str(root), "rev-parse", "HEAD"]).strip() != COMPCERT_REVISION:
        raise ValueError("Unexpected CompCert revision.")
    run(["git", "-C", str(root), "diff", "--exit-code", "HEAD", "--", "*.v"])
    for name in ["lib/Floats.vo", "lib/Integers.vo", "x86_64/Archi.vo"]:
        if not (root / name).is_file():
            raise ValueError(f"Missing compiled dependency: {name}")

    lean_source = repo / "Quadrature/Binary64/ExceptionalValues.lean"
    rocq_source = repo / "compcert/ExceptionalValues.v"
    if re.search(r"\b(sorry|axiom|native_decide)\b", lean_source.read_text()):
        raise ValueError("Unproved Lean declarations or native decision procedure.")
    if re.search(r"\b(Admitted|admit|Axioms?|Parameters?|Abort|native_compute)\b",
                 rocq_source.read_text()):
        raise ValueError("Unproved Rocq declarations or native computation.")
    (work / "ExceptionalValues.v").write_bytes(rocq_source.read_bytes())
    (work / "LeanAudit.lean").write_text(LEAN_AUDIT)

    local = [str(repo / "scripts/run-local.sh")]
    print("Building the Lean exceptional-value certificates", flush=True)
    lean_log = run(local + ["lake", "build", "Quadrature.Binary64.ExceptionalValues"])
    lean_log += run(local + ["lake", "env", "lean", str(work / "LeanAudit.lean")])
    lean_version = run(local + ["lake", "env", "lean", "--version"]).strip()
    floatlib_revision = run(local + [
        "git", "-C", ".lake/packages/floatlib", "rev-parse", "HEAD"
    ]).strip()
    if floatlib_revision != FLOATLIB_REVISION:
        raise ValueError("Unexpected FloatLib revision.")
    run(local + ["git", "-C", ".lake/packages/floatlib",
                 "diff", "--exit-code", "HEAD", "--", "*.lean"])
    (work / "lean.log").write_text(lean_log)

    common = [
        "docker", "run", "--rm", "--read-only", "--network", "none",
        "--user", f"{os.getuid()}:{os.getgid()}",
        "-v", f"{root}:/compcert:ro", "-v", f"{work}:/work",
        "--entrypoint", COQC, IMAGE,
    ]
    load_path = []
    for name in ["lib", "common", "x86_64"]:
        load_path += ["-R", f"/compcert/{name}", f"compcert.{name}"]
    load_path += ["-R", "/compcert/flocq", "Flocq"]
    print("Checking the Rocq exceptional-value certificates", flush=True)
    rocq_log = run(common + load_path + ["/work/ExceptionalValues.v"])
    (work / "rocq.log").write_text(rocq_log)
    assumptions = set()
    if rocq_log.count("Axioms:\n") != 6:
        raise ValueError("Expected six Rocq assumption audits.")
    for section in rocq_log.split("Axioms:\n")[1:]:
        assumptions.update(re.findall(
            r"^([A-Za-z_][A-Za-z0-9_.']*)[ \t]*:", section, re.M
        ))
    if assumptions != ROCQ_ASSUMPTIONS:
        raise ValueError(f"Unexpected Rocq dependencies: {sorted(assumptions)}")
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "independent kernel certificates for six exceptional-value disagreements",
        "lean_version": lean_version,
        "floatlib_revision": floatlib_revision,
        "compcert_revision": COMPCERT_REVISION,
        "compcert_target": "x86_64",
        "rocq_version": run(common + ["--version"]).strip(),
        "container_image": IMAGE,
        "checker_sha256": digest(Path(__file__)),
        "lean_proof_sha256": digest(lean_source),
        "rocq_proof_sha256": digest(rocq_source),
        "lean_audit_sha256": digest(work / "LeanAudit.lean"),
        "lean_log_sha256": digest(work / "lean.log"),
        "rocq_log_sha256": digest(work / "rocq.log"),
        "rocq_assumptions": sorted(assumptions),
        "certificates_per_kernel": 6,
        "cross_kernel_proof_translation": False,
        "finite_operation_correspondence_proved": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Both sets of certificates and assumption audits passed: {args.output}")


if __name__ == "__main__":
    main()
