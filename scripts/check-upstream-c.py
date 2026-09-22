#!/usr/bin/env python3
"""Exercise every stored rule of the original C quadrature implementation natively.

Inputs: the pinned quadrules.c and quadrules.h (downloaded, or read from --source-dir), the
--compiler (clang by default), Quadrature/Clight/TableData.lean, and
scripts/tests/upstream_quadrature.c. Output: the --output JSON record and a sibling logs
directory named after it.
Requires a C compiler with address and undefined-behavior sanitizers. All 110 stored words are
checked against Lean and 336 monomial integrals against exact rational references. The original
cosine example is also compared with the platform's sin(1) and the paper's error bound.
This is a native regression experiment, not a proof of the C semantics or libm accuracy.
"""

import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import re
import struct
import subprocess
import tempfile

from upstream_sources import REVISION, SOURCES, read_source


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def line_moment(degree):
    return Fraction(0) if degree % 2 else Fraction(2, degree + 1)


def expected_moments():
    cases = {
        ("line", n, k): line_moment(k)
        for n in range(1, 11) for k in range(2 * n)
    }
    cases.update({
        ("square", d * d, px, py): line_moment(px) * line_moment(py)
        for d in range(1, 6) for px in range(2 * d) for py in range(2 * d)
    })
    cases.update({
        ("triangle", px, py):
            Fraction(math.factorial(px) * math.factorial(py), math.factorial(px + py + 2))
        for px in range(3) for py in range(3 - px)
    })
    return cases


def expected_tables(source):
    cases = {}
    for kind, name in (("node", "nodeBits"), ("weight", "weightBits")):
        match = re.search(rf"def {name}\b[^[]*\[([^]]*)\]", source, re.S)
        require(match is not None, f"Missing Lean table: {name}")
        entries = [int(value.strip(), 0) for value in match[1].split(",") if value.strip()]
        require(len(entries) == 55, f"Wrong length for {name}")
        for n in range(1, 11):
            for i in range(n):
                cases[kind, n, i] = entries[n * (n - 1) // 2 + i]
    return cases


def check_output(output, tables):
    """Require the complete case set; reject duplicate, missing and extra records."""
    moments = expected_moments()
    cosine_key, reference_key = ("cosine", 2, 0), ("reference", 1, 0)
    expected = set(tables) | set(moments) | {cosine_key, reference_key}
    seen, errors, example = set(), [], {}
    for line in output.splitlines():
        fields = line.split()
        require(len(fields) >= 4, f"Malformed C result: {line}")
        key = (fields[0], *(int(value) for value in fields[1:-1]))
        require(key in expected, f"Unexpected C result: {key}")
        require(key not in seen, f"Duplicate C result: {key}")
        require(re.fullmatch(r"[0-9a-f]{16}", fields[-1]) is not None,
                f"Malformed binary64 word: {line}")
        seen.add(key)
        bits = int(fields[-1], 16)
        if key in tables:
            require(bits == tables[key], f"C/Lean table mismatch at {key}")
            continue
        value = struct.unpack(">d", bits.to_bytes(8, "big"))[0]
        require(math.isfinite(value), f"Nonfinite C result: {key}")
        if key in (cosine_key, reference_key):
            example[key] = value
            continue
        exact = moments[key]
        error = abs(Fraction(value) - exact)
        # A regression tolerance, not a proved error bound. It includes decimal
        # table approximation and the rounding in monomial evaluation and summation.
        tolerance = Fraction(64, 2**52) * max(1, abs(exact))
        require(error <= tolerance, f"Monomial check failed at {key}: {error} > {tolerance}")
        errors.append({
            "case": list(key), "result_bits": fields[-1], "reference": str(exact),
            "absolute_error": str(error), "test_tolerance": str(tolerance),
        })
    require(seen == expected, f"Missing C results: {sorted(expected - seen)}")
    result, reference = example[cosine_key], example[reference_key]
    error = abs(Fraction(result) - Fraction(reference))
    require(abs(reference - math.sin(1)) <= 2 * math.ulp(math.sin(1)),
            "Unexpected native sin(1) reference")
    require(Fraction(224, 100000) < error <= Fraction(356, 100000),
            "Cosine example does not reproduce the advertised-bound failure")
    return {
        "monomial_checks": errors,
        "cosine_example": {
            "result": result,
            "reference_sin_one": reference,
            "absolute_error": str(error),
            "advertised_bound": "0.00224",
            "corrected_bound": "0.00356",
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path,
                        help="Directory containing the pinned quadrules.c and quadrules.h.")
    parser.add_argument("--compiler", default="clang")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    table_path = repo / "Quadrature/Clight/TableData.lean"
    harness = repo / "scripts/tests/upstream_quadrature.c"
    project_inputs = {
        path: path.read_bytes()
        for path in (table_path, harness, Path(__file__), repo / "scripts/upstream_sources.py")
    }
    tables = expected_tables(project_inputs[table_path].decode())
    logs = args.output.parent / f"{args.output.stem}-logs"
    logs.mkdir(parents=True, exist_ok=True)
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "Native C regression experiment with address and undefined-behavior sanitizers",
        "upstream_revision": REVISION,
        "source_sha256": {name: SOURCES[name][1] for name in ("quadrules.c", "quadrules.h")},
        "project_sha256": {
            str(path.relative_to(repo)): hashlib.sha256(content).hexdigest()
            for path, content in project_inputs.items()
        },
        "status": "failed",
    }
    try:
        with tempfile.TemporaryDirectory(prefix="quadrature-c-domain-") as directory:
            work = Path(directory)
            for name in ("quadrules.c", "quadrules.h"):
                (work / name).write_bytes(read_source(name, args.source_dir))
            checked_harness = work / harness.name
            checked_harness.write_bytes(project_inputs[harness])
            compiler = subprocess.run([args.compiler, "--version"], check=True, text=True,
                                      capture_output=True).stdout
            record["compiler"] = compiler.splitlines()[0]
            command = [
                args.compiler, "-std=c11", "-O2", "-Wall", "-Wextra", "-Wpedantic",
                "-Wconversion", "-Wshadow", "-fno-builtin", "-ffp-contract=off",
                "-fsanitize=address,undefined", "-fno-sanitize-recover=all",
                "-fno-omit-frame-pointer", "-I", str(work),
                str(work / "quadrules.c"), str(checked_harness), "-lm", "-o", str(work / "check"),
            ]
            record["build_command"] = command
            with (logs / "build.txt").open("w") as stream:
                subprocess.run(command, check=True, stdout=stream, stderr=subprocess.STDOUT)
            environment = dict(os.environ)
            environment["ASAN_OPTIONS"] = "detect_leaks=1:halt_on_error=1"
            environment["UBSAN_OPTIONS"] = "halt_on_error=1:print_stacktrace=1"
            result = subprocess.run([str(work / "check")], text=True, capture_output=True,
                                    env=environment)
            (logs / "results.txt").write_text(result.stdout)
            (logs / "sanitizers.txt").write_text(result.stderr)
            require(result.returncode == 0, f"C harness failed with exit {result.returncode}")
            record.update(check_output(result.stdout, tables))
            record["table_words_checked"] = len(tables)
            require(all(path.read_bytes() == content for path, content in project_inputs.items()),
                    "Project inputs changed during the C regression check")
            record["inputs_unchanged"] = True
            record["status"] = "passed"
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        record["error"] = str(error)
        raise
    finally:
        record["logs"] = {
            path.name: {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
            for path in sorted(logs.glob("*.txt"))
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Passed: {len(tables)} table words, {len(record['monomial_checks'])} monomials, "
          "and the original cosine example.")
    print(f"Report: {args.output}")


if __name__ == "__main__":
    main()
