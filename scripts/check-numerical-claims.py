#!/usr/bin/env python3
"""Check the paper's concrete numbers independently with exact rational arithmetic.

Inputs: the four pinned upstream sources named in SOURCE_NAMES (downloaded, or read from
--source-dir) and the project files listed in main. Output: the --output JSON record.
Requires only the standard library, plus network access when --source-dir is not given.
Binary64 rounding uses integer division with ties to even, transcendental values use alternating
series, and Legendre roots use rational bisection and interval arithmetic. This is a regression
check that imports neither floating-point library, not a substitute for the proofs.
"""

import argparse
from datetime import datetime, timezone
from fractions import Fraction as Q
import hashlib
import json
from math import factorial
from pathlib import Path
import re

from upstream_sources import LAPROOF_REVISION, REVISION, SOURCES, read_source


SOURCE_NAMES = ("quadrules.c", "quadmodel.v", "quadmodel_accuracy.v", "laproof-common.v")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def power2(exponent):
    return Q(2**exponent) if exponent >= 0 else Q(1, 2**-exponent)


def round_integer(value):
    quotient, remainder = divmod(value.numerator, value.denominator)
    twice = 2 * remainder
    return quotient + int(twice > value.denominator or
                          (twice == value.denominator and quotient % 2 == 1))


def binary64_bits(value):
    """Round a rational to finite binary64; exact zero is encoded as +0."""
    value = Q(value)
    if value == 0:
        return 0
    sign = (1 << 63) if value < 0 else 0
    value = abs(value)
    exponent = value.numerator.bit_length() - value.denominator.bit_length()
    if value < power2(exponent):
        exponent -= 1
    if exponent < -1022:
        return sign | round_integer(value / power2(-1074))
    significand = round_integer(value / power2(exponent - 52))
    if significand == 2**53:
        significand //= 2
        exponent += 1
    require(exponent <= 1023, "The independent calculation overflowed.")
    return sign | ((exponent + 1023) << 52) | (significand - 2**52)


def decode(bits):
    require(0 <= bits < 2**64, "Invalid binary64 encoding.")
    sign = -1 if bits >> 63 else 1
    exponent = (bits >> 52) & 0x7FF
    significand = bits & (2**52 - 1)
    require(exponent != 0x7FF, "The independent calculation requires finite values.")
    if exponent == 0:
        return sign * significand * power2(-1074)
    return sign * (2**52 + significand) * power2(exponent - 1075)


def rounded(value):
    return decode(binary64_bits(value))


def interval_mul(left, right):
    products = [a * b for a in left for b in right]
    return min(products), max(products)


def polynomial_interval(coefficients, interval):
    result = (Q(0), Q(0))
    for coefficient in reversed(coefficients):
        lo, hi = interval_mul(result, interval)
        result = lo + coefficient, hi + coefficient
    return result


def polynomial_value(coefficients, x):
    return polynomial_interval(coefficients, (x, x))[0]


def legendre_coefficients(n):
    """Standard normalization P_n(1) = 1, using the three-term recurrence."""
    previous, current = [Q(1)], [Q(0), Q(1)]
    if n == 0:
        return previous
    for k in range(1, n):
        next_polynomial = [Q(0)] * (k + 2)
        for i, coefficient in enumerate(current):
            next_polynomial[i + 1] += Q(2 * k + 1, k + 1) * coefficient
        for i, coefficient in enumerate(previous):
            next_polynomial[i] -= Q(k, k + 1) * coefficient
        previous, current = current, next_polynomial
    return current


def isolate_root(coefficients, stored):
    tolerance = Q(6, 10**16)
    lo, hi = stored - tolerance, stored + tolerance
    left, right = polynomial_value(coefficients, lo), polynomial_value(coefficients, hi)
    require(left * right < 0, "A stored node has no sign-changing root bracket.")
    for _ in range(100):
        mid = (lo + hi) / 2
        value = polynomial_value(coefficients, mid)
        if value == 0:
            return mid, mid
        if left * value < 0:
            hi = mid
        else:
            lo, left = mid, value
    return lo, hi


def weight_interval(coefficients, root):
    derivative = [i * coefficient for i, coefficient in enumerate(coefficients)][1:]
    derivative_interval = polynomial_interval(derivative, root)
    derivative_squared = interval_mul(derivative_interval, derivative_interval)
    x_squared = interval_mul(root, root)
    denominator = interval_mul(
        (1 - x_squared[1], 1 - x_squared[0]), derivative_squared)
    require(denominator[0] > 0, "The Gaussian weight denominator is not positive.")
    return 2 / denominator[1], 2 / denominator[0]


def alternating_enclosure(term, count=24):
    partial = sum((term(k) for k in range(count)), Q(0))
    next_partial = partial + term(count)
    return min(partial, next_partial), max(partial, next_partial)


def absolute_error_interval(value, reference):
    lo, hi = value - reference[1], value - reference[0]
    lower = 0 if lo <= 0 <= hi else min(abs(lo), abs(hi))
    return Q(lower), max(abs(lo), abs(hi))


def interval_record(interval):
    return {"lower": str(interval[0]), "upper": str(interval[1]),
            "approximate_midpoint": float(sum(interval) / 2)}


def extract_list(text, pattern, separator):
    match = re.search(pattern, text, re.S)
    require(match is not None, f"Missing source list: {pattern}")
    return [item.strip() for item in match.group(1).split(separator) if item.strip()]


def parse_cases(text, name, rocq=False):
    pattern = (rf"Definition {name}\b.*?:=.*?\n(.*?)\n  end\."
               if rocq else rf"def {name}\b[^\n]*\n(.*?)(?:\n\n|\Z)")
    match = re.search(pattern, text, re.S)
    require(match is not None, f"Missing definition: {name}")
    cases = dict((int(n), value) for n, value in re.findall(
        r"^\s*\|\s*(\d+)(?:%nat)?\s*=>\s*(.*?)\s*$", match.group(1), re.M))
    require(set(cases) == set(range(1, 11)), f"Incomplete order cases: {name}")
    return cases


def parse_rational(text):
    numerator, denominator = text.split("/")
    powers = denominator.strip().split("^")
    require(len(powers) <= 2 and all(p.strip().isdigit() for p in powers),
            f"Unexpected rational denominator: {text}")
    denominator_value = int(powers[0]) ** (int(powers[1]) if len(powers) == 2 else 1)
    return Q(int(numerator), denominator_value)


def overflow_counterexamples():
    """Check the hand-transcribed helper inequalities, as in the Lean proof.

    The content-checked source and its pinned LAProof definitions identify
    the formulas. Neither this script nor the Lean module translates Rocq.
    """
    epsilon, eta, threshold = power2(-53), power2(-1075), power2(1024)
    bound = threshold / 4
    parameter = (1 + epsilon / (1 + epsilon)) * (2 + epsilon) * bound + eta
    product = 2 * bound * (1 + epsilon) + eta
    maxwf = bound * epsilon**2 + 3 * bound * epsilon + eta
    summation_left = 2 * bound + maxwf
    summation_right = threshold / (1 + epsilon) / 2
    require(parameter < threshold, "The positive-order witness violates parameter_limits.")
    require(product < threshold, "The positive-order witness fails the product helper.")
    require(summation_right < threshold / 2 < summation_left,
            "The positive-order summation counterexample failed.")
    zero_product = 2 * threshold * (1 + epsilon) + eta
    require(0 < threshold < zero_product, "The zero-order product counterexample failed.")
    return {
        "constants": {"unit_roundoff": "2^-53", "absolute_roundoff": "2^-1075",
                      "overflow_threshold": "2^1024"},
        "one_node": {
            "function_bound": "2^1022", "callback_error": "0", "derivative_bound": "0",
            "parameter_left_divided_by_threshold": str(parameter / threshold),
            "product_left_divided_by_threshold": str(product / threshold),
            "summation_left_divided_by_threshold": str(summation_left / threshold),
            "summation_right_divided_by_threshold": str(summation_right / threshold),
            "parameter_limits_holds": True, "product_helper_holds": True,
            "summation_helper_is_false": True,
        },
        "zero_nodes": {
            "function_bound": "2^1024", "callback_error": "0", "derivative_bound": "0",
            "parameter_left": "0", "parameter_limits_holds": True,
            "product_helper_is_false": True,
        },
        "scope": "False real helper inequalities; no overflowing execution is claimed.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path,
                        help="Read the four content-checked source files here instead of downloading.")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    sources, hashes = {}, {}
    for name in SOURCE_NAMES:
        content = read_source(name, args.source_dir)
        hashes[name] = SOURCES[name][1]
        sources[name] = content.decode()

    project_paths = [
        "Quadrature/Clight/TableData.lean", "Quadrature/Examples/PolynomialRules.lean",
        "Quadrature/Clight/StoredAccuracy.lean", "compcert/InternalCosine.v",
        "compcert/StoredPolynomialAccuracy.v", "Quadrature/Examples/Overflow.lean",
        "scripts/check-numerical-claims.py", "scripts/upstream_sources.py",
    ]
    project_inputs = {path: (root / path).read_bytes() for path in project_paths}
    project = {path: content.decode() for path, content in project_inputs.items()}
    project_hashes = {path: hashlib.sha256(content).hexdigest()
                      for path, content in project_inputs.items()}
    c_text = re.sub(r"/\*.*?\*/", "", sources["quadrules.c"], flags=re.S)
    model_text = re.sub(r"\(\*.*?\*\)", "", sources["quadmodel.v"], flags=re.S)
    tables, mismatches = {}, []
    for kind, c_name, lean_name in [
        ("nodes", "gauss_pts", "nodeBits"), ("weights", "gauss_wts", "weightBits"),
    ]:
        c_literals = extract_list(c_text, rf"{c_name}\[\]\s*=\s*\{{(.*?)\}}", ",")
        model_literals = extract_list(
            model_text, rf"Definition {c_name}_list\b.*?:=\s*\[(.*?)\]%F64", ";")
        lean_literals = extract_list(project["Quadrature/Clight/TableData.lean"],
                                     rf"def {lean_name}\b.*?:=\s*\[(.*?)\]", ",")
        c_bits = [binary64_bits(Q(value)) for value in c_literals]
        model_bits = [binary64_bits(Q(value)) for value in model_literals]
        require(len(c_bits) == len(model_bits) == 55, f"Unexpected {kind} table length.")
        require(c_bits == [int(value, 0) for value in lean_literals],
                f"Original C {kind} differ from the imported Lean table.")
        for index, (c_value, model_value) in enumerate(zip(c_bits, model_bits)):
            if c_value != model_value:
                mismatches.append({"table": kind, "zero_based_index": index,
                                   "c_literal": c_literals[index],
                                   "model_literal": model_literals[index],
                                   "c_bits": f"{c_value:016x}",
                                   "model_bits": f"{model_value:016x}"})
        tables[kind] = list(map(decode, c_bits))
    require([(item["table"], item["zero_based_index"]) for item in mismatches] ==
            [("weights", 3), ("weights", 5)], "The upstream table mismatch has changed.")

    coefficient_bits = [binary64_bits(Q((-1)**k, factorial(2 * k))) for k in range(8)]
    lean_coefficients = extract_list(project["Quadrature/Examples/PolynomialRules.lean"],
                                     r"def coefficients\b.*?:=\s*\[(.*?)\]", ",")
    rocq_coefficients = extract_list(project["compcert/InternalCosine.v"],
                                     r"Definition coefficients\b.*?\[(.*?)\]", ";")
    require(coefficient_bits == list(map(int, lean_coefficients)) ==
            list(map(int, rocq_coefficients)), "The Taylor coefficient encodings differ.")
    coefficients = list(map(decode, coefficient_bits))
    lean_results = parse_cases(project["Quadrature/Clight/StoredAccuracy.lean"], "resultBits")
    rocq_results = parse_cases(project["compcert/StoredPolynomialAccuracy.v"],
                              "result_bits", rocq=True)
    lean_bounds = parse_cases(project["Quadrature/Clight/StoredAccuracy.lean"], "errorBound")
    rocq_bounds = parse_cases(project["compcert/StoredPolynomialAccuracy.v"],
                             "error_bound", rocq=True)
    sine = alternating_enclosure(lambda k: Q((-1)**k, factorial(2 * k + 1)))
    cosine_node = alternating_enclosure(lambda k: Q((-1)**k, 3**k * factorial(2 * k)))
    one_error = absolute_error_interval(Q(1), sine)
    two_error = sine[0] - cosine_node[1], sine[1] - cosine_node[0]
    require(Q(2, 100) < one_error[0] <= one_error[1] < Q(159, 1000),
            "The one-node counterexample or corrected bound failed.")
    require(Q(223, 100000) < two_error[0] <= two_error[1] < Q(356, 100000),
            "The two-node counterexample or corrected bound failed.")
    require(Q(8414709848078965, 10**16) <= sine[0] <= sine[1] <=
            Q(8414709848078966, 10**16), "The stated sine enclosure failed.")
    outer_weight_error = abs(tables["weights"][3] - Q(5, 9))
    require(outer_weight_error == Q(19, 40532396646334464) > Q(1, 2**53),
            "The three-node weight counterexample failed.")
    quartic_error = Q(2, 5) - 2 * Q(1, 3)**2
    require(quartic_error == Q(8, 45), "The quartic counterexample failed.")

    orders, largest_node_error, largest_weight_error = [], Q(0), Q(0)
    for n in range(1, 11):
        offset = n * (n - 1) // 2
        nodes = tables["nodes"][offset:offset + n]
        weights = tables["weights"][offset:offset + n]
        polynomial = legendre_coefficients(n)
        previous_root_hi, result = Q(-1), Q(0)
        for node, weight in zip(nodes, weights):
            bracket = isolate_root(polynomial, node)
            require(-1 < bracket[0] <= bracket[1] < 1 and previous_root_hi < bracket[0],
                    "The Legendre root brackets are not distinct and interior.")
            previous_root_hi = bracket[1]
            node_error = absolute_error_interval(node, bracket)[1]
            weight_error = absolute_error_interval(weight, weight_interval(polynomial, bracket))[1]
            largest_node_error = max(largest_node_error, node_error)
            largest_weight_error = max(largest_weight_error, weight_error)
            require(node_error <= Q(6, 10**16), f"Order {n}: node tolerance failed.")
            require(weight_error <= Q(5, 10**16), f"Order {n}: weight tolerance failed.")
            square, horner = rounded(node * node), Q(0)
            for coefficient in reversed(coefficients):
                horner = rounded(coefficient + rounded(square * horner))
            callback = rounded(rounded(Q(1, 2) * rounded(1 - node)) * horner)
            result = rounded(result + rounded(weight * callback))
        bits = binary64_bits(result)
        require(bits == int(lean_results[n], 0) == int(rocq_results[n]),
                f"Order {n}: the independent result differs from Lean or Rocq.")
        bound = parse_rational(lean_bounds[n])
        require(bound == parse_rational(rocq_bounds[n]),
                f"Order {n}: Lean and Rocq advertise different bounds.")
        error = absolute_error_interval(result, sine)
        require(error[1] <= bound, f"Order {n}: the advertised error bound failed.")
        orders.append({"order": n, "result_bits": f"{bits:016x}",
                       "result_exact": str(result), "error": interval_record(error),
                       "claimed_bound": str(bound)})
    require(Q(orders[6]["error"]["upper"]) < Q(orders[7]["error"]["lower"]),
            "The seven-node versus eight-node comparison failed.")
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "kind": "Independent exact-rational numerical regression check; not a formal proof",
        "upstream_revision": REVISION, "upstream_sha256": hashes,
        "laproof_revision": LAPROOF_REVISION,
        "source_urls": {name: SOURCES[name][0] for name in SOURCE_NAMES},
        "project_sha256": project_hashes,
        "method": [
            "Integer nearest-even rounding, separately at every multiplication and addition.",
            "24-term alternating series with the next term bounding each transcendental value.",
            "Distinct rational sign-changing brackets for every Legendre root; 100 bisections.",
            "Rational interval evaluation of 2 / ((1-x*x) * P_n'(x)^2) for the weights.",
            "No Lean, FloatLib, Rocq, Flocq, libm, or host floating-point evaluation in the checks.",
            "Approximate midpoints in this JSON are display values only.",
            "The rational evaluator forgets zero signs; this check makes no general signed-zero claim.",
        ],
        "table_mismatches": mismatches,
        "one_node_ideal_error": interval_record(one_error),
        "two_node_ideal_error": interval_record(two_error),
        "outer_weight_error": str(outer_weight_error),
        "quartic_two_node_error": str(quartic_error),
        "overflow_helpers": overflow_counterexamples(),
        "maximum_node_error_upper": str(largest_node_error),
        "maximum_weight_error_upper": str(largest_weight_error),
        "coefficient_bits": [f"{bits:016x}" for bits in coefficient_bits],
        "orders": orders,
    }
    require(all((root / path).read_bytes() == content
                for path, content in project_inputs.items()),
            "Project inputs changed during the numerical check.")
    record["inputs_unchanged"] = True
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print("Passed: four original findings, two overflow-helper counterexamples, "
          "110 table entries, eight coefficients, and all ten Lean/Rocq results and error bounds.")
    print(f"Report: {args.output}")


if __name__ == "__main__":
    main()
