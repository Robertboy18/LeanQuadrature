"""Check that incomplete or misleading native-C regression results are rejected.

Inputs: check-upstream-c.py, loaded with runpy. Output: unittest results.
Requires scripts/check-upstream-c.py and scripts/upstream_sources.py.
"""

from pathlib import Path
import math
import runpy
import struct
import sys
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
CHECKER = runpy.run_path(str(Path(__file__).resolve().parents[1] / "check-upstream-c.py"))
check_output = CHECKER["check_output"]
expected_moments = CHECKER["expected_moments"]


def complete_output():
    """Nearest binary64 references stand in for the harness's output protocol."""
    moments = "\n".join(
        " ".join(map(str, key)) + " " + struct.pack(">d", float(value)).hex()
        for key, value in expected_moments().items()
    )
    return (moments + "\ncosine 2 0 " + struct.pack(">d", 0.83791182769499317).hex()
            + "\nreference 1 0 " + struct.pack(">d", math.sin(1)).hex())


class DomainCoverageTests(unittest.TestCase):
    def test_covers_every_advertised_monomial(self):
        cases = expected_moments()
        self.assertEqual(sum(key[0] == "line" for key in cases), 110)
        self.assertEqual(sum(key[0] == "square" for key in cases), 220)
        self.assertEqual(sum(key[0] == "triangle" for key in cases), 6)
        self.assertIn(("line", 10, 19), cases)
        self.assertIn(("square", 25, 9, 9), cases)
        self.assertIn(("triangle", 2, 0), cases)
        self.assertEqual(len(check_output(complete_output(), {})["monomial_checks"]), 336)

    def test_missing_case_fails(self):
        lines = complete_output().splitlines()
        with self.assertRaisesRegex(RuntimeError, "Missing C results"):
            check_output("\n".join(lines[:-1]), {})

    def test_duplicate_case_fails(self):
        output = complete_output()
        with self.assertRaisesRegex(RuntimeError, "Duplicate C result"):
            check_output(output + "\n" + output.splitlines()[0], {})

    def test_unexpected_case_fails(self):
        with self.assertRaisesRegex(RuntimeError, "Unexpected C result"):
            check_output(complete_output() + "\nline 11 0 4000000000000000", {})

    def test_nonfinite_result_fails(self):
        output = complete_output().replace("4000000000000000", "7ff0000000000000", 1)
        with self.assertRaisesRegex(RuntimeError, "Nonfinite C result"):
            check_output(output, {})

    def test_incorrect_integral_fails(self):
        output = complete_output().replace("4000000000000000", "3ff0000000000000", 1)
        with self.assertRaisesRegex(RuntimeError, "Monomial check failed"):
            check_output(output, {})

    def test_changed_table_word_fails(self):
        with self.assertRaisesRegex(RuntimeError, "C/Lean table mismatch"):
            check_output("node 1 0 3ff0000000000000", {("node", 1, 0): 0})

    def test_cosine_result_must_exceed_advertised_bound(self):
        output = complete_output().replace(
            struct.pack(">d", 0.83791182769499317).hex(),
            struct.pack(">d", math.sin(1)).hex())
        with self.assertRaisesRegex(RuntimeError, "advertised-bound failure"):
            check_output(output, {})

    def test_nonfinite_cosine_reference_fails(self):
        output = complete_output().replace(
            "reference 1 0 " + struct.pack(">d", math.sin(1)).hex(),
            "reference 1 0 7ff8000000000000")
        with self.assertRaisesRegex(RuntimeError, "Nonfinite C result"):
            check_output(output, {})

    def test_incorrect_cosine_reference_fails(self):
        output = complete_output().replace(
            "reference 1 0 " + struct.pack(">d", math.sin(1)).hex(),
            "reference 1 0 " + struct.pack(">d", 1).hex())
        with self.assertRaisesRegex(RuntimeError, "Unexpected native sin"):
            check_output(output, {})


if __name__ == "__main__":
    unittest.main()
