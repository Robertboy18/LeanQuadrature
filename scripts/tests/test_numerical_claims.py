"""Check the independent numerical checker's rounding boundaries and fail-closed source parsing.

Inputs: check-numerical-claims.py, loaded with runpy. Output: unittest results.
Requires scripts/check-numerical-claims.py and scripts/upstream_sources.py.
"""

from fractions import Fraction as Q
from pathlib import Path
import runpy
import struct
import sys
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
CHECKER = runpy.run_path(str(Path(__file__).resolve().parents[1] /
                             "check-numerical-claims.py"))
binary64_bits = CHECKER["binary64_bits"]
decode = CHECKER["decode"]
parse_cases = CHECKER["parse_cases"]


class RationalRoundingTests(unittest.TestCase):
    def test_ties_choose_even_significand(self):
        self.assertEqual(binary64_bits(1 + Q(1, 2**53)), 0x3FF0000000000000)
        self.assertEqual(binary64_bits(1 + Q(3, 2**53)), 0x3FF0000000000002)
        self.assertEqual(binary64_bits(-1 - Q(1, 2**53)), 0xBFF0000000000000)

    def test_rounding_carries_into_next_exponent(self):
        self.assertEqual(binary64_bits(2 - Q(1, 2**53)), 0x4000000000000000)

    def test_subnormal_boundaries(self):
        self.assertEqual(binary64_bits(Q(1, 2**1075)), 0)
        self.assertEqual(binary64_bits(Q(3, 2**1075)), 2)
        self.assertEqual(binary64_bits(Q(1, 2**1022) - Q(1, 2**1075)),
                         0x0010000000000000)

    def test_decode_and_round_against_host_conversions(self):
        # These include both signs, a subnormal, and both sides of a binade.
        encodings = [1, 0x0010000000000000, 0x3FEFFFFFFFFFFFFF,
                     0x3FF0000000000001, 0xBFE279A74590331C,
                     0x7FEFFFFFFFFFFFFF]
        for bits in encodings:
            with self.subTest(bits=bits):
                host = struct.unpack(">d", bits.to_bytes(8, "big"))[0]
                self.assertEqual(decode(bits), Q(host))
                self.assertEqual(binary64_bits(Q(host)), bits)

    def test_nonfinite_values_are_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "finite"):
            decode(0x7FF0000000000000)
        with self.assertRaisesRegex(RuntimeError, "overflowed"):
            binary64_bits(Q(2**1024))


class SourceParsingTests(unittest.TestCase):
    def test_lean_equation_syntax_without_assignment(self):
        source = "def resultBits : Nat → Nat\n"
        source += "\n".join(f"  | {n} => {n}" for n in range(1, 11))
        source += "\n  | _ => 0\n\n"
        self.assertEqual(parse_cases(source, "resultBits"),
                         {n: str(n) for n in range(1, 11)})

    def test_missing_order_cannot_pass(self):
        with self.assertRaisesRegex(RuntimeError, "Incomplete order"):
            parse_cases("def resultBits : Nat → Nat\n  | 1 => 42\n\n", "resultBits")


if __name__ == "__main__":
    unittest.main()
