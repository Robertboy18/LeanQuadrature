"""Check that upstream VST proof evidence cannot hide assumptions or source changes.

Inputs: check-upstream-vst.py, loaded with runpy. Output: unittest results.
Requires scripts/check-upstream-vst.py and scripts/upstream_sources.py.
"""

from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
CHECKER = runpy.run_path(str(Path(__file__).resolve().parents[1] / "check-upstream-vst.py"))
parse_assumptions = CHECKER["parse_assumptions"]
tracked_inputs = CHECKER["tracked_inputs"]
clight_metadata = CHECKER["clight_metadata"]
scope_sigma_products = CHECKER["scope_sigma_products"]
check_review_assumptions = CHECKER["check_review_assumptions"]


class AssumptionReportTests(unittest.TestCase):
    def test_closed_report(self):
        self.assertEqual(parse_assumptions("Closed under the global context\n"), [])

    def test_multiline_types_retain_every_axiom(self):
        report = (
            "Axioms:\n"
            "CFEM.quadmodel_accuracy.perturb_sum\n"
            "  : forall a b, (forall i, a i = b i) -> a = b\n"
            "FunctionalExtensionality.functional_extensionality_dep\n"
            "  : forall (A : Type) (B : A -> Type) (f g : forall x, B x),\n"
            "    (forall x, f x = g x) -> f = g\n"
            "CFEM.C.verif_quadrules.testfun_fbound : True\n"
        )
        self.assertEqual(parse_assumptions(report), [
            "CFEM.quadmodel_accuracy.perturb_sum",
            "FunctionalExtensionality.functional_extensionality_dep",
            "CFEM.C.verif_quadrules.testfun_fbound",
        ])

    def test_truncated_or_unrecognized_reports_fail(self):
        for report in ["", "Axioms:\n", "Error: unknown constant\n", "Closed\n"]:
            with self.subTest(report=report), self.assertRaises(ValueError):
                parse_assumptions(report)

    def diagnostic_reports(self):
        reports = {name: {"axioms": []} for name in CHECKER["QUERIES"]}
        reports["CFEM.quadrature.Rintegral_gt_0"]["axioms"] = ["original_admission"]
        reports[CHECKER["MATHCOMP_SINGLETON_INTEGRAL"]]["axioms"] = ["library_logic"]
        reports[CHECKER["ADMITTED_DIAGNOSTIC"]]["axioms"] = [
            "original_admission", "library_logic",
        ]
        return reports

    def test_diagnostic_inherits_both_admission_and_library_assumptions(self):
        result = check_review_assumptions(self.diagnostic_reports())
        diagnostic = result[CHECKER["ADMITTED_DIAGNOSTIC"]]
        self.assertEqual(diagnostic["unexpected_axioms"], [])
        self.assertEqual(diagnostic["baselines"], [
            "CFEM.quadrature.Rintegral_gt_0", CHECKER["MATHCOMP_SINGLETON_INTEGRAL"],
        ])

    def test_diagnostic_cannot_hide_admission_or_add_assumptions(self):
        for axioms in [
            ["library_logic"],
            ["original_admission"],
            ["original_admission", "library_logic", "unproved_review_claim"],
        ]:
            reports = self.diagnostic_reports()
            reports[CHECKER["ADMITTED_DIAGNOSTIC"]]["axioms"] = axioms
            with self.subTest(axioms=axioms), self.assertRaises(RuntimeError):
                check_review_assumptions(reports)


class SourceProvenanceTests(unittest.TestCase):
    def test_scope_fix_is_limited_to_two_expected_product_types(self):
        original = "X: {n: 'I_5 & 'I_n * 'I_n}"
        scoped = "X: {n: 'I_5 & ('I_n * 'I_n)%type}"
        text = f"PRE {original}\nUNCHANGED PROOF\nPOST {original}\n"
        self.assertEqual(
            scope_sigma_products(text),
            f"PRE {scoped}\nUNCHANGED PROOF\nPOST {scoped}\n",
        )
        for count in [0, 1, 3]:
            with self.subTest(count=count), self.assertRaises(ValueError):
                scope_sigma_products(original * count)

    def test_target_metadata_is_explicit_and_complete(self):
        text = (
            'Module Info.\nDefinition version := "3.17".\n'
            'Definition arch := "aarch64".\nDefinition model := "default".\n'
            'Definition abi := "apple".\nDefinition bitsize := 64.\n'
            "Definition big_endian := false.\nEnd Info.\n"
        )
        self.assertEqual(clight_metadata(text), {
            "version": "3.17", "arch": "aarch64", "model": "default",
            "abi": "apple", "bitsize": 64, "big_endian": False,
        })
        with self.assertRaisesRegex(ValueError, "no Info module"):
            clight_metadata("")
        with self.assertRaisesRegex(ValueError, "no abi metadata"):
            clight_metadata(text.replace('Definition abi := "apple".\n', ""))

    def test_tracks_both_repositories_and_excludes_compiled_files(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary)
            for root in [source, source / "LAProof"]:
                root.mkdir(exist_ok=True)
                subprocess.run(["git", "init", "-q", str(root)], check=True)
                (root / "Proof.v").write_text("Lemma identity : True. Proof. exact I. Qed.\n")
                (root / "_CoqProject").write_text("Proof.v\n")
                subprocess.run(["git", "add", "Proof.v", "_CoqProject"], cwd=root, check=True)
                (root / "Proof.vo").write_bytes(b"compiled output")
                (root / "Untracked.v").write_text("not a pinned source\n")
            before = tracked_inputs(source)
            self.assertEqual(set(before), {
                "Proof.v", "_CoqProject", "LAProof/Proof.v", "LAProof/_CoqProject",
            })
            (source / "LAProof" / "Proof.v").write_text("Lemma changed : True.\n")
            self.assertNotEqual(tracked_inputs(source), before)
            (source / "Proof.vo").write_bytes(b"changed compiled output")
            self.assertEqual(tracked_inputs(source)["Proof.v"], before["Proof.v"])


if __name__ == "__main__":
    unittest.main()
