"""Regression checks for omissions from the project assumption audit driver.

Inputs: check-lean.py, loaded with runpy. Output: unittest results.
Requires scripts/check-lean.py. Run with `python3 -m unittest discover -s scripts/tests`.
"""

from pathlib import Path
import runpy
import tempfile
import unittest


CHECKER = runpy.run_path(str(Path(__file__).resolve().parents[1] / "check-lean.py"))
audited_project_modules = CHECKER["audited_project_modules"]
source_hashes = CHECKER["source_hashes"]


class ModuleCoverageTests(unittest.TestCase):
    def test_complete_imports_ignore_nonproject_inputs(self):
        sources = {
            "Quadrature.lean": "",
            "Quadrature/Compiler/Execution/Run.lean": "",
            "scripts/Audit.lean": "",
            "vendor/clean/CCLib.lean": "",
            "lakefile.toml": "",
            "Quadrature/CSource/Cosine/cosine.c": "",
        }
        log = 'Project modules: ["Quadrature.Compiler.Execution.Run","Quadrature"]\n'
        self.assertEqual(
            audited_project_modules(log, sources),
            ["Quadrature", "Quadrature.Compiler.Execution.Run"],
        )

    def test_unimported_source_cannot_pass(self):
        # Theorems in a new file are invisible to collectAxioms until it is imported.
        sources = {"Quadrature.lean": "", "Quadrature/Unimported.lean": ""}
        with self.assertRaisesRegex(SystemExit, "omitted from the audit: Quadrature.Unimported"):
            audited_project_modules('Project modules: ["Quadrature"]\n', sources)

    def test_stale_compiled_module_cannot_pass(self):
        log = 'Project modules: ["Quadrature","Quadrature.Removed"]\n'
        with self.assertRaisesRegex(SystemExit, "without source files: Quadrature.Removed"):
            audited_project_modules(log, {"Quadrature.lean": ""})

    def test_theorem_count_alone_is_insufficient(self):
        with self.assertRaisesRegex(SystemExit, "Missing project-module inventory"):
            audited_project_modules("Audited 100 Quadrature theorems\n", {"Quadrature.lean": ""})

    def test_invalid_inventory_cannot_pass(self):
        with self.assertRaisesRegex(SystemExit, "Invalid project-module inventory"):
            audited_project_modules('Project modules: ["Quadrature", null]\n', {"Quadrature.lean": ""})


class SourceInputTests(unittest.TestCase):
    def test_c_edits_change_the_recorded_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in (
                "Quadrature.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
                "scripts/run-local.sh", "scripts/check-lean.py",
            ):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("")
            cosine = root / "Quadrature/CSource/Cosine/cosine.c"
            cosine.parent.mkdir(parents=True)
            cosine.write_text("double cos(double x) { return x; }\n")
            before = source_hashes(root)
            cosine.write_text("double cos(double x) { return 0.0; }\n")
            after = source_hashes(root)
            name = str(cosine.relative_to(root))
            self.assertIn(name, before)
            self.assertNotEqual(before[name], after[name])
            self.assertEqual(
                {key: value for key, value in before.items() if key != name},
                {key: value for key, value in after.items() if key != name},
            )


if __name__ == "__main__":
    unittest.main()
