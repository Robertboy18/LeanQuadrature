#!/usr/bin/env python3
"""Render the ten RTL programs immediately before register allocation in Lean and Rocq.

Inputs: --export-directory holding order1.out to order10.out. Outputs: --lean-output (checked
against Quadrature/Compiler/RTL/Preallocation.lean) and --rocq-output.
Requires scripts/import-rtl.py, loaded by path for the shared instruction format and program
family checks. reproduce-rtl-preallocation.py drives this script. The generated Rocq proof checks
this later compiler boundary and its place in Compiler.transf_rtl_program.
"""

import argparse
import importlib.util
import json
from pathlib import Path
import tempfile


SPEC = importlib.util.spec_from_file_location(
    "rtl_rendering", Path(__file__).with_name("import-rtl.py")
)
RTL = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RTL)

TRANSPARENCY = """Local Transparent SelectOp.symbol_is_relocatable Compopts.optim_for_size
  Selection.compile_switch Selection.if_conversion_heuristic RTLgen.more_likely
  Compopts.optim_tailcalls Compopts.optim_constprop Compopts.optim_CSE
  Compopts.optim_redundancy Inlining.inlining_info Inlining.inlining_analysis
  Inlining.should_inline Compiler.print_RTL
  Iteration.PrimIter.iterate Iteration.PrimIter.bounded_iter."""


def replace_once(text, before, after):
    if text.count(before) != 1:
        raise ValueError(f"unexpected RTL importer template: {before!r}")
    return text.replace(before, after)


def generate(directory, lean_path, rocq_path):
    with tempfile.TemporaryDirectory(prefix="quadrature-preallocation-") as temporary:
        tmp = Path(temporary)
        inventory = RTL.generate(directory, tmp / "Imported.lean", tmp / "ImportedRTL.v")
        lean = (tmp / "Imported.lean").read_text()
        rocq = (tmp / "ImportedRTL.v").read_text()
    lean = replace_once(lean, "# Actual RTL output for all ten applications",
                        "# RTL applications immediately before register allocation")
    lean = replace_once(lean, "`scripts/import-rtl.py`",
                        "`scripts/import-rtl-preallocation.py`")
    lean = replace_once(
        lean,
        "A separate Rocq certificate checks exact syntax against `RTLgen.transl_program`;",
        "A separate Rocq certificate checks exact syntax after the configured RTL passes,\n"
        "and identifies this boundary in `Compiler.transf_rtl_program`;"
    )
    lean = lean.replace("Quadrature.RTL.Imported", "Quadrature.RTL.Preallocation")
    rocq = replace_once(rocq, "Selection SelectOp Compopts RTLgen.",
                        "Selection SelectOp Compopts RTLgen Inlining Iteration Compiler.")
    rocq = replace_once(rocq, "Import EqualityRTL.",
                        "Import EqualityRTL RTLPreallocation.")
    rocq = replace_once(
        rocq,
        "Local Transparent SelectOp.symbol_is_relocatable Compopts.optim_for_size\n"
        "  Selection.compile_switch Selection.if_conversion_heuristic.",
        TRANSPARENCY
    )
    rocq = replace_once(
        rocq,
        "Definition translated n := match selected n with\n"
        "  | Errors.OK p => RTLgen.transl_program p | Errors.Error e => Errors.Error e end.",
        "Definition generated n := match selected n with\n"
        "  | Errors.OK p => RTLgen.transl_program p | Errors.Error e => Errors.Error e end.\n"
        "Definition translated n := match generated n with\n"
        "  | Errors.OK p => preallocation p | Errors.Error e => Errors.Error e end."
    )
    rocq += """
(** The corollary reuses the syntax certificate without reducing the backend. *)
Local Opaque generated imported_program preallocation allocate_and_finish
  Compiler.transf_rtl_program.

Definition remaining_backend n := match generated n with
  | Errors.OK p => Compiler.transf_rtl_program p
  | Errors.Error e => Errors.Error e end.

(** The backend consumes this exact program at the allocation boundary. *)
Theorem compiler_uses_imported_program n (hlo : (1 <= n)%nat)
    (hhi : (n <= 10)%nat) :
  remaining_backend n = allocate_and_finish (Errors.OK (imported_program n)).
Proof.
  pose proof (imported_program_is_compiler_output n hlo hhi) as H.
  unfold translated in H. unfold remaining_backend.
  destruct (generated n) as [p | e].
  - exact (compiler_from_preallocation p (imported_program n) H).
  - discriminate.
Qed.

Print Assumptions compiler_uses_imported_program.
"""
    lean_path.parent.mkdir(parents=True, exist_ok=True)
    rocq_path.parent.mkdir(parents=True, exist_ok=True)
    lean_path.write_text(lean)
    rocq_path.write_text(rocq)
    return inventory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export-directory", type=Path, required=True)
    parser.add_argument("--lean-output", type=Path, required=True)
    parser.add_argument("--rocq-output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(generate(args.export_directory, args.lean_output, args.rocq_output), indent=2))


if __name__ == "__main__":
    main()
