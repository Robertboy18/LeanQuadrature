import CCLib
import Lean.Util.CollectAxioms

/-!
# Assumption audit of the imported CLean modules

Audit every theorem defined in `CCLib` or a `CCLib.*` module, the FloatLib adaptation of
Certora CLean under `vendor/clean`. Each theorem's transitive axioms must lie in `propext`,
`Classical.choice`, and `Quot.sound`, and no CLean module may declare an axiom. Any other axiom,
or any axiom declaration, fails the run. The `#print axioms` lines below show the dependencies
of the interpreter-soundness, step-determinism, and endpoint-uniqueness theorems.

`check-lean.py` drives this file together with `Audit.lean` and `AuditCSourceWrapper.lean` and
records the printed count as `audited_clight_theorem_count`.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[moduleIdx.toNat]!.toString
    let isClight := moduleName == "CCLib" || moduleName.startsWith "CCLib."
    if isClight && info.isAxiom then
      throwError m!"Clight axiom declaration is not allowed: {name}"
    if isClight && info.isTheorem then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError m!"{name} depends on unapproved axiom {axiomName}"
      checked := checked + 1
  logInfo m!"Audited {checked} Clight theorems; only propext, Classical.choice, and Quot.sound allowed."

#print axioms CC.doStep_sound
#print axioms CC.step_determ
#print axioms CC.starE0_endpoint_unique
#check @CC.doStep_sound
#check @CC.step_determ
