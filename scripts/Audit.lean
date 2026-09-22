import Quadrature
import Lean.Util.CollectAxioms

/-!
# Project assumption audit

Audit every theorem defined in `Quadrature` or a `Quadrature.*` module, public and private,
selecting declarations by their defining module rather than their namespace. Each theorem's
transitive axioms must lie in `propext`, `Classical.choice`, and `Quot.sound`, and no project
module may declare an axiom. Any other axiom, or any project axiom declaration, fails the run.
The imported project modules are reported so `check-lean.py` can reject source files that are
missing from this audit.

`check-lean.py` drives this file together with `AuditClight.lean` and `AuditCSourceWrapper.lean`
after `lake build`, and records the theorem counts printed below.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames.filterMap fun name =>
    let text := name.toString
    if text == "Quadrature" || text.startsWith "Quadrature." then some text else none
  logInfo m!"Project modules: {(toJson modules).compress}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut privateChecked : Nat := 0
  for (name, info) in env.constants do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[moduleIdx.toNat]!.toString
    let isProject := moduleName == "Quadrature" || moduleName.startsWith "Quadrature."
    let isPrivate := name.toString.startsWith "_private."
    if isProject && info.isAxiom then
      throwError m!"Project axiom declaration is not allowed: {name}"
    if isProject && info.isTheorem then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError m!"{name} depends on unapproved axiom {axiomName}"
      checked := checked + 1
      if isPrivate then
        privateChecked := privateChecked + 1
  logInfo m!"Audited {checked} Quadrature theorems; only propext, Classical.choice, and Quot.sound allowed."
  logInfo m!"Included {privateChecked} private project theorems."
