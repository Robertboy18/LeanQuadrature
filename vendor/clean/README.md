# CLean adaptation

These Lean sources come from Certora CLean, revision
`123f7f7767e215aceb4821f0d044336d78103ade`. `upstream.json` records the original
file hashes. `LICENSE` is retained from upstream; its list of dual-licensed
files includes the `export/` directory from which these sources originate.
`LEAN.md` is the unchanged upstream description, not a report of local checks.

The inherited library includes Clight and memory semantics, a sound execution
checker, and a separation logic with function contracts, a frame rule, and
function-pointer call rules. `CC.Sep.closure` combines verified bodies using
a decreasing measure on calls. The linking code merges generated modules
and resolves declarations against definitions; CompCert's general linking
theory is not ported. Our quadrature proofs use the execution rules directly.

Local changes replace native floating-point arithmetic with FloatLib and
replace global external-call axioms with explicit environment parameters and
determinism contracts. Dependent semantic and program-logic declarations carry
those parameters.

Binary32 and binary64 operations use pure FloatLib definitions, including
arithmetic, comparisons, sign operations, and format conversions. Integer
conversion truncates the exact finite dyadic value and checks the destination
range; NaNs and infinities have no integer result. The four upstream external-call
axioms become an `ExternalCalls` environment and an
`ExternalCallsDeterministic` contract. Interpreter soundness holds for every
environment; determinism requires the contract.

The local port also uses the current Lean names for conditional simplification
lemmas, removes redundant tactics and a file-wide unused-variable linter
exception, and documents its entailment predicate.
Both vendored library targets treat warnings as errors. The `State.State`
constructor retains its upstream name for compatibility with exported programs;
only that declaration disables the duplicate-namespace linter. Upstream names,
module layout, and licensing remain intact.

The arithmetic follows FloatLib, including its NaN policy. This adaptation does
not prove agreement with Rocq's CompCert semantics, transfer the compiler
correctness theorem, or prove a particular quadrature program correct.

The [Lean build and audit](../../evidence/lean-quality.json) checks this library
alongside the project, including every private and generated theorem. Only
`propext`, `Classical.choice`, and `Quot.sound` are allowed. The
[coverage ledger](../../docs/coverage.md) links the quadrature applications and
states their context and callback requirements. The upstream example suite and
differential tests are separate from these project checks.
