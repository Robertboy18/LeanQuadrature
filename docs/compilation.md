# The numerical theorem and CompCert

The internal-cosine application has a kernel-checked integral-accuracy theorem
through a concrete compilation to CompCert's x86-64 assembly semantics.
The concrete compilation certificates described first below are **Rocq proofs**.
Lean separately proves the ten imported polynomial applications through formal
assembly and total correctness of the initialized C library with the internal
cosine polynomial. The C library's normalization proof has not yet been composed
with those application proofs. A general connection between Lean and Rocq also
remains open. For the current comparison and the meaning of replacing GCC with
CompCert, start with
[CompCert and Lean](compcert-and-lean.md).

The application's observed binary64 value is finite and differs from the real
integral by at most `0.00356`. The numerical certificate also proves that its
error exceeds the `0.00224` bound stated for the example in the Appel–Bindel paper.
The [review record](../evidence/upstream-review.json) identifies the PDF examined.
The theorem has neither
a cosine-call hypothesis nor a successful-compilation hypothesis.
It uses an explicit compiler configuration whose complete preservation proof
is rebuilt from source.

The application retaining external `cos` also has a concrete compilation
certificate for this configuration. Its accuracy theorem still requires
exact-result contracts for the two external calls.
The certificate family also covers complete internal-polynomial applications
for orders one through ten. The first four integral-error bounds are `0.159`,
`0.00356`, `0.000031`, and `0.00000015`; the remaining six are `4e-10`,
`8e-13`, `2e-15`, `4e-15`, `4e-15`, and `3e-15`. Each bound holds for every assembly
behavior, with no cosine or compilation-success hypothesis.
All certificates are in [`compcert/certification`](../compcert/certification/README.md).
They establish assembly semantics; assembly printing, linking, and
operating-system output remain outside the proof.

The numerical theorem and the compiler theorem meet at a particular program
semantics. Suppose a Lean theorem establishes that `quadrature64` returns a value
within a specified error of an integral. To transfer this conclusion to a binary,
each transformation must preserve the meaning used by that theorem:

```text
real integral
    │ analytic and floating-point accuracy proofs
    ▼
Lean functional floating-point model
    │ program refinement + agreement with Rocq semantics — not fully connected
    ▼
CompCert C / Clight program
    │ CompCert semantic preservation
    ▼
assembly program
```

CompCert's documented theorem starts from CompCert C abstract syntax after parsing
and elaboration. A successful compilation guarantees that the generated assembly
improves on an allowed behavior of that source program. It does not certify the
transformation that produced the C program.

Thus compiling the ordinary Lean compiler's generated C with CompCert would
strengthen the final compiler step. It would leave a proof obligation connecting
the original Lean program to that C, including the runtime calls it makes.
Likewise, compiling a hand-written quadrature implementation would still require
proving that implementation satisfies its numerical specification.

For the concrete example, we also prove the integral identity and numerical
bounds directly in Rocq. This gives the Clight proof a numerical specification
in its own logic. It does not establish a general translation between Lean
and Rocq or an equivalence of their floating-point libraries.

The unrestricted bitwise equivalence is false for the pinned libraries, FloatLib at
the revision checked in through `lake-manifest.json`,
`393bea610296bf9a9ee5a479508c351edb65cc6d`, and unmodified CompCert 3.17 at revision
`7b1f02b09954b9b916eb2a91d283c9b5355bf172`.
Their NaN payload and sign policies differ, as six paired kernel certificates
now show. The quadrature range budget supplies an explicit certificate that
every weighted product and accumulator value is finite, and Lean proves its
decoded semantics as a separately rounded real fold.
Lean and Rocq independently prove the arithmetic sign rules and show that the
signed recurrence uniquely determines the full finite encoding. Both kernels
now reduce their real rounding functions to integer algorithms and prove
complete integer specifications for finite loops. A checked connection between
those integer representations and algorithm definitions remains open.
[The model correspondence note](float-models.md) gives
the exact counterexamples, proof statements, and reproduction command.

For this small numerical program, a direct proof of the C loop against the
functional model may be smaller than verifying the production Lean compiler.
The paper follows that route using VST. Preserving its endpoint requires the
array bounds, pointer accesses, loop invariant, callback contract, exact order
of floating-point operations, and calling convention to be represented in the
program proof.

The original sources contain VST function-body proofs for the table accessors
and loop. Those proofs assume predicates describing the global arrays. The
generated Clight initializer contains the C three-point outer weight, while the
weight-array predicate uses the differing Rocq model literal. Establishing the
initial global state therefore needs attention before composing a complete
program proof. The [VST rebuild](../evidence/upstream-vst-verified.json)
records the source hashes, compilation, and assumption reports for these
body proofs. [The review](review.md) explains the two required type annotations
and the original admissions that remain.

Cosine introduces another precise boundary. A theorem about a certified polynomial
approximation to cosine applies to that implementation. A call to an arbitrary
platform `libm` needs a contract for that particular implementation. Neither the
Lean compiler nor CompCert supplies a numerical accuracy theorem for `cos`.
LeanQuadrature now certifies FloatLib's default executable cosine at the two
stored example nodes and proves the concrete Lean program's accuracy without an
external cosine hypothesis. It also provides a theorem for any cosine satisfying
the stated two-input contract. The original C call still needs that contract
established for its own implementation.

## Native C check and Clight proof

`scripts/check-upstream-c.py` compiles the original C source with Clang and
address and undefined-behavior sanitizers. Alongside the tables and monomial
cases, it runs the original cosine example. The result is
`0.83791182769499317`; comparison with the platform's `sin(1)` gives an observed
error of about `0.0035591571`. The source hashes, compiler, and complete results
are in [upstream-c-checked.json](../evidence/upstream-c-checked.json).
This experiment reproduces the numerical counterexample. The formal compilation
certificates described below establish their own execution and accuracy results.

## Checked execution of the example in Clight

`compcert/ClightExample.v` now proves an execution of the pinned generated
Clight syntax using CompCert's own `ClightBigstep.Clight2.eval_funcall` relation.
The proof establishes that the program's globals can be initialized and derives
the required table loads from `Genv.init_mem_characterization`. It then constructs
executions of both node accesses, both weight accesses, both callback calls, the
two loop iterations, and `integrate_testfun`. The result has bits
`0x3fead02c771c35ed`, and the execution leaves memory unchanged.
`integrate_testfun_steps` transfers that execution to `Clight.step2`, the
small-step relation used by the next compiler pass.

`compcert/CsharpminorExample.v` proves that `Cshmgen.transl_program` succeeds
on the pinned artifact. It applies the official pass simulation to the proved
library call, establishing an execution in the resulting Csharpminor program
with the same return value and memory. The target program initializes with
that memory, and its symbol table resolves the translated library function.
This is a checked application of the first compiler-pass proof to the concrete
execution.

`compcert/CminorExample.v` checks that `Cminorgen.transl_program` succeeds
on that Csharpminor program and applies its official simulation. Both the
concrete example and all four callback-parametric rules have Cminor executions
with exactly the same floating-point return values and empty traces.
The target initializes with the source memory. Its final memory may contain
additional allocated and freed stack blocks; the theorem establishes
`Mem.inject` from the source's initialized memory to that final memory.
`compcert/CminorSafety.v` proves total correctness of all four compiled library
calls under the source callback contracts. CompCert's Cminor determinacy theorem
and the generic argument in `compcert/SilentTermination.v` show that every
reachable state can step or is the prescribed return. The successor relation
is accessible, excluding infinite executions; every return has the same value
and final memory.
The application proof below composes the later pass simulations conditionally.

`compcert/ClightRules.v` proves the loop for each order from one to four and
an arbitrary callback satisfying a local execution contract. The contract
requires a valid function pointer with the expected type and a terminating
callback execution at each stored node, with no events or memory changes.
Under that contract, `integrate_rule_execution` constructs the complete Clight
loop execution. It proves the loop returns `rule_value`, a left fold of
CompCert's `Float.mul` and `Float.add` using entries read directly from the
pinned initializers. The table-load lemmas cover all 55 initialized entries.
This earlier loop theorem covers orders 1–4; the newer `RuleLibrary.v`
theorem below covers all ten stored slices.
`integrate_rule_compiled_execution` transfers this general result through
Cshmgen and Cminorgen. A general correspondence between these CompCert operations
and FloatLib's operations on the finite domain remains a separate obligation.

`compcert/FiniteArithmetic.v` now proves a general range and rounding theorem
directly for these CompCert operations. `compcert/ClightRoundoff.v` combines it
with the C total-correctness theorem: finite callback outputs and an absolute-mass
budget imply finite products and accumulators, a separately rounded real
recurrence, and error at most `2*n*epsilon(radius)` for every return.
This first error bound is measured from the exact sum of stored weights and
decoded callback outputs.
`compcert/TableAccuracy.v` certifies the actual C nodes and weights against
explicit real rules, including the larger error of the C three-point weight.
It also proves positivity, total weight two, and the exact polynomial moments.
`compcert/CallbackAccuracy.v` then accounts for callback approximation and
node displacement under an integrand bound and a Lipschitz condition.
`compcert/ClightAccuracy.v` combines these errors with rounding and proves the
bound from ideal quadrature for every C return. A numerical range condition
derives operation finiteness.
`compcert/ClightIntegralAccuracy.v` adds an independently proved analytic
term `c_n*M` and establishes integrability and accuracy against the integral.
`SharpAccuracy.v` proves `c_n = 1/3, 1/135, 1/15750, 1/3472875` for orders 1–4
from the Hermite remainder and exact nodal-square integrals. It assumes ordinary
derivatives through order `2*n` on the closed interval.
`compcert/CminorIntegralAccuracy.v` preserves this budget for the lowered
library calls, with total correctness and a bound for every returning execution.
The source callback contracts suffice, and both lowering translations have
proved success. This general four-rule result reaches Cminor; the assembly
certificates below concern the concrete example applications.
The sharp constants are checked independently in Rocq. The ordinary endpoint
derivative hypotheses differ from Lean's `ContDiffOn` formulation, and a checked
transfer between the kernels remains open.
`compcert/FiniteRepresentation.v` adds the sign component and proves that the
resulting recurrence uniquely characterizes the complete finite value.
`compcert/ClightRepresentation.v` proves that signed specification for every
return of the four C loops under the same hypotheses.
`compcert/IntegerRounding.v` reduces Flocq's real rounding to integer quotient,
remainder, and parity operations. `compcert/FiniteInteger.v` uses this result
to characterize each complete finite loop result by an integer recurrence,
including its zero sign. `compcert/ClightInteger.v` attaches that specification
to every C return. The corresponding Lean proofs remain independent.
The proof and reproduction command are described in
[the model correspondence note](float-models.md).

The concrete example theorem has two explicit hypotheses. At each stored node, the external
`cos` call must return bits `0x3fead02c771c35ed`, produce an empty event trace, and
preserve memory. These are exact-result contracts at two inputs, stronger than
an error bound alone. They are not a verification of the C library implementation.
Lean's `certified_program_value` proves the same final encoding for its own
implementation, and `certified_program_accuracy` proves that value is within
`0.00356` of the real integral. These certificates are checked by separate kernels;
there is no general translation of the Lean floating-point model into Rocq here.

`compcert/ValueAccuracy.v` independently decodes that encoding as the exact rational
`7547238789953005 / 9007199254740992`. The standard library's sine series gives a
rational enclosure of `sin 1`, from which rational arithmetic establishes the
corrected error bound and refutes the draft's bound.
`compcert/ExampleIntegral.v` proves continuity and uses the antiderivative
`(1/2)*((1-x)*sin x-cos x)` to show that the target Riemann integral equals `sin 1`.
No numerical theorem is imported from Lean.

`compcert/ClightDeterminism.v` proves that a silent step in normalized Clight
determines every competing trace and successor. This uses CompCert's standard
external-call determinacy contract. It lifts a terminating silent execution
to total correctness: every reachable state either has a valid next step or is
the specified return state, the successor relation is accessible (ruling out
infinite executions), and every return has the same value and memory.
`compcert/ClightSafety.v` applies these results to all four callback-parametric
rules and to the concrete example, with the same callback or cosine hypotheses.
The concrete theorem also establishes the output bits for every return.

The library results establish source-level total correctness. To supply a
whole-program entry, `compcert/ClightApplication.v` appends an authored normalized
Clight `main` to the pinned definitions. `compcert/ClightLibrary.v` proves that
the example runs in this larger environment, whose memory is initialized
separately. The proof checks every required symbol, function, and table load.
The main function calls `integrate_testfun`, emits
`Event_annot "quadrature-result" [EVfloat cosine_value]`, and returns integer zero.
Under the same two cosine contracts, the theorem derives this terminating
behavior from CompCert's actual initial-state relation.

`compcert/CminorApplication.v` proves that both lowering passes succeed on this
application. It composes their official whole-program forward simulations and
transfers the finite Clight run to a terminating Cminor behavior with the same
annotation and exit status. Both application files then prove
`application_all_behaviors`: every behavior is exactly this termination.
`compcert/AnnotatedBehavior.v` derives this from determinacy and a finite run
whose only events are annotations. It proves accessibility of the successor
relation and excludes both forms of divergence and stuck execution.
The general lemma has no axiom dependencies; its applications use the recorded
CompCert dependencies and explicit cosine contracts.

`compcert/CompilerBackend.v` proves a forward simulation from any Cminor program
to the assembly returned by `Compiler.transf_cminor_program`, assuming that
compilation succeeds. CompCert's public complete-compiler theorem starts at
Csyntax; this proof composes the official backend pass theorems at our Cminor
entry. `compcert/AsmApplication.v` applies it to the initialized application:
under successful compilation and the two cosine contracts, every assembly
behavior terminates with the same result annotation and exit status.

`compcert/ApplicationAccuracy.v` composes these behavior theorems with the
Rocq numerical certificate. Its `accurate_behavior` specification includes
termination with the observed floating-point result, finiteness, error at most
`356/100000` from the Riemann integral, and failure of the `224/100000` bound.
The Clight and Cminor theorems require the two cosine contracts. The assembly
theorem requires those contracts and the backend success equation.

## A variant with internal cosine

`compcert/InternalCosine.v` defines a degree-14 Taylor polynomial evaluated by
Horner's rule in binary64. The stored coefficients are checked against the
encodings obtained by rounding `(-1)^n / (2n)!`, for `n = 0, ..., 7`.
Its Clight function squares the input and evaluates this polynomial without
external calls. A generic execution theorem connects the syntax to CompCert's
floating-point operations. Kernel computation proves that both stored
quadrature nodes return bits `0x3fead02c771c35ed`.

`compcert/PolynomialApplication.v` replaces the pinned library's external
cosine declaration with this internal function. Every other library definition
and table entry is retained. The initialized-memory proof is repeated for the
new program, and the shared library proof is instantiated with the two proved
internal cosine executions. The whole program has the same unique terminating
behavior without any external cosine-call hypotheses.

`compcert/PolynomialCompilation.v` checks the two lowering passes, proves the
Cminor behavior, and applies the backend preservation theorem. Its Clight and
Cminor integral-accuracy theorems have no cosine premises. Its assembly accuracy
theorem requires only the backend success equation, in addition to the audited
upstream logical and semantic dependencies.

This variant establishes a concrete alternative implementation of the example.
The original program's platform cosine remains outside its proof. No
whole-domain accuracy claim is made for the polynomial; the certificate covers
the two inputs used by this application.

`compcert/PolynomialRules.v` adds an entry point for each of orders 1–4.
It calls `integrate` directly, retaining the pinned tables and using the same
internal cosine polynomial. `RuleLibrary.v` proves that the loop works in this
enlarged program from local table, symbol, and accessor conditions.
`PolynomialRulesAccuracy.v` computes each complete result in Rocq, decodes it
as an exact rational, and compares it with a proved enclosure of `sin 1`.
This establishes the four integral-error bounds without a separate assumption
about approximation at the callback inputs.
`PolynomialRulesCompilation.v` proves both lowering passes succeed and
transfers the terminating behavior and accuracy to Cminor.

`StoredPolynomialRules.v`, `StoredPolynomialAccuracy.v`, and
`StoredPolynomialCompilation.v` extend this concrete application proof to all
ten stored orders. `StoredRules.v` describes each slice of the pinned tables.
`RuleLibrary.v` proves the callback-parametric loop for each slice, retaining
the original four-order API as an instance. The new numerical proof computes
each complete encoding and proves a sine enclosure narrow enough for the
smallest bounds. Both systems independently establish those concrete results;
this extension does not transfer a Lean theorem into Rocq.

## Concrete backend compilation

`compcert/certification/CertifiedPolynomial.v`, `CertifiedExternal.v`, and
`CertifiedPolynomialRules.v` retain the earlier application certificates.
`CertifiedStoredPolynomial.v` proves the concrete success equations and
assembly accuracy for all ten stored orders. The proof evaluates an
explicit compiler configuration based on the pinned CompCert revision.
For example, the imported library contains two helper functions with switches.
The configuration defines `Selection.compile_switch` as a chain of equality
tests, which the existing validator checks. The inliner selects no functions,
compiler options are false, and register allocation tries twenty-two stored
candidates, accepting only those that pass the original validator.

Six new caller candidates reuse the fourth caller's allocation with its order
constant changed to 5–10. Candidate construction is outside the trusted proof. A candidate is useful
only if its validation succeeds during kernel-checked evaluation.
The finite pool can reject other programs; no general allocator is claimed.
The iterator uses a structural budget of 10,000 steps, with its invariant
theorem proved by induction. Graph postorder and union-find representatives
have computational paths proved equal to their original definitions.
Two module interfaces expose their computations, and two termination proofs
are made transparent. These changes and small upstream proof-script adaptations
are distributed as a patch; all compiler theorem statements are retained.

`scripts/check-configured-compcert.py` starts with an archive of the pinned
source commit, checks the configuration's hashes, rebuilds the full compiler
proof, and checks the twenty-seven project files, four certificate files,
and an explicit 107-declaration assumption audit.
`evidence/assembly-certificate.json` records the completed check and its
assumptions. No certificate contains an abstract compiler-choice parameter
or a compilation-success hypothesis. Standard logical and external-semantics
dependencies remain. The internal-polynomial certificates also have no external
cosine hypothesis.

To reproduce this separate compiler target:

```sh
python3 scripts/check-configured-compcert.py \
  --compcert-root /path/to/compcert \
  --clight-source /path/to/quadrules.v \
  --work-dir /path/to/empty/local/certificate-build \
  --output /tmp/quadrature-assembly-certificate.json
```

The [configuration documentation](../compcert/certification/README.md) explains
the generated-parser hash, build requirements, candidate validation, and exact
semantic endpoint. The unmodified compiler remains a separate target with
the conditional preservation theorems below.

The annotation is an
observable CompCert event, not a verified operating-system output operation.
The new entry is a Clight AST; no claim of verified parsing from a C wrapper
is made.

The normalized parameters also matter: `Clight2` stores parameters in
temporaries, while CompCert's ordinary Clight compiler entry performs the
`SimplLocals` pass from `Clight1` to `Clight2`. That connection must be handled
explicitly when composing compiler passes. The checked application starts
directly at `Clight2`, then uses Cshmgen and Cminorgen.

The imported AST metadata names AArch64 and the Apple ABI. The checked proof
interprets that AST under the available CompCert 3.17 x86_64 semantics. This is
stated in the evidence file; the proof does not establish a cross-architecture
or original-AArch64 compilation theorem.

To reproduce the proof, provide a built CompCert 3.17 tree at revision
`7b1f02b09954b9b916eb2a91d283c9b5355bf172`, built for x86_64 with Coq 8.20:

```sh
python3 scripts/check-clight.py \
  --compcert-root /path/to/compcert \
  --work-dir /path/to/local/clight-build \
  --output /tmp/quadrature-clight-proof.json
```

`check-clight.py` checks the generated AST's SHA-256, uses a pinned Coq container,
mounts CompCert read-only, and compiles the needed export modules and project
proof into a separate build directory. The proof's printed assumptions contain
the standard classical principles used by CompCert/Flocq:
`ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec`,
`FunctionalExtensionality.functional_extensionality_dep`, and
`Classical_Prop.classic`. They also contain CompCert's abstract
`external_functions_sem` and `inline_assembly_sem` relations. No inline assembly
is executed in the example. Using the compiler-pass simulation adds
`Axioms.proof_irr`, `external_functions_properties`, and
`inline_assembly_properties`. Cminorgen's simulation additionally uses
`Eqdep.Eq_rect_eq.eq_rect_eq`, the standard dependent-equality principle imported
by its dependent induction proofs. These are upstream CompCert assumptions;
the latter two impose its `extcall_properties` requirements on abstract
external functions and inline assembly. The checker rejects project admissions and assumptions
outside this allowlist.

The release-compiler backend proof additionally depends on computational parameters exposed by
CompCert: compiler options, switch construction, register allocation, inlining
decisions, block enumeration, branch and instruction-selection heuristics,
printing hooks, and the x86 ABI selector `Archi.win64`. Their presence does not
assert that an oracle is correct; the pass proofs establish preservation when
the compiler's checks succeed. The audit records the complete names under
`upstream_computational_parameters`, separately from logical and external-call
assumptions. The ABI selector is still abstract in this conditional theorem.
These Rocq dependencies are distinct from the Lean axiom
audit; the external cosine contracts remain theorem arguments.
The configured compiler audit uses the same logical allowlist and rejects
every remaining computational parameter.

## Existing Lean compiler work

The local SideraCert development explicitly targets the production
LCNF-to-C/runtime/Clight chain. Its README describes proved fragments and names
`UniversalBodyCorrespondence`, full-program semantic preservation, and concrete
runtime refinements as open obligations. It is relevant infrastructure to
investigate, but it is not currently a discharged Lean-to-C compiler theorem
that can simply be attached to this project.

Lean4Lean concerns verification of Lean's type-theoretic foundation and checker.
That contribution does not itself establish production compiler correctness.
Other small verified compilers found in the source survey target restricted
languages; their existence does not establish a compiler theorem for this
floating-point implementation.

## Primary sources

- CompCert manual, semantic preservation and compilation phases:
  https://compcert.org/man/manual001.html
- Lean4Lean project:
  https://github.com/digama0/lean4lean
- The paper and accompanying source, identified in `evidence/upstream-review.json`.

The compiler-source survey was performed on September 18, 2026. Finding no
applicable completed library in that survey is not a proof that none exists.
