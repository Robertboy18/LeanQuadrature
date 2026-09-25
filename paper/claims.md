# Manuscript claims and supporting sources

The general Gaussian theory was developed in this project and has moved to
LeanPDE. Source links below point to its shared owners; the explicit Legendre,
floating-point, and execution proofs remain in LeanQuadrature.

This map records the support for *Gaussian Quadrature in Lean and Rocq*.
The original Appel–Bindel Rocq development and the separate Rocq proofs in
LeanQuadrature are separate developments. The formal
statements in the linked files govern the exact assumptions. “Proved in Lean”
below means the relevant source belongs to the recorded full build and audit;
the [build and audit record](../evidence/lean-quality.json) identifies
the checked source snapshot and retains its command logs.

## Proof-status labels

The PDF marks proved results in green with ✓, partial or conditional
application results in amber with ◐, open connections in blue-gray with ○,
and refuted claims in red with ×. Symbols always have accompanying text.
A checkmark covers the stated theorem under its hypotheses. An amber
application label means a required connection or premise has not been
discharged for that application; it does not mean a conditional theorem
failed to check. The original Rocq column is supported by source inspection
and a [rebuild with assumption reports](../evidence/upstream-vst-verified.json).
The rebuild uses two explicit type annotations, described below; it leaves
the original proofs and admissions unchanged.

The manuscript omits the administrative dates and printed commit hashes.
The exact paper version, source revisions, and declaration locations remain in
this map, the [review record](../evidence/upstream-review.json), the bibliography's link
targets, and the evidence records.

## Reusable program logic in Lean

CLean already includes a Clight separation logic, function contracts, a
frame rule, function-pointer call rules, and module-linking operations.
The retained [upstream description](../vendor/clean/LEAN.md), Sections 6.1–6.6,
documents these components. Their implementations are
[Funspec.lean](../vendor/clean/CCLib/Funspec.lean),
[FunPtr.lean](../vendor/clean/CCLib/FunPtr.lean),
[SepHoare.lean](../vendor/clean/CCLib/SepHoare.lean), and
[Linking.lean](../vendor/clean/CCLib/Linking.lean).
`CC.Sep.closure` combines verified bodies using a decreasing measure on calls.
The linking module implements merging; it does not port CompCert's general
linking theory. Our quadrature proofs use execution rules directly.
These inherited capabilities should not be counted as new project results.

Section 5 cites [*Iris in Lean*, arXiv:2609.24252v1](https://arxiv.org/abs/2609.24252v1).
Sections 2 and 2.2 of that paper describe its Iris base logic, language-parametric
program logic, proof mode, HeapLang instance, and adequacy theorem. Section 5.2
discusses building further language-specific program logics. The
[project README](https://github.com/leanprover-community/iris-lean/blob/740e2c4a9c672c61d76ad2f9c478c922f7461cf6/readme.md)
lists its supported components.

This supports the statement that reusable program-verification infrastructure
exists in Lean. Applying it to our C/Clight semantics would require a language
instance, verified rules for memory operations and calls, and an application
of its adequacy theorem. LeanQuadrature does not depend on Iris-Lean, and the cited
paper does not supply that integration or a Lean transfer of CompCert's compiler theorem.

## Code shown in the PDF

The Lean listing copies `corrected_two_point_bound` from
[Examples/TwoPointCosine.lean](../Quadrature/Examples/TwoPointCosine.lean), including its complete proof.
It uses the enclosures proved earlier in that module. The C listing copies
the complete original `integrate` function decoded from
[CSource/Frontend/SourceData.lean](../Quadrature/CSource/Frontend/SourceData.lean).
These are source excerpts in their existing contexts, not standalone programs.
Their text is compared with the validated sources in the
[PDF checks](../evidence/paper-checks.json).

## Mathematical results

Appendix A and the [24-paragraph source map](../docs/stewart-comparison.md)
compare the exact real mathematics with Section 2 of the original
*Preliminary Draft*. Paragraphs 6–7 are bypassed by the projection
construction; the root theorem uses an alternative proof; the
infinite-interval families in paragraphs 22–23 remain outside this project.
The table does not claim a separate proof of every textbook paragraph.

| Manuscript result | Source and declarations | Scope |
| --- | --- | --- |
| Monic orthogonal family | [Orthogonal.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Orthogonal.lean): `exists_monic_orthogonal`, `orthogonalPolynomial_unique` | Positive definite polynomial inner product; integral specialization on compact intervals |
| Roots and Gaussian construction | [Roots.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Roots.lean), [Gaussian.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Gaussian.lean): `exists_gaussian_quadrature` | Every positive order; positive continuous weight |
| Exactness and positive weights | [Algebra.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Algebra.lean), [Weighted.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Weighted.lean) | Degree at most `2*n-1`; nodes and weights satisfying the stated rule |
| Three-term recurrence | [Recurrence.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Recurrence.lean) | Constructed orthogonal family and positive norm ratio |
| Integrated Gaussian remainder | [Remainder.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Remainder.lean): `GaussianRule.remainder` | `ContDiffOn` through order `2*n` on the closed interval |
| Multi-node Hermite remainder | [Hermite.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Hermite.lean), [Remainder.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Remainder.lean): `hermite_remainder` | Value and first derivative at distinct nodes; positive order and an explicit derivative chain. Highest-derivative continuity is needed for our integrated identity, not for this pointwise result |
| Pointwise-to-integrated witness | [IntegralMeanValue.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/IntegralMeanValue.lean): `integral_eq_value_mul_of_pointwise_image` | Continuous derivative image, nonnegative factor with positive integral; no measurable selector premise |
| Convergence | [Weighted.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Weighted.lean): `gaussian_rules_converge` | Continuous integrand, compact interval, positive continuous weight |
| Low-order family identification | [Legendre/Identification.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Legendre/Identification.lean) | Explicit rules identified with the constructed monic family |

## Library contributions

The level comparison identifies libraries by the definitions and theorems
used in this development. LeanPDE is required by the current implementation;
replacing it would mean supplying the reused interfaces and proofs elsewhere.
This is not a claim that Gaussian quadrature can only be formalized with LeanPDE.

| Library contribution | Source and use | What is reused |
| --- | --- | --- |
| LeanPDE quadrature framework | [Legendre/Identification.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Legendre/Identification.lean), used by [Rules/Basic.lean](../Quadrature/Rules/Basic.lean) | `QuadratureRule`, the existing midpoint and two-point rules, and the shared three- and four-point rules with their exactness and family identification proofs |
| LeanPDE approximation bounds | [PositiveRule.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/PositiveRule.lean): `valueOn_eq_integral_polynomial`, `error_le_of_polynomial_approx` | `QuadratureRule.exactFor_polynomial`, affine interval transport, and `QuadratureRule.abs_valueOn_sub_le` |
| LeanPDE root certificates | [Legendre/RootCertificates.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Legendre/RootCertificates.lean), used by [Rules/RootData.lean](../Quadrature/Rules/RootData.lean) | `nodes`, `nodes_mem`, `nodes_root`, and `rule` turn certified rational brackets into Gaussian rules; this project supplies the brackets for the stored tables |
| LeanPDE weight enclosures | [Legendre/WeightCertificates.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Legendre/WeightCertificates.lean), used by [Rules/Tables.lean](../Quadrature/Rules/Tables.lean) and [Rules/Certificates.lean](../Quadrature/Rules/Certificates.lean) | The shared weight formula, `weightInterval_sound`, and `weight_mem` use `evalInterval_sound` and `RationalInterval` arithmetic; this project checks the stored weights against those enclosures |
| LeanPDE symbolic integration and enclosures | [Examples/TwoPointCosine.lean](../Quadrature/Examples/TwoPointCosine.lean): `integral_eq`, `sin_one_lower`, `quartic_two_point_error` | `cas [integrate]` and `cega [enclose ...]` produce checked proofs of the concrete calculations |
| LeanPDE Taylor inequalities | [TrigonometricTaylorBounds.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/TrigonometricTaylorBounds.lean), used by [Examples/TwoPointCosine.lean](../Quadrature/Examples/TwoPointCosine.lean) | Alternating bounds through degree nine, including `cos_le_taylor_four`, `taylor_six_le_cos`, and `sin_le_taylor_nine`; the additional bounds developed here are now shared in LeanPDE |
| mathlib foundations and shared general proofs | [Orthogonal.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Orthogonal.lean), [Weighted.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Weighted.lean), [Remainder.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Remainder.lean) | Real analysis, polynomials, orthogonal projection, Rolle's theorem, and uniform approximation support the weighted construction, remainder, and convergence now shared through LeanPDE |
| FloatLib arithmetic | [Binary64/Constants.lean](../Quadrature/Binary64/Constants.lean), [Roundoff.lean](../Quadrature/Binary64/Roundoff.lean), [Examples/CosineEvaluation.lean](../Quadrature/Examples/CosineEvaluation.lean) | Binary64 semantics, rounding bounds, and concrete cosine operations |
| Adapted CLean | [Vendored README](../vendor/clean/README.md), [upstream components](../vendor/clean/LEAN.md), [Clight/Execution.lean](../Quadrature/Clight/Execution.lean) | Syntax, values, memory, execution semantics, interpreter soundness, separation logic, contracts, function-pointer rules, and module-linking operations. Our application proofs use the execution semantics directly |
| TorchLean dependency | [Lake configuration](../lakefile.toml), [resolved dependencies](../lake-manifest.json) | LeanPDE requires TorchLean; no project module imports TorchLean directly |

The reused LeanPDE modules are inspected at the revision pinned in the Lake
configuration. The latest full code validation records that dependency
revision. Library attribution does not extend any theorem's scope.

That LeanPDE revision also contains
`norm_integral_sub_gaussLegendreTwoRule_valueOn_le` in
`PDE/Symbolic/Continuum/Quadrature/GaussLegendrePeano.lean`: for a `C⁴`
function it bounds the two-point error by `M * (b - a)^5 / 4320`.
It is an existing dependency result, though our general remainder proof
does not use it. Likewise, mathlib already supplies
`taylor_mean_remainder_lagrange`. The new general proof uses multi-node
first-derivative Hermite interpolation and repeated Rolle arguments.
The [source map](../docs/stewart-comparison.md) states the within-derivative
hypotheses precisely, and the [paper checks](../evidence/paper-checks.json)
record the declaration checks. LeanPDE is private; its source links and
the full build require access from Robert.

## Floating-point results

| Manuscript result | Source and declarations | Scope |
| --- | --- | --- |
| Accuracy with a finite range budget | [Rules/Accuracy.lean](../Quadrature/Rules/Accuracy.lean): `StoredRule.Certificate.accuracy`, `finite_execution` | Finite callback/error contract, Lipschitz and derivative bounds, explicit range budget; separate products and left-fold sums |
| All ten stored certificates | [Rules/Certificates.lean](../Quadrature/Rules/Certificates.lean): `table_certificate` | Orders 1–10; common node error `6e-16` and weight error `5e-16` |
| Stored-rule integral accuracy | [Clight/RuleAccuracy.lean](../Quadrature/Clight/RuleAccuracy.lean): `StoredRule.accuracy` | Theorem specialized to the retained tables |
| Concrete FloatLib cosine | [Examples/CosineEvaluation.lean](../Quadrature/Examples/CosineEvaluation.lean) | The two specified stored nodes, not a theorem about platform `libm` |
| Ten polynomial result bits and errors | [Clight/StoredAccuracy.lean](../Quadrature/Clight/StoredAccuracy.lean): `StoredPolynomial.result_value`, `integral_accuracy` | Complete polynomial computations; table “Proved error bounds” |
| Independent Rocq polynomial accuracy | [StoredPolynomialAccuracy.v](../compcert/StoredPolynomialAccuracy.v) | Independently checked real/numerical certificates |
| Integer rounding and remaining connection | [IntegerRounding.lean](../Quadrature/Binary64/IntegerRounding.lean), [IntegerRounding.v](../compcert/IntegerRounding.v), [model comparison](../docs/float-models.md) | Separate kernel results; no proved general Lean–Rocq interpretation |

## The four discrepancies

All four remain in the author PDF, explicitly titled *Preliminary Draft*, identified by the
[review record](../evidence/upstream-review.json). The accompanying source revision is
`e79a28dba247db9f934289bcf4e4debd5eebc884`. Page numbers refer to that 12-page PDF.

| Finding | Original source location at that revision |
| --- | --- |
| Two-point bound | `proof/quadrature2.v:368`, `error_1_0_2` |
| One-point bound | `proof/quadrature2.v:359`, `error_1_0_1` |
| Remainder indexing | `proof/quadrature.v:1629`, `roots_of_ortho_p`; line 1832, `G`; line 2063, `quadrature_error` |
| Three-point outer weight | `src/quadrules.c:99` and 101; `proof/quadmodel.v:122` and 124; table predicate in `proof/C/spec_quadrules.v:33` |

1. **Two-point ideal bound, paper page 5.**
   [Examples/TwoPointCosine.lean](../Quadrature/Examples/TwoPointCosine.lean):
   `integral_eq`, `two_point_eq`, `paper_two_point_analytic_bound_false`,
   `corrected_two_point_bound`.
   The ideal bound is `0.00223`; the valid replacement is `0.00356`.
   The separate `paper_two_point_bound_false` also refutes the `0.00224`
   inequality for the **ideal rule**. That theorem alone is not a theorem
   about arbitrary C executions. Program conclusions require their callback
   and execution specifications; see the certificate documentation below.
2. **One-point ideal bound, paper page 5.**
   Same file: `one_point_eq`, `paper_one_point_bound_false`,
   `corrected_one_point_bound`. False bound `0.02`; valid bound `0.159`.
3. **Remainder indexing, paper page 4.**
   Same file: `quartic_two_point_error`, `quartic_sixth_derivative`,
   `sixth_derivative_bound_impossible`.
   Two-node quartic error is `8/45`, while the sixth derivative is zero.
   The counterexample theorem rules out every constant `C` in a proposed
   bound `error ≤ C * M`, where `M ≥ 0` bounds the absolute sixth derivative.
   The quartic meets that derivative bound with `M = 0`.
   Corrected general theorem: `GaussianRule.remainder`.
   The finding is the mismatch with an `n`-node collection: `2*n+2` is correct
   for a convention with `n+1` nodes. It is not intrinsically wrong.
   For **two nodes, the required derivative is the fourth**, not the second.
   The admitted source statement also quantifies over arbitrary `f : R -> R`
   without an explicit smoothness premise; the Lean theorem requires
   `ContDiffOn` through order `2*n` on the closed interval.
4. **Three-point weight, C listing page 6 and model page 7.**
   [Rules/Constants.lean](../Quadrature/Rules/Constants.lean):
   `threeOuterWeight_toReal`, `threeOuterWeight_exceeds_draft_tolerance`,
   `threeOuterWeight_ne_model`.
   C bits `3fe1c71c71c71c76`; model bits `3fe1c71c71c71c72`.
   The stored-table certificates retain the C bits and prove the weaker,
   valid tolerance. Our polynomial C library now proves global initialization
   with those actual C constants and composes it with numerical accuracy.
   The original VST development still needs its quadrature VSU, including
   initializer/model alignment and initialization proofs. This composition
   step checks that global data satisfies the program's assumptions; a body
   theorem assuming the table predicate does not supply that check.

The two example-bound proofs apply `quadrature_error_bound_is_bound`
(`proof/quadrature.v:3356`), which uses `legendre_quadrature_error'`
(line 3339), specializing the admitted general remainder. Their final `Qed`
therefore does not establish the truth of that admitted premise. The paper
explains this dependency instead of attributing the false bounds to a failure
of Interval or the Rocq kernel.

The pinned upstream `proof/C/verif_quadrules.v` contains a `Qed` proof of
`body_integrate`, admitted example helper lemmas, and a wrapper proof using
those helpers. The pinned `proof/quadrature.v` contains an admitted general
remainder. The original quadrature target and its LAProof dependencies have
been rebuilt in a separate environment. The review retains 43 assumption
reports, including all nine body theorems and all twelve admitted declarations
in the nine quadrature files. The wrapper depends on ten of those admissions;
the low-level integrator body depends on none of them. This is a targeted
rebuild and review, not a completed proof of every admitted statement or an
audit of the whole finite-element project.
The revision is recorded in [upstream-review.json](../evidence/upstream-review.json).
The paper acknowledges the admitted remainder on page 4 and labels itself
preliminary. Its concluding description of the complete verification chain
should be read alongside those pending obligations. Our comparison reports
the checked state of each part and does not treat every admission as a
newly discovered error.

## Public work on the derivative bounds

The examined revision already contains
[`proof/g_max_deriv.v`](https://github.com/VeriNum/simple_cfem/blob/e79a28dba247db9f934289bcf4e4debd5eebc884/proof/g_max_deriv.v).
It develops revised function and derivative bounds on a nondegenerate
interval. The displacement estimate requires both `x` and `x + y` to lie
in that interval. Its final `g_max_deriv` has a `Qed`, but depends on the
admitted `g_max_deriv_oneway`; other supporting lemmas are also unfinished.
It is public work toward a corrected statement, not an integrated completed
quadrature proof. Our generic numerical accuracy theorem keeps its
Lipschitz premise explicit, with concrete application certificates supplying
their required bounds.

## Two additional false overflow helpers in the source

The further finding concerns the overflow argument in
`proof/quadmodel_accuracy.v` at the same upstream revision:

| Source declaration | Location | Counterexample |
| --- | --- | --- |
| `parameter_limits` | Line 135 | The range condition used in both examples |
| `maxwf` | Line 180 | The per-product error expression in the summation helper |
| `gauss_pt_wt_limit_aux` | Line 202; admitted at 203 | Zero nodes, function bound `2^1024`, zero callback error |
| `finite_integrate_model_aux` | Line 373; admitted at 382 | One node, function bound `2^1022`, zero derivative and callback-error bounds |

The source allows `n : 'I_5`, including zero. In both examples the mathematical
function and callback can be identically zero. At one node, the exact node
zero and weight two satisfy the table conditions. These are counterexamples
to helper inequalities, not examples of an overflowing program.

The pinned LAProof submodule is
`4286f63f456e47ea9da25d9474ca7f3e20523784`.
Its `accuracy_proofs/common.v` defines `default_rel` at line 211,
`default_abs` at line 214, `fmax` at line 294, and `g` at line 434.
For binary64 these specialize to `2^-53`, `2^-1075`, `2^1024`, and
`g(k)=(1+2^-53)^k-1`. In particular, `fmax` names an overflow threshold,
not the largest finite number.

[Examples/Overflow.lean](../Quadrature/Examples/Overflow.lean)
transcribes these real inequalities. Its three theorems prove the one-node
counterexample, verify that the preceding product helper holds at that
same witness, and prove the zero-node counterexample. All belong to the
full Lean build and assumption audit. Their correspondence with the Rocq
source is established by inspection, not a verified translation.

The source uses the summation helper in `Fsum_gauss_wt_pt_finite` and
`finite_integrate_model`; these support the subsequent rounded-error result.
The invalid implication is in the quadrature development's use of LAProof,
not a demonstrated defect in LAProof's theorem.
Our [BoundedRoundoff.lean](../Quadrature/Binary64/BoundedRoundoff.lean) and
[FunctionalAccuracy.lean](../Quadrature/Binary64/FunctionalAccuracy.lean) use and
prove a different sufficient range budget.

The [independent numerical check](../evidence/upstream-numerical-checked.json)
retains source URLs and hashes and checks both witnesses with exact rational
arithmetic. It also reconfirms the four earlier findings, every stored table
entry, and all ten polynomial results. The [review](../docs/review.md)
distinguishes these checks from the kernel proofs.

## A missing hypothesis in integral positivity

`proof/quadrature.v:732–739` states `Rintegral_gt_0` without `a < b` and
ends with `Admitted`. The constant function one on `[0, 0]` is continuous,
nonnegative, and not identically zero there, while its integral is zero.
[Examples/IntegralPositivity.lean](../Quadrature/Examples/IntegralPositivity.lean)
proves all these facts in `singleton_interval_positivity_counterexample`.
This is a Lean counterexample to the mathematical statement.
[MathematicalAudit.v](../scripts/upstream/MathematicalAudit.v) independently
checks it in Rocq using MathComp-Analysis. Its separate
`admitted_positivity_is_inconsistent` diagnostic applies the original declaration
to those premises and derives `False`; the assumption report retains
`Rintegral_gt_0`. Thus the correspondence with the actual original statement
is checked in Rocq as well. The independent counterexample does not use that
admission, and the diagnostic is outside our program certificates.
The [counterexample report](../evidence/upstream-vst-verified-logs/assumptions-37.txt)
contains only the three logical axioms inherited from MathComp's
singleton-integral theorem. The [diagnostic report](../evidence/upstream-vst-verified-logs/assumptions-38.txt)
adds the original `Rintegral_gt_0` admission. The driver checks that exact
relationship.

The use at line 1433 is in `sqr_poly_positive`, within the section whose
`Hab : a < b` is declared at line 775. Adding the missing premise is a
plausible repair for that application; the finding does not refute it on a
nondegenerate interval. Our `polynomialIntegral_square_pos` in
[Integral.lean](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Integral.lean) already requires `a < b`.

## Program and compilation results

The additional VST source findings concern the same pinned original revision:

| Finding | Original location | Consequence |
| --- | --- | --- |
| Wrong Hughes identifier | `proof/C/spec_quadrules.v:168–179`, `hughes_weight_spec`; `proof/C/spec_quadrules_highlevel.v:212–221`, `quadrules_ASI` | The interface registers `_gauss2d_weight` twice and omits `_hughes_weight`. |
| Missing callback body proof | `proof/C/quadrules.v`, ten internal functions; `proof/C/verif_quadrules.v`, nine `body_` lemmas | `testfun_spec` is assumed by the wrapper; no `body_testfun` establishes the C callback's contract. |

VST's `floyd/SeparationLogicAsLogic.v:273` defines `semax_body` by matching
the specification as `(_, mk_funspec ...)`. It deliberately ignores the
identifier. The function-list and whole-program obligations establish the
association between identifiers and bodies. A VSU assembles compatible
caller and callee specifications, checks initialization, and supports the
whole-program theorem. The quadrature VSU is not present in the examined
source. This explains how the original Hughes body proof can check despite
the wrong name; the missing composition check is where the mismatch matters.
The review module [SpecAudit.v](../scripts/upstream/SpecAudit.v) checks the
identifiers, the duplicate and missing registrations, and the actual table
definitions. Its retagged body theorem keeps the original `Gprog`; it is not
a completed repair of the interface.

The unmodified source fails to compile in the recorded Rocq 9.0.1,
MathComp 2.5, VST 2.16 environment at
`proof/C/spec_quadrules_highlevel.v:128` and 143. The product `'I_n * 'I_n`
needs an explicit `%type` scope. A separate source copy adds precisely those
two annotations and compiles all nine original body proofs. This is a
compilation compatibility finding, separate from a false numerical claim.
The [rebuild record](../evidence/upstream-vst-verified.json) retains both source
hashes and the diff. The original checkout is unchanged.

The committed Clight metadata identifies AArch64 with the Apple ABI; the
review's installed CompCert is configured for x86-64. The review checks the
committed syntax under that installed configuration and does not recreate the
authors' Apple toolchain or regenerate the original C-to-Clight translation.

| Manuscript result | Source/evidence | Precise limit |
| --- | --- | --- |
| Reused CLean infrastructure | [Vendored README](../vendor/clean/README.md), [integration evidence](../evidence/lean-quality.json) | Adapted arithmetic and explicit external calls; no automatic CompCert theorem transfer |
| Original source parsing and tables | [CSource/Frontend/SourceData.lean](../Quadrature/CSource/Frontend/SourceData.lean), [CSource/Tables/Literals.lean](../Quadrature/CSource/Tables/Literals.lean), [CSource/Frontend/ClightFunctions.lean](../Quadrature/CSource/Frontend/ClightFunctions.lean) | Selected functions and 110 initializers from the complete retained character data; not a general verified C frontend |
| Original wrapper with external cosine | [CSource/Wrapper/Accuracy.lean](../Quadrature/CSource/Wrapper/Accuracy.lean): `integrate_testfun_external_accuracy` | Generic adapted-strategy call under context, table, cosine-call and numerical contracts |
| Verified C cosine replacement | [CSource/Cosine/cosine.c](../Quadrature/CSource/Cosine/cosine.c), [CSource/Cosine/Total.lean](../Quadrature/CSource/Cosine/Total.lean): `call_correct` | Every permitted evaluation order returns exactly the functional polynomial for every binary64 input and preserves caller memory; numerical accuracy is certified for the application separately |
| Termination and progress for C calls | [CSource/Semantics/TotalCorrectness.lean](../Quadrature/CSource/Semantics/TotalCorrectness.lean): `Total.reaches`, `CallCorrect.accessible`, `CallCorrect.progress` | The inductive total-correctness judgment gives a terminating execution, excludes infinite executions, and rules out reachable stuck states. The transition rules are manually adapted from CompCert's C semantics; their agreement with Rocq is not mechanically proved |
| Initialized polynomial C library (Theorem `c-total`) | [CSource/Library/Initialization.lean](../Quadrature/CSource/Library/Initialization.lean): `from_sources`, `initialized`; [CSource/Library/Total.lean](../Quadrature/CSource/Library/Total.lean): `integral_total_accuracy`, `parsed_wrapper_total_accuracy` | Original five selected functions and 110 table literals plus the replacement C polynomial; total correctness and numerical accuracy for orders 1–10, in every permitted evaluation order, with no table or cosine hypothesis. General frontend correctness and Lean/Rocq correspondence remain open |
| Preservation by C-to-Clight normalization (Theorem `c-preservation`) | [CSource/Library/Preservation.lean](../Quadrature/CSource/Library/Preservation.lean): `parsed_refinement`, `initialized_outcomes_iff`, `wrapper_outcomes`; [CSource/Frontend/Refinement.lean](../Quadrature/CSource/Frontend/Refinement.lean); [Clight/Internal.lean](../Quadrature/Clight/Internal.lean) | Both frontend outputs, initialization, and function lookup are checked. The six selected functions have the same returned values and traces, terminate, and preserve caller memory on the supported inputs. Integrator counts are 0–10; accessors require valid stored cells; callback and cosine accept every binary64 input. No external-call determinism premise. A general parser/elaborator theorem and Lean/Rocq correspondence remain open |
| Initialized Clight applications | [Clight/Main.lean](../Quadrature/Clight/Main.lean), [Clight/StoredAccuracy.lean](../Quadrature/Clight/StoredAccuracy.lean), [evidence](../evidence/lean-quality.json) | Internal polynomial and authored entry points, orders 1–10. The normalized library's returns are related to these applications' observations in `normalized_integrate_application_observations_iff`, retaining the application theorem's external-call determinism premise |
| C returns and assembly observations (Theorem `c-assembly-observations`) | [CSourcePrograms.lean](../Quadrature/Compiler/Correspondence/CSourcePrograms.lean): `csource_integrate_asm_observations_iff`, `csource_wrapper_asm_observations_iff`, `parsed_wrapper_asm_accuracy`; [C total correctness](../Quadrature/CSource/Library/Total.lean); [assembly total correctness](../Quadrature/Compiler/Asm/StoredTotalCorrectness.lean) | Initialized C calls and imported assembly applications agree on the binary64 value under an explicit convention: C returns silently; assembly reports that value in an annotation and exits zero. All ten orders and the original two-node wrapper are covered, with no external-call determinism premise. Both sides terminate. The parsed wrapper theorem also includes source selection, exact bits, finiteness, and the `0.00356` bound. This does not prove that compiling the original C text produces these assembly trees |
| Lean assembly total correctness | [StoredTotalCorrectness.lean](../Quadrature/Compiler/Asm/StoredTotalCorrectness.lean): `StoredPrograms.progress`, `not_infinite`, `final_observations_iff`, `final_accuracy`; [evidence](../evidence/lean-quality.json) | Particular imported programs in Lean's adapted semantics; formal annotation and exit code |
| Return-address checks | [GeneratedReturnAddresses.lean](../Quadrature/Compiler/Asm/GeneratedReturnAddresses.lean), [evidence](../evidence/lean-quality.json) | All sixteen retained call sites; not a general compiler pass theorem |
| Rocq compilation and accuracy | [CertifiedStoredPolynomial.v](../compcert/certification/CertifiedStoredPolynomial.v), [certificate README](../compcert/certification/README.md), [evidence](../evidence/assembly-certificate.json) | Separately checked configuration; no cosine or successful-compilation premise for polynomial applications; logical dependencies recorded separately |
| Source-to-native chain | [Coverage ledger](../docs/coverage.md) | Incomplete. No general cross-kernel semantic connection, verified printing/linking/OS output, or platform cosine result is claimed |

## Evidence and publication scope

The [current validation](../evidence/lean-quality.json) records a full Lean
build, transitive project and CLean theorem audits, and a separate inspection
of the generic and initialized C wrapper theorems. The replacement C file is
a Lake input dependency and is checked against the text embedded in Lean.
The audits permit only `propext`,
`Classical.choice`, and `Quot.sound`. The audit selects declarations by their
defining module, including private helpers and declarations added to imported
namespaces. Generated certificates contribute to the counts.
Source and configuration hashes identify the checked snapshot; all pinned
dependency checkouts must be clean.

No speedup, proof-effort reduction, priority, or universal compiler-correctness
claim is made. The source archive includes working-tree changes and identifies
them in its manifest; it is not equivalent to `git archive HEAD`.
