# Where the Gaussian theory came from

We first developed the general Gaussian construction in LeanQuadrature, on top of
LeanPDE’s normalized rule interface and two-point estimates. We have since moved
that theory into LeanPDE and removed the local copies. LeanQuadrature now imports
the shared proofs for orthogonal polynomials, roots, recurrence, remainder, and
convergence, then uses them to verify stored rules and compiled programs.

The table keeps the original comparison with LeanPDE at revision
`03f523aff09fe3ff3069d54088770a264fc281f1`. It records where the proofs came from;
it is not a description of what the current LeanPDE dependency lacks. Links in
the final column now lead to the shared files.

This answers the question paragraph by paragraph for Section 2 of Appel and
Bindel's *Formalization of Gaussian Quadrature and Application Verification
(Preliminary Draft)*. Their numbering follows Chapter 23 of Stewart's
*Afternotes on Numerical Analysis*. The PDF abbreviates several paragraphs
and skips 14; the comments in their `quadrature.v` include that root argument.

“In LeanPDE” below means present in that earlier revision. It does not mean that every fact in its imported mathlib was developed
in LeanPDE. Nor does availability imply that our proof uses the theorem:
the sharp two-point Peano-kernel bound and mathlib's Taylor–Lagrange theorem
are available, but our general Gaussian remainder follows a separate
Hermite and Rolle argument.

## The 24 paragraphs

The comparison concerns **exact real mathematics**. It does not count the
floating-point or C proofs as proofs of a mathematical paragraph.
For the general Gaussian results, assume a finite interval with `a < b`,
a continuous weight strictly positive on `[a, b]`, and a positive node count.
Definitions, equivalent results proved by another route, and omitted lemmas
are distinguished below.

General Gaussian names now have prefix `PDE.Symbolic.Continuum.`; the explicit
Legendre rules retain `Quadrature.Legendre.`. The source links resolve shorter
names, including those inside the `GaussianRule` namespace.

| ¶ | Mathematical content | LeanPDE at `03f523af` | Developed in LeanQuadrature; now shared where linked |
| --- | --- | --- | --- |
| 1 | A finite Gaussian sum for a weighted integral | `QuadratureRule` represents normalized finite rules; `normalizedValue` and `valueOn` evaluate them. This is a general interface, without a general weighted Gaussian construction. [Rule][pde-rule] | ✓ `GaussianRule` represents the weighted rule; `GaussianRule.value` evaluates its sum. General existence is proved separately. [Weighted](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Weighted.lean) |
| 2 | Notation for integration against a fixed weight | Uses mathlib's interval integral. The normalized rule interface targets unit weight on `[0, 1]`. [Rule][pde-rule] | ✓ `polynomialIntegral` is the integral of a polynomial times the weight function. [Integral](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Integral.lean) |
| 3 | Linearity of integration | mathlib supplies integral linearity; `normalizedValue_add` and `normalizedValue_const_mul` prove linearity of rule evaluation. [Rule][pde-rule] | ✓ `polynomialIntegral` packages the weighted polynomial integral as a linear map using mathlib. This reuses integral theory. [Integral](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Integral.lean) |
| 4 | Orthogonality via the integral of a product | No general quadrature inner product in these modules. | ✓ `momentInnerCore` constructs the polynomial inner product from a linear functional positive on nonzero squares. `polynomialIntegral_square_pos` provides the integral case. [Orthogonal](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Orthogonal.lean), [Integral](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Integral.lean) |
| 5 | Orthogonal polynomials, one of each degree | No general family in the quadrature development. | ✓ `exists_monic_orthogonal`, `orthogonalPolynomial_degree`, and `orthogonalPolynomial_orthogonal`. Projection constructs the unique monic polynomial orthogonal to every lower degree. [Orthogonal](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Orthogonal.lean) |
| 6 | Unique expansion in an arbitrary monic polynomial family | No corresponding quadrature lemma. | **Not separately formalized.** `exists_monic_orthogonal` bypasses this basis-expansion lemma by using mathlib's orthogonal projection. Its conclusion is not the arbitrary-family expansion statement. [Orthogonal](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Orthogonal.lean) |
| 7 | Induction proving that expansion | No corresponding quadrature proof. | **Not a separate proof of paragraph 6.** `degree_sub_coeff_mul_lt` formalizes the leading-coefficient elimination used later in our recurrence proof. [Recurrence](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Recurrence.lean) |
| 8 | Orthogonality to every polynomial of lower degree | No general Gaussian-family theorem. | ✓ `orthogonalPolynomial_orthogonal` proves precisely this property for the constructed family. [Orthogonal](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Orthogonal.lean) |
| 9 | The degree-zero and degree-one polynomials | Explicit two-point nodes, without this general family construction. [GaussLegendre][pde-gauss] | ✓ `orthogonalPolynomial_zero` and `orthogonalPolynomial_one`, including the coefficient expressed as a ratio of integrals. [Recurrence](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Recurrence.lean) |
| 10 | The recurrence coefficients | No general recurrence coefficients. | ✓ `recurrenceAlpha` and `recurrenceBeta` give the formulas; `orthogonalPolynomial_recurrence` proves the identity with those coefficients. [Recurrence](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Recurrence.lean) |
| 11 | Terms below the previous polynomial vanish | No general recurrence proof. | ✓ The three-term identity has no additional lower terms. Its proof uses lower-degree orthogonality; it does not define an infinite list of coefficients and prove each one zero separately. [Recurrence](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Recurrence.lean) |
| 12 | The three-term recurrence | No general recurrence theorem. | ✓ `orthogonalPolynomial_recurrence`, `recurrenceBeta_eq_norm_ratio`, and `recurrenceBeta_pos`. The recurrence is derived after constructing the family by projection. [Recurrence](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Recurrence.lean) |
| 13 | All roots are real, simple, and inside the interval | Explicit formulas for the two nodes and proofs that they lie in `[0, 1]`. [GaussLegendre][pde-gauss] | ✓ `orthogonal_splits`, `orthogonal_squarefree`, and `orthogonal_root_mem_Ioo`; `exists_gaussian_quadrature` supplies the distinct interior nodes at every positive order. [Roots](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Roots.lean), [Gaussian](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Gaussian.lean) |
| 14 | The argument establishing the root claim | No general root argument. | ✓ **An alternative proof of paragraph 13.** `orthogonal_factor_has_root` uses constant sign and integral positivity; factorization gives splitting, and a separate square argument gives simple roots. It is not a transcription of Stewart's sign-change counting proof. [Roots](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Roots.lean) |
| 15 | Weights obtained by integrating the Lagrange basis | Exactness from moments and a concrete two-point rule; no general construction on orthogonal roots. [Rule][pde-rule], [GaussLegendre][pde-gauss] | ✓ `interpolatoryWeight`, `interpolatory_exact`, and `GaussianRule.weights_eq_interpolatoryWeight`. [Algebra](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Algebra.lean), [Characterization](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Characterization.lean) |
| 16 | Exactness through degree `2n − 1` for `n` nodes | `gaussLegendreTwoRule.exactUpTo_three` and its polynomial/affine corollaries. [GaussLegendre][pde-gauss] | ✓ `gaussian_exact` proves the general result by polynomial division and lower-degree orthogonality. [Algebra](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Algebra.lean) |
| 17 | Positive Gaussian weights | The two normalized weights are explicitly `1/2`. [GaussLegendre][pde-gauss] | ✓ `gaussian_weight_pos`, using the positive integral of a squared Lagrange basis polynomial. [Algebra](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Algebra.lean) |
| 18 | Weights sum to the integral mass; each is bounded by it | `gaussLegendreTwoRule.weightVariation_eq_one` for the normalized two-point rule. [GaussLegendre][pde-gauss] | ✓ `GaussianRule.sum_weights` and `GaussianRule.weight_le_mass`. The bound is `∫ w`, not always one. The original Rocq theorem already states the correct mass bound; the discrepancy is in the quoted prose. [Weighted](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Weighted.lean) |
| 19 | Gaussian remainder | **The sharp two-point fourth-derivative bound was already present.** It is an absolute error estimate proved with a Peano kernel. [GaussLegendrePeano][pde-peano] | ✓ `hermite_remainder`, `GaussianRule.remainder_of_derivative_chain`, `GaussianRule.remainder`, and `GaussianRule.abs_error_le`. These give the general `n`-node identity and bound with explicit regularity. See the hypotheses below. [Remainder](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Remainder.lean) |
| 20 | Convergence for continuous integrands as order increases | Stability estimates under uniform approximation, and composite/adaptive two-point methods. These do not supply the general increasing-order Gaussian convergence theorem. [Approximation][pde-approx] | ✓ `gaussian_rules_converge` proves the weighted compact-interval limit. `QuadratureRule.tendsto_valueOn_of_nonneg_of_exactUpTo_self` separately treats normalized positive rules of increasing exactness, using LeanPDE's interface and stability estimate. [Weighted](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Weighted.lean), [PositiveRule](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/PositiveRule.lean) |
| 21 | Gauss–Legendre: unit weight on `[-1, 1]` | The normalized two-point rule, affine transport, cubic exactness, and sharp error bound. [GaussLegendre][pde-gauss], [GaussLegendrePeano][pde-peano] | ✓ `Legendre.two` directly reuses LeanPDE. Our explicit rules through four nodes are identified with `Legendre.monicPolynomial`; the general construction specializes to unit weight. Separate root, weight, and stored-table certificates cover ten orders. [Basic](../Quadrature/Legendre/Basic.lean), [Identification](../Quadrature/Legendre/Identification.lean), [Certificates](../Quadrature/Rules/Certificates.lean) |
| 22 | Gauss–Laguerre on `[0, ∞)` | Outside the quadrature development inspected here. | ○ No unbounded-domain Gaussian construction, remainder, or convergence theorem in this project. The original paper explicitly leaves this family unimplemented. |
| 23 | Gauss–Hermite on the real line | Outside the quadrature development inspected here. | ○ No such quadrature development here. Hermite **interpolation**, used in paragraph 19, is different from Gauss–Hermite **quadrature**. Existing Hermite polynomial definitions do not by themselves supply this quadrature theory. |
| 24 | Other choices of interval and weight give other Gaussian rules | A concluding observation, not a theorem to check separately. | The general compact-interval theorem allows other positive continuous weights. It does not implement every named Gaussian family or allow infinite endpoints. |

The table therefore does **not** support “all 24 paragraphs were already
done in LeanPDE,” or “we separately formalized all 24 textbook paragraphs.”
The central compact-interval results are proved, with a different route
through the orthogonal-polynomial construction and the remainder. Paragraphs
6–7 are bypassed, 22–23 are outside the development, and 24 is an observation.

## The two-point theorem already in LeanPDE

In the namespace `PDE.Symbolic.Continuum`, the theorem
`norm_integral_sub_gaussLegendreTwoRule_valueOn_le` states

$$
\left|\int_a^b f(x)\,dx-Q_2(f)\right|
\le \frac{M(b-a)^5}{4320}.
$$

Its hypotheses are `a < b`, `ContDiffOn ℝ 4 f (Set.Icc a b)`, and a bound by
`M` on the norm of `iteratedDerivWithin 4 f (Set.Icc a b)` at every point of
the closed interval. Its proof integrates an explicitly nonnegative Peano
kernel. `gaussLegendreTwoRule.sharpCert` packages the estimate as a quadrature
certificate.

On `[-1, 1]`, `(b − a)^5 / 4320 = 1 / 135`. Thus the fourth-derivative bound
`M / 135` for the two-point rule was available in LeanPDE. Our general
remainder theorem implies the same coefficient when specialized to that
rule. The two proofs have different conclusions and constructions: the
LeanPDE theorem gives an absolute bound directly, while the general
theorem also supplies a point `ξ` for the integrated remainder identity.

## Exactly which interpolation and remainder we proved

Write `n` for the **number of nodes**, let the nodes be distinct, and put

$$
p_n(x)=\prod_{i=1}^{n}(x-x_i).
$$

Our `hermiteInterpolant` is a polynomial of degree less than `2n` matching
the prescribed value and first derivative at each of the `n` nodes.
`hermiteInterpolant_eval`, `hermiteInterpolant_derivative_eval`, and
`hermiteInterpolant_natDegree_lt` prove those properties. This is
first-derivative Hermite interpolation at an arbitrary positive number of
distinct nodes. We have not provided an interpolant API for arbitrary
derivative multiplicities.

The pointwise theorem `hermite_remainder` assumes:

- `a < b` and `n > 0`;
- distinct nodes in the closed interval `[a, b]`;
- functions `F₀, …, F₂ₙ`, with `Fₖ` continuous on `[a, b]` for `k < 2n`;
- `HasDerivAt Fₖ (Fₖ₊₁ y) y` for `y ∈ (a, b)` and `k < 2n`.

For each `x ∈ [a, b]`, it gives some `ξ ∈ [a, b]` such that

$$
F_0(x)-H(x)=\frac{F_{2n}(\xi)}{(2n)!}\,p_n(x)^2,
$$

where `H` matches `F₀` and `F₁` at the nodes. The repeated Rolle theorem
counts the double zeros at the nodes and the additional zero at `x`.
Continuity of the highest derivative `F₂ₙ` is not a hypothesis of this
pointwise result.

The integrated theorem `GaussianRule.remainder_of_derivative_chain` adds
continuity of `F₂ₙ`, a positive continuous weight, and a Gaussian rule on
the interval. It proves

$$
\int_a^b F_0(x)w(x)\,dx-Q_n(F_0)
=\frac{F_{2n}(\xi)}{(2n)!}\int_a^b p_n(x)^2w(x)\,dx
$$

for some `ξ ∈ [a, b]`. The proof does not assume that the pointwise witnesses
depend measurably on `x`. Instead, extrema of the continuous highest
derivative bound the integral, and the intermediate value theorem supplies
a single witness for that integral.

`GaussianRule.remainder` obtains the derivative chain from
`ContDiffOn ℝ (2 * n) f (Set.Icc a b)`. The derivative in its conclusion is
`iteratedDerivWithin (2 * n) f (Set.Icc a b) ξ`. Using derivatives within
the closed interval avoids assuming a smooth extension outside it.
`GaussianRule.abs_error_le` replaces the derivative at the witness with a
uniform absolute bound.

With two nodes, the derivative order is **four**. Stewart's `2n + 2` is
correct when his rule has `n + 1` nodes. The problem in the preliminary
formal statement is mixing that convention with a record that has `n`
nodes. The derivative order is not intrinsically wrong without reference
to the node count.

## Taylor–Lagrange and the inherited analysis

The pinned mathlib already has `taylor_mean_remainder_lagrange` in
[`Mathlib/Analysis/Calculus/Taylor.lean`][mathlib-taylor]. For a Taylor
polynomial of degree `m` about one center, it assumes `ContDiffOn` through
order `m` on the closed segment and differentiability of the `m`th within
derivative on the open segment. It gives the order-`m + 1` Lagrange
remainder at an interior point.

That theorem is inherited library work. Our contribution here is the
multi-node first-derivative Hermite result and the passage to the weighted
integral. They use mathlib's polynomial algebra, Lagrange basis,
orthogonal projection, calculus, and integral theory. The convergence
argument also uses mathlib's Weierstrass approximation theorem.

## Sources and reproduction

The comparison uses these exact revisions:

- LeanPDE: `03f523aff09fe3ff3069d54088770a264fc281f1`.
- mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- Appel–Bindel source: `e79a28dba247db9f934289bcf4e4debd5eebc884`,
  especially [`proof/quadrature.v`][upstream-quadrature].

These are source-attribution checks against the dependency revision, not
a reconstruction of when each mathematical idea was first developed.
The [paper checks](../evidence/paper-checks.json) record the declaration
and assumption checks for this comparison. The
[full Lean validation](../evidence/lean-quality.json) records the build and
assumption audit of the project proofs.

LeanPDE is private. Its links require access; contact Robert to obtain it
before attempting the full build. The public LeanQuadrature source archive
does not include the private dependency.

[pde-rule]: https://github.com/lean-dojo/LeanPDE/blob/03f523aff09fe3ff3069d54088770a264fc281f1/PDE/Symbolic/Continuum/Quadrature/Rule.lean
[pde-gauss]: https://github.com/lean-dojo/LeanPDE/blob/03f523aff09fe3ff3069d54088770a264fc281f1/PDE/Symbolic/Continuum/Quadrature/GaussLegendre.lean
[pde-approx]: https://github.com/lean-dojo/LeanPDE/blob/03f523aff09fe3ff3069d54088770a264fc281f1/PDE/Symbolic/Continuum/Quadrature/Approximation.lean
[pde-peano]: https://github.com/lean-dojo/LeanPDE/blob/03f523aff09fe3ff3069d54088770a264fc281f1/PDE/Symbolic/Continuum/Quadrature/GaussLegendrePeano.lean
[mathlib-taylor]: https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Analysis/Calculus/Taylor.lean
[upstream-quadrature]: https://github.com/VeriNum/simple_cfem/blob/e79a28dba247db9f934289bcf4e4debd5eebc884/proof/quadrature.v
