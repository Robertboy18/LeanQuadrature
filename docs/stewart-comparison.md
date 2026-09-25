# Gaussian quadrature in LeanPDE

LeanPDE provides weighted Gaussian rules of every positive order on compact
intervals, with proofs of their construction, roots, exactness, positive
weights, recurrence, remainder, and convergence. It also provides explicit
Legendre rules through four nodes, general root and weight certificates,
Taylor bounds, and a [normalized quadrature interface][pde-rule].
LeanQuadrature imports these results to verify the stored tables and programs.

The table identifies the current LeanPDE definitions and theorems for
each mathematical paragraph in Section 2 of Appel and
Bindel's *Formalization of Gaussian Quadrature and Application Verification
(Preliminary Draft)*. Their numbering follows Chapter 23 of Stewart's
*Afternotes on Numerical Analysis*. The PDF abbreviates several paragraphs
and skips 14; the comments in their `quadrature.v` include that root argument.

The source links refer to the LeanPDE dependency used by this project.
mathlib supplies the polynomial algebra, orthogonal projection, calculus,
and integral theory on which these results build.

## The 24 paragraphs

The comparison concerns **exact real mathematics**. It does not count the
floating-point or C proofs as proofs of a mathematical paragraph.
For the general Gaussian results, assume a finite interval with `a < b`,
a continuous weight strictly positive on `[a, b]`, and a positive node count.
Definitions, equivalent results proved by another route, and omitted lemmas
are distinguished below.

General Gaussian names have prefix `PDE.Symbolic.Continuum.`; the explicit
Legendre rules use `PDE.Symbolic.Continuum.Legendre.`. The source links resolve shorter
names, including those inside the `GaussianRule` namespace.

| ¶ | Mathematical topic | LeanPDE result |
| --- | --- | --- |
| 1 | A finite Gaussian sum for a weighted integral | ✓ `GaussianRule` represents the weighted rule; `GaussianRule.value` evaluates its sum. General existence is proved separately. [Weighted](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Weighted.lean) |
| 2 | Notation for integration against a fixed weight | ✓ `polynomialIntegral` is the integral of a polynomial times the weight function. [Integral](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Integral.lean) |
| 3 | Linearity of integration | ✓ `polynomialIntegral` packages the weighted polynomial integral as a linear map using mathlib. This reuses integral theory. [Integral](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Integral.lean) |
| 4 | Orthogonality via the integral of a product | ✓ `momentInnerCore` constructs the polynomial inner product from a linear functional positive on nonzero squares. `polynomialIntegral_square_pos` provides the integral case. [Orthogonal](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Orthogonal.lean), [Integral](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Integral.lean) |
| 5 | Orthogonal polynomials, one of each degree | ✓ `exists_monic_orthogonal`, `orthogonalPolynomial_degree`, and `orthogonalPolynomial_orthogonal`. Projection constructs the unique monic polynomial orthogonal to every lower degree. [Orthogonal](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Orthogonal.lean) |
| 6 | Unique expansion in an arbitrary monic polynomial family | **Not separately formalized.** `exists_monic_orthogonal` bypasses this basis-expansion lemma by using mathlib's orthogonal projection. Its conclusion is not the arbitrary-family expansion statement. [Orthogonal](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Orthogonal.lean) |
| 7 | Induction proving that expansion | **Not a separate proof of paragraph 6.** `degree_sub_coeff_mul_lt` formalizes the leading-coefficient elimination used later in our recurrence proof. [Recurrence](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Recurrence.lean) |
| 8 | Orthogonality to every polynomial of lower degree | ✓ `orthogonalPolynomial_orthogonal` proves precisely this property for the constructed family. [Orthogonal](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Orthogonal.lean) |
| 9 | The degree-zero and degree-one polynomials | ✓ `orthogonalPolynomial_zero` and `orthogonalPolynomial_one`, including the coefficient expressed as a ratio of integrals. [Recurrence](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Recurrence.lean) |
| 10 | The recurrence coefficients | ✓ `recurrenceAlpha` and `recurrenceBeta` give the formulas; `orthogonalPolynomial_recurrence` proves the identity with those coefficients. [Recurrence](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Recurrence.lean) |
| 11 | Terms below the previous polynomial vanish | ✓ The three-term identity has no additional lower terms. Its proof uses lower-degree orthogonality; it does not define an infinite list of coefficients and prove each one zero separately. [Recurrence](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Recurrence.lean) |
| 12 | The three-term recurrence | ✓ `orthogonalPolynomial_recurrence`, `recurrenceBeta_eq_norm_ratio`, and `recurrenceBeta_pos`. The recurrence is derived after constructing the family by projection. [Recurrence](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Recurrence.lean) |
| 13 | All roots are real, simple, and inside the interval | ✓ `orthogonal_splits`, `orthogonal_squarefree`, and `orthogonal_root_mem_Ioo`; `exists_gaussian_quadrature` supplies the distinct interior nodes at every positive order. [Roots](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Roots.lean), [Gaussian](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Gaussian.lean) |
| 14 | The argument establishing the root claim | ✓ **An alternative proof of paragraph 13.** `orthogonal_factor_has_root` uses constant sign and integral positivity; factorization gives splitting, and a separate square argument gives simple roots. It is not a transcription of Stewart's sign-change counting proof. [Roots](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Roots.lean) |
| 15 | Weights obtained by integrating the Lagrange basis | ✓ `interpolatoryWeight`, `interpolatory_exact`, and `GaussianRule.weights_eq_interpolatoryWeight`. [Algebra](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Algebra.lean), [Characterization](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Characterization.lean) |
| 16 | Exactness through degree `2n − 1` for `n` nodes | ✓ `gaussian_exact` proves the general result by polynomial division and lower-degree orthogonality. [Algebra](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Algebra.lean) |
| 17 | Positive Gaussian weights | ✓ `gaussian_weight_pos`, using the positive integral of a squared Lagrange basis polynomial. [Algebra](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Algebra.lean) |
| 18 | Weights sum to the integral mass; each is bounded by it | ✓ `GaussianRule.sum_weights` and `GaussianRule.weight_le_mass`. The bound is `∫ w`, not always one. The original Rocq theorem already states the correct mass bound; the discrepancy is in the quoted prose. [Weighted](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Weighted.lean) |
| 19 | Gaussian remainder | ✓ `hermite_remainder`, `GaussianRule.remainder_of_derivative_chain`, `GaussianRule.remainder`, and `GaussianRule.abs_error_le`. These give the general `n`-node identity and bound with explicit regularity. See the hypotheses below. [Remainder](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Remainder.lean) |
| 20 | Convergence for continuous integrands as order increases | ✓ `gaussian_rules_converge` proves the weighted compact-interval limit. `QuadratureRule.tendsto_valueOn_of_nonneg_of_exactUpTo_self` separately treats normalized positive rules of increasing exactness, using LeanPDE's interface and stability estimate. [Weighted](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Gaussian/Weighted.lean), [PositiveRule](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/PositiveRule.lean) |
| 21 | Gauss–Legendre: unit weight on `[-1, 1]` | ✓ LeanPDE provides explicit rules through four nodes. `Legendre.twoGaussian` uses `gaussLegendreTwoRule`; all four rules are identified with `Legendre.monicPolynomial`. The general construction specializes to unit weight. Shared root and weight certificate proofs support the ten stored-table certificates. [Basic](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Legendre/Basic.lean), [Identification](https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Legendre/Identification.lean), [Certificates](../Quadrature/Rules/Certificates.lean) |
| 22 | Gauss–Laguerre on `[0, ∞)` | ○ No unbounded-domain Gaussian construction, remainder, or convergence theorem in this project. The original paper explicitly leaves this family unimplemented. |
| 23 | Gauss–Hermite on the real line | ○ No such quadrature development here. Hermite **interpolation**, used in paragraph 19, is different from Gauss–Hermite **quadrature**. Existing Hermite polynomial definitions do not by themselves supply this quadrature theory. |
| 24 | Other choices of interval and weight give other Gaussian rules | The general compact-interval theorem allows other positive continuous weights. It does not implement every named Gaussian family or allow infinite endpoints. |

The compact-interval construction, remainder, and convergence are LeanPDE
results. LeanQuadrature supplies the particular stored-table certificates
and the floating-point and program proofs that use this theory.

## The sharp two-point bound

In the namespace `PDE.Symbolic.Continuum`, the theorem
`norm_integral_sub_gaussLegendreTwoRule_valueOn_le` states

$$
\left|\int_a^b f(x)\,dx-Q_2(f)\right|
\le \frac{M(b-a)^5}{4320}.
$$

Its hypotheses are `a < b`, `ContDiffOn ℝ 4 f (Set.Icc a b)`, and a bound by
`M` on the norm of `iteratedDerivWithin 4 f (Set.Icc a b)` at every point of
the closed interval. Its proof in [GaussLegendrePeano][pde-peano] integrates
an explicitly nonnegative Peano kernel. `gaussLegendreTwoRule.sharpCert`
packages the estimate as a quadrature certificate.

On `[-1, 1]`, `(b − a)^5 / 4320 = 1 / 135`, giving the fourth-derivative
bound `M / 135`. LeanPDE's general remainder theorem gives the same
coefficient when specialized to the two-point rule. The Peano-kernel
theorem gives an absolute bound directly; the general theorem also
supplies a point `ξ` for the integrated remainder identity.

## The interpolation and remainder theorems

Write `n` for the **number of nodes**, let the nodes be distinct, and put

$$
p_n(x)=\prod_{i=1}^{n}(x-x_i).
$$

LeanPDE's `hermiteInterpolant` is a polynomial of degree less than `2n` matching
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

## Analysis supplied by mathlib

mathlib supplies `taylor_mean_remainder_lagrange` in
[`Mathlib/Analysis/Calculus/Taylor.lean`][mathlib-taylor]. For a Taylor
polynomial of degree `m` about one center, it assumes `ContDiffOn` through
order `m` on the closed segment and differentiability of the `m`th within
derivative on the open segment. It gives the order-`m + 1` Lagrange
remainder at an interior point.

LeanPDE's multi-node first-derivative Hermite result and its passage to the
weighted integral use mathlib's polynomial algebra, Lagrange basis,
orthogonal projection, calculus, and integral theory. The Gaussian
convergence argument uses mathlib's Weierstrass approximation theorem.

## Sources and reproduction

The declarations above are checked against the dependencies recorded in
[`lake-manifest.json`](../lake-manifest.json):

- **LeanPDE:** the current mathematical library linked throughout the table.
- **mathlib:** its polynomial, analysis, and approximation libraries.
- **Appel–Bindel source:** [`proof/quadrature.v`][upstream-quadrature] at the
  revision identified in the [source review](../evidence/upstream-review.json).

The [paper checks](../evidence/paper-checks.json) record the declaration
and assumption checks for this map. The
[full Lean validation](../evidence/lean-quality.json) records the build and
assumption audit of the project proofs.

LeanPDE is private. Its links require access; contact Robert to obtain it
before attempting the full build. The public LeanQuadrature source archive
does not include the private dependency.

[pde-rule]: https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/Rule.lean
[pde-peano]: https://github.com/lean-dojo/LeanPDE/blob/40ad295c230f2f8d97249d93aedbdd77671327de/PDE/Symbolic/Continuum/Quadrature/GaussLegendrePeano.lean
[mathlib-taylor]: https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Analysis/Calculus/Taylor.lean
[upstream-quadrature]: https://github.com/VeriNum/simple_cfem/blob/e79a28dba247db9f934289bcf4e4debd5eebc884/proof/quadrature.v
