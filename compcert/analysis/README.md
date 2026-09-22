# Integral accuracy for the four C rules

[`ClightIntegralAccuracy.v`](../ClightIntegralAccuracy.v) proves an error bound
against the real integral for the actual initialized C quadrature loops.
It handles orders one through four under the existing callback execution
contracts. The analytic proof is independent of the Lean development.

Let \(n\) be the order, \(\eta\) the callback error, \(B\) a bound on the
integrand's absolute value, \(L\) a bound on its first derivative, and \(M\)
a bound on its derivative of order \(2n\). With the certified table tolerances
\(\delta_x=10^{-16}\), \(\delta_w=5\cdot10^{-16}\), the theorem gives

$$
\left|a_n-\int_{-1}^{1}g(x)\,dx\right|
\le
c_n M
+2n\varepsilon(r)
+(2+n\delta_w)(\eta+L\delta_x)
+n\delta_w B.
$$

Here \(a_n\) is the decoded C return value, \(r\) is the arithmetic radius,
and \(c_n\) is the sharp Gaussian constant:

| Order \(n\) | \(c_n\) |
| --- | --- |
| 1 | \(1/3\) |
| 2 | \(1/135\) |
| 3 | \(1/15750\) |
| 4 | \(1/3472875\) |

The numerical range condition is

$$
r\le\mathrm{maxFinite},\qquad
(2+n\delta_w)(B+\eta)+2n\varepsilon(r)\le r.
$$

The callback must return a finite value within \(\eta\) of \(g\) at every
finite input in `[-1,1]`. Its execution at each stored node must be silent
and preserve the initial memory. The function and derivative bounds are
nonnegative. Ordinary real derivatives through order \(2n\) must exist at all
points of `[-1,1]`, including its endpoints. The theorem derives integrability,
the Lipschitz condition, and finite arithmetic from these hypotheses.

The analytic constant comes from the Hermite interpolant \(H\), which agrees
with \(g\) and \(g'\) at the \(n\) nodes and has degree below \(2n\).
Consequently \(Q_n(g)=Q_n(H)=\int H\). For each \(x\), repeated Rolle gives

$$
g(x)-H(x)=\frac{g^{(2n)}(\xi_x)}{(2n)!}p_n(x)^2,
\qquad \xi_x\in[-1,1].
$$

Taking absolute values and integrating gives
\(c_n=\int_{-1}^{1}p_n(x)^2\,dx/(2n)!\).
[`SharpAccuracy.v`](../SharpAccuracy.v) evaluates these four polynomial
integrals exactly. The pointwise witness may depend on \(x\); the proof of
the absolute bound needs no continuity of the highest derivative.

[`PolynomialAccuracy.v`](../PolynomialAccuracy.v) proves that cancellation
for every polynomial through degree \(2n-1\).
[`RealPolynomials.v`](../RealPolynomials.v) supplies coefficient-list evaluation
and differentiation.
[`HermiteInterpolation.v`](../HermiteInterpolation.v) constructs the interpolant
by adding a linear multiple of the preceding squared nodal polynomial. Its
double zeros preserve the values and derivatives already matched.
[`HermiteRolle.v`](../HermiteRolle.v) counts the derivative zeros between the
nodes and at the double zeros; [`HermiteRemainder.v`](../HermiteRemainder.v)
uses that count to prove the pointwise formula for arbitrary distinct sorted
nodes in a closed interval.

[`TaylorAccuracy.v`](../TaylorAccuracy.v) proves the Taylor formula in either
direction using a moving expansion: differentiating with respect to its center
cancels the lower derivative terms, and the mean value theorem supplies the
remainder point. Its weaker `4*M/(2*n)!` bound remains available; the C integral
budget now uses the sharp Hermite bound. Both arguments need derivative
existence at points of the closed segment.

Ordinary endpoint derivatives are a different hypothesis from the
Lean `ContDiffOn` formulation. The weighted integral formula with a single
witness remains a Lean theorem. This certificate does not transfer Lean terms
to Rocq, prove a platform cosine implementation, or certify a linked executable.
Its C conclusion is total correctness and the bound for every returning
Clight execution under the stated callback contracts.

[`CminorIntegralAccuracy.v`](../CminorIntegralAccuracy.v) gives the same
conclusion at the Cminor entry produced by the two checked lowering passes.
[`CminorSafety.v`](../CminorSafety.v) proves that the compiled library call
cannot get stuck or execute infinitely, and that its return value and final
memory are unique. The argument uses CompCert's Cminor determinacy theorem:
[`SilentTermination.v`](../SilentTermination.v) shows that a finite silent
execution to a terminal state fixes every competing prefix.

The Cminor function is located through the actual compiled symbol table.
Both translations succeed by checked computation. The theorem retains the
source callback contracts and needs no separate target callback or
compiler-success assumption. Cminor introduces stack allocation, so its final
memory is related to initial source memory by `Mem.inject`. The general
four-rule theorem stops at Cminor. The separate concrete example certificates
cover the remaining backend.

## Reproduction

The checker first repeats the 14-file numerical check of `check-clight-roundoff.py`. It then exports clean
source archives at the following exact revisions, builds the required MathComp
closure and complete Coquelicot library, and checks the analytic files, both
lowering passes, and the Cminor total-correctness and integral theorems.
It does not reuse compiled MathComp or Coquelicot artifacts.

| Library | Version | Revision |
| --- | --- | --- |
| MathComp | 1.19.0 | `f7528eb05b49bca45fb07e274021a8c4a3200efb` |
| Coquelicot | 3.4.2 | `594b782cef83a8ae214c44152c72dcb80f88d93c` |

The compiler is the same pinned Coq 8.20.1 container used by the CompCert
certificates. MathComp 1.19.0's opam manifest declares Coq `<8.20~`.
The required `seq.vo` dependency closure builds from unmodified source here
on 8.20.1; this is observed compatibility for this subset, rather than a claim
of upstream support for that version combination. The retained logs include
the upstream deprecation and coercion warnings.

```sh
python3 scripts/check-clight-integral.py \
  --compcert-root /path/to/built/unmodified/CompCert-3.17 \
  --clight-source /path/to/pinned/quadrules.v \
  --mathcomp-root /path/to/mathcomp-at-pinned-revision \
  --coquelicot-root /path/to/coquelicot-at-pinned-revision \
  --work-dir /path/to/empty/local/build \
  --output /path/to/empty/local/build/result.json
```

[`evidence/clight-integral.json`](../../evidence/clight-integral.json) records
the completed 27-file check and all 210 theorem assumption audits, including
the underlying numerical record. The combined audit lists ten standard
real-analysis and CompCert dependencies. Relative to the eight dependencies
of the Clight analytic theorem, the lowering simulations add
`Axioms.proof_irr` and `Eqdep.Eq_rect_eq.eq_rect_eq`, both already present in
the CompCert allowlist. The checker rejects project admissions or custom axioms.
