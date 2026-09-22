# The FloatLib–CompCert correspondence

The two libraries return the same certified bits for the quadrature example
and for all ten stored orders using the internal cosine polynomial.
[`Clight/StoredAccuracy.lean`](../Quadrature/Clight/StoredAccuracy.lean) and
[`StoredPolynomialAccuracy.v`](../compcert/StoredPolynomialAccuracy.v) independently
prove those ten encodings and their integral-error bounds, using the actual
C weights and the same Horner operation order.
They do not return the same bits for every binary64 operation. For example,
take a quiet NaN with payload 1 and a signaling NaN with payload 2:

```text
q = 0x7ff8000000000001
s = 0x7ff0000000000002

FloatLib:       q + s = 0x7ff8000000000002
CompCert x86:   q + s = 0x7ff8000000000001
```

FloatLib chooses a signaling NaN before a quiet one, then sets the quiet bit.
CompCert's x86 model chooses the first NaN operand. Their policies also differ
for invalid operations: FloatLib's canonical NaN has positive sign, while
CompCert's x86 default NaN has negative sign. FloatLib implements subtraction
by negating the right operand before addition; this can change a NaN's sign
where CompCert's subtraction preserves it.

These are differences in the libraries being connected, not additional errors
in the quadrature paper.

| Operation | FloatLib result bits | CompCert x86_64 result bits |
| --- | --- | --- |
| `q + s` | `7ff8000000000002` | `7ff8000000000001` |
| `q * s` | `7ff8000000000002` | `7ff8000000000001` |
| `+∞ + -∞` | `7ff8000000000000` | `fff8000000000000` |
| `+∞ * +0` | `7ff8000000000000` | `fff8000000000000` |
| `+0 / +0` | `7ff8000000000000` | `fff8000000000000` |
| `1 - q` | `fff8000000000001` | `7ff8000000000001` |

Every entry is certified by reduction in its own proof assistant:
[`Quadrature/Binary64/ExceptionalValues.lean`](../Quadrature/Binary64/ExceptionalValues.lean)
checks FloatLib, and
[`compcert/ExceptionalValues.v`](../compcert/ExceptionalValues.v)
checks CompCert. Both files state the input encodings explicitly.
The paired certificates refute unrestricted bitwise agreement. They are not a
translation of either library or a proof imported between the two kernels.
The check uses FloatLib revision
`393bea610296bf9a9ee5a479508c351edb65cc6d` and unmodified CompCert 3.17 revision
`7b1f02b09954b9b916eb2a91d283c9b5355bf172`, with the x86_64 architecture module.

## The finite quadrature obligation

The quadrature loop multiplies each weight by a callback result and adds the
product to an accumulator. Its accuracy theorem requires finite callback
results and supplies a range budget. This budget excludes overflow as well as
NaNs in these multiplications and additions.

[`FiniteExecution.lean`](../Quadrature/Binary64/FiniteExecution.lean) makes that fact
available as a reusable certificate. It proves finiteness of every weighted
sample, the accumulator after any number of iterations, and the full
`integrationTree`. `StoredRule.Certificate.finite_execution` instantiates the
certificate using the general callback and table bounds for the supported
rules. No finite-execution assumption is added.

The same file proves the following decoded semantics. Write \(R\) for FloatLib's
binary64 nearest-even rounding on real numbers, and let \(w_i\) and \(y_i\)
denote the decoded stored weight and callback output. Then

$$
p_i=R(w_i y_i),\qquad a_0=0,\qquad a_{i+1}=R(a_i+p_i),
$$

and the executable loop's decoded result is \(a_n\).
`integrate_toReal_from_budget` proves this equality using FloatLib's existing
arithmetic and reduction-tree refinement theorems. It preserves the source
operation order and rounds each product and sum separately.

There is now an independent general proof of this recurrence in CompCert's
model. [`FiniteArithmetic.v`](../compcert/FiniteArithmetic.v) defines \(R\)
using Flocq's actual binary64 exponent function and nearest-even rounding.
For an arbitrary list of finite weights and callback outputs, it proves that

$$
\sum_{i=0}^{n-1}|w_i y_i|+2n\varepsilon(r)\le r,
\qquad r\le \mathrm{maxFinite},
$$

implies finiteness of every product and accumulator, the recurrence above, and

$$
\left|a_n-\sum_{i=0}^{n-1}w_i y_i\right|\le2n\varepsilon(r).
$$

Here \(\varepsilon(r)\) is half a Flocq ULP at the chosen radius. The proof
derives operation finiteness and rounding error from Flocq's `Bplus_correct`
and `Bmult_correct`; they are not extra hypotheses.
The theorem also permits a finite initial accumulator, adding its absolute
value to the range budget and its decoded value to the exact reference sum.

[`ClightRoundoff.v`](../compcert/ClightRoundoff.v) connects that numerical
result to the initialized C tables and existing total-correctness theorem.
For orders 1–4, every return is finite, obeys the recurrence and error bound,
has an empty trace, and preserves memory. The callback must satisfy the
existing execution contract and return finite values at the stored nodes.
The theorem uses the actual three-point C weights, including their discrepancy
with the functional specification in the Appel–Bindel paper. The
[review record](../evidence/upstream-review.json) identifies the PDF and source
examined. This first bound measures only rounding error from the exact stored
samples.

[`TableAccuracy.v`](../compcert/TableAccuracy.v) and
[`CallbackAccuracy.v`](../compcert/CallbackAccuracy.v) extend the comparison to
the ideal real quadrature rule. Rocq decodes each actual initializer as an exact
rational and proves uniform absolute node and weight tolerances
\(\delta_x=10^{-16}\) and \(\delta_w=5\cdot10^{-16}\). The weight tolerance
accounts for the three-point C literal: the same file refutes the draft's
\(2^{-53}\) tolerance directly in CompCert's model. The ideal rules have positive
weights of total mass two and the correct moments through degree \(2n-1\).

Suppose the callback approximates \(g\) at every finite input in \([-1,1]\)
with error at most \(\eta\) and returns a finite value. Assume also
\(|g(x)|\le B\) and that \(g\) is Lipschitz with constant \(L\) on this interval,
with \(\eta,B,L\ge0\). A proved mean-value lemma obtains the Lipschitz condition
from differentiability and \(|g'(x)|\le L\). Displacing a node then adds at most
\(L\delta_x\) to its sample error. The stored weights have absolute mass at most
\(2+n\delta_w\), so the numerical range budget becomes

$$
(2+n\delta_w)(B+\eta)+2n\varepsilon(r)\le r,
\qquad r\le\mathrm{maxFinite}.
$$

Under this budget, the callback and table bounds prove finiteness of the loop
arithmetic and

$$
|a_n-Q_n(g)|\le
2n\varepsilon(r)+(2+n\delta_w)(\eta+L\delta_x)+n\delta_w B.
$$

[`ClightAccuracy.v`](../compcert/ClightAccuracy.v) attaches this bound to total
correctness and every return of all four C rules, under the existing callback
execution contract. Here \(Q_n(g)\) is the explicit ideal rule. The analytic
difference between \(Q_n(g)\) and the integral is handled by
[`SharpAccuracy.v`](../compcert/SharpAccuracy.v). If ordinary derivatives
through order \(2n\) exist at every point of `[-1,1]` and
\(\lvert g^{(2n)}\rvert\le M\), Hermite interpolation and repeated Rolle give
a pointwise remainder bounded by \(M p_n(x)^2/(2n)!\). The interpolant agrees
with the quadrature samples and integrates exactly. Integrating its error gives
\(\lvert Q_n(g)-\int_{-1}^{1}g\rvert\le c_n M\), with
\(c_n=1/3,1/135,1/15750,1/3472875\) for orders 1–4.

[`ClightIntegralAccuracy.v`](../compcert/ClightIntegralAccuracy.v) therefore
proves the preceding numerical budget plus \(c_n M\) against the integral
for every return. It also proves integrability and derives the Lipschitz
condition from a first-derivative bound. The derivative assumptions refer to
points in the closed interval, with ordinary real derivatives at its endpoints;
they do not assert smoothness on an enclosing neighborhood.
[`CminorIntegralAccuracy.v`](../compcert/CminorIntegralAccuracy.v) gives the
same bound for the four compiled Cminor library calls. Their total correctness
follows from the checked lowering passes and CompCert's determinacy theorem;
the callback and numerical assumptions are unchanged.

These sharp constants are proved independently of Lean. The endpoint hypotheses
differ from the Lean `ContDiffOn` theorem.
[The analytic certificate notes](../compcert/analysis/README.md)
give the precise scope and the fresh dependency-build command.

Real decoding alone cannot determine a binary64 encoding: both `+0` and `-0`
decode to zero. Retaining the sign bit resolves this ambiguity for finite values.
[`FiniteRepresentation.lean`](../Quadrature/Binary64/FiniteRepresentation.lean) proves
that a finite FloatLib value is uniquely determined by its real value and sign.
[`FiniteRepresentation.v`](../compcert/FiniteRepresentation.v) proves the
corresponding result for CompCert using Flocq's `B2R_Bsign_inj`.

Both files then specify the complete observation of each finite arithmetic
result. For input real values \(u,v\) and sign bits \(s,t\), the rules are:

| Operation | Real component | Sign component |
| --- | --- | --- |
| Addition | \(R(u+v)\) | \(s\land t\) if \(u+v=0\); otherwise \(u+v<0\) |
| Multiplication | \(R(uv)\) | \(s\mathbin{\mathrm{xor}}t\) |

The sign depends on the exact operation before rounding. Thus a negative
product that underflows retains a negative zero, while exact cancellation in
addition gives positive zero unless both inputs are negative zeros. The Lean
sign theorems derive these rules from FloatLib's dyadic arithmetic and packing;
the Rocq proofs derive them from Flocq's operation specifications.

The range budget lets us carry these observations through every iteration,
starting from \((0,\mathrm{false})\). In each kernel, `integrate_eq_iff` proves
that a candidate finite value equals the executable result exactly when its
observation equals this signed recurrence. The specification therefore
determines the entire binary64 encoding, including a zero result's sign.
[`ClightRepresentation.v`](../compcert/ClightRepresentation.v) attaches the
specification to every return of each of the four C rules, using the actual
initialized weights and the existing callback contract.

The abstract real rounding operation can now be eliminated from both result
specifications. Consider a positive dyadic \(m2^e\), where \(m\) and \(e\) are
integers. Binary64 selects the output exponent

$$
k=\max\bigl(\lfloor\log_2 m\rfloor+e+1-53,\,-1074\bigr).
$$

Move the remaining scale \(2^{e-k}\) into an integer numerator \(N\) or a
positive denominator \(D\). Divide \(N=qD+r\), with \(0\le r<D\).
Nearest-even rounding selects \(q\) when \(2r<D\), \(q+1\) when \(2r>D\),
and the even member of \(\{q,q+1\}\) when \(2r=D\). The resulting dyadic is
that coefficient times \(2^k\). Negative values use the opposite coefficient;
zero is handled separately. The lower exponent limit accounts for subnormals
and underflow.

[`IntegerRounding.lean`](../Quadrature/Binary64/IntegerRounding.lean) proves that this
integer algorithm denotes FloatLib's real rounding result.
[`IntegerRounding.v`](../compcert/IntegerRounding.v) proves the corresponding
fact for Flocq's actual rounding function. Both developments also prove exact
dyadic addition by exponent alignment, exact multiplication, and equality by
comparing aligned integer coefficients. Their binary64 exponent functions
reduce to the displayed formula.

[`FiniteInteger.lean`](../Quadrature/Binary64/FiniteInteger.lean) and
[`FiniteInteger.v`](../compcert/FiniteInteger.v) replace the signed real
recurrences with these integer operations. In each kernel, `integrate_eq_iff`
proves that a candidate encoding is the complete loop result exactly when
its signed dyadic representation satisfies the integer recurrence.
The existing range budget supplies finiteness; no new execution hypothesis is
introduced. The sign is retained even when a coefficient rounds to zero.
[`ClightInteger.v`](../compcert/ClightInteger.v) proves this specification for
every return of all four actual C rules under their existing callback contracts.
The recurrence consumes the encoded callback outputs; it does not implement
an arbitrary callback.

This reduces the remaining general correspondence to a checked connection
between the two kernels' integer representations and algorithm definitions.
The paired proofs are independent: no verified translation or proof import
connects the Lean and Rocq developments yet. Giving their integer algorithms
the same mathematical description does not discharge that obligation.
The existing concrete Rocq accuracy theorem avoids this general connection by
proving its numerical result directly in Rocq.

If the correspondence is extended to division, finite operands alone are
insufficient: the certified `0 / 0` example above already has finite operands.
The operation's domain must exclude invalid division, or the comparison must
explicitly identify the different NaN encodings.

## Reproduction

With the Lean dependencies available and a built, unmodified CompCert tree:

```sh
python3 scripts/check-exceptional-values.py \
  --compcert-root /path/to/compcert \
  --work-dir /path/to/empty/local/exceptional-values \
  --output /tmp/exceptional-values.json

scripts/run-local.sh lake build
scripts/run-local.sh lake env lean scripts/Audit.lean
```

The first command checks both sets of six certificates and their axiom
dependencies. It records versions and source, checker, and log hashes in the
output; the retained run is
[`evidence/exceptional-values.json`](../evidence/exceptional-values.json).
The other commands check the complete Lean development, including the general
finite-execution, decoded-semantics, signed-representation, and integer-rounding
theorems.

To rebuild the general Rocq numerical proof and its C connection:

```sh
python3 scripts/check-clight-roundoff.py \
  --compcert-root /path/to/compcert \
  --clight-source /path/to/pinned/quadrules.v \
  --work-dir /path/to/empty/local/clight-roundoff \
  --output /tmp/clight-roundoff.json
```

This check verifies the pinned Clight hash (the generated `quadrules.v` checked in upstream at
revision `e79a28dba247db9f934289bcf4e4debd5eebc884`), rebuilds all fourteen project proof files,
and audits 90 numerical lemmas and theorems against the existing CompCert/Flocq
assumption allowlist. It permits no compiler-choice parameters. The retained
run is [`evidence/clight-roundoff.json`](../evidence/clight-roundoff.json).
