# What the review found

Appel and Bindel's *Formalization of Gaussian Quadrature and Application
Verification (Preliminary Draft)* presents an unfinished development.
Its admitted remainder is explicit, and its public source includes ongoing
work to correct the derivative-bound hypotheses. This review separates
false statements from missing proofs and from the module-assembly checks
that have yet to connect the C function proofs.

Among the source findings are a false integral-positivity lemma and a wrong
function name in the VST specifications. **`Rintegral_gt_0` omits the condition
`a < b`**, and **`hughes_weight_spec` declares `_gauss2d_weight`**. The first
has a counterexample checked in both Lean and Rocq. The second registers the Gauss weight
identifier twice and omits the Hughes weight identifier.

The four numerical findings and the counterexamples to two admitted overflow
helpers also survive independent checking. The original callback has a
specification but no body proof in the quadrature verification file. That is a
coverage gap, separate from a wrong numerical result.

The Lean build and assumption audit pass. The original VST body
proofs also compile after two explicit type annotations in a separate copy.
Their assumption reports retain the original admitted lemmas. The integrator
body does not depend on any of the twelve quadrature admissions; the example
wrapper depends on ten. Compilation therefore does not complete its numerical
argument.

The [paper](../paper/main.pdf), [claim map](../paper/claims.md), and
[interactive explanation](interactive/index.html#claims) explain the findings
and their consequences. The [24-paragraph comparison](stewart-comparison.md)
identifies the existing LeanPDE results and the mathematical proofs added here.

The public author PDF was downloaded again and compared with the previously
examined copy. The four numerical and indexing findings below remain in it.
The [review record](../evidence/upstream-review.json) identifies this PDF by hash
and records the source revision used for the code findings.

## What is resolved and what remains

The corrections here belong to LeanQuadrature. They do not complete the admitted
proofs or assemble the VSU in the authors' Rocq development. The comparison uses
the paper and source revision identified in the review record.

| Topic | Status in this repository |
| --- | --- |
| Preliminary title and attribution | ✓ Corrected throughout the paper and documentation. The discussion credits the authors' existing work on the derivative hypotheses and distinguishes false statements from unfinished proofs. |
| Numerical bounds and hypotheses | ✓ Counterexamples and corrected results are proved in our separate development. Integrating the corresponding corrections into the original Rocq proofs remains upstream work. |
| Function calls and initialized tables | ✓ The selected C library with our polynomial cosine has composed, initialized-call proofs in Lean. This is not a completed VST VSU for the original library. |
| Which mathematics came from LeanPDE | ✓ The [24-paragraph map](stewart-comparison.md) identifies reused results, new proofs, and omitted or bypassed textbook arguments. Our general quadrature theory concerns compact intervals. Infinite-interval families remain outside it. |
| Faithfulness of the C model | ◐ The particular C calls are proved correct in our adapted semantics. A general frontend theorem and a semantic correspondence with Rocq remain open; a successful Lean build does not establish them. |
| Modular C and VST-style reasoning | ◐ CLean supplies reusable contracts and separation-logic rules, but our direct execution proofs do not establish a framework for large modular or concurrent C programs. An Iris instantiation for this semantics and suitable automation remain further work. |
| Compilation | ◐ Particular assembly programs have Lean proofs, and separate Rocq certificates use CompCert. Transferring CompCert's general compiler theorem to Lean remains open. Merely compiling with CompCert does not supply that transfer. |

## The findings in the paper and source

| Finding | Evidence | What our development establishes |
| --- | --- | --- |
| Two-point ideal bound `0.00223` | The ideal error is about `0.0035591571`. | Lean refutes the stated bound and proves `0.00356`. |
| One-point ideal bound `0.02` | The error is `1 − sin 1`, about `0.1585290152`. | Lean refutes the stated bound and proves `0.159`. |
| Remainder indexing | An `n`-node rule is paired with derivative order `2n+2`. For two nodes, `x⁴` has error `8/45` and zero sixth derivative. | Lean proves the counterexample and the corrected `2n` remainder with explicit smoothness assumptions. **Two nodes require the fourth derivative.** |
| Three-point outer weight | The C and model encodings differ. The C weight's error exceeds `2⁻⁵³`. | Lean certifies the actual C constants with a valid weight tolerance of `5·10⁻¹⁶`. |
| Overflow helpers in the source | `parameter_limits` holds at witnesses where two admitted helper conclusions fail. | Three new Lean theorems check the counterexamples and distinguish the two failures. Our finiteness proof uses a different sufficient budget. |
| Hughes function identifier | `hughes_weight_spec` declares `_gauss2d_weight`; the interface repeats that identifier and omits `_hughes_weight`. | The source error concerns function registration. Correcting the identifier still requires checking the assembled interface. |
| Original callback body | Ten internal Clight functions, nine body lemmas; no `body_testfun`. | The original wrapper assumes the callback contract, and its callback body still needs a proof. Our separate polynomial-cosine variant supplies its own callback body proof. |
| Integral positivity | `Rintegral_gt_0` allows `a = b`. The constant function one on `[0, 0]` meets its premises and has integral zero. | Lean and MathComp-Analysis prove the counterexample. Our polynomial-positivity theorem already requires `a < b`. |

The overflow, positivity, function-identifier, and callback findings concern the accompanying
source. They should not be described as additional false numerical
bounds in the PDF. The [claim map](../paper/claims.md) gives the exact declarations
and locations.

The middle three-point weight is **not another mismatch**. Its decimal spellings
in C and Rocq differ, but they round to the same bits. The independent checker
compared every node and weight: only the two outer entries of the three-point
weight table disagree between C and the model.

## Corrections already under development

The public
[`g_max_deriv.v`](https://github.com/VeriNum/simple_cfem/blob/e79a28dba247db9f934289bcf4e4debd5eebc884/proof/g_max_deriv.v)
is present at the examined revision. It changes the function and derivative
bounds to use an interval with `a < b`. Its mean-value estimate requires
both evaluation points to be in that interval. These conditions address
the intended use of `g_max_deriv` and the definitions underlying the
example-specific bounds.

The file is work in progress. Its final `g_max_deriv` depends on an admitted
one-way estimate and other unfinished lemmas, and it has not been integrated
into the quadrature proofs. The appropriate comparison is with that stated
work, rather than an implication that all the missing hypotheses were
previously unnoticed. Our numerical accuracy theorem has an explicit
Lipschitz premise; the concrete applications supply their own certificates.

The C proofs have a separate missing composition step. In VST, a
**Verified Software Unit (VSU)** checks compatible specifications for
functions and their callers. Its whole-program construction also connects
initialized global data to the precondition of `main`. That is where the
stored-weight mismatch and the Hughes identifier must be resolved.
The examined quadrature source has individual body proofs but no assembled
quadrature VSU. This is unfinished use of the framework, not a missing
capability in VST. The
[VST implementation](https://github.com/PrincetonUniversity/VST/blob/v2.16/floyd/VSU.v)
provides these composition and initialization rules.

## A separate correction to the prose

Paragraph 18 on page 4, in the discussion quoted from Stewart, says that no
quadrature weight can exceed one. The sum of the positive weights is the total
mass of the weight function, so the general bound is
\(A_i \le \int_a^b w(x)\,dx\). For the one-point Legendre rule on `[-1, 1]`,
the sole weight is two.

The original Rocq statement `gauss_weight_leq_1` already uses the correct
integral bound. This discrepancy is in the prose, not that theorem's statement.
Our [weight bound](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Weighted.lean) proves the same
total-mass bound. It is separate from the four numerical and indexing findings
discussed in our paper.

## Rebuilding the original Rocq proofs

The [rebuild record](../evidence/upstream-vst-verified.json) covers the nine
original quadrature files and their LAProof dependencies. Rocq 9.0.1,
CompCert 3.17, VST 2.16, and the numerical libraries were built from source.
The [reproduction instructions](../scripts/upstream/README.md) give the
dependency versions and commands.

The [unmodified build](../evidence/upstream-vst-checked.json) fails in two
high-level 2D specifications. In this environment, the expression
`'I_n * 'I_n` is interpreted in logic scope rather than as a product type.
Making the intended type explicit, `('I_n * 'I_n)%type`, lets those
specifications and all nine original body proofs compile. The separate build
copy contains exactly those two annotations; the record retains the diff and
hashes. No original proof, admitted lemma, or C implementation was repaired
by this adjustment. The original checkout remains unchanged.

The review obtains 43 transitive assumption reports, including all nine body
theorems and all twelve admitted declarations in the quadrature files.
The [wrapper report](../evidence/upstream-vst-verified-logs/assumptions-08.txt)
contains ten of those admissions: the general remainder, integral positivity,
the three floating-point helpers, the derivative-bound helper, and four
example-specific helpers. The [integrator body report](../evidence/upstream-vst-verified-logs/assumptions-07.txt)
contains none of the twelve. Library logic, primitive-operation assumptions,
and external math-function assumptions are also reported; they should not
all be counted as unfinished quadrature lemmas.

The final [kernel recheck](../evidence/upstream-vst-verified-logs/kernel-recheck.txt)
also passes. It uses `coqchk -norec` on the original body-proof module and
both review modules. Their dependencies were compiled during the source
builds; this was not a recursive `coqchk` run over every library. Like
compilation, this recheck accepts the retained admissions.

The committed Clight program says it was generated for AArch64 with the Apple
ABI. This review checks that syntax under the installed x86-64 CompCert
configuration. It does not reproduce the authors' Apple toolchain or
regenerate their C-to-Clight translation.

## Why the overflow helpers fail

For binary64, the pinned LAProof definitions give

$$
u=2^{-53},\qquad \eta=2^{-1075},\qquad T=2^{1024}.
$$

Here LAProof's `fmax` is the threshold \(T\), not the largest finite value.
Take a one-node rule and choose the zero function and a callback returning zero.
The function bound \(F=T/4\) is loose but valid. Set the derivative bound and
callback-error bound to zero. The exact node zero and weight two satisfy the
table conditions.

The source's `parameter_limits` holds:

$$
\left(1+\frac{u}{1+u}\right)(2+u)\frac{T}{4}+\eta<T.
$$

Its product helper also holds at this witness. But the admitted
`finite_integrate_model_aux` asks for

$$
\underbrace{\frac{T}{2}+\frac{T}{4}(u^2+3u)+\eta}_{>T/2}
<
\underbrace{\frac{T}{2(1+u)}}_{<T/2}.
$$

That inequality is false. This example uses a positive order, so restricting
the application to nonempty rules does not resolve it.

The other helper, `gauss_pt_wt_limit_aux`, fails at zero nodes. The source's type
`'I_5` allows zero. With \(F=T\), zero callback error, and the same zero function,
the range condition is \(0<T\), while the helper asks for
\(2T(1+u)+\eta<T\). The empty reduction needs separate handling, or the helper
needs a positive-order premise.

The zero callbacks do not overflow. These are false sufficient inequalities
inside the proof, not examples of a crashing or overflowing program. LAProof's
summation result has its own valid precondition; the quadrature development
has not derived it from its proposed condition.

[Examples/Overflow.lean](../Quadrature/Examples/Overflow.lean) proves:

- `one_node_finiteness_helper_false`: the one-node range condition holds and
  the summation helper's conclusion fails.
- `one_node_product_helper_holds`: the preceding product helper holds at that
  same witness.
- `zero_node_product_helper_false`: the zero-node condition holds and the
  product helper's conclusion fails.

These proofs check manually transcribed real inequalities. The correspondence
with Rocq and the dependency definitions was inspected; it is not a verified
Rocq-to-Lean translation. The source hashes make that correspondence reviewable.

Our [finite-range proof](../Quadrature/Binary64/BoundedRoundoff.lean) and
[functional accuracy proof](../Quadrature/Binary64/FunctionalAccuracy.lean) use an
explicit budget for absolute products and accumulated rounding errors.
They establish finite intermediate results from that budget. They neither
prove the false helpers nor repair the authors' source files.

## The missing interval hypothesis

The original `Rintegral_gt_0` assumes that a function is continuous,
nonnegative, and not identically zero on `[a, b]`. It concludes that its
integral is positive. It does not assume `a < b`.

Set `a = b = 0` and let the function be constantly one. All three premises
hold, but a singleton has Lebesgue measure zero, so the integral is zero.
[Examples/IntegralPositivity.lean](../Quadrature/Examples/IntegralPositivity.lean)
proves the premises and the failure of the conclusion together.

[MathematicalAudit.v](../scripts/upstream/MathematicalAudit.v) checks the same
example in Rocq using MathComp-Analysis. This counterexample does not depend on
the original admitted lemma. A separate diagnostic applies that lemma to the
example and derives `False`, with the admission retained in its assumption
report. That direct application also checks that the example matches the
original statement. The diagnostic is not imported by our program certificates.

The source uses this admitted lemma in `sqr_poly_positive`, inside a section
that already assumes `a < b`. Adding that premise to the helper is a natural
repair for this use. The counterexample does not refute polynomial positivity
on the nondegenerate interval. Our
[`polynomialIntegral_square_pos`](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Integral.lean) already carries
the interval hypothesis and proves the result using mathlib.

## Why the wrong function name can escape a body proof

In VST, a function specification pairs an identifier with a contract.
`semax_body` checks the supplied function body against the contract; its
definition discards the identifier. Connecting identifiers, bodies, and
contracts belongs to the separate function-list or whole-program proof.
The planned VSU is the relevant composition mechanism for this library.

The original `body_hughes_weight` can therefore prove the intended body contract
despite the wrong identifier in `hughes_weight_spec`. This is not a failure of
VST's logic. The declaration names the wrong function, and the missing interface
assembly is precisely where that mismatch matters.

The original file also contains no body proof for `testfun`. Its wrapper uses
`make_func_ptr _testfun` to obtain the contract from the global specification
environment. That step does not prove the callback body. The four admitted
example lemmas—function bound, derivative bound, callback accuracy, and
quadrature error—are additional numerical obligations.

## What was checked in our work

The upstream checker retains its sources, the exact compatibility diff,
build logs, and all assumption reports. It compares each review theorem's
assumptions with the definitions or library results it uses. For example, the
positivity diagnostic requires the singleton-integral theorem's logical
assumptions and the original admission; the checker rejects missing or
additional assumptions.

The [Lean validation](../evidence/lean-quality.json) runs the full
default Lake build, then checks transitive assumptions of all project and
adapted CLean theorems, including private helpers and generated declarations.
The record lists the current module and theorem counts. The audit permits only
`propext`, `Classical.choice`, and `Quot.sound`. It also separately checks the
original wrapper theorem's assumptions, rejects omitted source modules by
comparing the source inventory with imported modules, and verifies that every
dependency checkout is clean and matches its pinned revision. This was an
incremental full-target build, not a clean rebuild of every Lean dependency.

The [Rocq validation](../evidence/independent-review-rocq.json) rebuilt
the configured compiler proof from pinned sources. It checked 27
project proof files, four application certificate files, and 107 explicit
assumption queries. The polynomial certificates have no successful-compilation
or external-cosine premise. The record lists their logical and external
semantics dependencies. The [source comparison](../evidence/independent-review-rocq-coverage.json)
matches all 72 current Rocq files to their verification records. The other
files are covered by separate checks, identified in that comparison.
A matching source hash is not a new proof check.

The [independent numerical checker](../scripts/check-numerical-claims.py) uses
integer and rational arithmetic, without importing FloatLib or Flocq. It
checks all 110 stored C constants, all eight polynomial coefficients, the
ten complete rounded computations, and every advertised error bound.
Alternating series bound sine and cosine; rational root brackets and interval
arithmetic check the Legendre nodes and weights. It also checks the
overflow witnesses. [All checks passed](../evidence/upstream-numerical-checked.json).
The evaluator forgets zero signs, so it makes no general signed-zero claim.
The full signed results remain matters for the formal proofs.

The original C example is included in the [native regression check](../evidence/upstream-c-checked.json).
It returned `0.83791182769499317`; the observed error against the platform sine
was about `0.0035591571`, exceeding `0.00224`. This is an experiment. It does not
verify the platform's cosine implementation.

The [C regression check](../evidence/upstream-c-checked.json) builds the
unchanged source with Clang's address and undefined-behavior sanitizers. It
compares all 110 compiled table words and exercises 336 monomials: 110 line
cases at orders 1–10, 220 square cases at orders 1–5 in each dimension, and six
triangle cases through degree two. All pass the recorded floating-point
tolerance, with no sanitizer report. This is finite regression coverage, not
a theorem about every input or a replacement for an error proof.
The numerical and C checkers hash the inputs they actually use and refuse to
record success if those project files change during checking. The C harness
is compiled from the retained input snapshot.

Manual code inspection followed the mathematical construction and remainder,
the finite-range and callback hypotheses, the complete-value certificates,
the original wrapper's contracts, and the particular assembly programs.
Kernel success alone cannot tell us whether an intended theorem has been
stated correctly; the upstream helper counterexamples illustrate why
that distinction matters.

The [PDF checks](../evidence/paper-checks.json) compare both code listings
with their sources and all ten result rows with the numerical check.
The [website checks](../evidence/website-checks.json) cover strict equation
rendering, local links, interactive controls, and desktop and mobile layouts.
The records identify the files and counts actually checked.

## Scope of the proofs

Our general mathematics concerns compact intervals and positive continuous
weights. General floating-point theorems retain callback accuracy and range
hypotheses; concrete examples discharge those obligations.

For the **original external-cosine C program**, the source-call theorems use
adapted strategy semantics and explicit table, function-context, and cosine
contracts. These conditional theorems do not verify the platform cosine.

For the **selected C library with the verified polynomial cosine**,
`CSource/Library/Total.lean` proves total correctness of initialized calls for
orders 1–10 in the adapted C small-step semantics. Every permitted evaluation
order terminates with the certified binary64 result. The proof covers allocation,
parameter binding, nested calls, assignments, the loop, return, and freeing.
It supplies the table and callback proofs rather than assuming their contracts.
The generic progress and accessibility theorems rule out reachable stuck states
and infinite executions. `CSource/Library/Preservation.lean` also proves that
the actual C and Clight frontend outputs have the same returned values and
traces for all six selected functions, with termination and agreement on
pre-call memory. General parser/elaborator correctness, including static-array
hoisting from an independent source semantics and preprocessing, and the
correspondence with Rocq's semantics remain unproved.

For the **ten polynomial applications**, initialized Clight and formal assembly
have direct proofs, and independent Rocq certificates compose with a configured
CompCert. These applications have an internal polynomial and authored entry
points.
[CSourcePrograms.lean](../Quadrature/Compiler/Correspondence/CSourcePrograms.lean)
proves that their result annotations carry exactly the value returned by the
initialized C library, for all ten orders and the original two-node wrapper.
The theorem compares these particular programs' results; it does not prove that
compiling the original C text produces the imported assembly syntax.
The general Lean–Rocq interpretation, assembly printing and encoding, linking,
and operating-system output also remain outside the completed chain.
Compiling the original C with CompCert alone does not discharge these obligations.

The original quadrature target was rebuilt and its selected assumptions checked.
The broader finite-element project and original native executable were not
fully verified. This review establishes specific counterexamples and records
checks on both developments; it does not certify that either repository
contains no other errors.

## Repeating the checks

From the repository root:

```sh
python3 scripts/check-lean.py --output /tmp/quadrature-recheck/lean.json
python3 scripts/check-numerical-claims.py --output /tmp/quadrature-recheck/numerical.json
python3 scripts/check-upstream-c.py --output /tmp/quadrature-recheck/c-domain.json
python3 -m unittest discover -s scripts/tests -v
python3 scripts/build-paper.py
```

The numerical checker downloads four source files and rejects unexpected
hashes. `--source-dir` can use previously downloaded copies with the same
hashes. The Python tests cover audit completeness, rounding boundaries,
source integrity, missing and duplicate regression cases, and assumption-report
parsing and dependency checks. The [original VST instructions](../scripts/upstream/README.md) describe
its separate toolchain. The [CompCert certificate instructions](../compcert/certification/README.md)
describe the independent compiler certificates in this repository.
