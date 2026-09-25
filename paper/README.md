# Gaussian Quadrature in Lean and Rocq

**[Read the PDF](main.pdf)** · [LaTeX source](main.tex) ·
[Claim-to-source map](claims.md) · [Bibliography](references.bib)

*Gaussian Quadrature in Lean and Rocq* is by **Robert Joseph,
California Institute of Technology**.
Appel and Bindel's *Formalization of Gaussian Quadrature and Application
Verification (Preliminary Draft)* connects quadrature mathematics,
floating-point analysis, and C function proofs using MathComp, Flocq,
LAProof, Interval, VST, and CompCert. It presents work in progress, with
admitted statements and unfinished program assembly. Our paper takes their example and asks
how far its verification can be carried out in Lean:

- **Mathematics.** Gaussian rules
  of every positive order on a compact interval, the integrated remainder with the
  corrected derivative order, and convergence.
- **Floating point.** FloatLib's binary64 arithmetic and certified
  errors for all ten stored tables.
- **C: total correctness of the initialized library.** The original functions
  use a verified C polynomial replacing `cos`. Lean checks the selected parsed
  functions and initialized tables, then proves the call results and error bounds
  for all ten stored orders. Every permitted evaluation order terminates with the
  specified result in our Lean adaptation of CompCert's C small-step semantics.
  Calls to all six selected functions preserve their behavior when translated to
  Clight. General correctness of the source translation and agreement with Rocq's
  execution semantics remain open.
- **Compilation: application proofs.** The ten applications are proved at
  selected compiler stages through formal assembly in Lean, and separately
  composed with CompCert in Rocq. They start from authored Clight programs.
  Lean proves that their result annotations carry exactly the values returned
  by the initialized C library, including the original two-point wrapper.
  This compares the behavior of the particular programs. Proving that
  compilation of the original C text produces these assembly trees, proving a
  general compiler correct in Lean, and transferring CompCert's theorem into
  Lean remain open.

The paper also reviews the original work. It explains four
discrepancies in the manuscript (two false example bounds, the remainder
indexing, a stored weight that differs between C and the model) and the false
admitted helpers, wrong function identifier, and missing callback body proof
in the accompanying source, with calculations and supporting proofs. It
also describes the public corrections under development in `g_max_deriv.v`
and the role of the missing quadrature VSU. These gaps are distinguished
from false numerical bounds.

Section 1.1 explains the four connections between the five levels. Section 2
is the review. Sections 3 to 6 cover the mathematics, floating point, C, and
compilation in turn. Section 5 explains why the C proof covers every evaluation
order, including calls that allocate temporary memory in different orders.
Section 8 explains the library contributions and remaining proof obligations.
Appendix A maps all 24 numbered paragraphs of their mathematical discussion
to the definitions and theorems available in the current LeanPDE library. The
[companion source map](../docs/stewart-comparison.md) gives declaration names
and precise hypotheses. LeanPDE supplies both the sharp two-point Peano-kernel
bound and the general Hermite and integrated Gaussian remainder. Its
`PDE.Symbolic.Continuum` namespace contains the Gaussian and Legendre theory
that LeanQuadrature imports for the stored-table and program proofs.
The discussion credits CLean's existing separation logic, contracts,
function-pointer rules, and module-linking operations. Our quadrature proofs
use its execution rules directly. It also discusses *Iris in Lean*, whose
integration with the C/Clight semantics used here remains separate work.
The PDF includes the
Lean proof of the corrected two-point bound and the original C integrator as
exact excerpts from the retained sources.

The PDF uses colors, symbols, and words together:

- **Green ✓ Proved:** the stated result under its hypotheses.
- **Amber ◐ Partial / Conditional:** an application still has obligations to discharge.
- **Blue-gray ○ Open:** the specified connection remains unproved.
- **Red × Refuted:** a counterexample disproves the stated claim.

## Build

From the repository root:

```sh
python3 scripts/build-paper.py
```

Requirements: Python 3, `pdflatex`, `bibtex`, and standard TeX packages including
AMS mathematics, Latin Modern, TikZ, booktabs, longtable, listings, placeins, microtype,
and hyperref.
The script runs TeX without shell escape in a fresh local `/tmp` directory.
It copies only `paper/main.pdf` back into the repository and reports its logs.
It rejects unresolved references, missing characters, and overfull boxes. The generated PDF is
checked into Git alongside its LaTeX source and included in the source distribution.

## Include the source code

After building the PDF:

```sh
python3 scripts/package-artifact.py --output dist/LeanQuadrature-paper.tar.gz
```

This creates an archive and checksum containing the paper and current source
files, including uncommitted work. A manifest records the file hashes.
Dependency caches and compiled Lean files are excluded. Packaging does not
publish the changes. Rebuilding the Lean proofs requires access to the
private LeanPDE dependency; contact Robert to arrange it. Reading or
rebuilding the PDF does not require that dependency.

## Sources and checks

The [review record](../evidence/upstream-review.json) identifies the Appel–Bindel paper and
source revision examined. The [claim map](claims.md) links the mathematical
and program claims to their supporting declarations.

The [independent review](../docs/review.md) records the findings, checks, and
remaining limits. The [Lean validation](../evidence/lean-quality.json)
covers the full build and assumption audit. The
[Rocq validation](../evidence/independent-review-rocq.json) rebuilds the
configured compiler proof and the polynomial application certificates.
The [paper checks](../evidence/paper-checks.json) identify the PDF, its sources,
the build logs, and the checks on its code listings and result rows.
