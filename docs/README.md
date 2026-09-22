# Documentation

Start with the [repository overview](../README.md). The
[paper](../paper/main.pdf) asks whether the Rocq development can be redone in
Lean, gives the five verification levels,
the findings in the examined manuscript, and the corrections checked in Lean;
the [interactive guide](interactive/index.html) explains the layers with
rendered mathematics.

## Current scope

- [Stewart's 24 paragraphs](stewart-comparison.md): existing LeanPDE results,
  new general proofs, and the exact interpolation and remainder hypotheses
- [Initialized C polynomial library](../Quadrature/CSource/Library/Total.lean):
  verified C cosine, initialized tables, termination in every evaluation order,
  and error bounds for all ten stored orders
- [Independent review](review.md): confirmed findings, checks on our work, and remaining limits
- [CompCert and Lean: what compiling establishes](compcert-and-lean.md)
- [Coverage ledger](coverage.md): claims and their supporting files
- [Floating-point models](float-models.md): finite arithmetic, signs, and NaNs
- [CLean adaptation](../vendor/clean/README.md): reused semantics and local changes
- [Compilation details](compilation.md): Rocq certificates and their assumptions
- [Paper claim map](../paper/claims.md): statements used in the manuscript
- [From the integral to the machine](from-integral-to-machine.md): a detailed explanation

## Reproduction

The full Lean build requires access to the private LeanPDE dependency;
contact Robert to arrange it.

- [Lean build and audit instructions](../README.md#build-and-inspect)
- [Code conventions and full validation command](../CONTRIBUTING.md)
- [Configured CompCert certificate](../compcert/certification/README.md)
- [Rocq analysis proofs](../compcert/analysis/README.md)
- [Evidence index](../evidence/README.md)
- [Paper build and source archive](../paper/README.md)
