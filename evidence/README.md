# Verification records

Each record describes a check, its inputs, and its scope. Keep one record per
workflow; replace it when rerunning that workflow. The Lean build, Rocq checks,
compiler imports, and C experiments answer different questions.

| Record | What it checks |
| --- | --- |
| [lean-quality.json](lean-quality.json) | Full Lean build and assumption audits, including the C polynomial source, total correctness of the initialized library in every operand order, private helpers, and adapted CLean theorems |
| [paper-checks.json](paper-checks.json) | PDF build, equations and code listings, numerical result rows, and Lean declaration checks for the 24-paragraph library comparison |
| [website-checks.json](website-checks.json) | Equation rendering, browser controls, local links, and desktop, tablet, and phone layouts |
| [upstream-review.json](upstream-review.json) | Index of the original-source findings and the checks supporting them |
| [upstream-vst-verified.json](upstream-vst-verified.json) | Original quadrature proofs rebuilt with two product-type annotations, 43 assumption reports, and kernel rechecks of the body-proof and review modules |
| [upstream-vst-checked.json](upstream-vst-checked.json) | Unmodified-source build failure that identifies the two ambiguous product types |
| [upstream-numerical-checked.json](upstream-numerical-checked.json) | Exact rational checks of the stored constants, ten polynomial results and bounds, and numerical counterexamples |
| [upstream-c-checked.json](upstream-c-checked.json) | Original C with address and undefined-behavior sanitizers: 110 table words, 336 polynomial cases, and the cosine example's advertised error bound |
| [independent-review-rocq.json](independent-review-rocq.json) | Configured CompCert proof rebuild, 31 project/certificate files, and 107 assumption queries |
| [independent-review-rocq-coverage.json](independent-review-rocq-coverage.json) | Comparison of all 72 Rocq source hashes with their verification records |
| [assembly-certificate.json](assembly-certificate.json) | Rocq compilation certificates and the compiler configuration they use |
| [exceptional-values.json](exceptional-values.json) | Six exceptional-value disagreements checked separately in Lean and Rocq |

The `*-import.json` files record separate compiler-stage imports and their Rocq
syntax certificates. `mach-return-addresses.json` checks the imported return
addresses. The `clight-*.json` files record the execution and numerical checks
used by the compilation certificates. Source revisions are recorded with the
checks that use them and in `upstream-review.json`.

The commands and prerequisites are documented in [CONTRIBUTING.md](../CONTRIBUTING.md)
and the [certificate README](../compcert/certification/README.md). Build-directory
paths in a record identify where that check ran. A matching source hash confirms
which code was checked; it does not constitute another proof build.
