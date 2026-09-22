# Concrete compilation certificate

`CertifiedPolynomial.v` proves that the internal-cosine application compiles to
an assembly program, that this program terminates, and that every behavior has
the certified result. Its accuracy theorem gives absolute error at most
`0.00356` from the real integral and refutes the `0.00224` bound of the draft, the
Appel–Bindel manuscript of September 15, 2026 (Formalization of Gaussian Quadrature
and Application Verification). There
is no external cosine-call hypothesis or successful-compilation hypothesis.
The endpoint is CompCert's x86-64 assembly semantics.

`CertifiedStoredPolynomial.v` supplies the complete application certificate for
orders one through ten. Each authored Clight entry calls the original
`integrate` directly, with the internal degree-14 polynomial replacing external
cosine. The theorem proves compilation success, termination, unique behavior,
and the following absolute bounds from the real integral:

| Order | Observed binary64 bits | Error at most |
| --- | --- | --- |
| 1 | `3ff0000000000000` | `0.159` |
| 2 | `3fead02c771c35ed` | `0.00356` |
| 3 | `3feaed9520c8a014` | `0.000031` |
| 4 | `3feaed5443a06327` | `0.00000015` |
| 5 | `3feaed548f3f6f46` | `4e-10` |
| 6 | `3feaed548f08f234` | `8e-13` |
| 7 | `3feaed548f090ce1` | `2e-15` |
| 8 | `3feaed548f090cce` | `4e-15` |
| 9 | `3feaed548f090ccf` | `4e-15` |
| 10 | `3feaed548f090cd4` | `3e-15` |

The source proofs are in `StoredPolynomialRules.v`, `StoredPolynomialAccuracy.v`,
and `StoredPolynomialCompilation.v`. Exact computation of the rounded results and
a rational sine enclosure prove the error bounds independently of Lean.
There is no external cosine or compilation-success hypothesis.
`CertifiedPolynomialRules.v` retains and rechecks the earlier four-order API.
`RuleLibrary.v` proves the callback-parametric loop for all ten stored slices
under explicit context conditions, with the four-order interface as an instance.

`CertifiedExternal.v` supplies the same compilation certificate for the
application retaining external cosine. Its termination and accuracy theorems
keep the two explicit cosine-call contracts. All applications compile with the
same compiler configuration and allocation-candidate pool.

This certificate uses the explicit configuration in `configuration.patch`,
based on CompCert 3.17 revision
`7b1f02b09954b9b916eb2a91d283c9b5355bf172`. It is a separately checked compiler
variant. The release-compiler proofs and executable experiments elsewhere in
this repository remain separate targets.

## Reproduce

Use a built x86_64 CompCert tree at the pinned revision (the checked-in configuration
is based on revision `7b1f02b09954b9b916eb2a91d283c9b5355bf172`, named above), the
pinned generated `quadrules.v` (checked in upstream at revision
`e79a28dba247db9f934289bcf4e4debd5eebc884`), Docker, and Python 3.12 or later:

```sh
python3 scripts/check-configured-compcert.py \
  --compcert-root /path/to/compcert \
  --clight-source /path/to/quadrules.v \
  --work-dir /path/to/empty/local/certificate-build \
  --output /tmp/quadrature-assembly-certificate.json
```

The script creates an independent source archive from the pinned Git commit.
It checks the generated parser's hash, copies that source and the supplied
`Makefile.config`, regenerates the architecture-specific `.v` files, applies
the configuration patch, and rebuilds every CompCert proof object. It then
checks twenty-seven project files and four concrete certificate files.
An explicit audit checks all new lemmas and the six exported lemmas in each
certificate, 107 declarations in total.
Neither the original compiler checkout nor another project's build is changed.

The generated parser is copied because the pinned Rocq image lacks Menhir.
Its proof objects are rebuilt with the rest of CompCert. The application starts
from normalized Clight syntax; this certificate makes no claim about parsing a
C wrapper. The script uses the pinned container without network access and
does not import prebuilt proof objects from the input checkout.

`configuration-files.json` records the original and configured hashes of every
changed source file, the generated parser hash, and the build-configuration
hash. The resulting evidence records these hashes, project proof hashes,
checker versions, log hashes, and the assumption audit.

## Explicit computational choices

CompCert obtains some compiler decisions from external OCaml functions. Its
pass proofs establish correctness when the checked compilation succeeds.
To evaluate this particular compilation inside Rocq, the configuration gives
these functions explicit definitions:

| Choice | Definition used here |
| --- | --- |
| ABI | `Archi.win64 = false` |
| Optimization options | All listed `Compopts` flags are false |
| Inlining | No function is selected for inlining |
| Symbol relocation heuristic | Always false |
| Switch construction | A linear chain of equality tests |
| Branch and conditional-selection heuristics | Always false |
| Block enumeration | All code nodes, in `PTree.elements` order |
| Compiler printing hooks | Return `tt` |
| Register allocation | Try twenty-two stored LTL candidates, accepting only a candidate that passes CompCert's validator |

The first sixteen candidates came from CompCert's native allocator, including
four caller candidates for orders 1–4. Six more reuse the fourth caller's
allocation with its order constant changed to 5–10. Candidate construction is
outside the proof. Each accepted candidate is
validated during kernel-checked evaluation, so the allocator and candidate
printer are not trusted for correctness. The finite pool can reject other
programs; it is not a replacement general-purpose allocator.

The configuration also makes previously hidden computations available:

* `PrimIter.iterate` uses a structurally recursive budget of 10,000 steps.
  Its invariant theorem is proved again by induction. This changes the
  release compiler's much larger iteration budget; successful compilation
  still has the proved semantics.
* Graph postorder and union-find representatives have bounded computational
  paths with the original definitions as fallbacks. New proofs establish
  equality to the original results for every input.
* The backward dataflow solver and union-find module expose their definitions.
  The type-constraint solver and branch-tunneling termination proofs are
  transparent so their recursive functions can reduce.
* A few upstream proof scripts need shorter branches or an explicit type
  argument after these definitions become concrete. Their theorem statements
  are retained, and the full compiler proof is rebuilt.

No project proof is admitted, and no new axiom supplies compilation success.
`backend_succeeds` is proved with `vm_compute` and `reflexivity`.
`compiled` identifies the assembly witness. The three application theorems
then apply the checked compiler simulations and numerical certificate.

## What the endpoint means

Each program emits the CompCert annotation `quadrature-result` with the
corresponding binary64 value and exits with status zero.
The annotation is a semantic observation; the assembly printer represents it
as a comment. This is not a verified operating-system output operation.

The assumptions audit permits the existing classical, proof-irrelevance, and
external-semantics dependencies of CompCert and Flocq. It permits no remaining
abstract compiler-choice parameters. These logical dependencies are recorded
explicitly; “no compilation premise” does not mean “no logical assumptions.”

The certificate does not verify the assembler, linker, platform cosine, a
general Lean-to-C translation, or the original AArch64/Apple binary.
The concrete numerical certificates cover the complete computations at all
ten stored orders, without asserting whole-domain polynomial accuracy.
The Lean and Rocq numerical proofs are independent; general agreement between
FloatLib and CompCert's floating-point operations remains a separate obligation.
