# Checking the original VST development

`check-upstream-vst.py` builds the original quadrature proof and its source
dependencies in a separate Rocq environment. It uses the authors' committed
Clight program. The original checkout stays unchanged. The optional adjustment
described below adds two type annotations in a separate source copy; it changes
no proof script, admitted lemma, or C code. These are the original VST proofs,
separate from LeanQuadrature's CompCert certificates.

The checker requires these package versions:

```sh
opam repository add coq-released https://rocq-prover.org/opam/released
opam install \
  coq.9.0.1 coq-compcert.3.17 coq-flocq.4.2.2 \
  coq-vst.2.16 coq-vst-lib.2.15.1 coq-vcfloat.2.4.1 \
  coq-interval.4.11.4 coq-coquelicot.3.4.5 \
  coq-mathcomp-ssreflect.2.5.0 coq-mathcomp-algebra.2.5.0 \
  coq-mathcomp-analysis.1.15.0 coq-mathcomp-reals-stdlib.1.15.0 \
  coq-mathcomp-algebra-tactics.1.2.7 coq-mathcomp-finmap.2.2.2
```

`check-upstream-vst.py` verifies the installed versions of `coq`, `coq-compcert`,
`coq-flocq`, `coq-interval`, `coq-mathcomp-ssreflect`, `coq-mathcomp-algebra`,
`coq-mathcomp-analysis`, `coq-mathcomp-reals-stdlib`, `coq-vst`, `coq-vst-lib`, and
`coq-vcfloat`, plus `rocq-mathcomp-boot` 2.5.0, which `coq-mathcomp-ssreflect` 2.5.0
pulls in, while `coq-coquelicot`, `coq-mathcomp-algebra-tactics`, and
`coq-mathcomp-finmap` are transitive dependencies of the build that the checker does
not version-check.

Use a separate switch with OCaml 4.13.1. The evidence includes an opam switch
export with the full dependency selection. Interval 4.11.4 is intentional:
VCFloat 2.4.1 fails to build against Interval 4.11.5 because `le_contains`
changed its interface. That build incompatibility is separate from the
quadrature findings.

MathComp 2.5 supplies the `all_boot` module imported by the original proof.
MathComp 2.4 is insufficient; MathComp 2.6 falls outside Analysis 1.15's
supported dependency range.

The committed Clight file was generated for AArch64 with the Apple ABI.
This review uses CompCert's x86-64 configuration. The checker records both
targets and checks the committed syntax under the installed configuration;
it does not reproduce the authors' Apple compiler environment.

Make a separate checkout of the pinned original sources:

```sh
git clone https://github.com/VeriNum/simple_cfem.git /tmp/quadrature-original
git -C /tmp/quadrature-original checkout e79a28dba247db9f934289bcf4e4debd5eebc884
git -C /tmp/quadrature-original \
  -c url.https://github.com/.insteadOf=git@github.com: \
  submodule update --init LAProof
```

From LeanQuadrature, with that switch selected, run:

```sh
opam exec -- python3 scripts/check-upstream-vst.py \
  --source-dir /tmp/quadrature-original \
  --work-dir /tmp/quadrature-vst-check \
  --output /tmp/quadrature-vst-check.json \
  --type-scope-fix
```

In the recorded environment, the unmodified source fails in the two high-level
2D specifications: `'I_n * 'I_n` is interpreted in the open logic scope.
`--type-scope-fix` changes each to `('I_n * 'I_n)%type`, making the intended
product type explicit. The checker requires exactly those two occurrences,
retains the diff, and hashes both the original and adjusted sources. Omit the
option to repeat the unmodified build. This compatibility adjustment is
separate from the numerical and specification findings.

The source checkout and work directory must be separate. With the option,
the checker copies tracked source inputs into a new directory under the work
directory and compiles there, without reusing compiled quadrature modules.
Without it, compilation writes Rocq's generated files beside the original
sources. Both modes verify that the tracked original sources remain unchanged.
The record lists any existing compiled modules.
The checker requires a new output name so that it cannot overwrite earlier
evidence or logs.

The driver builds `CFEM.C.verif_quadrules` and its dependencies, compiles
[SpecAudit.v](SpecAudit.v) and [MathematicalAudit.v](MathematicalAudit.v), and asks
Rocq for the transitive assumptions of the selected declarations, including
every admitted lemma in the nine original quadrature files. It then rechecks
the three final modules with `coqchk
-norec`; the dependencies have already been compiled. Successful compilation
accepts the original `Admitted` declarations. The separate assumption reports
show where they enter the result.

The broader FEM project's `_CoqProject` files also name generated modules
absent from the checkout. The driver records those paths and builds from the
existing sources. If an absent module is needed by the quadrature target,
compilation fails; the checker does not supply a replacement proof.

The review module checks the Hughes specification's wrong identifier, its
duplicate registration, the missing correct registration, and the mismatch
between the three-point initializer and functional model. Some checks inherit
logical axioms through the definitions in their statements. The checker
compares those reports with the corresponding specification, initializer,
or VST definition and rejects any added axiom. The registration counts and
corrected identifier must have no axioms. The retagged Hughes body theorem
must likewise introduce no axioms beyond the original body theorem.
That retagging keeps the original global specification environment and does
not prove that the whole interface is assembled correctly.

The mathematical counterexample uses MathComp-Analysis's singleton-integral
theorem and must add no axioms beyond that library result. A separate diagnostic
applies the original `Rintegral_gt_0` to the counterexample and derives `False`.
The checker requires that diagnostic to retain exactly the original admission
together with the singleton-integral theorem's logical assumptions. It
demonstrates the consequence of a false admission; it is not an independent
proof of `False` or part of our program certificates.

The JSON record also compares the internal functions in the committed Clight
program with the body lemmas in the original verification file. This is a
source inventory, not a whole-program correctness theorem.
