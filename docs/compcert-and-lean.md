# CompCert and Lean

**Yes: a supported C program can be compiled with CompCert instead of GCC.**
The compiler's preservation theorem concerns the behavior of that C program
in CompCert's formal semantics. A numerical theorem proved in Lean must first
be connected to that same behavior before the two results compose.

Consider our two-point quadrature example. A Lean theorem bounds the error of
a particular rounded computation by `0.00356`. CompCert can preserve a C
program's behavior while compiling it. The missing general implication is:
“this C program, with these tables and this cosine implementation, performs
the computation covered by the Lean theorem.”

Compiling a program that computes an inaccurate approximation faithfully
preserves that inaccurate approximation. Compiler correctness does not
establish the numerical error bound.

## What the repository already supplies

| Route | Result | Remaining connection |
| --- | --- | --- |
| C library with the verified polynomial cosine, interpreted in Lean | Initialized total correctness in every C evaluation order, and behavioral preservation to the actual Clight frontend output for all six selected functions | General parser/elaborator correctness and correspondence with Rocq's semantics. The separate external-cosine variant retains its contract |
| Polynomial applications, checked in Lean | Initialized Clight applications and direct execution/total-correctness proofs through imported assembly for all ten orders | These are particular program certificates. They do not verify the general compiler, its exporters, or the correspondence with Rocq semantics |
| Polynomial applications, checked in Rocq | Independent numerical theorems composed with a separately checked CompCert configuration, including compilation success and termination | Formal assembly is the endpoint. No general transfer of Lean theorems is claimed |

The last route is already useful: the numerical result is proved directly in
the logic in which CompCert's theorem lives. It does not depend on importing
a Lean proof into Rocq.

## Why the same names do not provide a proof

Lean and Rocq have different representations of integers, floats, programs,
and execution. Defining something called `Clight` in both does not prove that
the definitions agree. Likewise, importing an assembly syntax tree and proving
its behavior in Lean does not certify that an exporter translated the Rocq
tree and semantics correctly.

This matters even for floating-point libraries. The pinned FloatLib and Flocq
models have different NaN policies. The repository contains counterexamples to
unrestricted bitwise equivalence and develops a more appropriate finite-value
comparison, including signed zero. Both kernels independently characterize
rounding using integer operations; a checked correspondence between those
integer representations and definitions remains open.

## Ways to connect the results

1. **Keep the numerical and compiler proof in Rocq.** This is the implemented
   route for the concrete applications. It reuses CompCert's proof directly,
   with independent numerical certificates.
2. **Prove a semantic connection between Lean and Rocq.** Give precise
   translations or interpretations for the relevant data, arithmetic, and
   program semantics; then establish that they preserve the propositions being
   transferred. A sound proof translation or a checked certificate interface
   could support this route. Merely exporting theorem statements cannot.
3. **Check particular compiled programs in Lean.** The repository already
   proves behavior for the imported polynomial applications. Extending this to
   a verified translation validator would require a sound certificate checker
   and a proved connection to the actual source and target representations.
   Direct verification can also prove the desired target property without a
   general compiler theorem, provided the target representation is justified.
4. **Verify more of the compiler in Lean.** This could make the compiler proof
   native to Lean. It is a larger project, and is not necessary to use the
   existing independent Rocq route.

These are different engineering choices. There is reusable Lean C semantics:
the project adapts CLean. It would be inaccurate to describe the problem as
“Lean has no C library,” or to say that levels four and five are impossible.
The unfinished work is the precise composition of the chosen models and their
assumptions.

## What “assembly” means here

CompCert documents its verified core from formal C syntax after parsing and
elaboration to formal assembly syntax. Its assembly printer, assembler, and
linker are outside that core theorem. Our ten concrete application certificates
observe a `quadrature-result` semantic annotation and exit status zero; the
annotation becomes an assembly comment, not an operating-system print call.

Therefore “proved through formal assembly” is accurate. “Verified the output
of the linked native executable” would require additional work.

Primary references are recorded in the [paper bibliography](../paper/references.bib):
the CompCert manual, the pinned CLean documentation, and the Appel–Bindel draft.
Local theorem and evidence references are in the [claim map](../paper/claims.md).
