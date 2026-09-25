import Quadrature.CSource.Library.Preservation
import Quadrature.CSource.Library.Total
import Quadrature.Clight.Main
import Quadrature.Compiler.Asm.StoredTotalCorrectness

/-!
# From initialized C returns to application observations

`csource_integrate_asm_observations_iff` connects all ten initialized C integrator calls
to the imported assembly applications. `parsed_wrapper_asm_accuracy` specializes this
connection to the original two-node wrapper, including the source text and error bound.

The observation convention is explicit: the C library returns silently, whereas an
application annotates that returned binary64 value and exits zero. The normalized Clight
library and the authored Clight entry points are connected by
`normalized_integrate_application_observations_iff`. Their cosine bodies have different
syntax but compute the same rounded polynomial.

These are correspondences between the results of the particular verified programs.
They use the existing total-correctness proofs; they do not assert that compiling the
original C text produces these assembly trees. General compiler correctness and the
interpretation of the imported syntax are separate obligations.
-/

namespace Quadrature.Compiler

open CC Binary64 CSource FloatLib.Floats.Formats.BinaryInterchange

/-- Reporting a return from the actual normalized library gives exactly the final observations
of the authored Clight application. This includes initialization on each side. -/
theorem normalized_integrate_application_observations_iff [calls : ExternalCalls]
    [ExternalCallsDeterministic calls] (n : Nat) (hn : n ≤ 10)
    (trace : Trace) (status : Integers.Int) :
    (∃ value : Value,
      ClightOutcome Library.Normalized.program ClightSource._integrate
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
        E0 (.Vfloat value) ∧
      trace = Clight.Application.resultTrace value ∧ status = Integers.Int.zero) ↔
    (∃ start memory, InitialState (Clight.Application.program n) start ∧
      Star (Step2 (Clight.Application.program n).globalenv) start trace
        (.Returnstate (.Vint status) .Kstop memory)) := by
  have hreturn (value : Value) :
      ClightOutcome Library.Normalized.program ClightSource._integrate
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
        E0 (.Vfloat value) ↔ value = Clight.StoredPolynomial.result n := by
    simpa using (Library.initialized_refinement (.integrate n hn)).target_outcome_iff
      E0 (.Vfloat value)
  constructor
  · rintro ⟨value, hvalue, rfl, rfl⟩
    obtain rfl := (hreturn value).mp hvalue
    exact ⟨Clight.Application.initialState n, Clight.Application.entryMemory,
      Clight.Application.initial_state n, Clight.Application.execution n hn⟩
  · rintro ⟨start, memory, hinit, hrun⟩
    obtain ⟨htrace, hstatus, _⟩ := Clight.Application.return_specification n hn
      start trace (.Vint status) memory hinit hrun
    exact ⟨Clight.StoredPolynomial.result n, (hreturn _).mpr rfl,
      htrace, Val.Vint.inj hstatus⟩

/-- The same application observations come from the initialized typed C integrator, with every
operand evaluation order covered by its call-refinement theorem. -/
theorem csource_integrate_application_observations_iff [calls : ExternalCalls]
    [ExternalCallsDeterministic calls] (n : Nat) (hn : n ≤ 10)
    (trace : Trace) (status : Integers.Int) :
    (∃ value : Value,
      Library.polynomialLibrary.InitializedOutcome ClightSource._integrate
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
        E0 (.Vfloat value) ∧
      trace = Clight.Application.resultTrace value ∧ status = Integers.Int.zero) ↔
    (∃ start memory, InitialState (Clight.Application.program n) start ∧
      Star (Step2 (Clight.Application.program n).globalenv) start trace
        (.Returnstate (.Vint status) .Kstop memory)) := by
  simp only [Library.initialized_outcomes_iff (.integrate n hn)]
  exact normalized_integrate_application_observations_iff n hn trace status

variable [ExternalCalls]

/-- For each stored order, the C integrator's returned value is exactly the value reported by
the imported assembly application, which exits zero. No external-determinism premise is needed:
the C calls are internal and the assembly theorem characterizes every final observation. -/
theorem csource_integrate_asm_observations_iff
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ value : Value,
      Library.polynomialLibrary.InitializedOutcome ClightSource._integrate
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
        E0 (.Vfloat value) ∧
      trace = Asm.StoredPrograms.resultTrace value ∧ status = Integers.Int.zero) ↔
    (∃ start finish, Asm.InitialState (Asm.Imported.program n) start ∧
      Asm.Steps (Asm.Imported.program n).globalenv start trace finish ∧
      Asm.FinalState finish status) := by
  have hreturn (value : Value) :
      Library.polynomialLibrary.InitializedOutcome ClightSource._integrate
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
        E0 (.Vfloat value) ↔ value = Clight.StoredPolynomial.result n := by
    simpa using (Library.initialized_refinement (.integrate n hhi)).source_outcome_iff
      E0 (.Vfloat value)
  simpa [hreturn] using
    (Asm.StoredPrograms.final_observations_iff n hlo hhi trace status).symm

/-- The original no-argument wrapper and the two-node assembly application agree on the value
that is returned by C and reported by the application. -/
theorem csource_wrapper_asm_observations_iff (trace : Trace) (status : Integers.Int) :
    (∃ value : Value,
      Library.polynomialLibrary.InitializedOutcome ClightSource._integrate_testfun []
        E0 (.Vfloat value) ∧
      trace = Asm.StoredPrograms.resultTrace value ∧ status = Integers.Int.zero) ↔
    (∃ start finish, Asm.InitialState (Asm.Imported.program 2) start ∧
      Asm.Steps (Asm.Imported.program 2).globalenv start trace finish ∧
      Asm.FinalState finish status) := by
  have hreturn (value : Value) :
      Library.polynomialLibrary.InitializedOutcome ClightSource._integrate_testfun []
        E0 (.Vfloat value) ↔ value = Clight.StoredPolynomial.result 2 := by
    simpa using (Library.initialized_refinement .wrapper).source_outcome_iff E0 (.Vfloat value)
  simpa [hreturn] using
    (Asm.StoredPrograms.final_observations_iff 2 (by decide) (by decide) trace status).symm

/-- The parsed two-node wrapper always returns the same finite value that the assembly
application reports. Both initializations succeed; a completed assembly run exists and every
completed run reports bits `0x3fead02c771c35ed` with exit zero. The integral error is at most
`0.00356`. Assembly progress and termination are in `Asm.StoredPrograms`. -/
theorem parsed_wrapper_asm_accuracy :
    ∃ library value,
      Library.fromSources CSourceData.source Cosine.source = some library ∧
      library.InitializedCallCorrect ClightSource._integrate_testfun [] (.Vfloat value) ∧
      (∀ trace status,
        (∃ start finish, Asm.InitialState (Asm.Imported.program 2) start ∧
          Asm.Steps (Asm.Imported.program 2).globalenv start trace finish ∧
          Asm.FinalState finish status) ↔
        trace = Asm.StoredPrograms.resultTrace value ∧ status = Integers.Int.zero) ∧
      value = Model.ofNatBits 0x3fead02c771c35ed ∧
      Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        (356 : ℝ) / 100000 := by
  obtain ⟨library, value, hparse, hcall, hbits, hfinite, haccuracy⟩ :=
    Library.parsed_wrapper_total_accuracy
  refine ⟨library, value, hparse, hcall, ?_, hbits, hfinite, haccuracy⟩
  intro trace status
  have hvalue : value = Clight.StoredPolynomial.result 2 :=
    hbits.trans (Clight.StoredPolynomial.result_value 2 (by decide) (by decide)).symm
  rw [hvalue]
  exact Asm.StoredPrograms.final_observations_iff 2 (by decide) (by decide) trace status

end Quadrature.Compiler
