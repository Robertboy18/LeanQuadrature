import Quadrature.CSource.Callback.Function
import Quadrature.CSource.Cosine.Total

/-!
# Total correctness of the original callback

`testfun_call_correct` permits every ordering of the arithmetic and nested
cosine call in `0.5 * (1 - x) * cos(x)`. `polynomial_callback_correct`
discharges the cosine contract with the verified internal C implementation.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step
open Binary64.ClightSource FloatLib.Floats.Formats.BinaryInterchange SmallStep

variable [ExternalCalls]

/-- A callback pointer resolves to a function that terminates correctly in every C evaluation
order and preserves the caller's memory. -/
structure CallbackCorrect (ge : GlobalEnv) (pointer : Val)
    (function : FunDef) (f : Floats.Float → Floats.Float) : Prop where
  function_eq : Genv.findFunct ge.globals pointer = some function
  type_eq : typeOfFundef function = callbackType
  execution : ∀ memory x, CallCorrect ge memory function [.Vfloat x] (.Vfloat (f x))

/-- The callback's expression retains its specified value in every operand order, including
orders that evaluate the cosine call before reading `x`. -/
theorem testfun_read_eval (ge : GlobalEnv) (memory : Mem) (block cosBlock : Block)
    (function : FunDef) (cosine : Floats.Float → Floats.Float) (x : Floats.Float)
    (hsymbol : Genv.findSymbol ge.globals _cos = some cosBlock)
    (contract : CallbackCorrect ge (.Vptr cosBlock Integers.Ptrofs.zero) function cosine)
    (hload : Mem.load .Mfloat64 memory block 0 = some (.Vfloat x)) :
    ReadEval ge (testfunLocals block) memory .RV testfunExpression
      (.value (.Vfloat (Binary64.testfun cosine x))) := by
  have hread := ReadEval.local ge (testfunLocals block) memory
    _x tdouble block .Mfloat64 (.Vfloat x) rfl rfl rfl hload
  apply ReadEval.binop
    (leftValue := .Vfloat (Model.mul Binary64.half (Model.sub Binary64.one x)))
    (rightValue := .Vfloat (cosine x))
  · apply ReadEval.binop (leftValue := .Vfloat Binary64.half)
      (rightValue := .Vfloat (Model.sub Binary64.one x))
    · exact .value _ _
    · exact .binop _ _ _ _ _ _ _ (.value _ _) hread
        (fun memory _ => testfun_subtraction ge.composites memory x)
    · intro memory _
      rfl
  · apply ReadEval.call (pointer := .Vptr cosBlock Integers.Ptrofs.zero)
      (parameters := [tdouble]) (returnType := tdouble) (cc := cc_default)
      (function := function) (values := [.Vfloat x])
    · exact .global_function ge _ memory _cos cosBlock [tdouble] tdouble cc_default rfl hsymbol
    · exact .cons _ _ _ _ _ _ _ hread (fun _ _ => rfl) .nil
    · exact contract.function_eq
    · exact contract.type_eq
    · rfl
    · intro memory _
      exact contract.execution memory x
  · intro memory _
    rfl

/-- Every complete call of the original callback returns its binary64 functional value. -/
theorem testfun_call_correct (ge : GlobalEnv) (memory : Mem) (cosBlock : Block)
    (function : FunDef) (cosine : Floats.Float → Floats.Float) (x : Floats.Float)
    (hsymbol : Genv.findSymbol ge.globals _cos = some cosBlock)
    (contract : CallbackCorrect ge (.Vptr cosBlock Integers.Ptrofs.zero) function cosine) :
    CallCorrect ge memory (.Internal Typed.testfun) [.Vfloat x]
      (.Vfloat (Binary64.testfun cosine x)) := by
  intro cont hcont
  obtain ⟨entered, hentry, hload, hfreeable, hentryMemory⟩ :=
    testfun_entry ge.expressionEnv memory x
  have heval := testfun_read_eval ge entered memory.nextblock cosBlock
    function cosine x hsymbol contract hload
  apply Total.internal (by simp [Typed.testfun]; rfl) hentry
  apply Total.statement (.return_start _ _ _ _ _)
  apply (heval.total (.refl _) Typed.testfun _).bind
  rintro state ⟨afterBody, rfl, hbodyMemory⟩
  obtain ⟨final, hfree, hmemory⟩ := testfun_free ge.composites memory entered afterBody x
    hload hfreeable hentryMemory hbodyMemory
  apply Total.value (.return_finish _ _ _ _ _ _ _ _ rfl hfree)
  exact .done ⟨final, by rw [Cont.callCont_eq hcont], hmemory⟩

/-- Resolving `cos` to the verified C polynomial establishes the complete callback contract. -/
theorem polynomial_callback_correct (ge : GlobalEnv) (callback cosBlock : Block)
    (hcallback : Genv.findFunct ge.globals (.Vptr callback Integers.Ptrofs.zero) =
      some (.Internal Typed.testfun))
    (hsymbol : Genv.findSymbol ge.globals _cos = some cosBlock)
    (hcosine : Genv.findFunct ge.globals (.Vptr cosBlock Integers.Ptrofs.zero) =
      some (.Internal Cosine.function)) :
    CallbackCorrect ge (.Vptr callback Integers.Ptrofs.zero) (.Internal Typed.testfun)
      (Binary64.testfun Binary64.Polynomial.cosine) :=
  ⟨hcallback, rfl, fun memory x =>
    testfun_call_correct ge memory cosBlock (.Internal Cosine.function)
      Binary64.Polynomial.cosine x hsymbol ⟨hcosine, rfl, Cosine.call_correct ge⟩⟩

end Quadrature.CSource.C
