import Quadrature.Clight.Execution
import Quadrature.Clight.Source
import Quadrature.Clight.TableData
import Quadrature.Examples.PolynomialRules

/-!
# A Clight library context for the polynomial quadrature applications

`polynomialLibrary` is a CLean `Program` holding the two tables and five
function bodies imported from the original C program, plus the internal
polynomial `polynomialFunction` at the `cos` symbol. This follows the
companion Rocq proofs in `compcert/InternalCosine.v`, which verify the same
application with a polynomial in place of the library cosine. `initialMemory`
is the program's initialized global memory, and `polynomialCall order` is the
call of `integrate` with the callback pointer and one of the four supported
orders. Vocabulary: see `Quadrature.Clight.Execution`.
-/

namespace Quadrature.Binary64.Clight

open FloatLib.Floats.Formats.BinaryInterchange
open ClightSource

/-- A read-only, nonvolatile global array of 55 `double`s initialized from the 64-bit encodings
`bits`, the shape of the two C tables. -/
def tableGlobal (bits : List Nat) : CC.GlobVar CC.Ty where
  gvar_info := CC.tarray CC.tdouble 55
  gvar_init := bits.map fun n => .Init_float64 (Model.ofNatBits n)
  gvar_readonly := true
  gvar_volatile := false

/-- The parameter identifier of `polynomialFunction`. -/
def polynomialArgument : CC.Ident := CC.Positive.ofNat 4000
/-- The temporary of `polynomialFunction` holding the squared argument. -/
def polynomialSquare : CC.Ident := CC.Positive.ofNat 4001

/-- The Clight expression for Horner evaluation of the coefficients `cs` at the temporary
`polynomialSquare`, `c₀ + z * (c₁ + z * (... + z * 0))`, with every multiplication and addition a
separate rounded `double` operation, as in `Polynomial.horner`. -/
def hornerExpression : List Value → CC.Expr
  | [] => .Econst_float zero CC.tdouble
  | c :: cs =>
    .Ebinop .Oadd (.Econst_float c CC.tdouble)
      (.Ebinop .Omul (.Etempvar polynomialSquare CC.tdouble)
        (hornerExpression cs) CC.tdouble) CC.tdouble

/-- The Clight function placed at the `cos` symbol: it squares its argument and evaluates the
polynomial `Polynomial.coefficients` (degree fourteen in `x`, eight coefficients in `x²`) by
Horner's rule, computing `Polynomial.cosine`. -/
def polynomialFunction : CC.Function where
  fn_return := CC.tdouble
  fn_callconv := CC.cc_default
  fn_params := [(polynomialArgument, CC.tdouble)]
  fn_vars := []
  fn_temps := [(polynomialSquare, CC.tdouble)]
  fn_body :=
    .Ssequence
      (.Sset polynomialSquare
        (.Ebinop .Omul (.Etempvar polynomialArgument CC.tdouble)
          (.Etempvar polynomialArgument CC.tdouble) CC.tdouble))
      (.Sreturn (some (hornerExpression Polynomial.coefficients)))

/-- The CLean program with the two tables, the five imported functions and `polynomialFunction`
at `cos`, in that order, so the blocks are 1 to 8. Its main symbol is `integrate_testfun`, and
globals of the original file that these functions do not reference are omitted. -/
def polynomialLibrary : CC.Program :=
  CC.mkprogram []
    [(_gauss_pts, .Gvar (tableGlobal ClightTableData.nodeBits)),
     (_gauss_wts, .Gvar (tableGlobal ClightTableData.weightBits)),
     (_gauss_point, .Gfun (.Internal f_gauss_point)),
     (_gauss_weight, .Gfun (.Internal f_gauss_weight)),
     (_integrate, .Gfun (.Internal f_integrate)),
     (_testfun, .Gfun (.Internal f_testfun)),
     (_integrate_testfun, .Gfun (.Internal f_integrate_testfun)),
     (_cos, .Gfun (.Internal polynomialFunction))]
    [] _integrate_testfun

/-- The program declares no composite types, so its composite environment is well formed. -/
theorem polynomialLibrary_composites :
    CC.compositesWellFormed polynomialLibrary = true := by decide

/-- The initialized global memory of `polynomialLibrary`. The `getD` fallback never applies, by
`polynomialLibrary_initialized`. -/
def initialMemory : CC.Mem := polynomialLibrary.initMem.getD CC.Mem.empty

-- Compute the global initialization of the eight definitions, including the 110 table words.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- Global initialization of `polynomialLibrary` succeeds, by kernel evaluation. -/
theorem polynomialLibrary_initializes :
    polynomialLibrary.initMem.isSome = true := by
  decide +kernel

/-- The initialized memory of `polynomialLibrary` is `initialMemory`. -/
theorem polynomialLibrary_initialized :
    polynomialLibrary.initMem = some initialMemory := by
  have h := polynomialLibrary_initializes
  unfold initialMemory
  cases hm : polynomialLibrary.initMem <;> simp_all

/-- The number of nodes of a supported order: 1, 2, 3 or 4. -/
def orderCount : Polynomial.Order → Nat
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4

/-- The block of the `testfun` symbol, the sixth global definition of `polynomialLibrary`. -/
def testfunBlock : CC.Block := CC.Positive.ofNat 6

/-- `testfun` resolves to `testfunBlock` in `polynomialLibrary`. -/
theorem testfun_symbol :
    CC.Genv.findSymbol polynomialLibrary.globalenv.genv_genv _testfun =
      some testfunBlock := by decide

/-- The state entering the imported `integrate` with the `testfun` pointer and `orderCount order`
nodes, from `initialMemory` under the empty continuation. -/
def polynomialCall (order : Polynomial.Order) : CC.State :=
  .Callstate (.Internal f_integrate)
    [.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0),
     .Vint (CC.Integers.Int.repr (orderCount order))]
    .Kstop initialMemory

end Quadrature.Binary64.Clight
