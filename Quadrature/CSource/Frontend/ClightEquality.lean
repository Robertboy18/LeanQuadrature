import CCLib.Clight

/-!
# Decidable equality for the imported Clight function syntax

Derived `DecidableEq` instances for CLean's `Expr`, `Stmt`, `LStmts` and
`Function`, so that `decide +kernel` can compare a translated function with the
imported one in `Quadrature.CSource.Frontend.ClightFunctions` without unfolding the source
processing in the elaborator.
-/

namespace CC

deriving instance DecidableEq for Expr
deriving instance DecidableEq for Stmt, LStmts
deriving instance DecidableEq for Function

end CC
