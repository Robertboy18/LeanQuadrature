import CCLib.Clight

/-!
# Imported quadrature function syntax

Provenance. The original C program is `quadrules.c` from Appel and Bindel's
`simple_cfem` repository, revision e79a28dba247db9f934289bcf4e4debd5eebc884.
Its Clight form is the output of CompCert 3.17's `clightgen` (the file's
metadata names the AArch64/Apple target), with SHA-256
7b19b9f1095cb7a36316633af3b959f79a1745be0b0e6c36103a1a38c000a1f7, from which
`scripts/import-clight-functions.py` generated the five function records below.
The Clight syntax and semantics they use are those of Certora's CLean
repository, revision 123f7f7767e215aceb4821f0d044336d78103ade, vendored with
FloatLib arithmetic in `vendor/clean`. The C syntax and strategy semantics in
`Quadrature.CSource` are adapted from the `AbsInt/CompCert` repository,
revision 7b1f02b09954b9b916eb2a91d283c9b5355bf172.

The identifiers `_name` are the C names as CLean identifiers, and `_t'1`,
`_t'2`, `_t'3` are clightgen's temporaries (positive numbers from 128). The
records `f_gauss_point`, `f_gauss_weight`, `f_integrate`, `f_testfun` and
`f_integrate_testfun` keep clightgen's expressions, types, calls and statement
nesting. Global declarations other than these five functions are omitted, and a
library context (`Quadrature.Clight.Program`) supplies the referenced functions
and tables. `Quadrature.CSource.Frontend.ClightFunctions` proves by kernel evaluation that
parsing and translating the C text gives these records, for example
`sourceFunction CSourceData.source "gauss_point" = some f_gauss_point`, and
likewise for the other four. Only the Python import script is outside Lean.
-/

namespace Quadrature.Binary64.ClightSource

def _cos : CC.Ident := CC.identOfString "cos"
def _f : CC.Ident := CC.identOfString "f"
def _gauss_point : CC.Ident := CC.identOfString "gauss_point"
def _gauss_pts : CC.Ident := CC.identOfString "gauss_pts"
def _gauss_weight : CC.Ident := CC.identOfString "gauss_weight"
def _gauss_wts : CC.Ident := CC.identOfString "gauss_wts"
def _i : CC.Ident := CC.identOfString "i"
def _integrate : CC.Ident := CC.identOfString "integrate"
def _integrate_testfun : CC.Ident := CC.identOfString "integrate_testfun"
def _n : CC.Ident := CC.identOfString "n"
def _npts : CC.Ident := CC.identOfString "npts"
def _s : CC.Ident := CC.identOfString "s"
def _testfun : CC.Ident := CC.identOfString "testfun"
def _x : CC.Ident := CC.identOfString "x"
def _t'1 : CC.Ident := CC.Positive.ofNat 128
def _t'2 : CC.Ident := CC.Positive.ofNat 129
def _t'3 : CC.Ident := CC.Positive.ofNat 130

def f_gauss_point : CC.Function where
  fn_return := CC.tdouble
  fn_callconv := CC.cc_default
  fn_params := [(_i, CC.tint), (_npts, CC.tint)]
  fn_vars := []
  fn_temps := [(_t'1, CC.tdouble)]
  fn_body := (CC.Stmt.Ssequence
      (CC.Stmt.Sset
        _t'1
        (CC.Expr.Ederef
          (CC.Expr.Ebinop
            CC.Binop.Oadd
            (CC.Expr.Evar _gauss_pts (CC.tarray CC.tdouble 55))
            (CC.Expr.Ebinop
              CC.Binop.Oadd
              (CC.Expr.Ebinop
                CC.Binop.Odiv
                (CC.Expr.Ebinop
                  CC.Binop.Omul
                  (CC.Expr.Etempvar _npts CC.tint)
                  (CC.Expr.Ebinop
                    CC.Binop.Osub
                    (CC.Expr.Etempvar _npts CC.tint)
                    (CC.Expr.Econst_int (CC.Integers.Int.repr 1) CC.tint)
                    CC.tint)
                  CC.tint)
                (CC.Expr.Econst_int (CC.Integers.Int.repr 2) CC.tint)
                CC.tint)
              (CC.Expr.Etempvar _i CC.tint)
              CC.tint)
            (CC.tptr CC.tdouble))
          CC.tdouble))
      (CC.Stmt.Sreturn (some (CC.Expr.Etempvar _t'1 CC.tdouble))))

def f_gauss_weight : CC.Function where
  fn_return := CC.tdouble
  fn_callconv := CC.cc_default
  fn_params := [(_i, CC.tint), (_npts, CC.tint)]
  fn_vars := []
  fn_temps := [(_t'1, CC.tdouble)]
  fn_body := (CC.Stmt.Ssequence
      (CC.Stmt.Sset
        _t'1
        (CC.Expr.Ederef
          (CC.Expr.Ebinop
            CC.Binop.Oadd
            (CC.Expr.Evar _gauss_wts (CC.tarray CC.tdouble 55))
            (CC.Expr.Ebinop
              CC.Binop.Oadd
              (CC.Expr.Ebinop
                CC.Binop.Odiv
                (CC.Expr.Ebinop
                  CC.Binop.Omul
                  (CC.Expr.Etempvar _npts CC.tint)
                  (CC.Expr.Ebinop
                    CC.Binop.Osub
                    (CC.Expr.Etempvar _npts CC.tint)
                    (CC.Expr.Econst_int (CC.Integers.Int.repr 1) CC.tint)
                    CC.tint)
                  CC.tint)
                (CC.Expr.Econst_int (CC.Integers.Int.repr 2) CC.tint)
                CC.tint)
              (CC.Expr.Etempvar _i CC.tint)
              CC.tint)
            (CC.tptr CC.tdouble))
          CC.tdouble))
      (CC.Stmt.Sreturn (some (CC.Expr.Etempvar _t'1 CC.tdouble))))

def f_integrate : CC.Function where
  fn_return := CC.tdouble
  fn_callconv := CC.cc_default
  fn_params :=
    [(_f, (CC.tptr (CC.Ty.Tfunction [CC.tdouble] CC.tdouble CC.cc_default))), (_n, CC.tint)]
  fn_vars := []
  fn_temps := [(_i, CC.tint),
     (_s, CC.tdouble),
     (_t'3, CC.tdouble),
     (_t'2, CC.tdouble),
     (_t'1, CC.tdouble)]
  fn_body := (CC.Stmt.Ssequence
      (CC.Stmt.Sset
        _s
        (CC.Expr.Econst_float (CC.Floats.Float.ofBits (CC.Integers.Int64.repr 0)) CC.tdouble))
      (CC.Stmt.Ssequence
        (CC.Stmt.Ssequence
          (CC.Stmt.Sset _i (CC.Expr.Econst_int (CC.Integers.Int.repr 0) CC.tint))
          (CC.Stmt.Sloop
            (CC.Stmt.Ssequence
              (CC.Stmt.Sifthenelse
                (CC.Expr.Ebinop
                  CC.Binop.Olt
                  (CC.Expr.Etempvar _i CC.tint)
                  (CC.Expr.Etempvar _n CC.tint)
                  CC.tint)
                CC.Stmt.Sskip
                CC.Stmt.Sbreak)
              (CC.Stmt.Ssequence
                (CC.Stmt.Ssequence
                  (CC.Stmt.Ssequence
                    (CC.Stmt.Scall
                      (some _t'1)
                      (CC.Expr.Evar
                        _gauss_weight
                        (CC.Ty.Tfunction [CC.tint, CC.tint] CC.tdouble CC.cc_default))
                      [(CC.Expr.Etempvar _i CC.tint), (CC.Expr.Etempvar _n CC.tint)])
                    (CC.Stmt.Scall
                      (some _t'2)
                      (CC.Expr.Evar
                        _gauss_point
                        (CC.Ty.Tfunction [CC.tint, CC.tint] CC.tdouble CC.cc_default))
                      [(CC.Expr.Etempvar _i CC.tint), (CC.Expr.Etempvar _n CC.tint)]))
                  (CC.Stmt.Scall
                    (some _t'3)
                    (CC.Expr.Etempvar
                      _f
                      (CC.tptr (CC.Ty.Tfunction [CC.tdouble] CC.tdouble CC.cc_default)))
                    [(CC.Expr.Etempvar _t'2 CC.tdouble)]))
                (CC.Stmt.Sset
                  _s
                  (CC.Expr.Ebinop
                    CC.Binop.Oadd
                    (CC.Expr.Etempvar _s CC.tdouble)
                    (CC.Expr.Ebinop
                      CC.Binop.Omul
                      (CC.Expr.Etempvar _t'1 CC.tdouble)
                      (CC.Expr.Etempvar _t'3 CC.tdouble)
                      CC.tdouble)
                    CC.tdouble))))
            (CC.Stmt.Sset
              _i
              (CC.Expr.Ebinop
                CC.Binop.Oadd
                (CC.Expr.Etempvar _i CC.tint)
                (CC.Expr.Econst_int (CC.Integers.Int.repr 1) CC.tint)
                CC.tint))))
        (CC.Stmt.Sreturn (some (CC.Expr.Etempvar _s CC.tdouble)))))

def f_testfun : CC.Function where
  fn_return := CC.tdouble
  fn_callconv := CC.cc_default
  fn_params := [(_x, CC.tdouble)]
  fn_vars := []
  fn_temps := [(_t'1, CC.tdouble)]
  fn_body := (CC.Stmt.Ssequence
      (CC.Stmt.Scall
        (some _t'1)
        (CC.Expr.Evar _cos (CC.Ty.Tfunction [CC.tdouble] CC.tdouble CC.cc_default))
        [(CC.Expr.Etempvar _x CC.tdouble)])
      (CC.Stmt.Sreturn
        (some
          (CC.Expr.Ebinop
            CC.Binop.Omul
            (CC.Expr.Ebinop
              CC.Binop.Omul
              (CC.Expr.Econst_float
                (CC.Floats.Float.ofBits (CC.Integers.Int64.repr 4602678819172646912))
                CC.tdouble)
              (CC.Expr.Ebinop
                CC.Binop.Osub
                (CC.Expr.Econst_int (CC.Integers.Int.repr 1) CC.tint)
                (CC.Expr.Etempvar _x CC.tdouble)
                CC.tdouble)
              CC.tdouble)
            (CC.Expr.Etempvar _t'1 CC.tdouble)
            CC.tdouble))))

def f_integrate_testfun : CC.Function where
  fn_return := CC.tdouble
  fn_callconv := CC.cc_default
  fn_params := []
  fn_vars := []
  fn_temps := [(_t'1, CC.tdouble)]
  fn_body := (CC.Stmt.Ssequence
      (CC.Stmt.Scall
        (some _t'1)
        (CC.Expr.Evar
          _integrate
          (CC.Ty.Tfunction
            [(CC.tptr (CC.Ty.Tfunction [CC.tdouble] CC.tdouble CC.cc_default)), CC.tint]
            CC.tdouble
            CC.cc_default))
        [(CC.Expr.Eaddrof
            (CC.Expr.Evar _testfun (CC.Ty.Tfunction [CC.tdouble] CC.tdouble CC.cc_default))
            (CC.tptr (CC.Ty.Tfunction [CC.tdouble] CC.tdouble CC.cc_default))),
         (CC.Expr.Econst_int (CC.Integers.Int.repr 2) CC.tint)])
      (CC.Stmt.Sreturn (some (CC.Expr.Etempvar _t'1 CC.tdouble))))

end Quadrature.Binary64.ClightSource
