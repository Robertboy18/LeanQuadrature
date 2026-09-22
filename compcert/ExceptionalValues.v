From Coq Require Import ZArith.
From compcert Require Import Integers Floats.

Local Open Scope Z_scope.

(** These inputs match Quadrature/ExceptionalValues.lean.  The x86_64
    CompCert model selects the first NaN, uses a negative default NaN,
    and preserves the right NaN's sign in subtraction.  The Lean and
    Rocq certificates are checked independently. *)
Definition quiet_nan := Float.of_bits (Int64.repr 0x7ff8000000000001).
Definition signaling_nan := Float.of_bits (Int64.repr 0x7ff0000000000002).
Definition positive_infinity := Float.of_bits (Int64.repr 0x7ff0000000000000).
Definition negative_infinity := Float.of_bits (Int64.repr 0xfff0000000000000).
Definition positive_zero := Float.of_bits (Int64.repr 0).
Definition positive_one := Float.of_bits (Int64.repr 0x3ff0000000000000).

Lemma mixed_nan_add :
  Float.to_bits (Float.add quiet_nan signaling_nan) = Int64.repr 0x7ff8000000000001.
Proof. vm_compute. reflexivity. Qed.

Lemma mixed_nan_mul :
  Float.to_bits (Float.mul quiet_nan signaling_nan) = Int64.repr 0x7ff8000000000001.
Proof. vm_compute. reflexivity. Qed.

Lemma opposite_infinities_add :
  Float.to_bits (Float.add positive_infinity negative_infinity) =
    Int64.repr 0xfff8000000000000.
Proof. vm_compute. reflexivity. Qed.

Lemma infinity_zero_mul :
  Float.to_bits (Float.mul positive_infinity positive_zero) =
    Int64.repr 0xfff8000000000000.
Proof. vm_compute. reflexivity. Qed.

Lemma zero_div_zero :
  Float.to_bits (Float.div positive_zero positive_zero) = Int64.repr 0xfff8000000000000.
Proof. vm_compute. reflexivity. Qed.

Lemma finite_sub_nan :
  Float.to_bits (Float.sub positive_one quiet_nan) = Int64.repr 0x7ff8000000000001.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions mixed_nan_add.
Print Assumptions mixed_nan_mul.
Print Assumptions opposite_infinities_add.
Print Assumptions infinity_zero_mul.
Print Assumptions zero_div_zero.
Print Assumptions finite_sub_nan.
