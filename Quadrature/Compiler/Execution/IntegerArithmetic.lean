import CCLib.Values
import Mathlib.Tactic.NormNum

/-!
# Integer arithmetic in the quadrature accessors

The source and target accessors use signed 32-bit division for the triangular
table index. These lemmas connect that calculation to natural-number arithmetic.
The product `n * (n - 1)` agrees in both representations even at `n = 0`.
-/

namespace CC.Integers.Int

/-- Converting a natural number below `2 ^ 31` to a signed 32-bit integer preserves its value. -/
theorem signed_repr_nat (n : Nat) (hn : n < 2 ^ 31) :
    signed (repr n) = (n : Z) := by
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · norm_num
  · exact_mod_cast hn

/-- Signed division by two agrees with natural-number division below the signed limit. -/
theorem divs_repr_nat_two (n : Nat) (hn : n < 2 ^ 31) :
    divs (repr n) (repr 2) = repr (n / 2 : Nat) := by
  apply BitVec.toInt_inj.mp
  change ((BitVec.ofInt 32 (n : Z)).sdiv (BitVec.ofInt 32 2)).toInt = _
  rw [BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr (by decide))]
  change (signed (repr n)).tdiv 2 = signed (repr (n / 2 : Nat))
  rw [signed_repr_nat n hn, signed_repr_nat (n / 2) (by omega)]
  simp

/-- Multiplication by `n` absorbs the difference between signed and natural predecessors. -/
theorem mul_pred_repr_nat (n : Nat) :
    mul (repr n) (sub (repr n) (repr 1)) = repr (n * (n - 1) : Nat) := by
  change BitVec.ofInt 32 (n : Z) *
    (BitVec.ofInt 32 (n : Z) - BitVec.ofInt 32 1) = _
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add,
    ← BitVec.ofInt_mul]
  congr 1
  cases n <;> simp

end CC.Integers.Int

namespace CC.Val

/-- The value-level guards allow division by two for every signed 32-bit dividend. -/
theorem divs_two (a : Integers.Int) :
    divs (.Vint a) (.Vint (Integers.Int.repr 2)) =
      some (.Vint (Integers.Int.divs a (Integers.Int.repr 2))) := by
  change (if (false || (a.eq (Integers.Int.repr Integers.Int.min_signed) && false)) = true
    then none else _) = _
  simp

end CC.Val
