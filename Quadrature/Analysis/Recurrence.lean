import Quadrature.Analysis.Orthogonal

/-!
# The three-term recurrence

The monic orthogonal polynomials `p_n` of a functional `L` positive on nonzero squares
satisfy `p_{n+2} = (X - α_{n+1}) p_{n+1} - β_n p_n`, with `α_n = L (X p_n ^ 2) / L (p_n ^ 2)`
and `β_n = L (p_{n+1} ^ 2) / L (p_n ^ 2) > 0`. Multiplication by `X` is symmetric for the
pairing `L (p * q)`, so once the components of `X p_{n+1}` along `p_{n+1}` and `p_n` are
removed, all lower components vanish by orthogonality, and `orthogonalPolynomial_unique`
identifies the result with `p_{n+2}`. The first three lemmas are degree bookkeeping.
-/

namespace Quadrature

open Polynomial

noncomputable section

/-- Subtracting `q.coeff n` times a monic polynomial of degree `n` from a polynomial `q` of
degree at most `n` leaves a polynomial of degree below `n`. -/
theorem degree_sub_coeff_mul_lt (p q : ℝ[X]) (n : ℕ) (hp : p.Monic)
    (hd : p.natDegree = n) (hq : q.degree ≤ n) :
    (q - C (q.coeff n) * p).degree < n := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  simp only [coeff_sub, coeff_C_mul]
  rcases eq_or_lt_of_le hm with rfl | hlt
  · rw [← hd, coeff_natDegree, hp, mul_one, sub_self]
  · have hqm : q.coeff m = 0 :=
      coeff_eq_zero_of_degree_lt (hq.trans_lt (by exact_mod_cast hlt))
    have hpm : p.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hqm, hpm]

/-- Multiplication by `X` raises a strict degree bound by one. -/
theorem degree_X_mul_lt_succ (q : ℝ[X]) (n : ℕ) (hq : q.degree < n) :
    (X * q).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
  by_cases hq0 : q = 0
  · simp [hq0]
  · rw [degree_mul, degree_X, degree_eq_natDegree hq0]
    rw [degree_eq_natDegree hq0] at hq
    have h : q.natDegree < n := by exact_mod_cast hq
    exact_mod_cast (show 1 + q.natDegree < n + 1 by omega)

/-- A polynomial degree below `n + 1` is at most `n`, including the zero polynomial. -/
theorem degree_le_of_lt_succ (q : ℝ[X]) (n : ℕ)
    (hq : q.degree < ((n + 1 : ℕ) : WithBot ℕ)) : q.degree ≤ n := by
  rw [degree_le_iff_coeff_zero]
  intro m hm
  apply (degree_lt_iff_coeff_zero q (n + 1)).mp hq m
  have h : n < m := by exact_mod_cast hm
  omega

variable (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hpositive : ∀ q : ℝ[X], q ≠ 0 → 0 < L (q ^ 2))

/-- The diagonal recurrence coefficient `α_n = L (X p_n ^ 2) / L (p_n ^ 2)`. -/
def recurrenceAlpha (n : ℕ) : ℝ :=
  L (X * orthogonalPolynomial L hpositive n ^ 2) /
    L (orthogonalPolynomial L hpositive n ^ 2)

/-- The off-diagonal recurrence coefficient `β_n = L (X p_{n+1} p_n) / L (p_n ^ 2)`. -/
def recurrenceBeta (n : ℕ) : ℝ :=
  L (X * orthogonalPolynomial L hpositive (n + 1) *
      orthogonalPolynomial L hpositive n) /
    L (orthogonalPolynomial L hpositive n ^ 2)

/-- The monic orthogonal polynomial of degree zero is the constant `1`. -/
theorem orthogonalPolynomial_zero :
    orthogonalPolynomial L hpositive 0 = 1 := by
  symm
  apply orthogonalPolynomial_unique L hpositive 0 1 monic_one (by simp)
  intro q hq
  have hq0 : q = 0 := by
    ext k
    simpa using (degree_lt_iff_coeff_zero q 0).mp hq k (Nat.zero_le k)
  simp [hq0]

/-- `p_1 = X - α_0`, where `α_0 = L X / L 1` is the mean of `X` for the functional `L`. -/
theorem orthogonalPolynomial_one :
    orthogonalPolynomial L hpositive 1 = X - C (recurrenceAlpha L hpositive 0) := by
  symm
  apply orthogonalPolynomial_unique L hpositive 1 _ (monic_X_sub_C _) (by simp)
  intro q hq
  have hqd : q.natDegree = 0 := by
    apply natDegree_eq_zero_iff_degree_le_zero.mpr
    exact degree_le_of_lt_succ q 0 hq
  rw [eq_C_of_natDegree_eq_zero hqd]
  have hden : L (1 : ℝ[X]) ≠ 0 := by
    simpa using ne_of_gt (hpositive 1 one_ne_zero)
  have hx : L (X - C (recurrenceAlpha L hpositive 0)) = 0 := by
    simp only [recurrenceAlpha, orthogonalPolynomial_zero, one_pow, mul_one, map_sub]
    have hc (c : ℝ) : L (C c) = c * L 1 := by
      simpa [smul_eq_C_mul] using L.map_smul c (1 : ℝ[X])
    rw [hc, div_mul_cancel₀ _ hden, sub_self]
  rw [mul_comm, ← smul_eq_C_mul, map_smul, hx, smul_zero]

/-- `β_n = L (p_{n+1} ^ 2) / L (p_n ^ 2)`. Since `X p_n - p_{n+1}` has degree below `n + 1`,
orthogonality of `p_{n+1}` gives `L (X p_{n+1} p_n) = L (p_{n+1} ^ 2)`. -/
theorem recurrenceBeta_eq_norm_ratio (n : ℕ) :
    recurrenceBeta L hpositive n =
      L (orthogonalPolynomial L hpositive (n + 1) ^ 2) /
        L (orthogonalPolynomial L hpositive n ^ 2) := by
  let p := orthogonalPolynomial L hpositive (n + 1)
  let r := orthogonalPolynomial L hpositive n
  have hp : p.Monic := orthogonalPolynomial_monic L hpositive (n + 1)
  have hr : r.Monic := orthogonalPolynomial_monic L hpositive n
  have hd : (X * r).degree = p.degree := by
    rw [degree_mul, degree_X, orthogonalPolynomial_degree,
      orthogonalPolynomial_degree]
    push_cast
    ring
  have hdiff : (X * r - p).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have h := degree_sub_lt_left hd (mul_ne_zero X_ne_zero hr.ne_zero)
      (by rw [monic_X.mul hr, hp])
    rwa [hd, orthogonalPolynomial_degree] at h
  have hz := orthogonalPolynomial_orthogonal L hpositive (n + 1) (X * r - p) hdiff
  have he : p * (X * r - p) = X * p * r - p ^ 2 := by ring
  change L (p * (X * r - p)) = 0 at hz
  rw [he, map_sub, sub_eq_zero] at hz
  exact congrArg (fun z => z / L (r ^ 2)) hz

/-- `β_n > 0`, being a ratio of values of `L` on two nonzero squares. -/
theorem recurrenceBeta_pos (n : ℕ) : 0 < recurrenceBeta L hpositive n := by
  rw [recurrenceBeta_eq_norm_ratio]
  exact div_pos
    (hpositive _ (orthogonalPolynomial_monic L hpositive (n + 1)).ne_zero)
    (hpositive _ (orthogonalPolynomial_monic L hpositive n).ne_zero)

/-- `p_{n+2} = (X - α_{n+1}) p_{n+1} - β_n p_n`. The right side is monic of degree `n + 2`
and orthogonal to `p_{n+1}`, to `p_n` and to every polynomial of degree below `n`, so
`orthogonalPolynomial_unique` applies. -/
theorem orthogonalPolynomial_recurrence (n : ℕ) :
    orthogonalPolynomial L hpositive (n + 2) =
      X * orthogonalPolynomial L hpositive (n + 1) -
      C (recurrenceAlpha L hpositive (n + 1)) *
        orthogonalPolynomial L hpositive (n + 1) -
      C (recurrenceBeta L hpositive n) * orthogonalPolynomial L hpositive n := by
  let p := orthogonalPolynomial L hpositive (n + 1)
  let r := orthogonalPolynomial L hpositive n
  let α := recurrenceAlpha L hpositive (n + 1)
  let β := recurrenceBeta L hpositive n
  let R := X * p - C α * p - C β * r
  have hp : p.Monic := orthogonalPolynomial_monic L hpositive (n + 1)
  have hr : r.Monic := orthogonalPolynomial_monic L hpositive n
  have hpd : p.degree = ((n + 1 : ℕ) : WithBot ℕ) :=
    orthogonalPolynomial_degree L hpositive (n + 1)
  have hrd : r.degree = n := orthogonalPolynomial_degree L hpositive n
  have hpn : p.natDegree = n + 1 := orthogonalPolynomial_natDegree L hpositive (n + 1)
  have hrn : r.natDegree = n := orthogonalPolynomial_natDegree L hpositive n
  have hxp : (X * p).degree = ((n + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_X, hpd]
    push_cast
    ring
  have hα : (C α * p).degree < (X * p).degree := by
    apply (show (C α * p).degree ≤ p.degree by
      simpa [smul_eq_C_mul] using degree_smul_le α p).trans_lt
    rw [hpd, hxp]
    exact_mod_cast (show n + 1 < n + 2 by omega)
  have hfirst : (X * p - C α * p).degree = ((n + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_sub_eq_left_of_degree_lt hα, hxp]
  have hβ : (C β * r).degree < (X * p - C α * p).degree := by
    apply (show (C β * r).degree ≤ r.degree by
      simpa [smul_eq_C_mul] using degree_smul_le β r).trans_lt
    rw [hrd, hfirst]
    exact_mod_cast (show n < n + 2 by omega)
  have hR : R.Monic := ((monic_X.mul hp).sub_of_left hα).sub_of_left hβ
  have hRd : R.degree = ((n + 2 : ℕ) : WithBot ℕ) := by
    dsimp only [R]
    rw [degree_sub_eq_left_of_degree_lt hβ, hfirst]
  have hpr : L (p * r) = 0 := orthogonalPolynomial_orthogonal L hpositive (n + 1) r
    (by rw [hrd]; exact_mod_cast (show n < n + 1 by omega))
  have hpp : L (p ^ 2) ≠ 0 := ne_of_gt (hpositive p hp.ne_zero)
  have hrr : L (r ^ 2) ≠ 0 := ne_of_gt (hpositive r hr.ne_zero)
  have hscalar (c : ℝ) (q : ℝ[X]) : L (C c * q) = c * L q := by
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  have hRp : L (R * p) = 0 := by
    have he : R * p = X * p ^ 2 - C α * p ^ 2 - C β * (p * r) := by
      dsimp [R]; ring
    rw [he, map_sub, map_sub, hscalar, hscalar, hpr, mul_zero, sub_zero]
    dsimp [α, recurrenceAlpha, p]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hpp).symm
  have hRr : L (R * r) = 0 := by
    have he : R * r = X * p * r - C α * (p * r) - C β * r ^ 2 := by
      dsimp [R]; ring
    rw [he, map_sub, map_sub, hscalar, hscalar, hpr, mul_zero, sub_zero]
    dsimp [β, recurrenceBeta, p, r]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hrr).symm
  have hRs (s : ℝ[X]) (hs : s.degree < n) : L (R * s) = 0 := by
    have hxs := orthogonalPolynomial_orthogonal L hpositive (n + 1) (X * s)
      (by exact_mod_cast degree_X_mul_lt_succ s n hs)
    have hps := orthogonalPolynomial_orthogonal L hpositive (n + 1) s
      (hs.trans (by exact_mod_cast (show n < n + 1 by omega)))
    have hrs := orthogonalPolynomial_orthogonal L hpositive n s hs
    have he : R * s = p * (X * s) - C α * (p * s) - C β * (r * s) := by
      dsimp [R]; ring
    rw [he, map_sub, map_sub, hscalar, hscalar, hxs, hps, hrs]
    ring
  symm
  apply orthogonalPolynomial_unique L hpositive (n + 2) R hR hRd
  intro q hq
  let q₁ := q - C (q.coeff (n + 1)) * p
  have hq₁ : q₁.degree < ((n + 1 : ℕ) : WithBot ℕ) :=
    degree_sub_coeff_mul_lt p q (n + 1) hp hpn
      (degree_le_of_lt_succ q (n + 1) hq)
  let s := q₁ - C (q₁.coeff n) * r
  have hs : s.degree < n := degree_sub_coeff_mul_lt r q₁ n hr hrn
    (degree_le_of_lt_succ q₁ n hq₁)
  have he : R * q =
      C (q.coeff (n + 1)) * (R * p) + C (q₁.coeff n) * (R * r) + R * s := by
    dsimp [s, q₁]
    ring
  rw [he, map_add, map_add, hscalar, hscalar, hRp, hRr, hRs s hs]
  ring

end
end Quadrature
