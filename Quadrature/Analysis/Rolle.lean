import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Multiset.Sort
import Mathlib.Tactic

/-!
# Rolle's theorem with repeated zeros

A derivative chain on `[a, b]` is a family `F : ℕ → ℝ → ℝ` such that each `F k` is
continuous on `[a, b]` and has derivative `F (k + 1)` at every point of `(a, b)`. For a
`C^m` function `f` the family `F k = iteratedDerivWithin k f (Icc a b)` is a derivative
chain (`derivative_chain_within` in `Remainder`), but the notion asks nothing of `f` outside
`[a, b]`, which is why it replaces `iteratedDeriv` throughout the remainder theory.

The generalized Rolle theorem proved here says that if `F 0` has `n + 1` zeros in `[a, b]`
counted with multiplicity, where a zero of multiplicity `m` means that `F 0, …, F (m - 1)`
all vanish there, then `F n` vanishes somewhere in `[a, b]`. Rolle's theorem supplies a zero
of `F 1` between distinct consecutive zeros, and a repeated zero supplies one directly.
-/

namespace Quadrature

open Set

/-- Between two zeros `l ≤ r` of `F 0` there is a zero of `F 1`, strictly between them when
`l < r`. For `l < r` this is Rolle's theorem, and for `l = r` the hypothesis `F 1 l = 0` is
used directly. -/
theorem exists_between_derivative_zero {a b : ℝ} {F : ℕ → ℝ → ℝ}
    (hcontinuous : ContinuousOn (F 0) (Icc a b))
    (hderiv : ∀ z ∈ Ioo a b, HasDerivAt (F 0) (F 1 z) z)
    {l r : ℝ} (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) (hle : l ≤ r)
    (hlzero : F 0 l = 0) (hrzero : F 0 r = 0)
    (hsame : l = r → F 1 l = 0) :
    ∃ y ∈ Icc l r, F 1 y = 0 ∧ (l < r → y ∈ Ioo l r) := by
  rcases hle.eq_or_lt with heq | hlt
  · exact ⟨l, ⟨le_rfl, heq.le⟩, hsame heq, fun h => (h.ne heq).elim⟩
  · obtain ⟨y, hy, hyzero⟩ := exists_hasDerivAt_eq_zero hlt
      (hcontinuous.mono (Icc_subset_Icc hl.1 hr.2)) (hlzero.trans hrzero.symm)
      (fun z hz => hderiv z ⟨hl.1.trans_lt hz.1, hz.2.trans_le hr.2⟩)
    exact ⟨y, ⟨hy.1.le, hy.2.le⟩, hyzero, fun _ => hy⟩

/-- Generalized Rolle theorem for a derivative chain: `n + 1` zeros of `F 0` in `[a, b]`,
listed in increasing order with repeats allowed, force a zero of `F n` in `[a, b]`. A run of
equal entries from index `i` to `j` must also be a zero of `F (j - i)`, which is how
multiplicity enters. Induction on `n`, passing to the chain `k ↦ F (k + 1)` and the `n`
zeros of `F 1` between consecutive entries. -/
theorem exists_derivative_chain_zero {a b : ℝ} (n : ℕ) (F : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ k < n, ContinuousOn (F k) (Icc a b))
    (hderiv : ∀ k < n, ∀ z ∈ Ioo a b, HasDerivAt (F k) (F (k + 1) z) z)
    (x : Fin (n + 1) → ℝ) (hmonotone : Monotone x)
    (hmem : ∀ i, x i ∈ Icc a b)
    (hzero : ∀ i j, i ≤ j → x i = x j → F (j.val - i.val) (x i) = 0) :
    ∃ z ∈ Icc a b, F n z = 0 := by
  induction n generalizing F with
  | zero =>
    exact ⟨x 0, hmem 0, by simpa using hzero 0 0 le_rfl rfl⟩
  | succ n ih =>
    have hbetween (i : Fin (n + 1)) :
        ∃ y ∈ Icc (x i.castSucc) (x i.succ),
          F 1 y = 0 ∧ (x i.castSucc < x i.succ → y ∈ Ioo (x i.castSucc) (x i.succ)) := by
      apply exists_between_derivative_zero (hcontinuous 0 (by omega))
        (hderiv 0 (by omega)) (hmem i.castSucc) (hmem i.succ)
        (hmonotone (show i.castSucc ≤ i.succ from Nat.le_succ _))
      · simpa using hzero i.castSucc i.castSucc le_rfl rfl
      · simpa using hzero i.succ i.succ le_rfl rfl
      · intro heq
        simpa using hzero i.castSucc i.succ (Nat.le_succ _) heq
    choose y hy hyzero hystrict using hbetween
    have hsep {i j : Fin (n + 1)} (hij : i < j) : x i.succ ≤ x j.castSucc :=
      hmonotone (by simpa using hij)
    have hymono : Monotone y := by
      intro i j hij
      rcases hij.eq_or_lt with rfl | hij
      · exact le_rfl
      · exact (hy i).2.trans ((hsep hij).trans (hy j).1)
    have hymem (i : Fin (n + 1)) : y i ∈ Icc a b :=
      ⟨(hmem i.castSucc).1.trans (hy i).1, (hy i).2.trans (hmem i.succ).2⟩
    have hyrepeat (i j : Fin (n + 1)) (hij : i ≤ j) (heq : y i = y j) :
        F (j.val - i.val + 1) (y i) = 0 := by
      rcases hij.eq_or_lt with rfl | hij
      · simpa using hyzero i
      · have hfirst : x i.castSucc = x i.succ := by
          by_contra hne
          have hlt := lt_of_le_of_ne
            (hmonotone (show i.castSucc ≤ i.succ from Nat.le_succ _)) hne
          have hi := (hystrict i hlt).2
          have hj := (hy j).1
          have hs := hsep hij
          linarith
        have hlast : x j.castSucc = x j.succ := by
          by_contra hne
          have hlt := lt_of_le_of_ne
            (hmonotone (show j.castSucc ≤ j.succ from Nat.le_succ _)) hne
          have hi := (hy i).2
          have hj := (hystrict j hlt).1
          have hs := hsep hij
          linarith
        have hyleft : y i = x i.castSucc := by
          exact le_antisymm (by simpa [← hfirst] using (hy i).2) (hy i).1
        have hyright : y j = x j.succ := by
          exact le_antisymm (hy j).2 (by simpa [hlast] using (hy j).1)
        have hx : x i.castSucc = x j.succ := by rw [← hyleft, ← hyright, heq]
        have hz := hzero i.castSucc j.succ
          (show i.val ≤ j.val + 1 from (Fin.le_iff_val_le_val.mp hij.le).trans
            (Nat.le_succ _)) hx
        have horder : j.succ.val - i.castSucc.val = j.val - i.val + 1 := by
          simp only [Fin.val_succ, Fin.val_castSucc]
          have := hij.le
          omega
        rw [horder, ← hyleft] at hz
        exact hz
    exact ih (fun k => F (k + 1))
      (fun k hk => hcontinuous (k + 1) (by omega))
      (fun k hk => hderiv (k + 1) (by omega)) y hymono hymem hyrepeat

/-- Multiset form of the generalized Rolle theorem: if `s` has `n + 1` elements of `[a, b]`
and `F k z = 0` for every `z ∈ s` and every `k` below the multiplicity of `z` in `s`, then
`F n` has a zero in `[a, b]`. Sort `s` and apply `exists_derivative_chain_zero`. -/
theorem exists_derivative_chain_zero_of_multiset {a b : ℝ} (n : ℕ)
    (F : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ k < n, ContinuousOn (F k) (Icc a b))
    (hderiv : ∀ k < n, ∀ z ∈ Ioo a b, HasDerivAt (F k) (F (k + 1) z) z)
    (s : Multiset ℝ) (hcard : s.card = n + 1)
    (hmem : ∀ z ∈ s, z ∈ Icc a b)
    (hzero : ∀ z ∈ s, ∀ k < s.count z, F k z = 0) :
    ∃ z ∈ Icc a b, F n z = 0 := by
  classical
  let v : List.Vector ℝ (n + 1) := ⟨s.sort (· ≤ ·), by simpa using hcard⟩
  have hmono : Monotone v.get := by
    intro i j hij
    exact (s.pairwise_sort (· ≤ ·)).rel_get_of_le hij
  have hvmem (i : Fin (n + 1)) : v.get i ∈ s :=
    (Multiset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)
  apply exists_derivative_chain_zero n F hcontinuous hderiv v.get hmono
    (fun i => hmem _ (hvmem i))
  intro i j hij heq
  apply hzero _ (hvmem i)
  have hsub : Finset.Icc i j ⊆ Finset.univ.filter (fun k => v.get k = v.get i) := by
    intro k hk
    obtain ⟨hik, hkj⟩ := Finset.mem_Icc.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply le_antisymm
    · exact (hmono hkj).trans heq.ge
    · exact hmono hik
  have hc := Finset.card_le_card hsub
  rw [Fin.card_Icc, Fin.card_filter_univ_eq_vector_get_eq_count] at hc
  have hcount : v.toList.count (v.get i) = s.count (v.get i) := by
    change (s.sort (· ≤ ·)).count _ = _
    rw [← Multiset.coe_count, Multiset.sort_eq]
  rw [hcount] at hc
  have := Fin.le_iff_val_le_val.mp hij
  omega

/-- If `F 0` and `F 1` vanish at `n` distinct nodes in `[a, b]` and `F 0` vanishes at one
further point `x`, then `F (2n)` has a zero in `[a, b]`. This is the multiset case with each
node of multiplicity two and `x` of multiplicity one, `2n + 1` zeros in all. It is the form
used for the Gaussian remainder. -/
theorem exists_derivative_chain_zero_of_double_zeros {a b : ℝ} (n : ℕ)
    (F : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ k < 2 * n, ContinuousOn (F k) (Icc a b))
    (hderiv : ∀ k < 2 * n, ∀ z ∈ Ioo a b, HasDerivAt (F k) (F (k + 1) z) z)
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (hmem : ∀ i, nodes i ∈ Icc a b)
    (hzero : ∀ i, F 0 (nodes i) = 0 ∧ F 1 (nodes i) = 0)
    (x : ℝ) (hx : x ∈ Icc a b) (hxne : ∀ i, x ≠ nodes i) (hxzero : F 0 x = 0) :
    ∃ z ∈ Icc a b, F (2 * n) z = 0 := by
  classical
  let t : Multiset ℝ := (Finset.univ : Finset (Fin n)).val.map nodes
  have htmem (z : ℝ) : z ∈ t ↔ ∃ i, nodes i = z := by simp [t]
  have htnodup : t.Nodup :=
    Multiset.Nodup.map hnodes Finset.univ.nodup
  have hxnot : x ∉ t := by
    rw [htmem]
    rintro ⟨i, hi⟩
    exact hxne i hi.symm
  let s := x ::ₘ (t + t)
  have hscard : s.card = 2 * n + 1 := by simp [s, t]; omega
  have hsmem (z : ℝ) (hz : z ∈ s) : z = x ∨ ∃ i, nodes i = z := by
    simpa [s, htmem] using hz
  apply exists_derivative_chain_zero_of_multiset (2 * n) F hcontinuous hderiv s hscard
  · intro z hz
    rcases hsmem z hz with rfl | ⟨i, rfl⟩
    · exact hx
    · exact hmem i
  · intro z hz k hk
    by_cases hzx : z = x
    · subst z
      have hcount : s.count x = 1 := by
        simp [s, Multiset.count_eq_zero.mpr hxnot]
      rw [hcount] at hk
      have : k = 0 := by omega
      simpa [this] using hxzero
    · obtain ⟨i, rfl⟩ := (hsmem z hz).resolve_left hzx
      have hcount : s.count (nodes i) ≤ 2 := by
        have ht := Multiset.nodup_iff_count_le_one.mp htnodup (nodes i)
        simp only [s, Multiset.count_cons, Multiset.count_add, hzx, ite_false]
        omega
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · exact (hzero i).1
      · exact (hzero i).2

end Quadrature
