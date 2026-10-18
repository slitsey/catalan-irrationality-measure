import CatalanLambda.Entries
import CatalanLambda.Alg

open Finset Matrix

namespace CatalanLambda

section Assembly
variable {ℓ : ℕ} [Fact ℓ.Prime] {K : ℕ}

/-- scaling `D = diag(1_low, ℓ_high)` -/
def Dq (ℓ K : ℕ) (a : ℕ) : ℚ := if a < K then 1 else ℓ

/-- the scaled matrix `D (r I + M0) D`. -/
noncomputable def Nq (ℓ K h : ℕ) (r : ℚ) : Matrix (Fin h) (Fin h) ℚ :=
  Matrix.of fun a b => Dq ℓ K a * Dq ℓ K b * ((if a = b then r else 0) + M0n a b)

lemma Nq_eq (ℓ K h : ℕ) (r : ℚ) : Nq ℓ K h r =
    Matrix.diagonal (fun a : Fin h => Dq ℓ K a) * (r • (1 : Matrix (Fin h) (Fin h) ℚ) + M0 h) *
      Matrix.diagonal (fun a : Fin h => Dq ℓ K a) := by
  ext a b
  simp only [Nq, M0, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

lemma det_Nq (ℓ K h : ℕ) (r : ℚ) :
    (Nq ℓ K h r).det = (∏ a : Fin h, Dq ℓ K a) ^ 2 * P h r := by
  rw [Nq_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  unfold P
  ring

/-- the low-low block -/
noncomputable def Xm (ℓ K : ℕ) [Fact ℓ.Prime] (rb : ZMod ℓ) : Matrix (Fin K) (Fin K) (ZMod ℓ) :=
  Matrix.of fun a b => (if a = b then rb else 0) +
    ((if a = b then cc ℓ K else 0) + G ℓ K a b) / 16

/-- the low-high block -/
noncomputable def Bm (ℓ K m : ℕ) [Fact ℓ.Prime] : Matrix (Fin K) (Fin m) (ZMod ℓ) :=
  Matrix.of fun a c => -(1 / (4 * ((((K + c : ℕ)) : ZMod ℓ) - ((a : ℕ) : ZMod ℓ))))

noncomputable def eq' (K m h : ℕ) (hKm : K + m = h) : Fin K ⊕ Fin m ≃ Fin h :=
  finSumFinEquiv.trans (finCongr hKm)

lemma eq'_inl (K m h : ℕ) (hKm : K + m = h) (a : Fin K) :
    ((eq' K m h hKm (Sum.inl a) : Fin h) : ℕ) = a := by
  simp [eq']

lemma eq'_inr (K m h : ℕ) (hKm : K + m = h) (c : Fin m) :
    ((eq' K m h hKm (Sum.inr c) : Fin h) : ℕ) = K + c := by
  simp [eq']

lemma entries_good (hlK : ℓ + 1 = 4 * K) {h m : ℕ} (hKm : K + m = h) (hhl : h ≤ ℓ)
    {r : ℚ} {rb : ZMod ℓ} (hr : Good ℓ r rb) (i j : Fin K ⊕ Fin m) :
    Good ℓ ((Nq ℓ K h r).submatrix (eq' K m h hKm) (eq' K m h hKm) i j)
      ((Matrix.fromBlocks (Xm ℓ K rb) (Bm ℓ K m) (Bm ℓ K m)ᵀ 1) i j) := by
  have hlt := fun (c : Fin m) => (eq' K m h hKm (Sum.inr c)).2
  rcases i with a | c <;> rcases j with b | d
  · have ha := a.2
    have hb := b.2
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Nq, Matrix.of_apply, eq'_inl, Dq,
      if_pos ha, if_pos hb, Xm, Equiv.apply_eq_iff_eq, Sum.inl.injEq]
    by_cases hab : a = b
    · subst hab
      simp only [if_true, one_mul]
      exact hr.add (entry_ll_diag hlK ha)
    · simp only [if_neg hab, zero_add, one_mul]
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
      · exact entry_ll_off hlK hlt hb
      · rw [M0n_comm, G_comm]; exact entry_ll_off hlK hgt ha
  · have ha := a.2
    have hd := d.2
    have hdl : K + (d : ℕ) < ℓ := by omega
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Nq, Matrix.of_apply, eq'_inl,
      eq'_inr, Dq, if_pos ha, if_neg (show ¬ (K + (d : ℕ) < K) by omega), Bm,
      Equiv.apply_eq_iff_eq, reduceCtorEq, if_false, one_mul, zero_add]
    exact entry_lh hlK ha (by omega) hdl
  · have hb := b.2
    have hc := c.2
    have hcl : K + (c : ℕ) < ℓ := by omega
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply, Nq,
      Matrix.of_apply, eq'_inl, eq'_inr, Dq, if_pos hb, if_neg (show ¬ (K + (c : ℕ) < K) by omega),
      Bm, Equiv.apply_eq_iff_eq, reduceCtorEq, if_false, mul_one, zero_add]
    rw [M0n_comm]
    exact entry_lh hlK hb (by omega) hcl
  · have hc := c.2
    have hd := d.2
    have hcl : K + (c : ℕ) < ℓ := by omega
    have hdl : K + (d : ℕ) < ℓ := by omega
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Nq, Matrix.of_apply, eq'_inr,
      Dq, if_neg (show ¬ (K + (c : ℕ) < K) by omega), if_neg (show ¬ (K + (d : ℕ) < K) by omega),
      Equiv.apply_eq_iff_eq, Sum.inr.injEq, Matrix.one_apply]
    by_cases hcd : c = d
    · subst hcd
      simp only [if_true]
      exact entry_hh_diag hlK (by omega) hcl hr
    · simp only [if_neg hcd, zero_add]
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hcd) with hlt | hgt
      · exact entry_hh_off hlK (by omega) (by omega) hdl
      · rw [M0n_comm]; exact entry_hh_off hlK (by omega) (by omega) hcl

/-- truncated sum `Gs s a b = ∑_{j=1}^s 1/((a+j)(b+j))`. -/
noncomputable def Gs (ℓ s a b : ℕ) [Fact ℓ.Prime] : ZMod ℓ :=
  ∑ t ∈ range s, 1 / ((((a : ℕ) : ZMod ℓ) + 1 + (t : ℕ)) * (((b : ℕ) : ZMod ℓ) + 1 + (t : ℕ)))

lemma G_eq_Gs (a b : ℕ) : G ℓ K a b = Gs ℓ (ℓ - K) a b := rfl

/-- shifted summand -/
noncomputable def Fa (ℓ : ℕ) [Fact ℓ.Prime] (s a b t : ℕ) : ZMod ℓ :=
  1 / ((((a : ℕ) : ZMod ℓ) + 1 + ((s + t : ℕ) : ZMod ℓ)) *
    (((b : ℕ) : ZMod ℓ) + 1 + ((s + t : ℕ) : ZMod ℓ)))

lemma Bsum (hlK : ℓ + 1 = 4 * K) {m s h : ℕ} (hKm : K + m = h) (hs : s = ℓ - h) (hhl : h ≤ ℓ)
    (a b : Fin K) :
    ∑ c : Fin m, Bm ℓ K m a c * Bm ℓ K m b c = (G ℓ K a b - Gs ℓ s a b) / 16 := by
  have hN : ℓ - K = s + m := by omega
  have hKl : K ≤ ℓ := by omega
  have hsplit : G ℓ K a b = Gs ℓ s a b + ∑ t ∈ range m, Fa ℓ s a b t := by
    rw [G_eq_Gs, hN]
    unfold Gs
    rw [Finset.sum_range_add]
    rfl
  have hrefl := Finset.sum_range_reflect (Fa ℓ s a b) m
  have key : ∀ c : Fin m, Bm ℓ K m a c * Bm ℓ K m b c = (1 / 16) * Fa ℓ s a b (m - 1 - c) := by
    intro c
    have hcm := c.2
    obtain ⟨t, ht⟩ : ∃ t, t = s + (m - 1 - (c : ℕ)) := ⟨_, rfl⟩
    have hnat : t + 1 + (c : ℕ) = ℓ - K := by omega
    have hcast : (t : ZMod ℓ) + 1 + ((c : ℕ) : ZMod ℓ) = -(K : ZMod ℓ) := by
      have := congrArg (Nat.cast : ℕ → ZMod ℓ) hnat
      push_cast at this
      rw [N_cast hKl] at this
      exact_mod_cast this
    unfold Fa
    rw [← ht]
    simp only [Bm, Matrix.of_apply]
    push_cast
    have e1 : (a : ZMod ℓ) + 1 + t = -((K : ZMod ℓ) + c - a) := by linear_combination hcast
    have e2 : (b : ZMod ℓ) + 1 + t = -((K : ZMod ℓ) + c - b) := by linear_combination hcast
    rw [e1, e2]
    field_simp
    ring
  have hfin : ∑ c : Fin m, Bm ℓ K m a c * Bm ℓ K m b c =
      ∑ c : Fin m, (1 / 16 : ZMod ℓ) * Fa ℓ s a b (m - 1 - (c : ℕ)) :=
    Finset.sum_congr rfl (fun c _ => key c)
  rw [hfin, Fin.sum_univ_eq_sum_range (fun c => (1 / 16 : ZMod ℓ) * Fa ℓ s a b (m - 1 - c)) m,
    ← Finset.mul_sum, hrefl, hsplit]
  ring

lemma schur_eq (hlK : ℓ + 1 = 4 * K) {m s h : ℕ} (hKm : K + m = h) (hs : s = ℓ - h) (hhl : h ≤ ℓ)
    (rb : ZMod ℓ) :
    Xm ℓ K rb - Bm ℓ K m * (Bm ℓ K m)ᵀ =
      (1 / 16 : ZMod ℓ) • ((16 * rb + cc ℓ K) • (1 : Matrix (Fin K) (Fin K) (ZMod ℓ)) +
        Cm ℓ K s * (Cm ℓ K s)ᵀ) := by
  ext a b
  have h4 := four_ne (ℓ := ℓ) hlK
  have h16 : (16 : ZMod ℓ) ≠ 0 := by
    have : (16 : ZMod ℓ) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h4 h4
  have hC : (Cm ℓ K s * (Cm ℓ K s)ᵀ) a b = Gs ℓ s a b := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Cm, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun j => 1 / (((a : ℕ) : ZMod ℓ) + 1 + (j : ℕ)) *
      (1 / (((b : ℕ) : ZMod ℓ) + 1 + (j : ℕ)))) s]
    unfold Gs
    exact Finset.sum_congr rfl fun j _ => one_div_mul_one_div _ _
  have hB : (Bm ℓ K m * (Bm ℓ K m)ᵀ) a b = (G ℓ K a b - Gs ℓ s a b) / 16 := by
    rw [Matrix.mul_apply]
    simpa only [Matrix.transpose_apply] using Bsum hlK hKm hs hhl a b
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, hB, hC, Xm, Matrix.of_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases hab : a = b
  · simp only [hab, if_true, mul_one]
    field_simp
    ring
  · simp only [hab, if_false, mul_zero, zero_add]
    field_simp
    ring

theorem key_det (hlK : ℓ + 1 = 4 * K) (hK : 2 ≤ K) {h : ℕ} (hh1 : K + 1 ≤ h) (hh2 : h ≤ ℓ - 1)
    {r : ℚ} (hr : r ∈ S ℓ) (hP : P h r = 0) :
    ((16 * red ℓ r + cc ℓ K) • (1 : Matrix (Fin K) (Fin K) (ZMod ℓ)) +
      Cm ℓ K (ℓ - h) * (Cm ℓ K (ℓ - h))ᵀ).det = 0 := by
  obtain ⟨m, hm⟩ : ∃ m, K + m = h := ⟨h - K, by omega⟩
  have hgood : Good ℓ r (red ℓ r) := ⟨hr, rfl⟩
  have hdet := red_det ((Nq ℓ K h r).submatrix (eq' K m h hm) (eq' K m h hm))
    (Matrix.fromBlocks (Xm ℓ K (red ℓ r)) (Bm ℓ K m) (Bm ℓ K m)ᵀ 1)
    (fun i j => entries_good hlK hm (by omega) hgood i j)
  rw [Matrix.det_submatrix_equiv_self, det_Nq, hP, mul_zero] at hdet
  have h0 : (Matrix.fromBlocks (Xm ℓ K (red ℓ r)) (Bm ℓ K m) (Bm ℓ K m)ᵀ 1).det = 0 := by
    have := hdet.2
    simpa [red] using this.symm
  rw [Matrix.det_fromBlocks_one₂₂, schur_eq hlK hm rfl (by omega), Matrix.det_smul] at h0
  have h4 := four_ne (ℓ := ℓ) hlK
  have h16 : (16 : ZMod ℓ) ≠ 0 := by
    have : (16 : ZMod ℓ) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h4 h4
  rcases mul_eq_zero.1 h0 with h | h
  · exfalso
    exact (pow_ne_zero _ (one_div_ne_zero h16)) h
  · exact h

end Assembly
end CatalanLambda
