module

public import CatalanLambda.Mirror.NVEntries

@[expose] public section

/-!
# Mirror constant: nonvanishing, part 2 (Schur complement and the three-`h` theorem)
-/

open Finset Matrix

namespace CatalanLambda.Mirror

section Assembly
variable {ℓ : ℕ} [Fact ℓ.Prime] {K : ℕ}

/-- the scaled matrix `D (r I + N₀) D`. -/
noncomputable def Nq (ℓ K h : ℕ) (r : ℚ) : Matrix (Fin h) (Fin h) ℚ :=
  Matrix.of fun a b => Dq ℓ K a * Dq ℓ K b * ((if a = b then r else 0) + N0n a b)

lemma Nq_eq (ℓ K h : ℕ) (r : ℚ) : Nq ℓ K h r =
    Matrix.diagonal (fun a : Fin h => Dq ℓ K a) * (r • (1 : Matrix (Fin h) (Fin h) ℚ) + N0 h) *
      Matrix.diagonal (fun a : Fin h => Dq ℓ K a) := by
  ext a b
  simp only [Nq, N0, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

lemma det_Nq (ℓ K h : ℕ) (r : ℚ) :
    (Nq ℓ K h r).det = (∏ a : Fin h, Dq ℓ K a) ^ 2 * Pbar h r := by
  rw [Nq_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  unfold Pbar
  ring

/-- the low-low block -/
noncomputable def Xm (ℓ K : ℕ) [Fact ℓ.Prime] (rb : ZMod ℓ) : Matrix (Fin K) (Fin K) (ZMod ℓ) :=
  Matrix.of fun a b => (if a = b then rb else 0) -
    ((if a = b then cc ℓ K else 0) + G ℓ K a b) / 16

/-- the low-high block -/
noncomputable def Bm (ℓ K m : ℕ) [Fact ℓ.Prime] : Matrix (Fin K) (Fin m) (ZMod ℓ) :=
  Matrix.of fun a c => 1 / (4 * ((((K + c : ℕ)) : ZMod ℓ) - ((a : ℕ) : ZMod ℓ)))

/-- the negated reduced block matrix -/
noncomputable def Tm (ℓ K m : ℕ) [Fact ℓ.Prime] (rb : ZMod ℓ) :
    Matrix (Fin K ⊕ Fin m) (Fin K ⊕ Fin m) (ZMod ℓ) :=
  Matrix.fromBlocks (-(Xm ℓ K rb)) (-(Bm ℓ K m)) (-(Bm ℓ K m)ᵀ) 1

lemma entries_good (hlK : ℓ + 3 = 4 * K) {h m : ℕ} (hKm : K + m = h) (hhl : h ≤ ℓ)
    {r : ℚ} {rb : ZMod ℓ} (hr : Good ℓ r rb) (i j : Fin K ⊕ Fin m) :
    Good ℓ (-((Nq ℓ K h r).submatrix (eq' K m h hKm) (eq' K m h hKm) i j))
      (Tm ℓ K m rb i j) := by
  rcases i with a | c <;> rcases j with b | d
  · have ha := a.2
    have hb := b.2
    simp only [Tm, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Nq, Matrix.of_apply, eq'_inl, Dq,
      if_pos ha, if_pos hb, Xm, Equiv.apply_eq_iff_eq, Sum.inl.injEq, Matrix.neg_apply]
    by_cases hab : a = b
    · subst hab
      simp only [if_true, one_mul]
      exact ((hr.add (entry_ll_diag hlK ha)).neg).congr (by ring)
    · simp only [if_neg hab, zero_add, one_mul]
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
      · exact (entry_ll_off hlK hlt hb).neg.congr (by ring)
      · rw [N0n_comm, G_comm]; exact (entry_ll_off hlK hgt ha).neg.congr (by ring)
  · have ha := a.2
    have hd := d.2
    have hdl : K + (d : ℕ) < ℓ := by omega
    simp only [Tm, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Nq, Matrix.of_apply, eq'_inl,
      eq'_inr, Dq, if_pos ha, if_neg (show ¬ (K + (d : ℕ) < K) by omega), Bm,
      Equiv.apply_eq_iff_eq, reduceCtorEq, if_false, one_mul, zero_add, Matrix.neg_apply]
    exact (entry_lh hlK ha (by omega) hdl).neg
  · have hb := b.2
    have hc := c.2
    have hcl : K + (c : ℕ) < ℓ := by omega
    simp only [Tm, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply, Nq,
      Matrix.of_apply, eq'_inl, eq'_inr, Dq, if_pos hb, if_neg (show ¬ (K + (c : ℕ) < K) by omega),
      Bm, Equiv.apply_eq_iff_eq, reduceCtorEq, if_false, mul_one, zero_add, Matrix.neg_apply]
    rw [N0n_comm]
    exact (entry_lh hlK hb (by omega) hcl).neg
  · have hc := c.2
    have hd := d.2
    have hcl : K + (c : ℕ) < ℓ := by omega
    have hdl : K + (d : ℕ) < ℓ := by omega
    simp only [Tm, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Nq, Matrix.of_apply, eq'_inr,
      Dq, if_neg (show ¬ (K + (c : ℕ) < K) by omega), if_neg (show ¬ (K + (d : ℕ) < K) by omega),
      Equiv.apply_eq_iff_eq, Sum.inr.injEq, Matrix.one_apply]
    by_cases hcd : c = d
    · subst hcd
      simp only [if_true]
      exact (entry_hh_diag hlK (by omega) hcl hr).neg.congr (by ring)
    · simp only [if_neg hcd, zero_add]
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hcd) with hlt | hgt
      · exact (entry_hh_off hlK (by omega) (by omega) hdl).neg.congr (by simp)
      · rw [N0n_comm]; exact (entry_hh_off hlK (by omega) (by omega) hcl).neg.congr (by simp)

lemma Bsum (hlK : ℓ + 3 = 4 * K) {m s h : ℕ} (hKm : K + m = h) (hs : s = ℓ - h) (hhl : h ≤ ℓ)
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

lemma schur_eq (hlK : ℓ + 3 = 4 * K) {m s h : ℕ} (hKm : K + m = h) (hs : s = ℓ - h) (hhl : h ≤ ℓ)
    (rb : ZMod ℓ) :
    -(Xm ℓ K rb) - Bm ℓ K m * (Bm ℓ K m)ᵀ =
      (1 / 16 : ZMod ℓ) • ((cc ℓ K - 16 * rb) • (1 : Matrix (Fin K) (Fin K) (ZMod ℓ)) +
        Cm ℓ K s * (Cm ℓ K s)ᵀ) := by
  ext a b
  have h16 := sixteen_ne hlK
  have hC : (Cm ℓ K s * (Cm ℓ K s)ᵀ) a b = Gs ℓ s a b := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Cm, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun j => 1 / (((a : ℕ) : ZMod ℓ) + 1 + (j : ℕ)) *
      (1 / (((b : ℕ) : ZMod ℓ) + 1 + (j : ℕ)))) s]
    unfold Gs
    exact Finset.sum_congr rfl fun j _ => one_div_mul_one_div _ _
  have hB : (Bm ℓ K m * (Bm ℓ K m)ᵀ) a b = (G ℓ K a b - Gs ℓ s a b) / 16 := by
    rw [Matrix.mul_apply]
    simpa only [Matrix.transpose_apply] using Bsum hlK hKm hs hhl a b
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply, hB, hC, Xm,
    Matrix.of_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hab : a = b
  · simp only [hab, if_true, mul_one]
    field_simp
    ring
  · simp only [hab, if_false, mul_zero, zero_add]
    field_simp
    ring

theorem key_det (hlK : ℓ + 3 = 4 * K) (hK : 2 ≤ K) {h : ℕ} (hh1 : K + 1 ≤ h) (hh2 : h ≤ ℓ - 1)
    {r : ℚ} (hr : r ∈ S ℓ) (hP : Pbar h r = 0) :
    ((cc ℓ K - 16 * red ℓ r) • (1 : Matrix (Fin K) (Fin K) (ZMod ℓ)) +
      Cm ℓ K (ℓ - h) * (Cm ℓ K (ℓ - h))ᵀ).det = 0 := by
  obtain ⟨m, hm⟩ : ∃ m, K + m = h := ⟨h - K, by omega⟩
  have hgood : Good ℓ r (red ℓ r) := ⟨hr, rfl⟩
  have hdet := red_det (-((Nq ℓ K h r).submatrix (eq' K m h hm) (eq' K m h hm)))
    (Tm ℓ K m (red ℓ r))
    (fun i j => by simpa using entries_good hlK hm (by omega) hgood i j)
  rw [Matrix.det_neg, Matrix.det_submatrix_equiv_self, det_Nq, hP, mul_zero, mul_zero] at hdet
  have h0 : (Tm ℓ K m (red ℓ r)).det = 0 := by
    have := hdet.2
    simpa [red] using this.symm
  unfold Tm at h0
  rw [Matrix.det_fromBlocks_one₂₂, Matrix.neg_mul, Matrix.mul_neg, neg_neg, schur_eq hlK hm rfl (by omega), Matrix.det_smul] at h0
  have h16 := sixteen_ne hlK
  rcases mul_eq_zero.1 h0 with h | h
  · exfalso
    exact (pow_ne_zero _ (one_div_ne_zero h16)) h
  · exact h

/-- **Mirror Theorem 1 (three `h`).**  Let `ℓ ≡ 1 (mod 4)` be a prime, `ℓ ≥ 13`, and `r ∈ ℚ` with
`ℓ ∤ den r`.  Then at least one of `P̄_{ℓ-1}(r)`, `P̄_{ℓ-2}(r)`, `P̄_{(3ℓ-3)/4}(r)` is nonzero. -/
theorem mirror_nonvanishing (ℓ : ℕ) [Fact ℓ.Prime] (h1 : ℓ % 4 = 1) (h13 : 13 ≤ ℓ) (r : ℚ)
    (hr : ¬ ℓ ∣ r.den) :
    Pbar (ℓ - 1) r ≠ 0 ∨ Pbar (ℓ - 2) r ≠ 0 ∨ Pbar ((3 * ℓ - 3) / 4) r ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨c1, c2, c3⟩ := hcon
  obtain ⟨K, hK⟩ : ∃ K, ℓ + 3 = 4 * K := ⟨(ℓ + 3) / 4, by omega⟩
  have hrS : r ∈ S ℓ := hr
  have k1 := key_det hK (by omega) (h := ℓ - 1) (by omega) (by omega) hrS c1
  have k2 := key_det hK (by omega) (h := ℓ - 2) (by omega) (by omega) hrS c2
  have k3 := key_det hK (by omega) (h := (3 * ℓ - 3) / 4) (by omega) (by omega) hrS c3
  have e1 : ℓ - (ℓ - 1) = 1 := by omega
  have e2 : ℓ - (ℓ - 2) = 2 := by omega
  have e3 : ℓ - (3 * ℓ - 3) / 4 = K := by omega
  rw [e1] at k1
  rw [e2] at k2
  rw [e3] at k3
  exact no_triple K (by omega) (by omega) (by omega) _ k1 k2 k3

end Assembly

end CatalanLambda.Mirror
