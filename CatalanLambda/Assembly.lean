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

end Assembly
end CatalanLambda
