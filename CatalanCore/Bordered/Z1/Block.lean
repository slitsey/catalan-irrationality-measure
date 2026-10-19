module

public import CatalanCore.Bordered.Z1.ChainDvd
public import CatalanCore.Bordered.Z1.Bisp

/-!
# Z1.3 / Z1.4: divisibility of `u(X′, e_s)`, vanishing patterns at `θ = -c`.
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Bordered.Z1

/-- **Z1.3**: `(θ + c)^{chainOrd} ∣ u(X′, e_s)` in `ℚ[X]`. -/
theorem kdet_Xp_dvd (s m c : ℕ) (hc : 1 ≤ c) :
    (X + C (c : ℚ)) ^ chainOrd s m c ∣ kdet (Xp s m (X : ℚ[X])) (es ℚ[X] s) := by
  obtain ⟨ε, -, h⟩ := kdet_Xp_poly s m
  rw [h]
  exact (chain_dvd s m c hc).mul_left _

/-- Zero patterns of the off-diagonal entries of `X′(-c)`: both vanish exactly when
`c = k + 1` or `c = k + 1 + K`. -/
theorem Xup_neg_eq_zero_iff (s m k c : ℕ) (hk : k + 1 < s) :
    Xup s m (-(c : ℚ)) k = 0 ↔ ((k : ℚ) + 1 = c ∨ (k : ℚ) + 1 + ((s + m : ℕ) : ℚ) = c) := by
  have hs : (k + 1 : ℚ) < s := by exact_mod_cast hk
  have hp : qc (pj s m k) ≠ (0 : ℚ) := by
    simp only [qc, Algebra.algebraMap_self, RingHom.id_apply]; exact pj_ne s m k hk
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  unfold Xup
  rw [mul_eq_zero, neg_eq_zero, mul_eq_zero, mul_eq_zero, mul_eq_zero]
  constructor
  · rintro ((((h | h) | h) | h) | h)
    · exfalso; linarith
    · left; linarith
    · right; linarith
    · exfalso; linarith
    · exact absurd h hp
  · rintro (h | h)
    · left; left; left; right; linarith
    · left; left; right; linarith

theorem Xlow_neg_eq_zero_iff (s m k c : ℕ) (hk : k + 1 < s) :
    Xlow s m (-(c : ℚ)) k = 0 ↔ ((k : ℚ) + 1 = c ∨ (k : ℚ) + 1 + ((s + m : ℕ) : ℚ) = c) := by
  have hs : (k + 1 : ℚ) < s := by exact_mod_cast hk
  have hp : qc (1 / pj s m k) ≠ (0 : ℚ) := by
    simp only [qc, Algebra.algebraMap_self, RingHom.id_apply]
    exact one_div_ne_zero (pj_ne s m k hk)
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  unfold Xlow
  rw [mul_eq_zero, neg_eq_zero, mul_eq_zero, mul_eq_zero, mul_eq_zero]
  constructor
  · rintro ((((h | h) | h) | h) | h)
    · exfalso; linarith
    · left; linarith
    · exfalso; linarith
    · right; push_cast at h ⊢; linarith
    · exact absurd h hp
  · rintro (h | h)
    · left; left; left; right; linarith
    · left; right; push_cast at h ⊢; linarith

/-- `Λ₁, Λ₂` vanish at `θ = -c` exactly on `O_c = {j : j ≤ c ≤ j + K - 1}` (`j = k + 1`). -/
theorem poch_neg_eq_zero_iff (K j c : ℕ) :
    poch (-(c : ℚ)) K j = 0 ↔ (j ≤ c ∧ c < j + K) := by
  unfold poch
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨a, ha, h⟩
    have ha' := mem_range.1 ha
    have : ((j + a : ℕ) : ℚ) = c := by linarith
    have : j + a = c := by exact_mod_cast this
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨c - j, mem_range.2 (by omega), ?_⟩
    have : j + (c - j) = c := by omega
    rw [this]; ring

theorem Lam1_neg_eq_zero_iff (s m k c : ℕ) (hk : k < s) :
    Lam1 s m (-(c : ℚ)) k = 0 ↔ (k + 1 ≤ c ∧ c < k + 1 + (s + m)) := by
  have h1 := PiY_ne s m (k + 1) (by omega)
  have h2 := omegaP_ne s (k + 1)
  unfold Lam1
  simp only [qc, Algebra.algebraMap_self, RingHom.id_apply, mul_eq_zero]
  rw [poch_neg_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (one_div_ne_zero (mul_ne_zero h1 h2))
    · exact h
  · exact Or.inr

theorem Lam2_neg_eq_zero_iff (s m k c : ℕ) (hk : k < s) :
    Lam2 s m (-(c : ℚ)) k = 0 ↔ (k + 1 ≤ c ∧ c < k + 1 + (s + m)) := by
  have h1 := PiX_ne s m (k + 1) (by omega)
  have h2 := omegaP_ne s (k + 1)
  unfold Lam2
  simp only [qc, Algebra.algebraMap_self, RingHom.id_apply, mul_eq_zero]
  rw [poch_neg_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (one_div_ne_zero (mul_ne_zero h1 h2))
    · exact h
  · exact Or.inr

/-- **Z1.1a**: at `θ > 0`, `A` is the Cauchy Gram `C_GᵀΩC_G`, `Ω_a = ρ_a (x_a+1)_s²`. -/
theorem Amat_cauchy (s m : ℕ) (θ : ℚ) (hθ : 0 < θ) (i j : Fin s) :
    Amat s m θ i j = ∑ a : Fin (s + m),
      (rho s m θ a * Pn s (θ + ((a : ℕ) : ℚ)) ^ 2) /
        ((θ + ((a : ℕ) : ℚ) + (((i : ℕ) : ℚ) + 1)) * (θ + ((a : ℕ) : ℚ) + (((j : ℕ) : ℚ) + 1))) := by
  rw [Amat, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  have ha : (0 : ℚ) ≤ ((a : ℕ) : ℚ) := Nat.cast_nonneg _
  have hi : (0 : ℚ) ≤ ((i : ℕ) : ℚ) := Nat.cast_nonneg _
  have hj : (0 : ℚ) ≤ ((j : ℕ) : ℚ) := Nat.cast_nonneg _
  have gi : lag s (θ + ((a : ℕ) : ℚ)) i = Pn s (θ + ((a : ℕ) : ℚ)) / (θ + ((a : ℕ) : ℚ) + (((i : ℕ) : ℚ) + 1)) :=
    lag_eq' s _ i.2 _ (by push_cast; ring) (by linarith)
  have gj : lag s (θ + ((a : ℕ) : ℚ)) j = Pn s (θ + ((a : ℕ) : ℚ)) / (θ + ((a : ℕ) : ℚ) + (((j : ℕ) : ℚ) + 1)) :=
    lag_eq' s _ j.2 _ (by push_cast; ring) (by linarith)
  show lag s (θ + ((a : ℕ) : ℚ)) i * rho s m θ a * lag s (θ + ((a : ℕ) : ℚ)) j = _
  rw [gi, gj]
  have n1 : θ + ((a : ℕ) : ℚ) + (((i : ℕ) : ℚ) + 1) ≠ 0 := by linarith
  have n2 : θ + ((a : ℕ) : ℚ) + (((j : ℕ) : ℚ) + 1) ≠ 0 := by linarith
  field_simp

end CatalanCore.Bordered.Z1
