import CatalanCore.Uniform.Content.BankShared.Normalise
set_option Elab.async false

/-! # Shared contract 2, continued (lane H17): decay transport and the block-family corollaries -/

namespace CatalanCore.Uniform.Content.BankShared
open Polynomial Finset CatalanCore CatalanCore.Rect CatalanCore.Uniform

/-- **Decay transport (shared contract 2).**  The scaled decay `D, c` of `Fam0` is the scaled decay
of the normalised family, with unchanged rates. -/
theorem normScale_hasScaledDecay (Fam0 : PolyFamily) (sc : Fam0.ι → ℕ) {D c : ℝ} {N : ℚ}
    (hN : N ≠ 0) (h : Fam0.ι → ℕ) (c1 : ℝ) (Q1 : Fam0.ι → ℚ[X])
    (hQ : ∀ i, Q1 i = C ((N⁻¹) ^ h i) * (Fam0.Q i).comp (C N * X))
    (hc1 : c1 = ((N⁻¹ : ℚ) : ℝ) * Fam0.const) {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hh : ∀ i, Fam0.Adm i → (h i : ℝ) ≤ A * sc i + K)
    (H : HasScaledDecay Fam0 sc D c) : HasScaledDecay (Fam0.reQ c1 Q1) sc D c := by
  intro ε hε
  obtain ⟨R0, hR0⟩ := H (ε / 2) (by positivity)
  set m : ℝ := max 1 |((N⁻¹ : ℚ) : ℝ)| with hm
  set Lh : ℝ := Real.log m with hLh
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm0 : 0 < m := by linarith
  have hLh0 : 0 ≤ Lh := Real.log_nonneg hm1
  set m' : ℝ := max 1 |(N : ℝ)| with hm'
  set Lm : ℝ := Real.log m' with hLm
  have hm'1 : 1 ≤ m' := le_max_left _ _
  have hm'0 : 0 < m' := by linarith
  obtain ⟨R2, hR2⟩ := affine_mul_le_sq A K Lh (ε / 2) hA hK hLh0 (by positivity)
  obtain ⟨R3, hR3⟩ := exists_nat_ge (2 * Lm / ε)
  refine ⟨max R0 (max R2 R3), fun i hi hR t ht => ?_⟩
  have hs0 : R0 ≤ sc i := (le_max_left _ _).trans hR
  have hs2 : R2 ≤ sc i := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hs3 : R3 ≤ sc i := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have hsc3 : 2 * Lm / ε ≤ sc i := hR3.trans (by exact_mod_cast hs3)
  have hLm' : Lm ≤ ε / 2 * sc i := by
    have := (div_le_iff₀ hε).1 hsc3
    linarith
  have hNN : (N : ℝ) * ((N⁻¹ : ℚ) : ℝ) = 1 := by
    have : (N : ℚ) * N⁻¹ = 1 := mul_inv_cancel₀ hN
    exact_mod_cast this
  have hnorm : |(N : ℝ) * t| ≤ Real.exp (-(c + ε / 2) * (sc i : ℝ)) := by
    have h1 : |(N : ℝ)| ≤ Real.exp Lm := by
      rw [hLm, Real.exp_log hm'0]; exact le_max_right _ _
    calc |(N : ℝ) * t| = |(N : ℝ)| * |t| := abs_mul _ _
      _ ≤ Real.exp Lm * Real.exp (-(c + ε) * (sc i : ℝ)) :=
          mul_le_mul h1 ht (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (Lm + -(c + ε) * (sc i : ℝ)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(c + ε / 2) * (sc i : ℝ)) := by
          apply Real.exp_le_exp.2
          nlinarith
  have hA0 := hR0 i hi hs0 ((N : ℝ) * t) hnorm
  have hconst : (Fam0.reQ c1 Q1).const = ((N⁻¹ : ℚ) : ℝ) * Fam0.const := hc1
  have hev := reQ_evalR Fam0 N h c1 Q1 hQ i (((N⁻¹ : ℚ) : ℝ) * Fam0.const + t)
  have hy : (N : ℝ) * (((N⁻¹ : ℚ) : ℝ) * Fam0.const + t) = Fam0.const + (N : ℝ) * t := by
    rw [mul_add, ← mul_assoc, hNN, one_mul]
  rw [hy] at hev
  rw [hconst, hev, abs_mul, abs_pow]
  have hpow : |((N⁻¹ : ℚ) : ℝ)| ^ h i ≤ Real.exp ((h i : ℝ) * Lh) := by
    rw [Real.exp_nat_mul, hLh, Real.exp_log hm0]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _
  have hhL : (h i : ℝ) * Lh ≤ ε / 2 * (sc i : ℝ) ^ 2 :=
    ((mul_le_mul_of_nonneg_right (hh i hi) hLh0)).trans (hR2 (sc i) hs2)
  calc |((N⁻¹ : ℚ) : ℝ)| ^ h i * |Fam0.evalR i (Fam0.const + (N : ℝ) * t)|
      ≤ Real.exp ((h i : ℝ) * Lh) * Real.exp (-(D - ε / 2) * (sc i : ℝ) ^ 2) :=
        mul_le_mul hpow hA0 (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((h i : ℝ) * Lh + -(D - ε / 2) * (sc i : ℝ) ^ 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(D - ε) * (sc i : ℝ) ^ 2) := by
        apply Real.exp_le_exp.2
        nlinarith

end CatalanCore.Uniform.Content.BankShared
