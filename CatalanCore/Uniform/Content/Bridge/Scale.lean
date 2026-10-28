module

public import CatalanCore.Uniform.Measure.NV0

@[expose] public section

/-!
# Bridge from degree-unit content to scale-unit content (lane H, bridge)

`HasContent Fam Λd` measures `log den ≤ (Λd+ε) deg²`; `HasScaledContent Fam sc Λ` measures
`log den ≤ (Λ+ε) sc²`.  If `deg ≤ γ sc + K1` and `sc ≤ γ⁻¹ deg + K0` then `Λ = γ² Λd`.
-/

namespace CatalanCore.Uniform
open Real

theorem hasScaledContent_of_hasContent (Fam : PolyFamily) (sc : Fam.ι → ℕ)
    {Λd γ K0 K1 : ℝ} (h : HasContent Fam Λd) (hΛ : 0 ≤ Λd) (hγ : 0 < γ) (hK1 : 0 ≤ K1)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ γ * sc n + K1)
    (hsc : ∀ n, Fam.Adm n → (sc n : ℝ) ≤ γ⁻¹ * Fam.deg n + K0) :
    HasScaledContent Fam sc (γ ^ 2 * Λd) := by
  obtain ⟨den, hpos, hint, hlog⟩ := h
  refine ⟨den, hpos, hint, ?_⟩
  intro ε hε
  set δ : ℝ := min 1 (ε / (2 * (γ ^ 2 + 1))) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (γ ^ 2 + 1) ≤ ε / 2 := by
    have : δ ≤ ε / (2 * (γ ^ 2 + 1)) := min_le_right _ _
    calc δ * (γ ^ 2 + 1) ≤ ε / (2 * (γ ^ 2 + 1)) * (γ ^ 2 + 1) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = ε / 2 := by field_simp
  set η : ℝ := min 1 (ε / (2 * (Λd + 1))) with hη
  have hηpos : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : Λd * η ≤ ε / 2 := by
    have h1 : η ≤ ε / (2 * (Λd + 1)) := min_le_right _ _
    calc Λd * η ≤ (Λd + 1) * (ε / (2 * (Λd + 1))) :=
          mul_le_mul (by linarith) h1 hηpos.le (by linarith)
      _ = ε / 2 := by field_simp
  obtain ⟨N0, hN0⟩ := hlog δ hδpos
  set S1 : ℝ := (2 * γ * K1 + K1 ^ 2) / η with hS1
  set S2 : ℝ := (N0 : ℝ) / γ + K0 with hS2
  obtain ⟨R0, hR0⟩ := exists_nat_ge (max (max S1 S2) 1)
  refine ⟨R0, fun n hn hR => ?_⟩
  have hs : (R0 : ℝ) ≤ sc n := by exact_mod_cast hR
  have hM := hR0.trans hs
  have hs1 : S1 ≤ (sc n : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hs2 : S2 ≤ (sc n : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hs3 : (1:ℝ) ≤ (sc n : ℝ) := le_trans (le_max_right _ _) hM
  have hsc' := hsc n hn
  have hdeg' := hdeg n hn
  have hN : N0 ≤ Fam.deg n := by
    have h1 : (N0 : ℝ) ≤ Fam.deg n := by
      have : (N0 : ℝ) / γ ≤ γ⁻¹ * Fam.deg n := by
        have : (N0 : ℝ) / γ + K0 ≤ γ⁻¹ * Fam.deg n + K0 := by linarith
        linarith
      rw [inv_mul_eq_div] at this
      exact (div_le_div_iff_of_pos_right hγ).1 this
    exact_mod_cast h1
  have hlg := hN0 n hn hN
  have hd0 : (0 : ℝ) ≤ Fam.deg n := Nat.cast_nonneg _
  have hsq : (Fam.deg n : ℝ) ^ 2 ≤ (γ * sc n + K1) ^ 2 := by
    exact pow_le_pow_left₀ hd0 hdeg' 2
  have hK : (γ * sc n + K1) ^ 2 ≤ (γ ^ 2 + η) * (sc n : ℝ) ^ 2 := by
    have hη' : 2 * γ * K1 + K1 ^ 2 ≤ η * sc n := by
      have := (div_le_iff₀ hηpos).1 hs1
      linarith
    nlinarith [sq_nonneg (sc n : ℝ), mul_le_mul_of_nonneg_right hη' (by linarith : (0:ℝ) ≤ sc n)]
  have hpos2 : 0 ≤ Λd + δ := by linarith
  calc Real.log (den n) ≤ (Λd + δ) * (Fam.deg n : ℝ) ^ 2 := hlg
    _ ≤ (Λd + δ) * ((γ ^ 2 + η) * (sc n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (hsq.trans hK) hpos2
    _ ≤ (γ ^ 2 * Λd + ε) * (sc n : ℝ) ^ 2 := by
        have e1 : (Λd + δ) * (γ ^ 2 + η) ≤ γ ^ 2 * Λd + ε := by
          nlinarith [mul_le_mul_of_nonneg_left hη1 hδpos.le]
        calc (Λd + δ) * ((γ ^ 2 + η) * (sc n : ℝ) ^ 2)
            = ((Λd + δ) * (γ ^ 2 + η)) * (sc n : ℝ) ^ 2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right e1 (sq_nonneg _)

end CatalanCore.Uniform
