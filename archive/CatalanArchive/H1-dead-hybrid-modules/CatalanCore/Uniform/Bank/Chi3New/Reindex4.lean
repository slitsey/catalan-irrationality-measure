module

public import CatalanCore.Uniform.Content.Shape.Reindex

@[expose] public section
set_option Elab.async false

/-! Scale-four reindexing for the measure theorem (lane B, B3f): the analogue of
`measure_of_family_nv0_even` for families whose admissible members all sit at scales divisible by `4`
(`r = 4 s`; constants rescale `Λ ↦ 16 Λ`, `D ↦ 16 D`, `c ↦ 4 c`, `γ ↦ 4 γ`, so `γ c / (D - Λ)`
is unchanged). -/

namespace CatalanCore.Uniform
open Real

theorem measure_of_family_nv0_four (Fam : PolyFamily) (scale : Fam.ι → ℕ)
    {Λ D c γ K : ℝ} (hΛ : HasScaledContent Fam scale Λ)
    (hD : HasScaledDecay Fam scale D c) (hη : Λ < D) (hc : 0 < c)
    (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ γ * scale n + K)
    (hfour : ∀ n, Fam.Adm n → scale n % 4 = 0)
    (hnv : ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, Fam.Adm n ∧ scale n = 4 * s ∧ Fam.evalQ n x ≠ 0) :
    Fam.MeasureLB (γ * c / (D - Λ)) := by
  have hcast : ∀ n, Fam.Adm n → (scale n : ℝ) = 4 * ((scale n / 4 : ℕ) : ℝ) := by
    intro n hn
    have := hfour n hn
    exact_mod_cast (by omega : scale n = 4 * (scale n / 4))
  have hΛ' : HasScaledContent Fam (fun n => scale n / 4) (16 * Λ) := by
    obtain ⟨den, hpos, hint, hlog⟩ := hΛ
    refine ⟨den, hpos, hint, ?_⟩
    intro ε hε
    obtain ⟨R0, h⟩ := hlog (ε / 16) (by positivity)
    refine ⟨R0, fun n hn hr => ?_⟩
    have h1 := h n hn (by have := hfour n hn; have hr' : R0 ≤ scale n / 4 := hr; omega)
    rw [hcast n hn] at h1
    nlinarith [h1]
  have hD' : HasScaledDecay Fam (fun n => scale n / 4) (16 * D) (4 * c) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hD (ε / 16) (by positivity)
    refine ⟨R0, fun n hn hr t ht => ?_⟩
    have hs := hcast n hn
    have hs0 : (0 : ℝ) ≤ ((scale n / 4 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 := h n hn (by have := hfour n hn; have hr' : R0 ≤ scale n / 4 := hr; omega) t (by
      refine ht.trans (Real.exp_le_exp.2 ?_)
      rw [hs]
      nlinarith)
    refine h1.trans (le_of_eq ?_)
    congr 1
    rw [hs]
    ring
  have hnv' : HasNV0 Fam (fun n => scale n / 4) := by
    obtain ⟨R0, h⟩ := hnv
    refine ⟨R0, fun r hr x => ?_⟩
    obtain ⟨n, hn, hs, hne⟩ := h r hr x
    exact ⟨n, hn, by show scale n / 4 = r; omega, hne⟩
  have hdeg' : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ (4 * γ) * ((scale n / 4 : ℕ) : ℝ) + K := by
    intro n hn
    have := hdeg n hn
    rw [hcast n hn] at this
    linarith
  have key := measure_of_family_nv0 Fam (fun n => scale n / 4) hΛ' hD' (by linarith)
    (by positivity) (by positivity) hK hdeg' hnv'
  have hDL : 0 < D - Λ := sub_pos.2 hη
  have hexp : 4 * γ * (4 * c) / (16 * D - 16 * Λ) = γ * c / (D - Λ) := by
    rw [show 16 * D - 16 * Λ = 16 * (D - Λ) by ring]
    field_simp
    ring
  rw [hexp] at key
  exact key

end CatalanCore.Uniform
