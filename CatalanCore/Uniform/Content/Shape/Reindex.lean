module

public import CatalanCore.Uniform.Measure.NV0

@[expose] public section

/-!
# Even-scale reindexing for the measure theorem (lane H7)

If the admissible members all sit at even scale `r = 2 s` (the only scales where the alternating
geometry is hybrid-shaped), the measure theorem holds with the same exponent:
with `s = r / 2` the constants rescale as `Λ ↦ 4Λ`, `D ↦ 4D`, `c ↦ 2c`, `γ ↦ 2γ`, so
`μ = γ c / (D - Λ)` is unchanged.  Only members at even scales `2s`, `s ≥ R0`, are required for
`HasNV0`-type nonvanishing.
-/

namespace CatalanCore.Uniform
open Real

/-- The family with the admissibility predicate further restricted to `P`. -/
def _root_.CatalanCore.PolyFamily.restrictAdm (Fam : PolyFamily) (P : Fam.ι → Prop) : PolyFamily :=
  { Fam with Adm := fun n => Fam.Adm n ∧ P n }

theorem measure_of_family_nv0_even (Fam : PolyFamily) (scale : Fam.ι → ℕ)
    {Λ D c γ K : ℝ} (hΛ : HasScaledContent Fam scale Λ)
    (hD : HasScaledDecay Fam scale D c) (hη : Λ < D) (hc : 0 < c)
    (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ γ * scale n + K)
    (heven : ∀ n, Fam.Adm n → scale n % 2 = 0)
    (hnv : ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, Fam.Adm n ∧ scale n = 2 * s ∧ Fam.evalQ n x ≠ 0) :
    Fam.MeasureLB (γ * c / (D - Λ)) := by
  have hcast : ∀ n, Fam.Adm n → (scale n : ℝ) = 2 * ((scale n / 2 : ℕ) : ℝ) := by
    intro n hn
    have := heven n hn
    exact_mod_cast (by omega : scale n = 2 * (scale n / 2))
  have hΛ' : HasScaledContent Fam (fun n => scale n / 2) (4 * Λ) := by
    obtain ⟨den, hpos, hint, hlog⟩ := hΛ
    refine ⟨den, hpos, hint, ?_⟩
    intro ε hε
    obtain ⟨R0, h⟩ := hlog (ε / 4) (by positivity)
    refine ⟨R0, fun n hn hr => ?_⟩
    have h1 := h n hn (by have := heven n hn; have hr' : R0 ≤ scale n / 2 := hr; omega)
    rw [hcast n hn] at h1
    nlinarith [h1]
  have hD' : HasScaledDecay Fam (fun n => scale n / 2) (4 * D) (2 * c) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hD (ε / 4) (by positivity)
    refine ⟨R0, fun n hn hr t ht => ?_⟩
    have hs := hcast n hn
    have hs0 : (0 : ℝ) ≤ ((scale n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 := h n hn (by have := heven n hn; have hr' : R0 ≤ scale n / 2 := hr; omega) t (by
      refine ht.trans (Real.exp_le_exp.2 ?_)
      rw [hs]
      nlinarith)
    refine h1.trans (le_of_eq ?_)
    congr 1
    rw [hs]
    ring
  have hnv' : HasNV0 Fam (fun n => scale n / 2) := by
    obtain ⟨R0, h⟩ := hnv
    refine ⟨R0, fun r hr x => ?_⟩
    obtain ⟨n, hn, hs, hne⟩ := h r hr x
    exact ⟨n, hn, by show scale n / 2 = r; omega, hne⟩
  have hdeg' : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ (2 * γ) * ((scale n / 2 : ℕ) : ℝ) + K := by
    intro n hn
    have := hdeg n hn
    rw [hcast n hn] at this
    linarith
  have key := measure_of_family_nv0 Fam (fun n => scale n / 2) hΛ' hD' (by linarith)
    (by positivity) (by positivity) hK hdeg' hnv'
  have hDL : 0 < D - Λ := sub_pos.2 hη
  have hexp : 2 * γ * (2 * c) / (4 * D - 4 * Λ) = γ * c / (D - Λ) := by
    rw [show 4 * D - 4 * Λ = 4 * (D - Λ) by ring]
    field_simp
    ring
  rw [hexp] at key
  exact key

end CatalanCore.Uniform
