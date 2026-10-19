module

public import CatalanCore.Measure.Core

@[expose] public section

/-!
# Rational form of the measure deduction, and the round-exponent helper

`measure_of_family` : the final shape `Fam.MeasureLB (measureExp c Λ D g₁ g₂ R.s)`;
`measure_of_family_le` : any rational `E' ≥ measureExp …` (rounding, e.g. 77.28 ≤ 78) also works.
Final theorems of instances are then `measure_of_family_le … (by norm_num [measureExp, …])`.
-/

namespace CatalanCore

namespace PolyFamily

/-- A measure statement may be weakened to a larger exponent. -/
theorem MeasureLB.mono {Fam : PolyFamily} {E E' : ℝ} (hE : E ≤ E') (h : Fam.MeasureLB E) :
    Fam.MeasureLB E' := by
  intro e he
  obtain ⟨q₀, H⟩ := h e he
  refine ⟨max q₀ 1, fun p q hq hcop => lt_of_le_of_lt ?_ (H p q (le_trans (le_max_left _ _) hq) hcop)⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_right _ _) hq
  exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)

end PolyFamily

namespace Measure

theorem measure_of_familyC (Fam : PolyFamily) {c Λ D g₁ g₂ s : ℚ}
    (hΛ : HasContent Fam (Λ : ℝ)) (hD : HasDecay Fam (D : ℝ) (c : ℝ)) (hη : Λ < D) (hc : 0 < c)
    {Cls : ℕ → Prop} {Bad : ℕ → ℕ → Prop} (hs : 0 < s) (hg : 0 < g₁ ∧ g₁ ≤ g₂)
    (hNV : HasNVC Fam Cls Bad (g₁ : ℝ) (g₂ : ℝ)) (hwin : HasWindowC Cls Bad (s : ℝ)) :
    Fam.MeasureLB ((measureExp c Λ D g₁ g₂ s : ℚ) : ℝ) := by
  intro e he
  obtain ⟨q₀, H⟩ := measure_of_family_realC Fam hΛ hD (by exact_mod_cast hη) (by exact_mod_cast hc)
    (by exact_mod_cast hs) ⟨by exact_mod_cast hg.1, by exact_mod_cast hg.2⟩ hNV hwin he
  refine ⟨q₀, fun p q hq hcop => ?_⟩
  have := H p q hq hcop
  have hcast : ((measureExp c Λ D g₁ g₂ s : ℚ) : ℝ) =
      (c : ℝ) * ((g₂ : ℝ) / ((g₁ : ℝ) * ((D : ℝ) - (Λ : ℝ))) + (g₂ : ℝ) * (s : ℝ)) := by
    unfold measureExp; push_cast; ring
  rw [hcast]; exact this

theorem measure_of_family (Fam : PolyFamily) {c Λ D g₁ g₂ : ℚ}
    (hΛ : HasContent Fam (Λ : ℝ)) (hD : HasDecay Fam (D : ℝ) (c : ℝ)) (hη : Λ < D) (hc : 0 < c)
    (R : PrimeRule) (hs : 0 < R.s) (hg : 0 < g₁ ∧ g₁ ≤ g₂)
    (hNV : HasNV Fam R (g₁ : ℝ) (g₂ : ℝ)) (hwin : R.HasWindow) :
    Fam.MeasureLB ((measureExp c Λ D g₁ g₂ R.s : ℚ) : ℝ) :=
  measure_of_familyC Fam hΛ hD hη hc hs hg hNV.toC (PrimeRule.hasWindowC R hwin)

/-- Rounding helper, generic prime class (G3). -/
theorem measure_of_family_leC (Fam : PolyFamily) {c Λ D g₁ g₂ s E' : ℚ}
    (hΛ : HasContent Fam (Λ : ℝ)) (hD : HasDecay Fam (D : ℝ) (c : ℝ)) (hη : Λ < D) (hc : 0 < c)
    {Cls : ℕ → Prop} {Bad : ℕ → ℕ → Prop} (hs : 0 < s) (hg : 0 < g₁ ∧ g₁ ≤ g₂)
    (hNV : HasNVC Fam Cls Bad (g₁ : ℝ) (g₂ : ℝ)) (hwin : HasWindowC Cls Bad (s : ℝ))
    (hE : measureExp c Λ D g₁ g₂ s ≤ E') : Fam.MeasureLB (E' : ℝ) :=
  PolyFamily.MeasureLB.mono (by exact_mod_cast hE) (measure_of_familyC Fam hΛ hD hη hc hs hg hNV hwin)

/-- Rounding helper: any rational `E' ≥ measureExp …` is also a valid exponent. -/
theorem measure_of_family_le (Fam : PolyFamily) {c Λ D g₁ g₂ E' : ℚ}
    (hΛ : HasContent Fam (Λ : ℝ)) (hD : HasDecay Fam (D : ℝ) (c : ℝ)) (hη : Λ < D) (hc : 0 < c)
    (R : PrimeRule) (hs : 0 < R.s) (hg : 0 < g₁ ∧ g₁ ≤ g₂)
    (hNV : HasNV Fam R (g₁ : ℝ) (g₂ : ℝ)) (hwin : R.HasWindow)
    (hE : measureExp c Λ D g₁ g₂ R.s ≤ E') :
    Fam.MeasureLB (E' : ℝ) :=
  PolyFamily.MeasureLB.mono (by exact_mod_cast hE) (measure_of_family Fam hΛ hD hη hc R hs hg hNV hwin)

/-- Square-frame corollary. -/
theorem measure_of_frame (Fr : Frame) {c Λ D g₁ g₂ : ℚ}
    (hΛ : HasContent (PolyFamily.ofFrame Fr) (Λ : ℝ))
    (hD : HasDecay (PolyFamily.ofFrame Fr) (D : ℝ) (c : ℝ)) (hη : Λ < D) (hc : 0 < c)
    (R : PrimeRule) (hs : 0 < R.s) (hg : 0 < g₁ ∧ g₁ ≤ g₂)
    (hNV : HasNV (PolyFamily.ofFrame Fr) R (g₁ : ℝ) (g₂ : ℝ)) (hwin : R.HasWindow) :
    (PolyFamily.ofFrame Fr).MeasureLB ((measureExp c Λ D g₁ g₂ R.s : ℚ) : ℝ) :=
  measure_of_family _ hΛ hD hη hc R hs hg hNV hwin

/-- Square-frame corollary with rounding. -/
theorem measure_of_frame_le (Fr : Frame) {c Λ D g₁ g₂ E' : ℚ}
    (hΛ : HasContent (PolyFamily.ofFrame Fr) (Λ : ℝ))
    (hD : HasDecay (PolyFamily.ofFrame Fr) (D : ℝ) (c : ℝ)) (hη : Λ < D) (hc : 0 < c)
    (R : PrimeRule) (hs : 0 < R.s) (hg : 0 < g₁ ∧ g₁ ≤ g₂)
    (hNV : HasNV (PolyFamily.ofFrame Fr) R (g₁ : ℝ) (g₂ : ℝ)) (hwin : R.HasWindow)
    (hE : measureExp c Λ D g₁ g₂ R.s ≤ E') :
    (PolyFamily.ofFrame Fr).MeasureLB (E' : ℝ) :=
  measure_of_family_le _ hΛ hD hη hc R hs hg hNV hwin hE

end Measure
end CatalanCore
