import CatalanCore.Uniform.Measure.NV0
set_option Elab.async false

/-! Lane B, B3e: the scale/eps half of the bridge, generic in the family.

`HasScaledDecay` on a family `F₁` with scale function `sc` gives `HasDecay` (for every window constant
strictly larger) on any family `F₂` that embeds in it: same constant, admissible members mapped to
admissible members with the same real evaluation, and degree = scale. -/

namespace CatalanCore.Uniform.Bank.Chi3Bridge
open CatalanCore.Uniform

theorem hasDecay_of_scaledDecay_embed (F₁ F₂ : PolyFamily) (sc : F₁.ι → ℕ) {D c : ℝ}
    (hD : HasScaledDecay F₁ sc D c) (φ : F₂.ι → F₁.ι) (hconst : F₂.const = F₁.const)
    (hadm : ∀ n, F₂.Adm n → F₁.Adm (φ n))
    (heval : ∀ n x, F₂.evalR n x = F₁.evalR (φ n) x)
    (hdeg : ∀ n, F₂.deg n = sc (φ n)) {c' : ℝ} (hc : c < c') :
    HasDecay F₂ D c' := by
  intro δ hδ
  set ε : ℝ := min δ (c' - c) with hε
  have hε0 : 0 < ε := lt_min hδ (by linarith)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεc : ε ≤ c' - c := min_le_right _ _
  obtain ⟨R0, h⟩ := hD ε hε0
  refine ⟨R0, fun n hn hN t ht => ?_⟩
  have hd : (F₂.deg n : ℝ) = (sc (φ n) : ℝ) := by rw [hdeg n]
  have hdn : (0 : ℝ) ≤ F₂.deg n := Nat.cast_nonneg _
  have ht' : |t| ≤ Real.exp (-(c + ε) * (sc (φ n) : ℝ)) := by
    refine ht.trans (Real.exp_le_exp.mpr ?_)
    rw [← hd]; nlinarith
  have := h (φ n) (hadm n hn) (by rw [← hdeg n]; exact hN) t ht'
  rw [heval n, hconst]
  refine this.trans (Real.exp_le_exp.mpr ?_)
  rw [← hd]
  have : 0 ≤ (F₂.deg n : ℝ) ^ 2 := sq_nonneg _
  nlinarith

end CatalanCore.Uniform.Bank.Chi3Bridge
