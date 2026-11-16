module

public import CatalanCore.Zeta5.Profile.All

@[expose] public section

/-!
# ZC37: the tail `∫₂₀₀^∞ R(x) x⁻³ dx ≤ −103109/24000000`

The argument of `Profile.TL40` (one fundamental theorem of calculus for the continuous piecewise
`C¹` function `Ω = λ/x + (P − P̄)/x² + 2C/x³ + 6D/x⁴ − 6D₊/x⁴ − (13/16)/x²`, with `R/x³ ≤ Ω′`)
evaluated at `T = 200` instead of `T = 40`. At `x = 200` both `{x}` and `{αx} = {15}` vanish, so
`P(200) = C(200) = 0` and `D(200) = 74/(360α²) − λ/360`, and the bound is
`−λ/200 + (P̄ + 13/16)/200² + λ/(32·200⁴)`, which is below the ledger's
`−λ/200 + (P̄ + 13/16)/200² + 32/200³ = −103109/24000000` (CONTENT-THEOREM (C15)).
-/

open Set MeasureTheory Filter Topology

namespace CatalanCore.Zeta5.Sum

open CatalanCore.Zeta5.Profile

lemma Om_two_hundred : Om 200 = (lam : ℝ) / 200 - Pbar / 200 ^ 2
    + 6 * (74 / (360 * (al : ℝ) ^ 2) - (lam : ℝ) / 360) / 200 ^ 4
    - 6 * Dplus / 200 ^ 4 - 13 / 16 / 200 ^ 2 := by
  have h1 : Int.fract (200 : ℝ) = 0 := by
    have : (200 : ℝ) = ((200 : ℤ) : ℝ) := by norm_num
    rw [this, Int.fract_intCast]
  have h2 : Int.fract ((al : ℝ) * 200) = 0 := by
    have : (al : ℝ) * 200 = ((15 : ℤ) : ℝ) := by unfold al; norm_num
    rw [this, Int.fract_intCast]
  have hP : Pp 200 = 0 := by unfold Pp; rw [h1, h2]; ring
  have hC : Cc 200 = 0 := by unfold Cc G0; rw [h1, h2]; ring
  have hD : Dd 200 = 74 / (360 * (al : ℝ) ^ 2) - (lam : ℝ) / 360 := by
    unfold Dd B4; rw [h1, h2]
    have : (al : ℝ) ≠ 0 := al_pos.ne'
    field_simp; ring
  unfold Om; rw [hP, hC, hD]; ring

/-- Lemma TL at `T = 200`. -/
theorem TL200 : ∫ x in Ioi (200 : ℝ), (Rg x : ℝ) / x ^ 3 ≤ -103109 / 24000000 := by
  have hOi : IntegrableOn Omd (Ioi 200) :=
    integrableOn_Ioi_of_bound (C := 2000) (by norm_num) measurable_Omd
      (fun x hx => Omd_bound x (by linarith))
  have hRi : IntegrableOn (fun x : ℝ => (Rg x : ℝ) / x ^ 3) (Ioi 200) :=
    integrableOn_Rg.mono_set (Ioi_subset_Ioi (by norm_num))
  have hFTC : ∀ X : ℝ, 200 ≤ X → ∫ x in (200 : ℝ)..X, Omd x = Om X - Om 200 := by
    intro X hX
    have hint : IntervalIntegrable Omd volume 200 X :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).2 (hOi.mono_set Ioc_subset_Ioi_self)
    refine integral_eq_of_hasDerivAt_off_countable_of_le Om Omd hX exc_countable ?_ ?_ hint
    · exact continuousOn_Om.mono (fun y hy => lt_of_lt_of_le (by norm_num) hy.1)
    · intro x hx
      exact hasDerivAt_Om hx.2 (by linarith [hx.1.1])
  have hle : ∀ X : ℝ, 200 ≤ X →
      ∫ x in (200 : ℝ)..X, (Rg x : ℝ) / x ^ 3 ≤ Om X - Om 200 := by
    intro X hX
    have hint : IntervalIntegrable Omd volume 200 X :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).2 (hOi.mono_set Ioc_subset_Ioi_self)
    have hint2 : IntervalIntegrable (fun x : ℝ => (Rg x : ℝ) / x ^ 3) volume 200 X :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).2 (hRi.mono_set Ioc_subset_Ioi_self)
    rw [← hFTC X hX]
    exact intervalIntegral.integral_mono_on hX hint2 hint
      (fun x hx => Rg_div_le x (by linarith [hx.1]))
  have hT := intervalIntegral_tendsto_integral_Ioi (a := 200) hRi tendsto_id
  have hT2 : Tendsto (fun X : ℝ => Om X - Om 200) atTop (nhds (0 - Om 200)) :=
    tendsto_Om.sub tendsto_const_nhds
  have := le_of_tendsto_of_tendsto hT hT2
    (eventually_atTop.2 ⟨200, fun X hX => hle X hX⟩)
  refine this.trans ?_
  rw [Om_two_hundred]
  unfold Dplus Pbar lam al
  norm_num

end CatalanCore.Zeta5.Sum
