module
public import CatalanCore.Li2.DecayCert.Simple.Penalty
public import CatalanCore.Li2.DecayCert.Lattice.Cert
/-! Assembly of the lattice dual value on the SIMPLE route. `simple_dual_ge` closes
`lower ≤ −(12 log 2 + 4) − I(σ) − 2θ − 2∫_{x≥0}(W − θ)₊ − atomPenalty` from the energy bound, the penalties
on `[0, Y]` and `[Y, C]`, the zero tail beyond `C`, the atom penalty on `[1, 4]` and one scalar check. -/
@[expose] public section
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple
open CatalanCore.Li2.DecayCert CatalanCore.Li2.Decay CatalanCore.Li2.DecayCert.LatticeSimple
noncomputable section

/-- The dual value of a lattice datum from its four parts: the energy bound `Iup`, the penalty on
`[0, Y]`, on `[Y, C]` (zero beyond `C`), and the atom penalty, closed by one scalar check. -/
theorem simple_dual_ge (z ρ θ : ℝ) (σ : Measure ℂ) (Y C : ℚ) (hY : 0 ≤ Y) (hYC : Y ≤ C)
    (Iup TW TR TA lower θq : ℚ) (hθ : (θq:ℝ)=θ) (terms : ℕ)
    (hI : I σ ≤ (Iup:ℝ))
    (hcont : Continuous (fun x : ℝ => pos (W z σ (x:ℂ)-θ)))
    (hW : (∫ x in ((0:ℚ):ℝ)..(Y:ℝ), pos (W z σ (x:ℂ)-θ)) ≤ (TW:ℝ))
    (hR : (∫ x in (Y:ℝ)..(C:ℝ), pos (W z σ (x:ℂ)-θ)) ≤ (TR:ℝ))
    (htail : ∀ x : ℝ, (C:ℝ) ≤ x → W z σ (x:ℂ) ≤ θ)
    (hA : (∫ x in ((1:ℚ):ℝ)..((4:ℚ):ℝ), pos (A z ρ σ x-θ)) ≤ (TA:ℝ))
    (hsc : scalarLowerCheck lower (seSum [seScale (-12) (.log terms 2),
      seRat (-4-Iup-2*θq-2*(TW+TR)-TA)])=true) :
    (lower:ℝ) ≤ -(12*Real.log 2+4)-I σ-2*θ-2*(∫ x in Ici (0:ℝ),pos (W z σ (x:ℂ)-θ))-atomPenalty z ρ σ θ := by
  have hl := scalarLowerCheck_sound _ _ hsc
  simp only [seSum_value,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    seScale_value,ScalarExpr.value,seRat_value,Rat.cast_neg,Rat.cast_ofNat] at hl
  push_cast at hl
  have hYR : (0:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
  have hYCR : (Y:ℝ) ≤ (C:ℝ) := by exact_mod_cast hYC
  have hzero : ∀ x : ℝ, (C:ℝ) ≤ x → pos (W z σ (x:ℂ)-θ)=0 := by
    intro x hx; unfold pos; exact max_eq_right (by linarith [htail x hx])
  rw [integral_Ici_of_zero_tail _ (C:ℝ) (hYR.trans hYCR) hzero,
    ← intervalIntegral.integral_add_adjacent_intervals (b:=(Y:ℝ)) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
  have hA' : atomPenalty z ρ σ θ ≤ (TA:ℝ) := by
    unfold atomPenalty; simpa using hA
  simp only [Rat.cast_zero] at hW
  rw [hθ] at hl
  linarith

end
end CatalanCore.Li2.DecayCert.Simple
