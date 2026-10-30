import CatalanCore.Uniform.Bank.Halves.Cover.Check
import CatalanCore.Uniform.Decay.AltDecay
import CatalanCore.Uniform.Bank.HalvesContent.AutoMeasure
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.HalvesContent.Bound
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Halves CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.HalvesContent.Auto CatalanCore.Uniform.Bank.HalvesContent.AutoMeasure
  CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Bank.Halves.Cover

theorem tab_RP : TabC.RP = altPieces (3 / 10) := by decide +kernel
theorem tab_CP : TabC.CP = altPieces (3 / 10) := by decide +kernel
theorem tab_Mq : TabC.Mq = 1 + (3 / 10 : ℚ) / 2 := by decide +kernel
theorem energy_ok : energyCheck 30 (altPieces (3 / 10)) (altPieces (3 / 10)) Dchi.Inu = true := by decide +kernel
theorem dim_eq : Dchi.dim = 2 := by decide +kernel
theorem eps_pos : 0 < Dchi.ε := by decide +kernel
theorem ccert_eq : Dchi.ccert = cH := by decide +kernel
theorem lam_lt : bankData.Λ < Dchi.Dt := by rw [bankData_Λ]; decide +kernel
theorem mu_margin : cH ≤ 327 / 50 * (Dchi.Dt - bankData.Λ) := by rw [bankData_Λ]; decide +kernel

theorem decay (depth : ℕ) :
    HasScaledDecay (FH.family halves depth) FH.scale (Dchi.Dt : ℝ) (cH : ℝ) := by
  have h := altGeom_hasScaledDecay (3 / 10) three_tenths_pos (by norm_num)
    (Fr := halves) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    TabC tab_RP tab_CP tab_Mq Dchi Pply check_true (by rw [dim_eq]; rfl) 30 energy_ok
    (m0 := 1 / 2) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [halves, CatalanFrames.Thirds.thirdsFrame])
    eps_pos depth
  rw [ccert_eq] at h
  exact h

/-- The half-shift bank gives the irrationality-measure bound 327/50 for pi squared. -/
theorem pi2_measure : Measure.MeasureLBAt (Real.pi ^ 2) ((327 / 50 : ℚ) : ℝ) :=
  halves_measure_at halves (by show 1 ≤ 2; norm_num) halves_w_ne halves_const
    (halves_content_auto _ (depth_le rfl)) _ lam_lt mu_margin (decay _)

end CatalanCore.Uniform.Bank.HalvesContent.Bound
