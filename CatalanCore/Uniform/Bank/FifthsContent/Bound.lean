import CatalanCore.Uniform.Bank.Fifths.Cover.Check
import CatalanCore.Uniform.Decay.AltDecay
import CatalanCore.Uniform.Bank.FifthsContent.AutoMeasure
set_option Elab.async false

/-! # The fifths bounds (coordinator)

The decay of the four fifths members follows from the generated cover (`Fifths.Cover`, with
`TabC.check Dchi Pply = true`) by `AltDecay.altGeom_hasScaledDecay` for `altGeom (2/9)`, at the cover's
rate `Dchi.Dt`. Each frame supplies its contour and floor conditions, which are decided. With the automatic
content (`AutoMeasure.fifths_measure_at`), this gives the four measures. -/

namespace CatalanCore.Uniform.Bank.FifthsContent.Bound
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.FifthsContent.Auto CatalanCore.Uniform.Bank.FifthsContent.AutoMeasure
  CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Bank.Fifths.Cover

theorem tab_RP : TabC.RP = altPieces (2 / 9) := by decide +kernel
theorem tab_CP : TabC.CP = altPieces (2 / 9) := by decide +kernel
theorem tab_Mq : TabC.Mq = 1 + (2 / 9 : ℚ) / 2 := by decide +kernel
theorem energy_ok : energyCheck 30 (altPieces (2 / 9)) (altPieces (2 / 9)) Dchi.Inu = true := by
  decide +kernel
theorem dim_eq : Dchi.dim = 2 := by decide +kernel
theorem eps_pos : 0 < Dchi.ε := by decide +kernel
theorem ccert_eq : Dchi.ccert = c5 := by decide +kernel
theorem lam_lt : bankData.Λ < Dchi.Dt := by rw [bankData_Λ]; decide +kernel
theorem mu_margin : c5 ≤ 59983 / 2500 * (Dchi.Dt - bankData.Λ) := by rw [bankData_Λ]; decide +kernel

/-- **Decay of a fifths frame from the generated cover.** -/
theorem decay_of_frame {Fr : Frame} (hC : Frame.contourCheck Fr = true)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (hd : Fr.d = 2) (hm0 : ∀ i, (1 / 5 : ℝ) ≤ Fr.μ i) (depth : ℕ) :
    HasScaledDecay (F5.family Fr depth) F5.scale (Dchi.Dt : ℝ) (c5 : ℝ) := by
  have h := altGeom_hasScaledDecay (2 / 9) two_ninths_pos (by norm_num) hC hAR hnorm1 TabC tab_RP tab_CP
    tab_Mq Dchi Pply check_true (by rw [dim_eq, hd]) 30 energy_ok (m0 := 1 / 5) (by norm_num) hm0
    eps_pos depth
  rw [ccert_eq] at h
  exact h

theorem m0_le (s xs δ0 : ℚ) (n0off : ℕ) (hs0 : 0 < s) (hs1 : s < 1) (hs : (1 / 5 : ℚ) ≤ s) :
    ∀ i, (1 / 5 : ℝ) ≤ (fifthsFrame s xs δ0 n0off hs0 hs1).μ i := by
  intro i
  fin_cases i
  · show (1 / 5 : ℝ) ≤ ((s : ℚ) : ℝ)
    have h := (Rat.cast_le (K := ℝ)).2 hs
    push_cast at h
    exact h
  · show (1 / 5 : ℝ) ≤ ((1 : ℚ) : ℝ); norm_num

/-- **`μ(fifthsTarget 1) ≤ 59983/2500`.** -/
theorem fifths1_measure : Measure.MeasureLBAt (fifthsTarget 1) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_measure_at fifths1 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) fifths1_const
    (fifths1_content_auto _ (depth_le rfl)) _ lam_lt mu_margin
    (decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
      (m0_le _ _ _ _ _ _ (by norm_num)) _)

/-- **`μ(fifthsTarget 2) ≤ 59983/2500`.** -/
theorem fifths2_measure : Measure.MeasureLBAt (fifthsTarget 2) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_measure_at fifths2 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) fifths2_const
    (fifths2_content_auto _ (depth_le rfl)) _ lam_lt mu_margin
    (decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
      (m0_le _ _ _ _ _ _ (by norm_num)) _)

/-- **`μ(fifthsTarget 3) ≤ 59983/2500`.** -/
theorem fifths3_measure : Measure.MeasureLBAt (fifthsTarget 3) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_measure_at fifths3 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) fifths3_const
    (fifths3_content_auto _ (depth_le rfl)) _ lam_lt mu_margin
    (decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
      (m0_le _ _ _ _ _ _ (by norm_num)) _)

/-- **`μ(fifthsTarget 4) ≤ 59983/2500`.** -/
theorem fifths4_measure : Measure.MeasureLBAt (fifthsTarget 4) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_measure_at fifths4 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) fifths4_const
    (fifths4_content_auto _ (depth_le rfl)) _ lam_lt mu_margin
    (decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
      (m0_le _ _ _ _ _ _ (by norm_num)) _)

end CatalanCore.Uniform.Bank.FifthsContent.Bound
