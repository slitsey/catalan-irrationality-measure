import CatalanCore.Uniform.Bank.Thirds.Cover.Check
import CatalanCore.Uniform.Decay.AltDecay
import CatalanCore.Uniform.Bank.ThirdsContent.MeasureUF
set_option Elab.async false

/-! # The thirds bounds (coordinator)

The decay of both thirds members follows from the generated cover (`Thirds.Cover`, with
`TabC.check Dchi Pply = true`) by `AltDecay.altGeom_hasScaledDecay` for `altGeom (3/10)`. Each frame
supplies its contour and floor conditions, which are decided. With the automatic content
(`MeasureUF`), this gives the two measures. -/

namespace CatalanCore.Uniform.Bank.ThirdsContent.Bound
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanFrames.Thirds CatalanFrames.P6
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Bank.ThirdsContent
  CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Bank.Thirds.Cover

theorem tab_RP : TabC.RP = altPieces (3 / 10) := by decide +kernel
theorem tab_CP : TabC.CP = altPieces (3 / 10) := by decide +kernel
theorem tab_Mq : TabC.Mq = 1 + (3 / 10 : ℚ) / 2 := by decide +kernel
theorem energy_ok : energyCheck 30 (altPieces (3 / 10)) (altPieces (3 / 10)) Dchi.Inu = true := by
  decide +kernel
theorem dim_eq : Dchi.dim = 2 := by decide +kernel
theorem eps_pos : 0 < Dchi.ε := by decide +kernel
theorem Dt_eq : Dchi.Dt = DtT := by decide +kernel
theorem ccert_eq : Dchi.ccert = ctT := by decide +kernel

/-- **Decay of a thirds frame from the generated cover.** -/
theorem decay_of_frame {Fr : Frame} (hC : Frame.contourCheck Fr = true)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (hd : Fr.d = 2) (hm0 : ∀ i, (1 / 3 : ℚ) ≤ Fr.μ i) (depth : ℕ) :
    ThirdsDecay Fr depth := by
  have h := altGeom_hasScaledDecay (3 / 10) c310_pos (by norm_num) hC hAR hnorm1 TabC tab_RP tab_CP
    tab_Mq Dchi Pply check_true (by rw [dim_eq, hd]) 30 energy_ok (m0 := 1 / 3) (by norm_num)
    (fun i => by
      have h := (Rat.cast_le (K := ℝ)).2 (hm0 i)
      push_cast at h
      exact h) eps_pos depth
  rw [Dt_eq, ccert_eq] at h
  exact h

theorem thirdsAc_decay : ThirdsDecay thirdsAc (depth0 thirdsAc) :=
  decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) _

theorem thirdsBc_decay : ThirdsDecay thirdsBc (depth0 thirdsBc) :=
  decay_of_frame (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) _

/-- **`μ(L(2,χ₋₃) + π²/9) ≤ 9.5133`.** -/
theorem thirds_plus_measure :
    Measure.MeasureLBAt (chi3L2 + Real.pi ^ 2 / 9) ((95133/10000 : ℚ) : ℝ) :=
  MeasureUF.thirds_measure_plus thirdsAc_decay

/-- **`μ(L(2,χ₋₃) − π²/9) ≤ 9.5133`.** -/
theorem thirds_minus_measure :
    Measure.MeasureLBAt (chi3L2 - Real.pi ^ 2 / 9) ((95133/10000 : ℚ) : ℝ) :=
  MeasureUF.thirds_measure_minus thirdsBc_decay

end CatalanCore.Uniform.Bank.ThirdsContent.Bound

#print axioms CatalanCore.Uniform.Bank.ThirdsContent.Bound.thirds_plus_measure
#print axioms CatalanCore.Uniform.Bank.ThirdsContent.Bound.thirds_minus_measure
