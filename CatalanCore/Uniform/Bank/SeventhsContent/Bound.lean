import CatalanCore.Uniform.Bank.Sevenths.Cover.Check
import CatalanCore.Uniform.Decay.AltDecay
import CatalanCore.Uniform.Bank.SeventhsContent.AutoMeasure
set_option Elab.async false

/-! # The sevenths bounds (coordinator)

The decay of all six sevenths frames follows from one generated cover (`Sevenths.Cover`, with
`TabC.check Dchi Pply = true`) by `AltDecay.altGeom_hasScaledDecay` for `altGeom (1/6)`. Each frame
supplies its contour and floor conditions, which are decided for all six at once. With the automatic
content (`AutoMeasure.sevenths_measure_auto`), this gives the six measures. -/

namespace CatalanCore.Uniform.Bank.SeventhsContent.Bound
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Sevenths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.SeventhsContent.AutoMeasure CatalanCore.Uniform.Decay.AltDecay
  CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Bank.Sevenths.Cover

theorem tab_RP : TabC.RP = altPieces (1 / 6) := by decide +kernel
theorem tab_CP : TabC.CP = altPieces (1 / 6) := by decide +kernel
theorem tab_Mq : TabC.Mq = 1 + (1 / 6 : ℚ) / 2 := by decide +kernel
theorem energy_ok : energyCheck 30 (altPieces (1 / 6)) (altPieces (1 / 6)) Dchi.Inu = true := by
  decide +kernel
theorem dim_eq : Dchi.dim = 2 := by decide +kernel
theorem eps_pos : 0 < Dchi.ε := by decide +kernel
theorem Dt_eq : Dchi.Dt = D7 := by decide +kernel
theorem ccert_eq : Dchi.ccert = c7 := by decide +kernel

/-- **Decay of a sevenths frame from the generated cover.** -/
theorem decay_of_frame {Fr : Frame} (hC : Frame.contourCheck Fr = true)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (hd : Fr.d = 2) (hm0 : ∀ i, (1 / 7 : ℚ) ≤ Fr.μ i) (depth : ℕ) :
    HasScaledDecay (F7.family Fr depth) F7.scale (D7 : ℝ) (c7 : ℝ) := by
  have h := altGeom_hasScaledDecay (1 / 6) one_sixth_pos (by norm_num) hC hAR hnorm1 TabC tab_RP tab_CP
    tab_Mq Dchi Pply check_true (by rw [dim_eq, hd]) 30 energy_ok (m0 := 1 / 7) (by norm_num)
    (fun i => by
      have h := (Rat.cast_le (K := ℝ)).2 (hm0 i)
      push_cast at h
      exact h) eps_pos depth
  rw [Dt_eq, ccert_eq] at h
  exact h

theorem frames_contour : ∀ a : Fin 6, Frame.contourCheck (seventhsFrameAt a) = true := by decide +kernel

theorem frames_hAR : ∀ a : Fin 6, ∀ i : Fin (seventhsFrameAt a).d,
    ((⌊(seventhsFrameAt a).xs - (seventhsFrameAt a).μ i⌋ : ℤ) : ℚ) + (seventhsFrameAt a).μ i ≤
      (seventhsFrameAt a).n0off := by decide +kernel

theorem frames_norm : ∀ a : Fin 6, (1 : ℚ) ≤ (seventhsFrameAt a).norm := by decide +kernel

theorem frames_m0 : ∀ a : Fin 6, ∀ i : Fin (seventhsFrameAt a).d, (1 / 7 : ℚ) ≤ (seventhsFrameAt a).μ i := by
  decide +kernel

theorem sevenths_decay (a : Fin 6) :
    HasScaledDecay (F7.family (seventhsFrameAt a) (F7.selectionDepth (seventhsFrameAt a) 2)) F7.scale
      (D7 : ℝ) (c7 : ℝ) :=
  decay_of_frame (frames_contour a) (frames_hAR a) (frames_norm a) rfl (frames_m0 a) _

/-- **`μ(seventhsTarget (a + 1)) ≤ 2801`** for each of the six members. -/
theorem sevenths_measure (a : Fin 6) :
    Measure.MeasureLBAt (seventhsTarget (seventhNumerator a)) ((2801 : ℚ) : ℝ) :=
  sevenths_measure_auto a (sevenths_decay a)

end CatalanCore.Uniform.Bank.SeventhsContent.Bound

#print axioms CatalanCore.Uniform.Bank.SeventhsContent.Bound.sevenths_measure
