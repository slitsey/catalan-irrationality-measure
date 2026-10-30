module

public import CatalanCore.Uniform.Bank.Fourths.Cover.Check
public import CatalanCore.Uniform.Decay.AltDecay
public import CatalanCore.Uniform.Bank.FourthsContent.AutoMeasure

@[expose] public section
set_option Elab.async false

/-! # The λ± bounds (coordinator)

The decay of both λ frames follows from the generated cover (`Fourths.Cover`, with
`TabC.check Dchi Pply = true`) by `AltDecay.altGeom_hasScaledDecay` for `altGeom (1/5)`. Each frame
supplies its contour and floor conditions, which are decided. With the automatic content
(`AutoMeasure.lambda_measure_auto`), this gives the two measures. -/

namespace CatalanCore.Uniform.Bank.FourthsContent.Bound
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Fourths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.FourthsContent.AutoMeasure CatalanCore.Uniform.Decay.AltDecay
  CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Bank.Fourths.Cover

theorem tab_RP : TabC.RP = altPieces (1 / 5) := by decide +kernel
theorem tab_CP : TabC.CP = altPieces (1 / 5) := by decide +kernel
theorem tab_Mq : TabC.Mq = 1 + (1 / 5 : ℚ) / 2 := by decide +kernel
theorem energy_ok : energyCheck 30 (altPieces (1 / 5)) (altPieces (1 / 5)) Dchi.Inu = true := by
  decide +kernel
theorem dim_eq : Dchi.dim = 2 := by decide +kernel
theorem eps_pos : 0 < Dchi.ε := by decide +kernel
theorem Dt_eq : Dchi.Dt = DL := by decide +kernel
theorem ccert_eq : Dchi.ccert = cL := by decide +kernel

/-- **Decay of a λ frame from the generated cover.** -/
theorem decay_of_frame {Fr : Frame} (hC : Frame.contourCheck Fr = true)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (hd : Fr.d = 2) (hm0 : ∀ i, (1 / 4 : ℚ) ≤ Fr.μ i) (depth : ℕ) :
    HasScaledDecay (FL.family Fr depth) FL.scale (DL : ℝ) (cL : ℝ) := by
  have h := altGeom_hasScaledDecay (1 / 5) one_fifth_pos (by norm_num) hC hAR hnorm1 TabC tab_RP tab_CP
    tab_Mq Dchi Pply check_true (by rw [dim_eq, hd]) 30 energy_ok (m0 := 1 / 4) (by norm_num)
    (fun i => by
      have h := (Rat.cast_le (K := ℝ)).2 (hm0 i)
      push_cast at h
      exact h) eps_pos depth
  rw [Dt_eq, ccert_eq] at h
  exact h

theorem frames_contour : ∀ sgn : Bool, Frame.contourCheck (lambdaFrame sgn) = true := by decide +kernel

theorem frames_hAR : ∀ sgn : Bool, ∀ i : Fin (lambdaFrame sgn).d,
    ((⌊(lambdaFrame sgn).xs - (lambdaFrame sgn).μ i⌋ : ℤ) : ℚ) + (lambdaFrame sgn).μ i ≤
      (lambdaFrame sgn).n0off := by decide +kernel

theorem frames_norm : ∀ sgn : Bool, (1 : ℚ) ≤ (lambdaFrame sgn).norm := by decide +kernel

theorem frames_m0 : ∀ sgn : Bool, ∀ i : Fin (lambdaFrame sgn).d, (1 / 4 : ℚ) ≤ (lambdaFrame sgn).μ i := by
  decide +kernel

theorem lambda_decay (sgn : Bool) :
    HasScaledDecay (FL.family (lambdaFrame sgn) (FL.selectionDepth (lambdaFrame sgn) 2)) FL.scale (DL : ℝ)
      (cL : ℝ) :=
  decay_of_frame (frames_contour sgn) (frames_hAR sgn) (frames_norm sgn) (lambdaFrame_d sgn)
    (frames_m0 sgn) _

/-- **`μ(L(2, χ₋₄) ± 5π²/48) ≤ 314411/10000`** (`lambdaTarget sgn`; `true` is plus). -/
theorem lambda_measure (sgn : Bool) : Measure.MeasureLBAt (lambdaTarget sgn) ((314411 / 10000 : ℚ) : ℝ) :=
  lambda_measure_auto sgn (lambda_decay sgn)

end CatalanCore.Uniform.Bank.FourthsContent.Bound

#print axioms CatalanCore.Uniform.Bank.FourthsContent.Bound.lambda_measure
