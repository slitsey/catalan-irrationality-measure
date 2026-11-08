module
public import CatalanMeasure.GenD.Signed.Davis.S1CheckedBlocks
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Davis.S1ValueBounds
open Polynomial CatalanMeasure.GenD.Analytic
open GaussianHorner GaussianCertificate S1PolynomialBounds S1CheckedBlocks
open CatalanMeasure.Refinement.Trimmed130
noncomputable section

theorem block_value_bound (cs : List (ℤ × ℤ)) (c : ℤ × ℤ) {q : ℤ} (hq : 0 < q)
    (hcheck : (Normalized130.normalizedCoefficients.reverse.foldl
      (shiftStep c q) ([],1)).1 = cs)
    (U : List ℤ) (hU : normsOK cs U = true)
    (x den num : ℤ) (hden : 0 < den) (hx : 0 ≤ x)
    (hnum : positiveHorner U x den = num) {B radius : ℝ}
    (hbound : (num : ℝ)*(den : ℝ) ≤ (den : ℝ)^U.length*(B*(scaleInt q : ℝ)))
    (hradius : 2*(q : ℝ)*radius ≤ (x : ℝ)/(den : ℝ))
    (z : ℂ) (hz : z ∈ Metric.closedBall (castPair c/(2*(q : ℂ))) radius) :
    ‖complexP.eval z‖ ≤ B := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  have hxR : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hs : 0 < scaleInt q := by unfold scaleInt; have := coefficientDenominator_pos; positivity
  have hsR : (0 : ℝ) < scaleInt q := by exact_mod_cast hs
  have he : 2*(q : ℂ)*z-castPair c =
      (2*(q : ℂ))*(z-castPair c/(2*(q : ℂ))) := by
    field_simp [hqC]
    <;> ring
  have hnorm : ‖2*(q : ℂ)‖=2*(q : ℝ) := by
    rw [norm_mul,Complex.norm_intCast,abs_of_pos hqR]
    norm_num
  have harg : ‖2*(q : ℂ)*z-castPair c‖ ≤ (x : ℝ)/(den : ℝ) := by
    rw [he,norm_mul,hnorm]
    exact (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz)
      (by positivity : (0 : ℝ) ≤ 2*(q : ℝ))).trans hradius
  have hhorner := positiveHorner_sound U x den hden.ne'
  rw [hnum] at hhorner
  have hHB : normHorner (U.map (fun (a : ℤ) => (a : ℝ))) ((x : ℝ)/(den : ℝ)) ≤
      B*(scaleInt q : ℝ) := by
    rw [hhorner] at hbound
    nlinarith [pow_pos hd U.length]
  have hB := (evalPairs_norm_le (normsOK_sound hU) (by positivity)
    (2*(q : ℂ)*z-castPair c) harg).trans hHB
  rw [translated_eval cs c hq.ne' hcheck z,norm_div,blockScale_eq_cast,
    Complex.norm_intCast,abs_of_pos hsR]
  apply (div_le_iff₀ hsR).mpr
  simpa only [← sub_eq_add_neg,polynomialOfPairs_eval] using hB

end
end CatalanMeasure.GenD.Signed.Davis.S1ValueBounds
#print axioms CatalanMeasure.GenD.Signed.Davis.S1ValueBounds.block_value_bound
