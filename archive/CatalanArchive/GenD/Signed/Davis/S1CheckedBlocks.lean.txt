module
public import CatalanMeasure.GenD.Signed.Davis.S1PolynomialBounds
public import CatalanMeasure.GenD.Analytic.GaussianNumericBounds
public import CatalanMeasure.GenD.Analytic.GaussianEllipse
public import CatalanMeasure.GenD.Analytic.S1BlockBounds
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Davis.S1CheckedBlocks
open Polynomial CatalanMeasure.GenD.Analytic
open GaussianHorner GaussianCertificate GaussianNumericBounds GaussianEllipse
open S1PolynomialBounds CatalanMeasure.Refinement.Trimmed130
noncomputable section

def scaleInt (q : ℤ) : ℤ := 2 * coefficientDenominator * q^130

theorem blockScale_eq_cast (q : ℤ) : blockScale q = (scaleInt q : ℂ) := by
  simp only [blockScale, scaleInt, Int.cast_mul, Int.cast_ofNat, Int.cast_pow]

theorem point_ellipse_bound (c v : ℤ × ℤ) {q : ℤ} (hq : 0 < q)
    (hcheck : (Normalized130.normalizedCoefficients.reverse.foldl
      (valueStep c q) ((0,0),1)).1 = v)
    (um up : ℤ) (hm : 0 ≤ um) (hp : 0 ≤ up)
    (hmsq : (v.1-scaleInt q)^2 + v.2^2 ≤ um^2)
    (hpsq : (v.1+scaleInt q)^2 + v.2^2 ≤ up^2) :
    ellipseH (complexP.eval (castPair c / (2*(q : ℂ)))) ≤
      ((um : ℝ)+(up : ℝ))/(2*(scaleInt q : ℝ)) := by
  rw [point_eval c v hq.ne' hcheck, blockScale_eq_cast]
  exact ellipseH_castPair_div_le v (scaleInt q) um up
    (by unfold scaleInt; have := coefficientDenominator_pos; positivity) hm hp hmsq hpsq

theorem block_derivative_bound (cs : List (ℤ × ℤ)) (c : ℤ × ℤ) {q : ℤ} (hq : 0 < q)
    (hcheck : (Normalized130.normalizedCoefficients.reverse.foldl
      (shiftStep c q) ([],1)).1 = cs)
    (U : List ℤ) (hU : normsOK (weightedPairs 1 cs.tail) U = true)
    (x den num : ℤ) (hden : 0 < den) (hx : 0 ≤ x)
    (hnum : positiveHorner U x den = num) {M radius : ℝ}
    (hbound : (num : ℝ)*(den : ℝ) ≤ (den : ℝ)^U.length *
      (M*((coefficientDenominator : ℝ)*(q : ℝ)^129)))
    (hradius : 2*(q : ℝ)*radius ≤ (x : ℝ)/(den : ℝ))
    (z : ℂ) (hz : z ∈ Metric.closedBall (castPair c / (2*(q : ℂ))) radius) :
    ‖complexP.derivative.eval z‖ ≤ M := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : 2*(q : ℂ)*z-castPair c =
      (2*(q : ℂ))*(z-castPair c/(2*(q : ℂ))) := by
    field_simp [hqC]
    <;> ring
  have hnorm : ‖2*(q : ℂ)‖ = 2*(q : ℝ) := by
    rw [norm_mul, Complex.norm_intCast, abs_of_pos hqR]
    norm_num
  have harg : ‖2*(q : ℂ)*z-castPair c‖ ≤ (x : ℝ)/(den : ℝ) := by
    rw [he, norm_mul, hnorm]
    exact (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)
      (by positivity : (0 : ℝ) ≤ 2*(q : ℝ))).trans hradius
  have hB := derivative_norm_le_of_checks cs U hU x den num hden hx hnum hbound
    (2*(q : ℂ)*z-castPair c) harg
  exact derivative_norm_bound cs c hq hcheck z hB le_rfl

end
end CatalanMeasure.GenD.Signed.Davis.S1CheckedBlocks
#print axioms CatalanMeasure.GenD.Signed.Davis.S1CheckedBlocks.point_ellipse_bound
#print axioms CatalanMeasure.GenD.Signed.Davis.S1CheckedBlocks.block_derivative_bound
