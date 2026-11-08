module

public import CatalanMeasure.GenD.Signed.Davis.Normalized130
public import CatalanMeasure.GenD.Analytic.AffinePolynomialBounds

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Davis.S1PolynomialBounds
open Polynomial CatalanMeasure.GenD.Analytic
open GaussianHorner Normalized130 CatalanMeasure.Refinement.Trimmed130
noncomputable section

def complexP : ℂ[X] := realP.map (algebraMap ℝ ℂ)
def blockScale (q : ℤ) : ℂ := 2 * (coefficientDenominator : ℂ) * (q : ℂ) ^ 130

theorem blockScale_ne_zero {q : ℤ} (hq : q ≠ 0) : blockScale q ≠ 0 := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hD : (coefficientDenominator : ℂ) ≠ 0 := by exact_mod_cast coefficientDenominator_pos.ne'
  exact mul_ne_zero (mul_ne_zero (by norm_num) hD) (pow_ne_zero _ hqC)

theorem cancel_normalized_horner {q : ℤ} (hq : q ≠ 0) {v w : ℂ}
    (h : v * (q : ℂ) = (q : ℂ) ^ 131 * (2 * (coefficientDenominator : ℂ) * w)) :
    v = blockScale q * w := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  apply mul_right_cancel₀ hqC
  calc
    v * (q : ℂ) = (q : ℂ) ^ 131 * (2 * (coefficientDenominator : ℂ) * w) := h
    _ = (blockScale q * w) * (q : ℂ) := by
      unfold blockScale
      rw [show (131 : ℕ) = 130 + 1 from rfl, pow_succ]
      ring

theorem translated_eval_mul (cs : List (ℤ × ℤ)) (c : ℤ × ℤ) {q : ℤ} (hq : q ≠ 0)
    (hcheck : (normalizedCoefficients.reverse.foldl (shiftStep c q) ([],1)).1 = cs) (z : ℂ) :
    (polynomialOfPairs cs).eval (2 * (q : ℂ) * z - castPair c) = blockScale q * complexP.eval z := by
  have ht := translation_polynomial_value_sound c hq normalizedCoefficients
    (2 * (q : ℂ) * z - castPair c)
  rw [hcheck, normalized_length] at ht
  change (polynomialOfPairs cs).eval _ * (q : ℂ) =
    (q : ℂ) ^ 131 * normalizedP.eval _ at ht
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have harg : (2 * (q : ℂ) * z - castPair c + castPair c) / (q : ℂ) = 2 * z := by
    field_simp
    <;> ring
  rw [harg, normalized_eval_scaled] at ht
  exact cancel_normalized_horner hq ht

theorem translated_eval (cs : List (ℤ × ℤ)) (c : ℤ × ℤ) {q : ℤ} (hq : q ≠ 0)
    (hcheck : (normalizedCoefficients.reverse.foldl (shiftStep c q) ([],1)).1 = cs) (z : ℂ) :
    complexP.eval z = (polynomialOfPairs cs).eval (2 * (q : ℂ) * z + (-castPair c)) / blockScale q := by
  apply (eq_div_iff (blockScale_ne_zero hq)).mpr
  rw [← sub_eq_add_neg, translated_eval_mul cs c hq hcheck]
  ring

theorem point_eval (c v : ℤ × ℤ) {q : ℤ} (hq : q ≠ 0)
    (hcheck : (normalizedCoefficients.reverse.foldl (valueStep c q) ((0,0),1)).1 = v) :
    complexP.eval (castPair c / (2 * (q : ℂ))) = castPair v / blockScale q := by
  have ht := point_value_polynomial_sound c hq normalizedCoefficients
  rw [hcheck, normalized_length] at ht
  change castPair v * (q : ℂ) = (q : ℂ) ^ 131 * normalizedP.eval (castPair c / (q : ℂ)) at ht
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have harg : castPair c / (q : ℂ) = 2 * (castPair c / (2 * (q : ℂ))) := by
    field_simp [hqC]
    <;> ring
  rw [harg, normalized_eval_scaled] at ht
  have he := cancel_normalized_horner hq ht
  apply (eq_div_iff (blockScale_ne_zero hq)).mpr
  rw [he]
  unfold complexP
  ring

theorem derivative_norm_bound (cs : List (ℤ × ℤ)) (c : ℤ × ℤ) {q : ℤ} (hq : 0 < q)
    (hcheck : (normalizedCoefficients.reverse.foldl (shiftStep c q) ([],1)).1 = cs)
    (z : ℂ) {B M : ℝ}
    (hB : ‖(polynomialOfPairs cs).derivative.eval (2 * (q : ℂ) * z - castPair c)‖ ≤ B)
    (hM : B ≤ M * ((coefficientDenominator : ℝ) * (q : ℝ) ^ 129)) :
    ‖complexP.derivative.eval z‖ ≤ M := by
  have hd := polynomial_derivative_affine_identity complexP (polynomialOfPairs cs)
    (2 * (q : ℂ)) (-castPair c) (blockScale q) (translated_eval cs c hq.ne' hcheck) z
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hD : (coefficientDenominator : ℂ) ≠ 0 := by exact_mod_cast coefficientDenominator_pos.ne'
  have hfactor : (2 * (q : ℂ)) / blockScale q =
      1 / ((coefficientDenominator : ℂ) * (q : ℂ) ^ 129) := by
    unfold blockScale
    rw [show (130 : ℕ) = 129 + 1 from rfl, pow_succ]
    field_simp [hqC, hD]
  rw [hfactor] at hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hDR : (0 : ℝ) < coefficientDenominator := by exact_mod_cast coefficientDenominator_pos
  have hqnorm : ‖(q : ℂ)‖ = (q : ℝ) := by rw [Complex.norm_intCast, abs_of_pos hqR]
  have hDnorm : ‖(coefficientDenominator : ℂ)‖ = (coefficientDenominator : ℝ) := by
    rw [Complex.norm_intCast, abs_of_pos hDR]
  rw [hd, norm_mul, norm_div, norm_one, norm_mul, norm_pow, hDnorm, hqnorm]
  have hB' : ‖(polynomialOfPairs cs).derivative.eval (2 * (q : ℂ) * z + -castPair c)‖ ≤
      M * ((coefficientDenominator : ℝ) * (q : ℝ) ^ 129) := by
    simpa only [sub_eq_add_neg] using hB.trans hM
  calc
    _ = ‖(polynomialOfPairs cs).derivative.eval (2 * (q : ℂ) * z + -castPair c)‖ /
        ((coefficientDenominator : ℝ) * (q : ℝ) ^ 129) := by ring
    _ ≤ M := (div_le_iff₀ (by positivity)).mpr hB'

end
end CatalanMeasure.GenD.Signed.Davis.S1PolynomialBounds
#print axioms CatalanMeasure.GenD.Signed.Davis.S1PolynomialBounds.blockScale_ne_zero
#print axioms CatalanMeasure.GenD.Signed.Davis.S1PolynomialBounds.cancel_normalized_horner
#print axioms CatalanMeasure.GenD.Signed.Davis.S1PolynomialBounds.translated_eval_mul
#print axioms CatalanMeasure.GenD.Signed.Davis.S1PolynomialBounds.translated_eval
#print axioms CatalanMeasure.GenD.Signed.Davis.S1PolynomialBounds.point_eval
#print axioms CatalanMeasure.GenD.Signed.Davis.S1PolynomialBounds.derivative_norm_bound
