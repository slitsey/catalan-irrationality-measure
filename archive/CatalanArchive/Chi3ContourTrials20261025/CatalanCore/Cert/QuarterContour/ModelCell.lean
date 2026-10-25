module
public import CatalanCore.Cert.QuarterCompute.ModelCell
public import CatalanCore.Cert.QuarterContour.DyadicIntervalInput
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelCell
open CatalanCore.Cert.QuarterCompute.ModelCell
open CatalanCore.Cert.QuarterCompute.DyadicInterval
open CatalanCore.Cert.QuarterContour.DyadicInterval

lemma vInterval_contains (p : CatalanCore.Cert.QuarterCompute.Model.Params)
    (hu : 0 < p.U) (hdy : 0 < p.DY) (yl yh : ℤ) (y : ℝ)
    (hy : (yl : ℝ)/2^40 ≤ y ∧ y ≤ (yh : ℝ)/2^40) :
    Contains H (vInterval p yl yh) (((p.U : ℝ)*y-p.Y0)/p.DY) := by
  have hH : 0 < H := by norm_num [H]
  have hden : 0 < p.DY*Z := mul_pos hdy (by norm_num [Z])
  have hur : (0 : ℝ) < p.U := by exact_mod_cast hu
  have hdyr : (0 : ℝ) < p.DY := by exact_mod_cast hdy
  have hz : (0 : ℝ) < Z := by norm_num [Z]
  have hb : (yl : ℝ)/(Z : ℝ) ≤ y ∧ y ≤ (yh : ℝ)/(Z : ℝ) := by
    norm_num [Z] at *
    exact hy
  have endpoint (t : ℤ) :
      (((t*(p.U : ℤ)-p.Y0*Z : ℤ) : ℝ)/(p.DY*Z : ℤ)) =
      (((p.U : ℝ)*((t : ℝ)/(Z : ℝ))-p.Y0)/(p.DY : ℝ)) := by
    push_cast
    field_simp [ne_of_gt hdyr,ne_of_gt hz] <;> ring
  apply encloseFractions_sound H _ _ _ hH hden
  constructor
  · rw [endpoint]
    apply (div_le_div_iff_of_pos_right hdyr).mpr
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left hb.1 hur.le) _
  · rw [endpoint]
    apply (div_le_div_iff_of_pos_right hdyr).mpr
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left hb.2 hur.le) _

lemma base_floor (base : ℤ) :
    (((-base)/562949953421312 : ℤ) : ℝ)/(H : ℝ) ≤ -(base : ℝ)/2^97 := by
  have h : (((-base)/562949953421312 : ℤ) : ℝ)*562949953421312 ≤ -(base : ℝ) := by
    exact_mod_cast Int.ediv_mul_le (-base) (by norm_num : (562949953421312 : ℤ) ≠ 0)
  apply (div_le_div_iff₀ (by norm_num [H]) (by positivity : (0 : ℝ) < 2^97)).mpr
  norm_num [H]
  linarith only [h]

lemma error_ceil (error : ℕ) :
    (error : ℝ)/2^64 ≤ (ceilDiv (error : ℤ) 65536 : ℝ)/(H : ℝ) := by
  have h : (error : ℤ) ≤ ceilDiv (error : ℤ) 65536*65536 := by
    have hh := Int.ediv_mul_le (-(error : ℤ)) (by norm_num : (65536 : ℤ) ≠ 0)
    unfold ceilDiv
    nlinarith only [hh]
  have hr : (error : ℝ) ≤ (ceilDiv (error : ℤ) 65536 : ℝ)*65536 := by exact_mod_cast h
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2^64) (by norm_num [H])).mpr
  norm_num [H]
  linarith only [hr]

/-- The exact fixed-point cell evaluator is below the analytic model lower bound. -/
theorem lower_sound (p : CatalanCore.Cert.QuarterCompute.Model.Params)
    (cs : List ℤ) (denom : ℕ) (base : ℤ) (error : ℕ) (yl yh : ℤ) (y sigma : ℝ)
    (hu : 0 < p.U) (hdy : 0 < p.DY) (hden : 0 < denom)
    (hy : (yl : ℝ)/2^40 ≤ y ∧ y ≤ (yh : ℝ)/2^40)
    (hanalytic : -(base : ℝ)/2^97 +
      RealPolynomial.evalReal (((p.U : ℝ)*y-p.Y0)/p.DY) cs/(denom : ℝ) -
      (error : ℝ)/2^64 -(1/2^20+1/2^39) ≤ sigma) :
    (sigmaLower p cs denom base error yl yh : ℝ)/(H : ℝ) ≤ sigma := by
  have hv := vInterval_contains p hu hdy yl yh y hy
  have hc := (coefficients_sound_normalized H (denom : ℤ) (by norm_num [H])
    (by exact_mod_cast hden) cs _ _ hv).1
  push_cast at hc
  have hb := base_floor base
  have he := error_ceil error
  have ht : (268435968 : ℝ)/(H : ℝ) = 1/2^20+1/2^39 := by norm_num [H]
  apply le_trans _ hanalytic
  unfold sigmaLower
  push_cast
  rw [sub_div,sub_div,add_div,ht]
  linarith only [hc,hb,he]
end CatalanCore.Cert.QuarterContour.ModelCell
#print axioms CatalanCore.Cert.QuarterContour.ModelCell.lower_sound