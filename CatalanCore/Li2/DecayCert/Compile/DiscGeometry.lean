module
public import CatalanCore.Li2.DecayCert.Compile.SegmentSeries
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Tools.Joukowski
noncomputable section

theorem slit_distance_lower (ζ : CQ) (δ : ℚ) (hδ : 0 ≤ δ) (hsq : δ^2 ≤ slitDistSq ζ) :
    (δ:ℝ) ≤ Metric.infDist (cqReal ζ) sourceSlit := by
  have hnonempty : sourceSlit.Nonempty := ⟨(0:ℂ),⟨0,by constructor <;> norm_num,rfl⟩⟩
  apply (Metric.le_infDist hnonempty).mpr
  rintro _ ⟨x,hx,rfl⟩
  have hs : (δ:ℝ)^2 ≤ (slitDistSq ζ:ℝ) := by exact_mod_cast hsq
  have hn : ‖cqReal ζ-(x:ℂ)‖^2=((ζ.1:ℝ)-x)^2+(ζ.2:ℝ)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,cqReal_mk]
    simp <;> ring
  have hlower : (δ:ℝ)^2 ≤ ‖cqReal ζ-(x:ℂ)‖^2 := by
    rw [hn]
    by_cases hl : ζ.1 < -1
    · simp only [slitDistSq,if_pos hl,Rat.cast_add,Rat.cast_pow,Rat.cast_one] at hs
      have hlR : (ζ.1:ℝ) < -1 := by exact_mod_cast hl
      nlinarith [mul_nonneg (by linarith [hx.1] : 0 ≤ x+1) (by linarith [hx.1] : 0 ≤ x-2*(ζ.1:ℝ)-1)]
    · by_cases hr : 1 < ζ.1
      · simp only [slitDistSq,if_neg hl,if_pos hr,Rat.cast_add,Rat.cast_sub,Rat.cast_pow,Rat.cast_one] at hs
        have hrR : 1 < (ζ.1:ℝ) := by exact_mod_cast hr
        nlinarith [mul_nonneg (by linarith [hx.2] : 0 ≤ 1-x) (by linarith [hx.2] : 0 ≤ 2*(ζ.1:ℝ)-x-1)]
      · simp only [slitDistSq,if_neg hl,if_neg hr,Rat.cast_pow] at hs
        nlinarith [sq_nonneg ((ζ.1:ℝ)-x)]
  rw [dist_eq_norm]
  have hδR : 0 ≤ (δ:ℝ) := by exact_mod_cast hδ
  nlinarith [norm_nonneg (cqReal ζ-(x:ℂ))]

private theorem disc_abs_re_le_jc (z : ℂ) : |z.re| ≤ jc z := by
  have h1 := Complex.abs_re_le_norm (z-1)
  have h2 := Complex.abs_re_le_norm (z+1)
  simp only [Complex.sub_re,Complex.add_re,Complex.one_re] at h1 h2
  have ha := abs_add_le (z.re-1) (z.re+1)
  have he : |(z.re-1)+(z.re+1)|=2*|z.re| := by
    rw [show (z.re-1)+(z.re+1)=2*z.re by ring,abs_mul]
    norm_num
  rw [he] at ha
  unfold jc
  linarith

private theorem disc_one_lt_jc_im {z : ℂ} (hz : z.im ≠ 0) : 1 < jc z := by
  have h1 := Complex.abs_re_lt_norm.mpr (show (z-1).im ≠ 0 by simpa using hz)
  have h2 := Complex.abs_re_lt_norm.mpr (show (z+1).im ≠ 0 by simpa using hz)
  simp only [Complex.sub_re,Complex.add_re,Complex.one_re] at h1 h2
  have ha := abs_sub (z.re+1) (z.re-1)
  rw [show z.re+1-(z.re-1)=2 by ring] at ha
  norm_num at ha
  unfold jc
  linarith

theorem one_lt_jc_of_not_mem_sourceSlit (z : ℂ) (hz : z ∉ sourceSlit) : 1 < jc z := by
  by_cases him : z.im=0
  · have hreal : z=(z.re:ℂ) := by apply Complex.ext <;> simp [him]
    have hnot : z.re ∉ Icc (-1:ℝ) 1 := by
      intro hx
      exact hz ⟨z.re,hx,hreal.symm⟩
    have ha : 1 < |z.re| := by
      by_contra h
      exact hnot (abs_le.mp (le_of_not_gt h))
    exact ha.trans_le (disc_abs_re_le_jc z)
  · exact disc_one_lt_jc_im him

theorem affine_off_slit_of_distance (ζ γ : ℂ) (R δ fraction : ℝ)
    (hδ : 0 < δ) (hf : fraction < 1)
    (hsep : ∀ x ∈ Icc (-1:ℝ) 1,δ ≤ ‖ζ-(x:ℂ)‖)
    (hbound : ‖γ‖*R ≤ fraction*δ) :
    ∀ u ∈ Metric.ball (0:ℂ) R,1 < jc (ζ+γ*u) := by
  intro u hu
  have huR : ‖u‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hu
  have hn : ‖γ*u‖ < δ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left huR.le (norm_nonneg γ)).trans_lt
      (hbound.trans_lt (by nlinarith))
  apply one_lt_jc_of_not_mem_sourceSlit
  rintro ⟨x,hx,he⟩
  have hd := hsep x hx
  rw [he,show ζ-(ζ+γ*u)= -(γ*u) by ring,norm_neg] at hd
  linarith

theorem checked_affine_off_slit (ζ γ : CQ) (δ R fraction gammaHi : ℚ)
    (hδ : 0 < δ) (hR : 0 ≤ R) (hf : fraction < 1) (hgamma : 0 ≤ gammaHi)
    (hsq : δ^2 ≤ slitDistSq ζ) (hg : cqSq γ ≤ gammaHi^2)
    (hbound : gammaHi*R ≤ fraction*δ) :
    ∀ u ∈ Metric.ball (0:ℂ) (R:ℝ),1 < jc (cqReal ζ+cqReal γ*u) := by
  have hlow := slit_distance_lower ζ δ hδ.le hsq
  have hn : ‖cqReal γ‖ ≤ (gammaHi:ℝ) := by
    have he : ‖cqReal γ‖^2 ≤ (gammaHi:ℝ)^2 := by
      rw [← cqSq_eq_norm_sq]
      exact_mod_cast hg
    have hnon : 0 ≤ (gammaHi:ℝ) := by exact_mod_cast hgamma
    nlinarith [norm_nonneg (cqReal γ)]
  apply affine_off_slit_of_distance (cqReal ζ) (cqReal γ) (R:ℝ) (δ:ℝ) (fraction:ℝ)
    (by exact_mod_cast hδ) (by exact_mod_cast hf)
  · intro x hx
    have hd := Metric.infDist_le_dist_of_mem (x := cqReal ζ) (show (x:ℂ) ∈ sourceSlit from ⟨x,hx,rfl⟩)
    exact hlow.trans (by simpa only [dist_eq_norm] using hd)
  · exact (mul_le_mul_of_nonneg_right hn (by exact_mod_cast hR)).trans (by exact_mod_cast hbound)

#print axioms one_lt_jc_of_not_mem_sourceSlit
#print axioms affine_off_slit_of_distance
#print axioms checked_affine_off_slit

#print axioms slit_distance_lower
end
end CatalanCore.Li2.DecayCert
