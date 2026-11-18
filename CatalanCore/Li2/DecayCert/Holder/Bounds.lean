module
public import CatalanCore.Li2.DecayCert.Holder.Potential
public import CatalanCore.Li2.DecayCert.Holder.Chebyshev
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section

theorem endPhi_relation (d : SegmentData) (b e : ℂ) (D : ℝ) (hD : 0 ≤ D) :
    (endPhi d b e D)^2=2*(endZ d b e D)*(endPhi d b e D)+1 := by
  have hs := Real.sq_sqrt (show 0 ≤ (endZ d b e D)^2+1 by positivity)
  unfold endPhi
  nlinarith

theorem end_path_norm_le (d : SegmentData) (b e : ℂ) (D t : ℝ) (ht : t ∈ Icc 0 D) :
    ‖(b+e*(t:ℂ)-d.M)/d.h‖ ≤ endZ d b e D := by
  have he : (b+e*(t:ℂ)-d.M)/d.h=(b-d.M)/d.h+(e/d.h)*(t:ℂ) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
  change ‖(b-d.M)/d.h‖+‖e/d.h‖*t ≤ ‖(b-d.M)/d.h‖+‖e/d.h‖*D
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left ht.2 (norm_nonneg (e/d.h)))

theorem fpoly_norm_bound (d : SegmentData) (z : ℂ) (Z Φ : ℝ)
    (hZ : 0 ≤ Z) (hz : ‖z‖ ≤ Z) (hΦ : 1 ≤ Φ) (hrel : Φ^2=2*Z*Φ+1) :
    ‖(fpoly d.c d.N).eval z‖ ≤ ∑ k ∈ Finset.range (d.N+1),|d.c k| *Φ^k := by
  unfold fpoly
  rw [Polynomial.eval_finset_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  simp only [Polynomial.eval_mul,Polynomial.eval_C,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (cheb_T_complex_bound z Z Φ hZ hz hΦ hrel k) (abs_nonneg _)

theorem rpoly_norm_bound (d : SegmentData) (z : ℂ) (Z Φ : ℝ)
    (hZ : 0 ≤ Z) (hz : ‖z‖ ≤ Z) (hΦ : 1 ≤ Φ) (hrel : Φ^2=2*Z*Φ+1) :
    ‖(rpoly d.c d.N).eval z‖ ≤ ∑ k ∈ Finset.range d.N,(k+1:ℕ)*|d.c (k+1)| *Φ^k := by
  unfold rpoly
  rw [Polynomial.eval_finset_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  simp only [Polynomial.eval_mul,Polynomial.eval_C,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ |d.c (k+1)| *((k+1:ℕ)*Φ^k) :=
      mul_le_mul_of_nonneg_left (cheb_U_complex_bound z Z Φ hZ hz hΦ hrel k) (abs_nonneg _)
    _ = _ := by ring

theorem segmentPathDerivative_bound (d : SegmentData) (b e : ℂ) (D t : ℝ)
    (hD : 0 ≤ D) (ht : t ∈ Icc 0 D) :
    |segmentPathDerivative d b e t| ≤ ‖e/d.h‖*
      ((∑ k ∈ Finset.range (d.N+1),|d.c k| *(endPhi d b e D)^k)/
        ‖jq ((b+e*(t:ℂ)-d.M)/d.h)‖+
      (∑ k ∈ Finset.range d.N,(k+1:ℕ)*|d.c (k+1)| *(endPhi d b e D)^k)) := by
  let z := (b+e*(t:ℂ)-d.M)/d.h
  have hz := end_path_norm_le d b e D t ht
  have hZ := endZ_nonneg d b e D hD
  have hΦ := endPhi_one_le d b e D hD
  have hrel := endPhi_relation d b e D hD
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sub_le _ _).trans
  rw [norm_div]
  exact add_le_add
    (div_le_div_of_nonneg_right (fpoly_norm_bound d z _ _ hZ hz hΦ hrel) (norm_nonneg _))
    (rpoly_norm_bound d z _ _ hZ hz hΦ hrel)

theorem norm_jq_sq_product (z : ℂ) (hs : 1 < jc z) :
    ‖jq z‖^2=‖z-1‖*‖z+1‖ := by
  calc
    _ = ‖(jq z)^2‖ := (norm_pow _ _).symm
    _ = ‖(z-1)*(z+1)‖ := by rw [jq_sq hs]; congr 1; ring
    _ = _ := norm_mul _ _
#print axioms endPhi_relation
#print axioms end_path_norm_le
#print axioms fpoly_norm_bound
#print axioms rpoly_norm_bound
#print axioms segmentPathDerivative_bound
#print axioms norm_jq_sq_product
end
end CatalanCore.Li2.DecayCert
