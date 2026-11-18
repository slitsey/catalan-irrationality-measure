module
public import CatalanCore.Li2.DecayCert.Compile.DiscGeometry
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
noncomputable section

theorem norm_cqReal_le_cqL1 (q : CQ) : ‖cqReal q‖ ≤ (cqL1 q:ℝ) := by
  have hh := Complex.norm_le_abs_re_add_abs_im (cqReal q)
  rw [cqReal_mk] at hh
  simpa only [cqReal_mk,cqL1,Rat.cast_add,Rat.cast_abs] using hh

theorem norm_pow_sub_pow_bound (a b : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖a^(n+1)-b^(n+1)‖ ≤ (n+1:ℕ)*r^n*‖a-b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : a^(n+1+1)-b^(n+1+1)=a*(a^(n+1)-b^(n+1))+(a-b)*b^(n+1) := by ring
    rw [he]
    calc
      _ ≤ ‖a*(a^(n+1)-b^(n+1))‖+‖(a-b)*b^(n+1)‖ := norm_add_le _ _
      _ = ‖a‖*‖a^(n+1)-b^(n+1)‖+‖a-b‖*‖b‖^(n+1) := by rw [norm_mul,norm_mul,norm_pow]
      _ ≤ r*((n+1:ℕ)*r^n*‖a-b‖)+‖a-b‖*r^(n+1) := by
        exact add_le_add (mul_le_mul ha ih (norm_nonneg _) hr)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg b) hb _) (norm_nonneg _))
      _ = (n+1+1:ℕ)*r^(n+1)*‖a-b‖ := by push_cast; ring

theorem norm_taylor_displacement (b : ℕ → ℂ) (J : ℕ) (u v : ℂ) (r δ : ℝ)
    (hr : 0 ≤ r) (hu : ‖u‖ ≤ r) (hv : ‖v‖ ≤ r) (hδ : ‖u-v‖ ≤ δ) :
    ‖(∑ j ∈ Finset.range (J+1), b j*u^j)-(∑ j ∈ Finset.range (J+1), b j*v^j)‖ ≤
      δ*(∑ k ∈ Finset.range J, (k+1:ℕ)*‖b (k+1)‖*r^k) := by
  have he : (∑ j ∈ Finset.range (J+1), b j*u^j)-(∑ j ∈ Finset.range (J+1), b j*v^j) =
      ∑ k ∈ Finset.range J,b (k+1)*(u^(k+1)-v^(k+1)) := by
    rw [← Finset.sum_sub_distrib,Finset.sum_range_succ']
    simp only [pow_zero,mul_one,sub_self,zero_add,add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul]
  calc
    _ ≤ ‖b (k+1)‖*((k+1:ℕ)*r^k*‖u-v‖) :=
      mul_le_mul_of_nonneg_left (norm_pow_sub_pow_bound u v r hr hu hv k) (norm_nonneg _)
    _ ≤ ‖b (k+1)‖*((k+1:ℕ)*r^k*δ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ (by positivity)) (norm_nonneg _)
    _ = δ*((k+1:ℕ)*‖b (k+1)‖*r^k) := by ring

#print axioms norm_taylor_displacement

#print axioms norm_cqReal_le_cqL1
#print axioms norm_pow_sub_pow_bound
end
end CatalanCore.Li2.DecayCert
