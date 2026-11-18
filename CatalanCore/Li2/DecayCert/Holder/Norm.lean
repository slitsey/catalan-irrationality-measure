module
public import CatalanCore.Li2.DecayCert.Holder.Bounds
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Tools.Joukowski
noncomputable section

theorem norm_jq_off_lower (ζ z : ℂ) (l : ℝ) (hl : 0 ≤ l)
    (hz : ‖z-ζ‖ ≤ l) (h1 : l < ‖ζ-1‖) (h2 : l < ‖ζ+1‖) (hs : 1 < jc z) :
    Real.sqrt ((‖ζ-1‖-l)*(‖ζ+1‖-l)) ≤ ‖jq z‖ := by
  have he1 : ‖ζ-1‖ ≤ ‖z-1‖+‖z-ζ‖ := by
    have he : ζ-1=(z-1)-(z-ζ) := by ring
    rw [he]
    exact norm_sub_le _ _
  have he2 : ‖ζ+1‖ ≤ ‖z+1‖+‖z-ζ‖ := by
    have he : ζ+1=(z+1)-(z-ζ) := by ring
    rw [he]
    exact norm_sub_le _ _
  have hlo1 : ‖ζ-1‖-l ≤ ‖z-1‖ := by linarith
  have hlo2 : ‖ζ+1‖-l ≤ ‖z+1‖ := by linarith
  have hprod : (‖ζ-1‖-l)*(‖ζ+1‖-l) ≤ ‖jq z‖^2 := by
    rw [norm_jq_sq_product z hs]
    exact mul_le_mul hlo1 hlo2 (sub_nonneg.mpr h2.le) (norm_nonneg _)
  exact (Real.sqrt_le_iff).2 ⟨norm_nonneg _,hprod⟩

theorem norm_jq_branch_lower (ε γ : ℂ) (t D : ℝ) (hε : ε=1 ∨ ε= -1)
    (ht : t ∈ Icc 0 D) (hl : ‖γ‖*D < 1) (hs : 1 < jc (ε+γ*(t:ℂ))) :
    Real.sqrt ‖γ‖*Real.sqrt t*Real.sqrt (2-‖γ‖*D) ≤ ‖jq (ε+γ*(t:ℂ))‖ := by
  have hDt : 0 ≤ D := ht.1.trans ht.2
  have hdelta : ‖γ*(t:ℂ)‖=‖γ‖*t := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
  have hδ : ‖γ*(t:ℂ)‖ ≤ ‖γ‖*D := by rw [hdelta]; exact mul_le_mul_of_nonneg_left ht.2 (norm_nonneg _)
  have hprod : (‖γ‖*t)*(2-‖γ‖*D) ≤ ‖jq (ε+γ*(t:ℂ))‖^2 := by
    rw [norm_jq_sq_product _ hs]
    rcases hε with rfl | rfl
    · have he1 : (1:ℂ)+γ*(t:ℂ)-1=γ*(t:ℂ) := by ring
      have he2 : (2:ℂ)=((1:ℂ)+γ*(t:ℂ)+1)-γ*(t:ℂ) := by ring
      have hn : 2 ≤ ‖(1:ℂ)+γ*(t:ℂ)+1‖+‖γ*(t:ℂ)‖ := by
        have hh := norm_sub_le ((1:ℂ)+γ*(t:ℂ)+1) (γ*(t:ℂ))
        rw [← he2] at hh
        simpa only [Complex.norm_two] using hh
      rw [he1,hdelta]
      exact mul_le_mul_of_nonneg_left (by linarith : 2-‖γ‖*D ≤ ‖(1:ℂ)+γ*(t:ℂ)+1‖)
        (mul_nonneg (norm_nonneg _) ht.1)
    · have he1 : (-1:ℂ)+γ*(t:ℂ)+1=γ*(t:ℂ) := by ring
      have he2 : (-2:ℂ)=((-1:ℂ)+γ*(t:ℂ)-1)-γ*(t:ℂ) := by ring
      have hn : 2 ≤ ‖(-1:ℂ)+γ*(t:ℂ)-1‖+‖γ*(t:ℂ)‖ := by
        have hh := norm_sub_le ((-1:ℂ)+γ*(t:ℂ)-1) (γ*(t:ℂ))
        rw [← he2] at hh
        simpa only [norm_neg,Complex.norm_two] using hh
      rw [he1,hdelta]
      have hh := mul_le_mul_of_nonneg_right (by linarith : 2-‖γ‖*D ≤ ‖(-1:ℂ)+γ*(t:ℂ)-1‖)
        (mul_nonneg (norm_nonneg γ) ht.1)
      simpa only [mul_comm] using hh
  have hsq : (Real.sqrt ‖γ‖*Real.sqrt t*Real.sqrt (2-‖γ‖*D))^2=(‖γ‖*t)*(2-‖γ‖*D) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (norm_nonneg _),Real.sq_sqrt ht.1,Real.sq_sqrt (by linarith)]
  have hnon : 0 ≤ Real.sqrt ‖γ‖*Real.sqrt t*Real.sqrt (2-‖γ‖*D) := by positivity
  nlinarith [norm_nonneg (jq (ε+γ*(t:ℂ)))]
#print axioms norm_jq_off_lower
#print axioms norm_jq_branch_lower
end
end CatalanCore.Li2.DecayCert
