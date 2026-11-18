module
public import CatalanCore.Li2.DecayCert.Holder.Defs
public import CatalanCore.Li2.DecayCert.Holder.Chebyshev
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem cheb_T_real_lipschitz (n : ℕ) (x y : ℝ)
    (hx : x ∈ Icc (-1:ℝ) 1) (hy : y ∈ Icc (-1:ℝ) 1) :
    |T n y-T n x| ≤ (n:ℝ)^2*|y-x| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (f:=fun x : ℝ => (Polynomial.Chebyshev.T ℝ (n:ℤ)).eval x)
    (fun u hu => Polynomial.differentiableAt _)
    (fun u hu => by rw [Polynomial.deriv]; exact cheb_T_derivative_real_bound n u hu)
    (convex_Icc (-1:ℝ) 1) hx hy
  simpa only [T,Real.norm_eq_abs] using hh

theorem holder_own_cell (d : SegmentData) (hpos : d.densityNonneg)
    (b e : ℂ) (D : ℝ) (hD : 0 ≤ D) (hgeom : EndCellGeometry d b e D .own) :
    ∀ τ ∈ Icc 0 D,|P d.ν (b+e*(τ:ℂ))-P d.ν b| ≤ endMajorant d b e D .own := by
  obtain ⟨x0,hx0,hb⟩ := hgeom 0 ⟨le_rfl,hD⟩
  have hb0 : b=d.M+d.h*(x0:ℂ) := by simpa using hb
  intro τ hτ
  obtain ⟨x,hx,hpoint⟩ := hgeom τ hτ
  have hdiff : (((x-x0:ℝ):ℂ))=(e/d.h)*(τ:ℂ) := by
    have he : d.h*(((x-x0:ℝ):ℂ))=e*(τ:ℂ) := by
      push_cast
      linear_combination hb0-hpoint
    apply (mul_left_cancel₀ d.h_ne)
    calc
      d.h*(((x-x0:ℝ):ℂ))=e*(τ:ℂ) := he
      _ = d.h*((e/d.h)*(τ:ℂ)) := by field_simp [d.h_ne]
  have hnorm : |x-x0|=‖e/d.h‖*τ := by
    have hh := congrArg norm hdiff
    simpa only [Complex.norm_real,Real.norm_eq_abs,norm_mul,abs_of_nonneg hτ.1] using hh
  have hp := segPot_closed_own d hpos x hx
  have hp0 := segPot_closed_own d hpos x0 hx0
  rw [← hpoint] at hp
  rw [← hb0] at hp0
  rw [hp,hp0]
  have hsum : (∑ k ∈ Finset.range d.N,d.c (k+1)*T (k+1) x/(k+1:ℕ))-
      (∑ k ∈ Finset.range d.N,d.c (k+1)*T (k+1) x0/(k+1:ℕ)) =
      ∑ k ∈ Finset.range d.N,d.c (k+1)*(T (k+1) x-T (k+1) x0)/(k+1:ℕ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hcancel : (d.c 0*(Real.log ‖d.h‖-Real.log 2)-∑ k ∈ Finset.range d.N,d.c (k+1)*T (k+1) x/(k+1:ℕ))-
      (d.c 0*(Real.log ‖d.h‖-Real.log 2)-∑ k ∈ Finset.range d.N,d.c (k+1)*T (k+1) x0/(k+1:ℕ)) =
      -((∑ k ∈ Finset.range d.N,d.c (k+1)*T (k+1) x/(k+1:ℕ))-
        (∑ k ∈ Finset.range d.N,d.c (k+1)*T (k+1) x0/(k+1:ℕ))) := by ring
  rw [hcancel,abs_neg,hsum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  unfold endMajorant
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hn : (0:ℝ)<(k+1:ℕ) := by positivity
  have hlip := cheb_T_real_lipschitz (k+1) x0 x hx0 hx
  rw [hnorm] at hlip
  calc
    |d.c (k+1)*(T (k+1) x-T (k+1) x0)/(k+1:ℕ)| =
        |d.c (k+1)| *|T (k+1) x-T (k+1) x0|/(k+1:ℕ) := by rw [abs_div,abs_mul,abs_of_pos hn]
    _ ≤ |d.c (k+1)| *((k+1:ℕ)^2*(‖e/d.h‖*τ))/(k+1:ℕ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlip (abs_nonneg _)) hn.le
    _ = (k+1:ℕ)*|d.c (k+1)| *‖e/d.h‖*τ := by field_simp [hn.ne'] <;> ring
    _ ≤ (k+1:ℕ)*|d.c (k+1)| *‖e/d.h‖*D := mul_le_mul_of_nonneg_left hτ.2 (by positivity)
#print axioms cheb_T_real_lipschitz
#print axioms holder_own_cell
end
end CatalanCore.Li2.DecayCert
