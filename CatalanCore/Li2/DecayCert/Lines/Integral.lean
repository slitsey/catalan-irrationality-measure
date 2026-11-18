module
public import CatalanCore.Li2.DecayCert.Lines.Basic
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem integral_affine_trapezoid (a b κ l r : ℝ) :
    (∫ u in l..r, a+b*u-κ) = ((a+b*l-κ)+(a+b*r-κ))*(r-l)/2 := by
  have hd (u : ℝ) : HasDerivAt (fun x : ℝ => a*x+(b/2)*x^2-κ*x) (a+b*u-κ) u := by
    convert (((hasDerivAt_id' u).const_mul a).add (((hasDerivAt_id' u).pow 2).const_mul (b/2))).sub
      ((hasDerivAt_id' u).const_mul κ) using 1 <;> ring
  have hf : Continuous (fun u : ℝ => a+b*u-κ) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hd u) (hf.intervalIntegrable l r)
  convert he using 1 <;> ring

theorem affine_between (a b κ l r u : ℝ) (hu : u ∈ Icc l r) :
    min (a+b*l-κ) (a+b*r-κ) ≤ a+b*u-κ ∧ a+b*u-κ ≤ max (a+b*l-κ) (a+b*r-κ) := by
  by_cases hb : 0 ≤ b
  · constructor
    · exact (min_le_left _ _).trans (by nlinarith [mul_nonneg hb (sub_nonneg.mpr hu.1)])
    · exact (show a+b*u-κ ≤ a+b*r-κ by nlinarith [mul_nonneg hb (sub_nonneg.mpr hu.2)]).trans (le_max_right _ _)
  · have hb' : b ≤ 0 := le_of_lt (lt_of_not_ge hb)
    constructor
    · exact (min_le_right _ _).trans (by nlinarith [mul_nonpos_of_nonpos_of_nonneg hb' (sub_nonneg.mpr hu.2)])
    · exact (show a+b*u-κ ≤ a+b*l-κ by nlinarith [mul_nonpos_of_nonpos_of_nonneg hb' (sub_nonneg.mpr hu.1)]).trans (le_max_left _ _)

theorem integral_pos_affine_nonneg (a b κ l r : ℝ) (hlr : l ≤ r)
    (hl : 0 ≤ a+b*l-κ) (hr : 0 ≤ a+b*r-κ) :
    (∫ u in l..r, pos (a+b*u-κ))=((a+b*l-κ)+(a+b*r-κ))*(r-l)/2 := by
  rw [← integral_affine_trapezoid]
  apply intervalIntegral.integral_congr
  intro u hu
  have hh := (affine_between a b κ l r u (by simpa [uIcc_of_le hlr] using hu)).1
  exact max_eq_left ((le_min hl hr).trans hh)

theorem integral_pos_affine_nonpos (a b κ l r : ℝ) (hlr : l ≤ r)
    (hl : a+b*l-κ ≤ 0) (hr : a+b*r-κ ≤ 0) :
    (∫ u in l..r, pos (a+b*u-κ))=0 := by
  have he : (∫ u in l..r, pos (a+b*u-κ))=∫ u in l..r, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hh := (affine_between a b κ l r u (by simpa [uIcc_of_le hlr] using hu)).2
    exact max_eq_right (hh.trans (max_le hl hr))
  simpa using he

theorem int_pos_line_cell_real (a b R κ : ℝ) (hR : 0 ≤ R) :
    (∫ u in (0:ℝ)..R, pos (a+b*u-κ))=linePosR a b R κ := by
  by_cases hzero : R=0
  · subst R
    simp [linePosR]
  have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
  have hf : Continuous (fun u : ℝ => pos (a+b*u-κ)) := by unfold pos; fun_prop
  unfold linePosR
  dsimp only
  split_ifs with hn hp hm
  · simpa using integral_pos_affine_nonneg a b κ 0 R hR (by simpa using hn.1) hn.2
  · have hb : b < 0 := by nlinarith [hp.1,hp.2]
    have hb0 : b ≠ 0 := ne_of_lt hb
    let q := (κ-a)/b
    have hq : a+b*q-κ=0 := by dsimp only [q]; field_simp [hb0] <;> ring
    have hq0 : 0 ≤ q := by nlinarith [hp.1]
    have hqR : q ≤ R := by nlinarith [hp.2]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 q) (hf.intervalIntegrable q R)]
    rw [integral_pos_affine_nonneg a b κ 0 q hq0 (by simpa using hp.1.le) hq.ge,
      integral_pos_affine_nonpos a b κ q R hqR hq.le hp.2.le]
    simp only [mul_zero,add_zero,sub_zero,hq]
    have hden : a-κ-(a+b*R-κ) ≠ 0 := by linarith [hp.1,hp.2]
    dsimp only [q]
    field_simp [hb0,hden] <;> ring
  · have hb : 0 < b := by nlinarith [hm.1,hm.2]
    have hb0 : b ≠ 0 := ne_of_gt hb
    let q := (κ-a)/b
    have hq : a+b*q-κ=0 := by dsimp only [q]; field_simp [hb0] <;> ring
    have hq0 : 0 ≤ q := by nlinarith [hm.2]
    have hqR : q ≤ R := by nlinarith [hm.1]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 q) (hf.intervalIntegrable q R)]
    rw [integral_pos_affine_nonpos a b κ 0 q hq0 (by simpa using hm.2.le) hq.le,
      integral_pos_affine_nonneg a b κ q R hqR hq.ge hm.1.le]
    simp only [zero_add,hq]
    have hden : a+b*R-κ-(a-κ) ≠ 0 := by linarith [hm.1,hm.2]
    dsimp only [q]
    field_simp [hb0,hden] <;> ring
  · have h0 : a-κ ≤ 0 := by
      by_contra hh
      have ha : 0 < a-κ := lt_of_not_ge hh
      by_cases h1 : 0 ≤ a+b*R-κ
      · exact hn ⟨ha.le,h1⟩
      · exact hp ⟨ha,lt_of_not_ge h1⟩
    have h1 : a+b*R-κ ≤ 0 := by
      by_contra hh
      have ha : 0 < a+b*R-κ := lt_of_not_ge hh
      by_cases h0' : 0 ≤ a-κ
      · exact hn ⟨h0',ha.le⟩
      · exact hm ⟨ha,lt_of_not_ge h0'⟩
    exact integral_pos_affine_nonpos a b κ 0 R hR (by simpa using h0) h1

theorem int_pos_line_cell (a b R κ : ℚ) (hR : 0 ≤ R) :
    (∫ u in (0:ℝ)..(R:ℝ), pos ((a:ℝ)+(b:ℝ)*u-(κ:ℝ)))=(linePos a b R κ:ℝ) := by
  rw [linePos_cast]
  exact int_pos_line_cell_real a b R κ (by exact_mod_cast hR)
#print axioms integral_affine_trapezoid
#print axioms affine_between
#print axioms integral_pos_affine_nonneg
#print axioms integral_pos_affine_nonpos
#print axioms int_pos_line_cell_real
#print axioms int_pos_line_cell
end
end CatalanCore.Li2.DecayCert
