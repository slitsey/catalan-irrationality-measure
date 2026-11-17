module
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
set_option Elab.async false
open Set
namespace CatalanCore.Li2.DecayCert
noncomputable def xlog (x : ℝ) : ℝ := x*Real.log x

theorem mul_log_le_chord (u R : ℝ) (hu : 0 ≤ u) (hR : 0 < R) (hur : u ≤ R) :
    xlog u ≤ u*Real.log R := by
  by_cases hu0 : u=0
  · simp [hu0,xlog]
  · exact mul_le_mul_of_nonneg_left (Real.log_le_log (lt_of_le_of_ne hu (Ne.symm hu0)) hur) hu

theorem mul_log_le_tangent (u t : ℝ) (hu : 0 ≤ u) (ht : 0 < t) :
    (Real.log t+1)*u-t ≤ xlog u := by
  by_cases hu0 : u=0
  · simp [hu0,xlog,ht.le]
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have h := Real.log_le_sub_one_of_pos (div_pos ht hup)
    rw [Real.log_div ht.ne' hup.ne'] at h
    have hm := mul_le_mul_of_nonneg_left h hu
    have he : u*(t/u-1)=t-u := by field_simp
    rw [he] at hm
    dsimp [xlog]
    nlinarith

theorem xlogx_hull (h u : ℝ) (hh : 0 < h) (hsmall : h ≤ Real.exp (-1))
    (hu : u ∈ Icc 0 h) : xlog u ∈ Icc (xlog h) 0 := by
  have hh' : h ∈ Icc 0 (Real.exp (-1)) := ⟨hh.le,hsmall⟩
  have hu' : u ∈ Icc 0 (Real.exp (-1)) := ⟨hu.1,hu.2.trans hsmall⟩
  have hz : (0:ℝ) ∈ Icc 0 (Real.exp (-1)) := ⟨le_rfl,(Real.exp_pos _).le⟩
  refine ⟨Real.mul_log_strictAntiOn.antitoneOn hu' hh' hu.2,?_⟩
  simpa [xlog] using Real.mul_log_strictAntiOn.antitoneOn hz hu' hu.1
#print axioms mul_log_le_chord
#print axioms mul_log_le_tangent
#print axioms xlogx_hull
end CatalanCore.Li2.DecayCert
