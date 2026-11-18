module
public import CatalanCore.Li2.Uniform.Candidate
public import CatalanCore.Li2.DecayCert.Density.Base
@[expose] public section
set_option Elab.async false
open Set
namespace CatalanCore.Li2.Uniform.FixedData
open CatalanCore.Li2.DecayCert

def logGapLow : ℚ := 111277/50000
def logGapHigh : ℚ := 44511/20000

theorem logGapLow_bound : Real.log (logGapLow:ℝ)≤(4/5:ℝ) := by
  have h := scalarUpperCheck_sound (.log 8 logGapLow) (4/5) (by decide +kernel)
  simpa only [ScalarExpr.value,Rat.cast_div,Rat.cast_ofNat] using h

theorem logGapHigh_bound : (4/5:ℝ)<Real.log (logGapHigh:ℝ) := by
  have h := scalarLowerCheck_sound (4/5+1/1000000) (.log 8 logGapHigh) (by decide +kernel)
  change ((4/5+1/1000000:ℚ):ℝ)≤Real.log (logGapHigh:ℝ) at h
  norm_num only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] at h
  linarith

theorem log_width_iff (x y : ℝ) (hx : 0<x) (hy : 0<y)
    (hgap : x/y≤(logGapLow:ℝ) ∨ (logGapHigh:ℝ)≤x/y) :
    Real.log (x/y)≤(4/5:ℝ) ↔ x/y≤(logGapLow:ℝ) := by
  constructor
  · intro h
    rcases hgap with hlo | hhi
    · exact hlo
    · have hp : (0:ℝ)<(logGapHigh:ℝ) := by norm_num [logGapHigh]
      have hh := Real.log_le_log hp hhi
      linarith [logGapHigh_bound]
  · intro h
    exact (Real.log_le_log (div_pos hx hy) h).trans logGapLow_bound

theorem node_t_lt (a b : Node) (ha : 0<a.magnitude) (hb : 0<b.magnitude) :
    a.t<b.t ↔ b.magnitude<a.magnitude := by
  have haR : (0:ℝ)<(a.magnitude:ℝ) := by exact_mod_cast ha
  have hbR : (0:ℝ)<(b.magnitude:ℝ) := by exact_mod_cast hb
  simp only [Node.t,one_div,Real.log_inv,neg_lt_neg_iff]
  rw [Real.log_lt_log_iff hbR haR]
  exact Rat.cast_lt

theorem node_width (a b : Node) (ha : 0<a.magnitude) (hb : 0<b.magnitude) :
    b.t-a.t=Real.log ((a.magnitude:ℝ)/(b.magnitude:ℝ)) := by
  have haR : (0:ℝ)<(a.magnitude:ℝ) := by exact_mod_cast ha
  have hbR : (0:ℝ)<(b.magnitude:ℝ) := by exact_mod_cast hb
  simp only [Node.t,one_div,Real.log_inv,Real.log_div haR.ne' hbR.ne']
  ring

theorem node_allowed_iff (a b : Node) (ha : 0<a.magnitude) (hb : 0<b.magnitude)
    (hgap : a.magnitude/b.magnitude≤logGapLow ∨ logGapHigh≤a.magnitude/b.magnitude) :
    (a.frame=b.frame ∧ a.t<b.t ∧ b.t-a.t≤(4/5:ℝ)) ↔
      (a.frame=b.frame ∧ b.magnitude<a.magnitude ∧ a.magnitude/b.magnitude≤logGapLow) := by
  have haR : (0:ℝ)<(a.magnitude:ℝ) := by exact_mod_cast ha
  have hbR : (0:ℝ)<(b.magnitude:ℝ) := by exact_mod_cast hb
  have hgR : (a.magnitude:ℝ)/(b.magnitude:ℝ)≤(logGapLow:ℝ) ∨
      (logGapHigh:ℝ)≤(a.magnitude:ℝ)/(b.magnitude:ℝ) := by exact_mod_cast hgap
  rw [node_t_lt a b ha hb,node_width a b ha hb,log_width_iff _ _ haR hbR hgR]
  norm_cast
#print axioms logGapLow_bound
#print axioms logGapHigh_bound
#print axioms node_allowed_iff
end CatalanCore.Li2.Uniform.FixedData
