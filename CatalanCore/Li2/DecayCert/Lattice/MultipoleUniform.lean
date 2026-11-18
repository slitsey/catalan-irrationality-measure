module
public import CatalanCore.Li2.DecayCert.Multipole
public import CatalanCore.Li2.DecayCert.RealCells
@[expose] public section
set_option Elab.async false
open MeasureTheory Set
open scoped BigOperators
open CatalanCore.Li2.Decay
namespace CatalanCore.Li2.DecayCert

theorem mpErr_mono_ratio (m u v : ℝ) (K : ℕ) (hm : 0≤m)
    (hu : 0≤u) (huv : u≤v) (hv : v<1) : mpErr m u K≤mpErr m v K := by
  have hv0 := hu.trans huv
  have hk : (0:ℝ)<(K+1:ℕ) := by positivity
  unfold mpErr
  apply div_le_div₀ (mul_nonneg hm (pow_nonneg hv0 _))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv _) hm)
    (mul_pos hk (sub_pos.mpr hv))
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left huv 1) hk.le

theorem logPot_multipole_uniform_right
    (σ : Measure ℂ) [IsFiniteMeasure σ] (y0 H a b : ℝ)
    (hH : 0≤H) (hs : σ {s | H<‖s-(y0:ℂ)‖}=0)
    (hsep : H<a-y0) (hab : a≤b) (K : ℕ) :
    ∀ x∈Icc a b,
      |U σ (x:ℂ)-mp σ (y0:ℂ) (x:ℂ) K|≤
        mpErr (σ.real univ) (H/(a-y0)) K := by
  intro x hx
  have ha : 0<a-y0 := hH.trans_lt hsep
  have hax : a-y0≤x-y0 := sub_le_sub_right hx.1 y0
  have hxp : 0<x-y0 := ha.trans_le hax
  have hn : ‖(x:ℂ)-(y0:ℂ)‖=x-y0 := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxp]
  have hsep' : H<‖(x:ℂ)-(y0:ℂ)‖ := by rw [hn]; exact hsep.trans_le hax
  have hbase := logPot_multipole σ (y0:ℂ) (x:ℂ) H hH hs hsep' K
  rw [hn] at hbase
  have hr : H/(x-y0)≤H/(a-y0) := div_le_div₀ hH le_rfl ha hax
  have hv : H/(a-y0)<1 := (div_lt_one ha).mpr hsep
  exact hbase.trans (mpErr_mono_ratio (σ.real univ) (H/(x-y0)) (H/(a-y0)) K
    ENNReal.toReal_nonneg (div_nonneg hH hxp.le) hr hv)

#print axioms mpErr_mono_ratio
#print axioms logPot_multipole_uniform_right
end CatalanCore.Li2.DecayCert
