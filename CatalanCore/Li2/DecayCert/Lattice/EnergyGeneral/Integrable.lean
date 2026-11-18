module
public import CatalanCore.Li2.DecayCert.Lattice.EnergyGeneral.Prelude
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem left_source_ae (μ : Measure ℂ) (hs : μ {s | s.im ≠ 0 ∨ s.re < 0}=0) :
    ∀ᵐ s : ℂ ∂μ,s.im=0 ∧ 0 ≤ s.re := by
  have hh := (measure_eq_zero_iff_ae_notMem).mp hs
  filter_upwards [hh] with s hs
  simpa only [Set.mem_setOf_eq,not_or,not_not,not_lt] using hs

theorem disk_source_ae (ν : Measure ℂ) (y0 h : ℝ)
    (hs : ν {s | h < ‖s-(y0:ℂ)‖}=0) : ∀ᵐ s : ℂ ∂ν,‖s-(y0:ℂ)‖ ≤ h := by
  have hh := (measure_eq_zero_iff_ae_notMem).mp hs
  filter_upwards [hh] with s hs
  simpa only [Set.mem_setOf_eq,not_lt] using hs

theorem left_log_integrable_iff (μ : Measure ℂ) [IsFiniteMeasure μ]
    (y0 h : ℝ) (hy : y0 < 0) (hh : 0 ≤ h) (hsep : h < -y0)
    (hs : μ {s | s.im ≠ 0 ∨ s.re < 0}=0) (w : ℂ) (hw : ‖w-(y0:ℂ)‖ ≤ h) :
    Integrable (fun s => Real.log ‖(y0:ℂ)-s‖) μ ↔ Integrable (fun s => Real.log ‖w-s‖) μ := by
  have hdiff : Integrable (fun s => Real.log ‖w-s‖-Real.log ‖(y0:ℂ)-s‖) μ := by
    apply (integrable_const (h/(-y0)/(1-h/(-y0)))).mono' (by fun_prop)
    filter_upwards [left_source_ae μ hs] with s hs
    have hp := left_log_jet_point s w y0 h hy hh hsep hs.1 hs.2 hw 0
    simpa only [Real.norm_eq_abs,Finset.range_zero,Finset.sum_empty,Complex.zero_re,add_zero,
      Nat.zero_add,Nat.cast_one,pow_one,one_mul] using hp
  constructor
  · intro hb
    convert hdiff.add hb using 1
    funext s
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · intro hwint
    convert hwint.sub hdiff using 1
    funext s
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

theorem log_base_integrable_of_cross (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hne : ν ≠ 0) (y0 h : ℝ) (hy : y0 < 0) (hh : 0 ≤ h) (hsep : h < -y0)
    (hs1 : μ {s | s.im ≠ 0 ∨ s.re < 0}=0) (hs2 : ν {s | h < ‖s-(y0:ℂ)‖}=0)
    (hcross : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) (ν.prod μ)) :
    Integrable (fun s => Real.log ‖(y0:ℂ)-s‖) μ := by
  haveI : NeZero ν := ⟨hne⟩
  rcases ((disk_source_ae ν y0 h hs2).and hcross.prod_right_ae).exists with ⟨w,hw,hi⟩
  exact (left_log_integrable_iff μ y0 h hy hh hsep hs1 w hw).mpr hi

theorem left_inverse_integrable (μ : Measure ℂ) [IsFiniteMeasure μ] (y0 : ℝ) (hy : y0 < 0)
    (hs : μ {s | s.im ≠ 0 ∨ s.re < 0}=0) (k : ℕ) :
    Integrable (fun s : ℂ => (s-(y0:ℂ))^(-((k+1:ℕ):ℤ))) μ := by
  apply (integrable_const ((-y0)⁻¹^(k+1))).mono' (by
    simp only [zpow_neg, zpow_natCast]
    exact ((measurable_id.sub_const (y0:ℂ)).pow_const (k+1)).inv.aestronglyMeasurable)
  filter_upwards [left_source_ae μ hs] with s hs
  have ht : 0 < s.re-y0 := by linarith [hs.2]
  have hsr : s=(s.re:ℂ) := by apply Complex.ext <;> simp [hs.1]
  have hn : ‖s-(y0:ℂ)‖=s.re-y0 := by
    rw [hsr,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
    simp only [Complex.ofReal_re]
  rw [zpow_neg,zpow_natCast,← inv_pow,norm_pow,norm_inv,hn]
  apply pow_le_pow_left₀ (inv_nonneg.mpr ht.le)
  exact inv_anti₀ (neg_pos.mpr hy) (by linarith [hs.2])

theorem disk_moment_integrable (ν : Measure ℂ) [IsFiniteMeasure ν] (y0 h : ℝ)
    (hs : ν {s | h < ‖s-(y0:ℂ)‖}=0) (k : ℕ) :
    Integrable (fun s : ℂ => (s-(y0:ℂ))^k) ν := by
  apply (integrable_const (h^k)).mono' (by fun_prop)
  filter_upwards [disk_source_ae ν y0 h hs] with s hs
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hs k
#print axioms left_log_integrable_iff
#print axioms log_base_integrable_of_cross
#print axioms left_inverse_integrable
#print axioms disk_moment_integrable
end
end CatalanCore.Li2.DecayCert
