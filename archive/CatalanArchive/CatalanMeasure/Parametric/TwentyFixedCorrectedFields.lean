module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyCorrectedFields
public import CatalanMeasure.Parametric.WeightedPopulationValue
@[expose] public section
namespace CatalanMeasure.Parametric.TwentyCertified
open OAI.InternalCatalan Set Filter
open scoped Topology
noncomputable section

theorem fixed_diagonal_eventually {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Icc (-1:ℝ) 0,
      reciprocalScale N*(a*Real.log (1+x^2)) ≤ δ :=by
  have hh :=(tendsto_order.mp (reciprocalScale_tendsto.mul_const (a*Real.log 2))).2 δ
    (by simpa only [zero_mul] using hδ)
  filter_upwards [hh] with N hc x hx
  have hsq : x^2 ≤ 1 :=by nlinarith only [hx.1,hx.2]
  have hlog : Real.log (1+x^2) ≤ Real.log 2 :=Real.log_le_log (by positivity) (by linarith only [hsq])
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog ha)
    (reciprocalScale_nonneg N)).trans hc.le
theorem fixed10_corrected_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0,
      populationPhysicalOneFixedField twenty N x+(lambda10:ℝ)*paramCaseField twenty N x-populationCommonLog twenty N x/(twenty.n N:ℝ) ≤ twentyFixed10+δ :=by
  have hh :=fixed_diagonal_eventually (a :=1/2) (by norm_num) hδ
  filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hc hN x hx
  have hb :=fixed10_bound hN hx.2
  have hd :=hc x ⟨hx.1,hx.2.le⟩
  have hnu : (twenty.n N:ℝ)=20*(N:ℝ) :=by simp [Parameters.n,twenty]
  have hcoef : 1/(2*(twenty.n N:ℝ))=reciprocalScale N/2 :=by
    simp only [hnu,reciprocalScale,div_eq_mul_inv,mul_inv_rev] <;> ring
  unfold populationPhysicalOneFixedField populationCommonLog
  rw [hcoef]
  nlinarith only [hb,hd]
theorem fixed11_corrected_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0,
      populationPhysicalOneFixedField twenty N x+(lambda11:ℝ)*paramCaseField twenty N x-populationCommonLog twenty N x/(twenty.n N:ℝ) ≤ twentyFixed11+δ :=by
  have hh :=fixed_diagonal_eventually (a :=1/2) (by norm_num) hδ
  filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hc hN x hx
  have hb :=fixed11_bound hN hx.2
  have hd :=hc x ⟨hx.1,hx.2.le⟩
  have hnu : (twenty.n N:ℝ)=20*(N:ℝ) :=by simp [Parameters.n,twenty]
  have hcoef : 1/(2*(twenty.n N:ℝ))=reciprocalScale N/2 :=by
    simp only [hnu,reciprocalScale,div_eq_mul_inv,mul_inv_rev] <;> ring
  unfold populationPhysicalOneFixedField populationCommonLog
  rw [hcoef]
  nlinarith only [hb,hd]
theorem fixed20_corrected_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0,
      populationPhysicalFixedField twenty N x-2*barrierTrialT p20 x-populationCommonLog twenty N x/(twenty.n N:ℝ) ≤ -(1/5:ℝ)+δ :=by
  have hh :=fixed_diagonal_eventually (a :=1) (by norm_num) hδ
  filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hc hN x hx
  have hb :=fixed20_bound hN hx.1 hx.2
  have hd :=hc x ⟨hx.1,hx.2.le⟩
  have hnu : (twenty.n N:ℝ)=20*(N:ℝ) :=by simp [Parameters.n,twenty]
  have hcoef : 1/(twenty.n N:ℝ)=reciprocalScale N :=by
    simp only [hnu,reciprocalScale,div_eq_mul_inv,mul_inv_rev] <;> ring
  unfold populationPhysicalFixedField populationCommonLog
  rw [hcoef]
  nlinarith only [hb,hd]
theorem fixed21_corrected_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0,
      populationPhysicalFixedField twenty N x-2*barrierTrialT p21 x-populationCommonLog twenty N x/(twenty.n N:ℝ) ≤ -(1/5:ℝ)+δ :=by
  have hh :=fixed_diagonal_eventually (a :=1) (by norm_num) hδ
  filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hc hN x hx
  have hb :=fixed21_bound hN hx.1 hx.2
  have hd :=hc x ⟨hx.1,hx.2.le⟩
  have hnu : (twenty.n N:ℝ)=20*(N:ℝ) :=by simp [Parameters.n,twenty]
  have hcoef : 1/(twenty.n N:ℝ)=reciprocalScale N :=by
    simp only [hnu,reciprocalScale,div_eq_mul_inv,mul_inv_rev] <;> ring
  unfold populationPhysicalFixedField populationCommonLog
  rw [hcoef]
  nlinarith only [hb,hd]

end
end CatalanMeasure.Parametric.TwentyCertified
