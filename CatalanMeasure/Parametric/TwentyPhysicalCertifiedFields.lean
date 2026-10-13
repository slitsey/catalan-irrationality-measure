module
public import CatalanMeasure.Parametric.TwentyFixedCorrectedFields
@[expose] public section
namespace CatalanMeasure.Parametric.TwentyCertified
open OAI.InternalCatalan Set Filter
open scoped Topology
noncomputable section

theorem physicalOne_row_identity (N : ℕ) (lambda : ℝ) (pp v : ℕ → ℝ) (x : ℝ) :
    populationPhysicalOneFreeField twenty N x+lambda*paramCaseField twenty N x-
      2*barrierTrialT pp x-barrierTrialS v x-Real.log (1-x)/(2*(twenty.n N:ℝ))=
    paramPopulationRowField twenty N 1 x+lambda*paramCaseField twenty N x-
      2*barrierTrialT pp x-barrierTrialS v x+
      reciprocalScale N*((3/2:ℝ)*Real.log (1+x^2)-(1/2)*Real.log (1-x)) :=by
  unfold populationPhysicalOneFreeField
  have hnu : (twenty.n N:ℝ)=20*(N:ℝ) :=by simp [Parameters.n,twenty]
  simp only [hnu,reciprocalScale,div_eq_mul_inv,mul_inv_rev]
  ring

theorem physicalTwo_row_identity (N : ℕ) (pp v : ℕ → ℝ) (x : ℝ) :
    populationPhysicalFreeField twenty N x-4*barrierTrialT pp x-barrierTrialS v x-
      Real.log (1-x)/(2*(twenty.n N:ℝ))=
    paramPopulationRowField twenty N 2 x-4*barrierTrialT pp x-barrierTrialS v x+
      reciprocalScale N*(2*Real.log (1+x^2)-(1/2)*Real.log (1-x)) :=by
  unfold populationPhysicalFreeField
  have hnu : (twenty.n N:ℝ)=20*(N:ℝ) :=by simp [Parameters.n,twenty]
  simp only [hnu,reciprocalScale,div_eq_mul_inv,mul_inv_rev]
  ring

theorem physical_column_identity {N : ℕ} (hN : 0<N) (a : ℝ) (v : ℕ → ℝ) (s : ℝ) :
    populationEndpointColumnField twenty N a s+2*barrierTrialT v s-
      Real.log (1-s)/(twenty.n N:ℝ)=
    (3/20:ℝ)*Real.log s+(1/20:ℝ)*Real.log (1-s)+a*Real.log (1+s)+
      2*barrierTrialT v s-reciprocalScale N*Real.log (1-s) :=by
  have hNR : (N:ℝ)≠0 :=by exact_mod_cast hN.ne'
  unfold populationEndpointColumnField reciprocalScale
  change (3*N:ℕ)/(20*N:ℕ)*Real.log s+(1*N:ℕ)/(20*N:ℕ)*Real.log (1-s)+a*Real.log (1+s)+
    2*barrierTrialT v s-Real.log (1-s)/(20*N:ℕ)=_
  push_cast
  field_simp <;> ring

theorem physical_row10_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      populationPhysicalOneFreeField twenty N x+(lambda10:ℝ)*paramCaseField twenty N x-
        2*barrierTrialT p10 x-barrierTrialS v10 x-Real.log (1-x)/(2*(twenty.n N:ℝ)) ≤
        (CatalanMeasure.TwentyTrial.K1A0.MX:ℝ)+ε :=by
  filter_upwards [row10_corrected_eventually hε] with N hc x hx
  rw [physicalOne_row_identity]
  simpa only [lambda10,Rat.cast_zero,zero_mul,add_zero] using hc x hx

theorem physical_column10_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ s ∈ Ioo (0:ℝ) 1,
      populationEndpointColumnField twenty N 0 s+2*barrierTrialT v10 s-
        Real.log (1-s)/(twenty.n N:ℝ) ≤ (CatalanMeasure.TwentyTrial.K1A0.MY:ℝ)+ε :=by
  filter_upwards [column10_corrected_eventually hε,eventually_gt_atTop (0:ℕ)] with N hc hN s hs
  rw [physical_column_identity hN]
  exact hc s hs

theorem physical_row11_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      populationPhysicalOneFreeField twenty N x+(lambda11:ℝ)*paramCaseField twenty N x-
        2*barrierTrialT p11 x-barrierTrialS v11 x-Real.log (1-x)/(2*(twenty.n N:ℝ)) ≤
        (CatalanMeasure.TwentyTrial.K1A1.MX:ℝ)+ε :=by
  filter_upwards [row11_corrected_eventually hε] with N hc x hx
  rw [physicalOne_row_identity]
  simpa only [lambda11,Rat.cast_zero,zero_mul,add_zero] using hc x hx

theorem physical_column11_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ s ∈ Ioo (0:ℝ) 1,
      populationEndpointColumnField twenty N 1 s+2*barrierTrialT v11 s-
        Real.log (1-s)/(twenty.n N:ℝ) ≤ (CatalanMeasure.TwentyTrial.K1A1.MY:ℝ)+ε :=by
  filter_upwards [column11_corrected_eventually hε,eventually_gt_atTop (0:ℕ)] with N hc hN s hs
  rw [physical_column_identity hN]
  exact hc s hs

theorem physical_row20_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      populationPhysicalFreeField twenty N x-4*barrierTrialT p20 x-barrierTrialS v20 x-Real.log (1-x)/(2*(twenty.n N:ℝ)) ≤
        (CatalanMeasure.TwentyTrial.K2A0.MX:ℝ)+ε :=by
  filter_upwards [row20_corrected_eventually hε] with N hc x hx
  rw [physicalTwo_row_identity]
  simpa only [lambda20,Rat.cast_zero,zero_mul,add_zero] using hc x hx

theorem physical_column20_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ s ∈ Ioo (0:ℝ) 1,
      populationEndpointColumnField twenty N 0 s+2*barrierTrialT v20 s-
        Real.log (1-s)/(twenty.n N:ℝ) ≤ (CatalanMeasure.TwentyTrial.K2A0.MY:ℝ)+ε :=by
  filter_upwards [column20_corrected_eventually hε,eventually_gt_atTop (0:ℕ)] with N hc hN s hs
  rw [physical_column_identity hN]
  exact hc s hs

theorem physical_row21_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      populationPhysicalFreeField twenty N x-4*barrierTrialT p21 x-barrierTrialS v21 x-Real.log (1-x)/(2*(twenty.n N:ℝ)) ≤
        (CatalanMeasure.TwentyTrial.K2A1.MX:ℝ)+ε :=by
  filter_upwards [row21_corrected_eventually hε] with N hc x hx
  rw [physicalTwo_row_identity]
  simpa only [lambda21,Rat.cast_zero,zero_mul,add_zero] using hc x hx

theorem physical_column21_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ s ∈ Ioo (0:ℝ) 1,
      populationEndpointColumnField twenty N 1 s+2*barrierTrialT v21 s-
        Real.log (1-s)/(twenty.n N:ℝ) ≤ (CatalanMeasure.TwentyTrial.K2A1.MY:ℝ)+ε :=by
  filter_upwards [column21_corrected_eventually hε,eventually_gt_atTop (0:ℕ)] with N hc hN s hs
  rw [physical_column_identity hN]
  exact hc s hs

end
end CatalanMeasure.Parametric.TwentyCertified
