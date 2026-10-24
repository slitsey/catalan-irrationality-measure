module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyCombinedOddLoss
@[expose] public section
namespace CatalanMeasure.Parametric
open Filter Real
open scoped Topology BigOperators
open OAI.Zeta5.Workers.W14 OAI.Zeta5.W12.ImportedPNTCoreBridge
noncomputable section

theorem twentyCombinedOddLoss_weighted_zero_one (R : ℝ) (hR : 0<R) :
    weightedPrimeIntervalSum twentyCombinedOddLoss 0 1 R=
      40*(Chebyshev.theta R/R) :=by
  have hc : weightedPrimeIntervalSum twentyCombinedOddLoss 0 1 R=
      weightedPrimeIntervalSum (fun _ =>40) 0 1 R :=by
    unfold weightedPrimeIntervalSum
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hh : p ≤ ⌊(1:ℝ)*R⌋₊ :=(Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
    have hr : (p:ℝ) ≤ 1*R :=(Nat.le_floor_iff (by positivity : (0:ℝ) ≤ 1*R)).mp hh
    rw [twentyCombinedOddLoss_small ((div_le_iff₀ hR).mpr hr)]
  rw [hc,weightedPrimeIntervalSum_const]
  simp only [primeIntervalSum,Chebyshev.theta,zero_mul,Nat.floor_zero,one_mul]

theorem twentyCombinedOddLoss_weighted_tendsto_real :
    Tendsto (weightedPrimeIntervalSum twentyCombinedOddLoss 0 27)
      atTop (𝓝 (8795/12:ℝ)) :=by
  have hfirst :=(theta_scaled_tendsto theta_ratio_tendsto_one
    (by norm_num : (0:ℝ)<1)).const_mul (40:ℝ)
  have hlast :=continuous_weightedPrime_tendsto
    (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<27)
    (continuous_twentyCombinedOddLoss.continuousOn : ContinuousOn twentyCombinedOddLoss (Set.Icc 1 27))
    theta_ratio_tendsto_one
  rw [integral_twentyCombinedOddLoss_one] at hlast
  have hh :=hfirst.add hlast
  norm_num at hh ⊢
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  simpa only [one_mul,twentyCombinedOddLoss_weighted_zero_one R hR] using
    (weightedPrimeIntervalSum_add_adjacent twentyCombinedOddLoss
      (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 27) hR.le)

theorem twentyCombinedOddLoss_prime_sum_tendsto :
    Tendsto (fun N : ℕ =>
      (∑ p ∈ Finset.Ioc 0 (27*N) with p.Prime,
        twentyCombinedOddLoss ((p:ℝ)/N)*Real.log (p:ℝ))/N)
      atTop (𝓝 (8795/12:ℝ)) :=by
  have hh :=twentyCombinedOddLoss_weighted_tendsto_real.comp tendsto_natCast_atTop_atTop
  have hf (N : ℕ) : ⌊(27:ℝ)*N⌋₊=27*N :=by
    rw [show (27:ℝ)*N=((27*N:ℕ):ℝ) by norm_num [Nat.cast_mul]]
    exact Nat.floor_natCast _
  simpa only [Function.comp_def,weightedPrimeIntervalSum,zero_mul,Nat.floor_zero,hf] using hh

theorem twentyCombinedOddLoss_normalized_prime_sum_tendsto :
    Tendsto (fun N : ℕ =>
      ((N:ℝ)*∑ p ∈ Finset.Ioc 0 (27*N) with p.Prime,
        twentyCombinedOddLoss ((p:ℝ)/N)*Real.log (p:ℝ))/(20*(N:ℝ))^2)
      atTop (𝓝 (8795/4800:ℝ)) :=by
  have hh :=twentyCombinedOddLoss_prime_sum_tendsto.div_const 400
  norm_num at hh ⊢
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hn : (N:ℝ)≠0 :=by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  <;> ring

end
end CatalanMeasure.Parametric
