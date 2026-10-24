module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyPrimeGain
public import CatalanArchive.CatalanMeasure.Parametric.TwentyParameters
public import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeLossNormalization
@[expose] public section
namespace CatalanMeasure.Parametric
open Filter Real
open OAI.InternalCatalan OAI.Zeta5.Workers.W14 OAI.Zeta5.W12.ImportedPNTCoreBridge
open scoped Topology BigOperators
noncomputable section

theorem twentyPrimeGain_weighted_tendsto :
    Tendsto (weightedPrimeIntervalSum twentyPrimeGain 1 27) atTop (𝓝 (4/3:ℝ)) :=by
  have hh :=continuous_weightedPrime_tendsto (F:=twentyPrimeGain)
    (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<27)
    (continuous_twentyPrimeGain.continuousOn : ContinuousOn twentyPrimeGain (Set.Icc 1 27))
    theta_ratio_tendsto_one
  rw [integral_twentyPrimeGain] at hh
  exact hh

theorem twentyPrimeGain_prime_sum {N : ℕ} (hN : 0<N) :
    (∑ p ∈ (Finset.Ioc 0 (twenty.H N)).filter Nat.Prime,
      twentyPrimeGain ((p:ℝ)/N)*Real.log p)/(N:ℝ)=
    weightedPrimeIntervalSum twentyPrimeGain 1 27 (N:ℝ) :=by
  have hNR : (0:ℝ)<N :=by exact_mod_cast hN
  unfold weightedPrimeIntervalSum
  simp only [one_mul,Nat.floor_natCast]
  have hfloor : ⌊(27:ℝ)*(N:ℝ)⌋₊=twenty.H N :=by
    have he : (27:ℝ)*(N:ℝ)=(twenty.H N:ℝ) :=by simp [twenty_H]
    rw [he,Nat.floor_natCast]
  rw [hfloor]
  apply congrArg (fun q : ℝ =>q/(N:ℝ))
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter,Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨lt_trans hN hp.1.1,hp.1.2⟩,hp.2⟩
  · intro p hp hnot
    simp only [Finset.mem_filter,Finset.mem_Ioc] at hp hnot
    have hpN : p ≤ N :=by
      by_contra hh
      exact hnot ⟨⟨by omega,hp.1.2⟩,hp.2⟩
    have hratio : (p:ℝ)/(N:ℝ) ≤ 22/3 :=by
      have hh : (p:ℝ) ≤ N :=by exact_mod_cast hpN
      rw [div_le_iff₀ hNR]
      nlinarith
    rw [twentyPrimeGain_left hratio,zero_mul]

theorem twentyPrimeGain_normalized_tendsto :
    Tendsto (fun N : ℕ =>(N:ℝ)*
      (∑ p ∈ (Finset.Ioc 0 (twenty.H N)).filter Nat.Prime,
        twentyPrimeGain ((p:ℝ)/N)*Real.log p)/(twenty.n N:ℝ)^2)
      atTop (𝓝 (1/300:ℝ)) :=by
  have hh :=(twentyPrimeGain_weighted_tendsto.comp tendsto_natCast_atTop_atTop).div_const (400:ℝ)
  norm_num only [show (4/3:ℝ)/400=1/300 by norm_num] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  dsimp only [Function.comp_apply]
  rw [← twentyPrimeGain_prime_sum hN]
  have hNR : (N:ℝ)≠0 :=by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [Parameters.n,twenty,Nat.cast_mul,Nat.cast_ofNat]
  field_simp
  ring

end
end CatalanMeasure.Parametric
