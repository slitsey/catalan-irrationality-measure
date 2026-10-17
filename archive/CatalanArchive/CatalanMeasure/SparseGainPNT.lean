module
public import CatalanMeasure.SparsePrimeGain
public import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeLossNormalization
@[expose] public section
namespace CatalanMeasure
open Filter Real
open OAI.InternalCatalan OAI.Zeta5.Workers.W14 OAI.Zeta5.W12.ImportedPNTCoreBridge
open scoped Topology BigOperators
noncomputable section

theorem sparsePrimeGain_weighted_tendsto :
    Tendsto (weightedPrimeIntervalSum sparsePrimeGain 1 65) atTop (𝓝 (1999/500:ℝ)) :=by
  have hh :=continuous_weightedPrime_tendsto (F:=sparsePrimeGain)
    (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<65)
    (continuous_sparsePrimeGain.continuousOn : ContinuousOn sparsePrimeGain (Set.Icc 1 65))
    theta_ratio_tendsto_one
  rw [integral_sparsePrimeGain] at hh
  exact hh

theorem sparsePrimeGain_prime_sum {N : ℕ} (hN : 0<N) :
    (∑ p ∈ (Finset.Ioc 0 (H N)).filter Nat.Prime,
      sparsePrimeGain ((p:ℝ)/N)*Real.log p)/(N:ℝ)=
    weightedPrimeIntervalSum sparsePrimeGain 1 65 (N:ℝ) :=by
  have hNR : (0:ℝ)<N :=by exact_mod_cast hN
  unfold weightedPrimeIntervalSum
  simp only [one_mul,Nat.floor_natCast]
  have hfloor : ⌊(65:ℝ)*(N:ℝ)⌋₊=H N :=by
    have he : (65:ℝ)*(N:ℝ)=(H N:ℝ) :=by simp [H]
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
    have hratio : (p:ℝ)/(N:ℝ) ≤ 58/3 :=by
      have hh : (p:ℝ) ≤ N :=by exact_mod_cast hpN
      rw [div_le_iff₀ hNR]
      nlinarith
    rw [sparsePrimeGain_left hratio,zero_mul]

theorem sparsePrimeGain_normalized_tendsto :
    Tendsto (fun N : ℕ =>(N:ℝ)*
      (∑ p ∈ (Finset.Ioc 0 (H N)).filter Nat.Prime,
        sparsePrimeGain ((p:ℝ)/N)*Real.log p)/(n N:ℝ)^2)
      atTop (𝓝 (1999/1152000:ℝ)) :=by
  have hh :=(sparsePrimeGain_weighted_tendsto.comp tendsto_natCast_atTop_atTop).div_const (2304:ℝ)
  norm_num only [show (1999/500:ℝ)/2304=1999/1152000 by norm_num] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  dsimp only [Function.comp_apply]
  rw [← sparsePrimeGain_prime_sum hN]
  have hNR : (N:ℝ)≠0 :=by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [n,Nat.cast_mul,Nat.cast_ofNat]
  field_simp
  ring

end
end CatalanMeasure
