module
public import CatalanArchive.CatalanMeasure.DenseGainBound
@[expose] public section
namespace OAI.InternalCatalan
open Filter Real CatalanMeasure
open scoped Topology BigOperators
noncomputable section

theorem log_denseDenomBound_gain_le {N : ℕ} (hN : 1000000 ≤ N) :
    Real.log (denseDenomBound N) ≤ Real.log (denomBound N)-
      (N:ℝ)*∑ p ∈ measurePrimes N,densePrimeGain ((p:ℝ)/N)*Real.log p :=by
  rw [log_denseDenomBound_eq,log_denomBound_eq]
  calc
    _ ≤ ∑ p ∈ measurePrimes N,((denomExp N p:ℝ)-(N:ℝ)*densePrimeGain ((p:ℝ)/N))*Real.log p :=by
      apply Finset.sum_le_sum
      intro p hp
      have hlog : 0 ≤ Real.log p :=Real.log_nonneg (by
        exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
      exact mul_le_mul_of_nonneg_right (denseDenomExp_gain_le hN) hlog
    _ = _ :=by
      simp_rw [sub_mul,mul_assoc]
      rw [Finset.sum_sub_distrib,← Finset.mul_sum]

theorem log_denseDenomBound_eventually_le {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,Real.log (denseDenomBound N) ≤
      (8609/4608+505/4608*Real.log 2-5/1728+ε)*(n N:ℝ)^2 :=by
  have hold :=log_denomBound_eventually_le (show 0<ε/2 by positivity)
  have hsave :=(tendsto_order.mp densePrimeGain_normalized_tendsto).1
    ((5/1728:ℝ)-ε/2) (by linarith)
  filter_upwards [hold,hsave,eventually_ge_atTop (1000000:ℕ)] with N hOld hSave hN
  have hn : (0:ℝ)<n N :=by
    exact_mod_cast (show 0<n N by unfold n; omega)
  have hSave' : ((5/1728:ℝ)-ε/2)*(n N:ℝ)^2 <
      (N:ℝ)*∑ p ∈ measurePrimes N,densePrimeGain ((p:ℝ)/N)*Real.log p :=by
    exact (lt_div_iff₀ (sq_pos_of_pos hn)).mp hSave
  have hh :=log_denseDenomBound_gain_le hN
  nlinarith

end
end OAI.InternalCatalan
