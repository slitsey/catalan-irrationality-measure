module
public import CatalanMeasure.Parametric.TwentyDenominators
public import CatalanMeasure.Parametric.TwentyOddWeightedLimit
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

open Filter Real
open scoped Topology
theorem twenty_log_denomBound_eq (N : ℕ) :
    Real.log (twentyDenomBound N) =
      ∑ ℓ ∈ measurePrimes N, (twentyDenomExp N ℓ : ℝ) * Real.log ℓ := by
  unfold twentyDenomBound
  rw [Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [Nat.cast_pow, Real.log_pow]
  · intro ℓ hℓ
    exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (Finset.mem_filter.mp hℓ).2.ne_zero)

/-- Termwise bound: each prime contributes to exactly one of the three error terms. -/
theorem twenty_denomExp_mul_log_le {N ℓ : ℕ} (hN : 0 < N) (hℓ : ℓ ∈ measurePrimes N) :
    (twentyDenomExp N ℓ : ℝ) * Real.log ℓ ≤
      (if ℓ = 2 then (twentyTwoAdicBound N + 1) * Real.log 2 else 0) +
      (if ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ 2 * Real.sqrt (H N) then 6 * (n N : ℝ) * Real.log (H N) else 0) +
      (if ℓ ≠ 2 ∧ 2 * Real.sqrt (H N) < (ℓ : ℝ) then
        (N : ℝ) * (twentyCombinedOddLoss ((ℓ : ℝ) / N) * Real.log ℓ) + Real.log ℓ else 0) := by
  obtain ⟨hmem, hp⟩ := Finset.mem_filter.mp hℓ
  have hlogℓ : 0 ≤ Real.log (ℓ : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hH : 0 < H N := by unfold H; omega
  unfold twentyDenomExp
  by_cases h2 : ℓ = 2
  · subst h2
    have hs : ¬ ((2 : ℕ) ≠ 2) := fun h => h rfl
    simp only [if_true, hs, false_and, if_false, add_zero]
    have hc := Nat.ceil_lt_add_one (twentyTwoAdicBound_nonneg hN)
    exact mul_le_mul_of_nonneg_right hc.le (Real.log_nonneg (by norm_num))
  · by_cases hsmall : (ℓ : ℝ) ≤ 2 * Real.sqrt (H N)
    · have hnot : ¬ (2 * Real.sqrt (H N) < (ℓ : ℝ)) := not_lt.mpr hsmall
      simp only [h2, if_false, hsmall, ne_eq, not_false_eq_true, and_self, if_true, hnot,
        and_false, zero_add, add_zero]
      have h := nat_log_mul_log_prime_le hp hH
      have hn : (0 : ℝ) ≤ n N := by positivity
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 6 * n N)]
    · have hlarge : 2 * Real.sqrt (H N) < (ℓ : ℝ) := not_le.mp hsmall
      simp only [h2, if_false, hsmall, ne_eq, not_false_eq_true, and_false, hlarge, and_self,
        if_true, zero_add]
      have hloss := (twentyCombinedOddLoss_bounds ((ℓ : ℝ) / N)).1
      have hN0 : (0 : ℝ) ≤ N := by positivity
      have hc := Nat.ceil_lt_add_one (mul_nonneg hN0 hloss)
      nlinarith [mul_le_mul_of_nonneg_right hc.le hlogℓ]

/-- `log D_N` is at most the sum of the three error terms. -/
theorem twenty_log_denomBound_le {N : ℕ} (hN : 0 < N) :
    Real.log (twentyDenomBound N) ≤
      (twentyTwoAdicBound N + 1) * Real.log 2 + smallOddPrimeError 1 N +
        ((N : ℝ) * ∑ p ∈ (Finset.Ioc 0 (H N)).filter
            (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
            twentyCombinedOddLoss ((p : ℝ) / N) * Real.log (p : ℝ) +
          Chebyshev.theta (H N : ℝ)) := by
  have hH : 0 < H N := by unfold H; omega
  have hn : (0 : ℝ) ≤ n N := by positivity
  have hlogH : 0 ≤ Real.log (H N : ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  rw [twenty_log_denomBound_eq]
  refine (Finset.sum_le_sum (fun ℓ hℓ => twenty_denomExp_mul_log_le hN hℓ)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- the prime `2`
    rw [Finset.sum_ite_eq']
    have h0 : 0 ≤ (twentyTwoAdicBound N + 1) * Real.log 2 :=
      mul_nonneg (by linarith [twentyTwoAdicBound_nonneg hN]) (Real.log_nonneg (by norm_num))
    split_ifs <;> linarith
  · -- small odd primes
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hsub : (measurePrimes N).filter
        (fun ℓ : ℕ => ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ 2 * Real.sqrt (H N)) ⊆ smallOddPrimes N := by
      intro ℓ hℓ
      simp only [measurePrimes, Finset.mem_filter] at hℓ
      exact (mem_smallOddPrimes_iff N ℓ).mpr ⟨hℓ.1.2, hℓ.2.1, hℓ.2.2⟩
    have hcard : (((measurePrimes N).filter
        (fun ℓ : ℕ => ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ 2 * Real.sqrt (H N))).card : ℝ) ≤ 2 * Real.sqrt (H N) :=
      (by exact_mod_cast Finset.card_le_card hsub : _ ≤ ((smallOddPrimes N).card : ℝ)).trans
        (smallOddPrimes_card_le N)
    have herr : smallOddPrimeError 1 N = 2 * Real.sqrt (H N) * (n N : ℝ) * (6 * Real.log (H N)) := by
      simp [smallOddPrimeError]
    rw [herr]
    have h6 : 0 ≤ 6 * (n N : ℝ) * Real.log (H N) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcard h6]
  · -- large odd primes
    rw [← Finset.sum_filter, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hNR : (0 : ℝ) ≤ N := by positivity
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ hNR) ?_
    · apply Finset.sum_le_sum_of_subset_of_nonneg (measurePrimes_large_subset N)
      intro p hp _
      simp only [Finset.mem_filter] at hp
      exact mul_nonneg (twentyCombinedOddLoss_bounds _).1
        (Real.log_nonneg (by exact_mod_cast hp.2.1.one_lt.le))
    · refine le_trans ?_ (sum_log_measurePrimes_le_theta N)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro ℓ hℓ _
      simp only [measurePrimes, Finset.mem_filter] at hℓ
      exact Real.log_nonneg (by exact_mod_cast hℓ.2.one_lt.le)


end
end CatalanMeasure.Parametric
