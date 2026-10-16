module
public import CatalanMeasure.Parametric.SecondaryTentPrimeGrowth
public import CatalanMeasure.Parametric.U3Content
@[expose] public section

/-!
# Logarithmic growth of the U3 content product

The third-band tent `min (x - 8) (18 - 2x)` on `[8, 9]` has area `1/3`; the
rounded product `∏ p ^ thirdTentExponent N p` over primes `8N < p < 9N`
therefore has logarithm at least `c N^2` eventually, for every `c < 1/3`.
-/

namespace CatalanMeasure.Parametric
open Filter Real MeasureTheory
open OAI.Zeta5.Workers.W14 OAI.Zeta5.W12.ImportedPNTCoreBridge
open scoped Topology BigOperators Interval
noncomputable section

/-- The tent profile of the third band. -/
def thirdTentProfile (x : ℝ) : ℝ := max 0 (min (x - 8) (18 - 2 * x))

theorem continuous_thirdTentProfile : Continuous thirdTentProfile := by
  unfold thirdTentProfile; fun_prop

theorem thirdTentProfile_nonneg (x : ℝ) : 0 ≤ thirdTentProfile x := le_max_left _ _

theorem thirdTentProfile_positive_parts (x : ℝ) :
    thirdTentProfile x = max (x - 8) 0 - 3 * max (x - 26 / 3) 0 + 2 * max (x - 9) 0 := by
  unfold thirdTentProfile
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem integral_thirdTentProfile :
    (∫ x in (8 : ℝ)..9, thirdTentProfile x) = 1 / 3 := by
  have hi (k : ℝ) : IntervalIntegrable (fun x : ℝ => max (x - k) 0) volume 8 9 :=
    (by fun_prop : Continuous (fun x : ℝ => max (x - k) 0)).intervalIntegrable 8 9
  simp_rw [thirdTentProfile_positive_parts]
  rw [intervalIntegral.integral_add (((hi _).sub ((hi _).const_mul 3)))
    ((hi _).const_mul 2),
    intervalIntegral.integral_sub (hi _) ((hi _).const_mul 3)]
  simp only [intervalIntegral.integral_const_mul]
  rw [CatalanMeasure.integral_positive_part 8 9 8 (by norm_num) (by norm_num),
    CatalanMeasure.integral_positive_part 8 9 (26 / 3) (by norm_num) (by norm_num),
    CatalanMeasure.integral_positive_part 8 9 9 (by norm_num) (by norm_num)]
  norm_num

theorem thirdTentProfile_weighted_tendsto :
    Tendsto (weightedPrimeIntervalSum thirdTentProfile 8 9) atTop (𝓝 (1 / 3 : ℝ)) := by
  have hh := continuous_weightedPrime_tendsto
    (F := thirdTentProfile) (by norm_num : (0 : ℝ) < 8) (by norm_num : (8 : ℝ) < 9)
    (continuous_thirdTentProfile.continuousOn : ContinuousOn thirdTentProfile (Set.Icc 8 9))
    theta_ratio_tendsto_one
  rw [integral_thirdTentProfile] at hh
  exact hh

/-- Primes in the encompassing interval. -/
def u3Primes (N : ℕ) : Finset ℕ := (Finset.Ioc (8 * N) (9 * N)).filter Nat.Prime

theorem thirdTent_scaled_profile {N : ℕ} (hN : 0 < N) (p : ℕ) :
    (N : ℝ) * thirdTentProfile ((p : ℝ) / N) =
      max 0 (min ((p : ℝ) - 8 * N) (18 * N - 2 * p)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold thirdTentProfile
  rw [mul_max_of_nonneg _ _ hNR.le, mul_zero, mul_min_of_nonneg _ _ hNR.le]
  congr 2 <;> field_simp <;> ring

theorem thirdTentExponent_rounding {N : ℕ} (hN : 0 < N) (p : ℕ) :
    (N : ℝ) * thirdTentProfile ((p : ℝ) / N) - 1 ≤ thirdTentExponent N p ∧
      (thirdTentExponent N p : ℝ) ≤ (N : ℝ) * thirdTentProfile ((p : ℝ) / N) := by
  rw [thirdTent_scaled_profile hN]
  have he : (thirdTentExponent N p : ℝ) =
      max (min ((p : ℝ) - 8 * N - 1) (18 * N - 2 * p - 1)) 0 := by
    unfold thirdTentExponent
    have h := Int.toNat_eq_max (min ((p : ℤ) - 8 * N - 1) (18 * (N : ℤ) - 2 * p - 1))
    have h2 : ((((min ((p : ℤ) - 8 * N - 1) (18 * (N : ℤ) - 2 * p - 1)).toNat : ℕ) : ℤ) : ℝ) =
        ((max (min ((p : ℤ) - 8 * N - 1) (18 * (N : ℤ) - 2 * p - 1)) 0 : ℤ) : ℝ) := by
      rw [h]
    push_cast at h2
    exact h2
  rw [he]
  constructor
  · by_cases h : min ((p : ℝ) - 8 * N) (18 * N - 2 * p) ≤ 0
    · rw [max_eq_left h]
      have := le_max_right (min ((p : ℝ) - 8 * N - 1) (18 * N - 2 * p - 1)) 0
      linarith
    · push_neg at h
      rw [max_eq_right h.le]
      have := le_max_left (min ((p : ℝ) - 8 * N - 1) (18 * N - 2 * p - 1)) 0
      have h3 : min ((p : ℝ) - 8 * N - 1) (18 * N - 2 * p - 1) =
          min ((p : ℝ) - 8 * N) (18 * N - 2 * p) - 1 := by
        simp only [min_def]; split_ifs <;> linarith
      linarith
  · apply max_le
    · exact (min_le_min (by linarith) (by linarith)).trans (le_max_right _ _)
    · exact le_max_left _ _

theorem thirdTentExponent_zero_left {N p : ℕ} (hp : p ≤ 8 * N) : thirdTentExponent N p = 0 := by
  unfold thirdTentExponent; omega

theorem thirdTentExponent_zero_right {N p : ℕ} (hp : 9 * N ≤ p) : thirdTentExponent N p = 0 := by
  unfold thirdTentExponent; omega

def u3PrimeWindow (N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 (9 * N)).filter (fun p => p.Prime ∧ 8 * N < p ∧ p < 9 * N)

def u3Content (N : ℕ) : ℕ := ∏ p ∈ u3PrimeWindow N, p ^ thirdTentExponent N p

theorem u3Content_log (N : ℕ) :
    Real.log (u3Content N) = ∑ p ∈ u3PrimeWindow N, (thirdTentExponent N p : ℝ) * Real.log p := by
  unfold u3Content
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (Finset.mem_filter.mp hp).2.1.ne_zero)

theorem u3_window_sum_eq (N : ℕ) (F : ℕ → ℝ) (hF : ∀ p, thirdTentExponent N p = 0 → F p = 0) :
    ∑ p ∈ u3PrimeWindow N, F p = ∑ p ∈ u3Primes N, F p := by
  apply Finset.sum_subset
  · intro p hp
    simp only [u3PrimeWindow, u3Primes, Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨hp.2.2.1, hp.1.2⟩, hp.2.1⟩
  · intro p hp hn
    apply hF
    simp only [u3PrimeWindow, u3Primes, Finset.mem_filter, Finset.mem_Ioc] at hp hn
    by_cases h : p < 9 * N
    · exact absurd ⟨⟨by omega, hp.1.2⟩, hp.2, hp.1.1, h⟩ hn
    · exact thirdTentExponent_zero_right (by omega)

theorem floor_eight (N : ℕ) : ⌊(8 : ℝ) * (N : ℝ)⌋₊ = 8 * N := by
  rw [show (8 : ℝ) * (N : ℝ) = ((8 * N : ℕ) : ℝ) by push_cast; ring]; exact Nat.floor_natCast _

theorem floor_nine (N : ℕ) : ⌊(9 : ℝ) * (N : ℝ)⌋₊ = 9 * N := by
  rw [show (9 : ℝ) * (N : ℝ) = ((9 * N : ℕ) : ℝ) by push_cast; ring]; exact Nat.floor_natCast _

theorem u3_prime_sum (N : ℕ) :
    (∑ p ∈ u3Primes N, thirdTentProfile ((p : ℝ) / N) * Real.log p) / (N : ℝ) =
      weightedPrimeIntervalSum thirdTentProfile 8 9 (N : ℝ) := by
  unfold weightedPrimeIntervalSum u3Primes
  rw [floor_eight N, floor_nine N]

theorem u3_prime_interval_sum (N : ℕ) :
    (∑ p ∈ u3Primes N, Real.log (p : ℝ)) = primeIntervalSum (8 * (N : ℝ)) (9 * (N : ℝ)) := by
  unfold primeIntervalSum u3Primes
  rw [floor_eight N, floor_nine N]

theorem u3Content_log_lower {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * (∑ p ∈ u3Primes N, thirdTentProfile ((p : ℝ) / N) * Real.log p) -
      (∑ p ∈ u3Primes N, Real.log (p : ℝ)) ≤ Real.log (u3Content N) := by
  rw [u3Content_log, u3_window_sum_eq N (fun p => (thirdTentExponent N p : ℝ) * Real.log p)
    (fun p hp => by simp [hp]), Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
  have hh := mul_le_mul_of_nonneg_right (thirdTentExponent_rounding hN p).1 hlog
  nlinarith

theorem u3Content_lower_normalized {N : ℕ} (hN : 0 < N) :
    weightedPrimeIntervalSum thirdTentProfile 8 9 (N : ℝ) -
      (primeIntervalSum (8 * (N : ℝ)) (9 * (N : ℝ)) / (N : ℝ)) * (1 / (N : ℝ)) ≤
      Real.log (u3Content N) / (N : ℝ) ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← u3_prime_sum, ← u3_prime_interval_sum]
  apply (le_div_iff₀ (sq_pos_of_pos hNR)).mpr
  convert u3Content_log_lower hN using 1 <;> field_simp <;> ring

theorem u3Content_eventual_growth {c : ℝ} (hc : c < 1 / 3) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ 2 ≤ Real.log (u3Content N) := by
  have hw := thirdTentProfile_weighted_tendsto.comp tendsto_natCast_atTop_atTop
  have he := ((primeIntervalSum_scaled_tendsto theta_ratio_tendsto_one
      (by norm_num : (0 : ℝ) < 8) (by norm_num : (8 : ℝ) < 9)).comp
      tendsto_natCast_atTop_atTop).mul (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hl := hw.sub he
  simp only [mul_zero, sub_zero] at hl
  have hev := hl.eventually (lt_mem_nhds hc)
  filter_upwards [hev, eventually_gt_atTop (0 : ℕ)] with N hbound hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hh := (le_of_lt hbound).trans (u3Content_lower_normalized hN)
  exact (le_div_iff₀ (sq_pos_of_pos hNR)).mp hh

theorem u3Content_eventual_3331 :
    ∀ᶠ N : ℕ in atTop, (3331 / 10000 : ℝ) * (N : ℝ) ^ 2 ≤ Real.log (u3Content N) :=
  u3Content_eventual_growth (by norm_num)

theorem u3PrimeWindow_above {N p : ℕ} (hp : p ∈ u3PrimeWindow N) : 8 * N < p := by
  simp only [u3PrimeWindow, Finset.mem_filter, Finset.mem_Ioc] at hp
  omega

end
end CatalanMeasure.Parametric
