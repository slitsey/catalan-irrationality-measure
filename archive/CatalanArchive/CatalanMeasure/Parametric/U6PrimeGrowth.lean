module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentPrimeGrowth
public import CatalanArchive.CatalanMeasure.Parametric.U6Content
@[expose] public section

/-!
# Logarithmic growth of the U6 content product

The sixth-window profile `(x - 4)/2` on `[4, 9/2]` has area `1/16`; the product
`∏ p ^ ((p - 4N - 1)/2)` over primes `4N < p < 9N/2` therefore has logarithm at
least `c N^2` eventually, for every `c < 1/16`.
-/

namespace CatalanMeasure.Parametric
open Filter Real MeasureTheory
open OAI.Zeta5.Workers.W14 OAI.Zeta5.W12.ImportedPNTCoreBridge
open scoped Topology BigOperators Interval
noncomputable section

/-- The profile of the sixth window. -/
def sixthProfile (x : ℝ) : ℝ := max (x - 4) 0 / 2

theorem continuous_sixthProfile : Continuous sixthProfile := by
  unfold sixthProfile; fun_prop

theorem sixthProfile_nonneg (x : ℝ) : 0 ≤ sixthProfile x := by
  unfold sixthProfile; positivity

theorem integral_sixthProfile : (∫ x in (4 : ℝ)..(9 / 2), sixthProfile x) = 1 / 16 := by
  unfold sixthProfile
  rw [intervalIntegral.integral_div,
    CatalanMeasure.integral_positive_part 4 (9 / 2) 4 (by norm_num) (by norm_num)]
  norm_num

theorem sixthProfile_weighted_tendsto :
    Tendsto (weightedPrimeIntervalSum sixthProfile 4 (9 / 2)) atTop (𝓝 (1 / 16 : ℝ)) := by
  have hh := continuous_weightedPrime_tendsto
    (F := sixthProfile) (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) < 9 / 2)
    (continuous_sixthProfile.continuousOn : ContinuousOn sixthProfile (Set.Icc 4 (9 / 2)))
    theta_ratio_tendsto_one
  rw [integral_sixthProfile] at hh
  exact hh

/-- Primes in the sixth window. -/
def u6Primes (N : ℕ) : Finset ℕ := (Finset.Ioc (4 * N) (9 * N / 2)).filter Nat.Prime

theorem sixth_scaled_profile {N : ℕ} (hN : 0 < N) (p : ℕ) :
    (N : ℝ) * sixthProfile ((p : ℝ) / N) = max ((p : ℝ) - 4 * N) 0 / 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold sixthProfile
  have h1 : (p : ℝ) / N - 4 = ((p : ℝ) - 4 * N) / N := by field_simp
  have h2 : max (((p : ℝ) - 4 * N) / N) 0 = max ((p : ℝ) - 4 * N) 0 / N := by
    rw [← zero_div (N : ℝ), max_div_div_right hNR.le, zero_div]
  rw [h1, h2]
  field_simp

theorem natCast_sub_helper {N p : ℕ} (h : 4 * N < p) :
    ((p - 4 * N - 1 : ℕ) : ℝ) = (p : ℝ) - 4 * N - 1 := by
  rw [Nat.cast_sub (by omega), Nat.cast_sub h.le]; push_cast; ring

theorem sixthExponent_rounding {N : ℕ} (hN : 0 < N) (p : ℕ) :
    (N : ℝ) * sixthProfile ((p : ℝ) / N) - 1 ≤ sixthExponent N p ∧
      (sixthExponent N p : ℝ) ≤ (N : ℝ) * sixthProfile ((p : ℝ) / N) := by
  rw [sixth_scaled_profile hN]
  unfold sixthExponent
  by_cases h : 4 * N < p
  · have hpos : (0 : ℝ) ≤ (p : ℝ) - 4 * N := by
      have : (4 * N : ℝ) < p := by exact_mod_cast h
      linarith
    rw [max_eq_left hpos]
    have h3 := natCast_sub_helper h
    have h1 : (p - 4 * N - 1) / 2 * 2 ≤ p - 4 * N - 1 := Nat.div_mul_le_self _ _
    have h2 : p - 4 * N ≤ ((p - 4 * N - 1) / 2 + 1) * 2 := by omega
    have h1' : (((p - 4 * N - 1) / 2 : ℕ) : ℝ) * 2 ≤ (p : ℝ) - 4 * N - 1 := by
      rw [← h3]; exact_mod_cast h1
    have h2' : (p : ℝ) - 4 * N ≤ ((((p - 4 * N - 1) / 2 : ℕ) : ℝ) + 1) * 2 := by
      have h4 : ((p - 4 * N : ℕ) : ℝ) = (p : ℝ) - 4 * N := by
        rw [Nat.cast_sub h.le]; push_cast; ring
      rw [← h4]; exact_mod_cast h2
    constructor <;> linarith
  · have h0 : p - 4 * N - 1 = 0 := by omega
    rw [h0]
    have : (p : ℝ) - 4 * N ≤ 0 := by
      have : (p : ℝ) ≤ 4 * N := by exact_mod_cast (not_lt.mp h)
      linarith
    rw [max_eq_right this]
    simp

theorem sixthExponent_zero {N p : ℕ} (hp : p ≤ 4 * N) : sixthExponent N p = 0 := by
  unfold sixthExponent; omega

def u6PrimeWindow (N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 (9 * N)).filter (fun p => p.Prime ∧ 4 * N < p ∧ 2 * p < 9 * N)

def u6Content (N : ℕ) : ℕ := ∏ p ∈ u6PrimeWindow N, p ^ sixthExponent N p

theorem u6PrimeWindow_eq (N : ℕ) : u6PrimeWindow N = u6Primes N := by
  ext p
  simp only [u6PrimeWindow, u6Primes, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h0, h1⟩, hp, h4, h9⟩
    exact ⟨⟨h4, by omega⟩, hp⟩
  · rintro ⟨⟨h4, h9⟩, hp⟩
    have h92 : 2 * p ≤ 9 * N := by omega
    have hne : 2 * p ≠ 9 * N := by
      intro h
      have h3 : 3 ∣ 2 * p := by rw [h]; exact ⟨3 * N, by ring⟩
      have h3' : 3 ∣ p := Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3
      have hp3 : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3'
      omega
    exact ⟨⟨hp.pos, by omega⟩, hp, h4, by omega⟩

theorem u6Content_log (N : ℕ) :
    Real.log (u6Content N) = ∑ p ∈ u6PrimeWindow N, (sixthExponent N p : ℝ) * Real.log p := by
  unfold u6Content
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (Finset.mem_filter.mp hp).2.1.ne_zero)

theorem floor_four (N : ℕ) : ⌊(4 : ℝ) * (N : ℝ)⌋₊ = 4 * N := by
  rw [show (4 : ℝ) * (N : ℝ) = ((4 * N : ℕ) : ℝ) by push_cast; ring]; exact Nat.floor_natCast _

theorem floor_nine_half (N : ℕ) : ⌊(9 / 2 : ℝ) * (N : ℝ)⌋₊ = 9 * N / 2 := by
  rw [show (9 / 2 : ℝ) * (N : ℝ) = ((9 * N : ℕ) : ℝ) / ((2 : ℕ) : ℝ) by push_cast; ring]
  exact Nat.floor_div_eq_div _ _

theorem u6_prime_sum (N : ℕ) :
    (∑ p ∈ u6Primes N, sixthProfile ((p : ℝ) / N) * Real.log p) / (N : ℝ) =
      weightedPrimeIntervalSum sixthProfile 4 (9 / 2) (N : ℝ) := by
  unfold weightedPrimeIntervalSum u6Primes
  rw [floor_four N, floor_nine_half N]

theorem u6_prime_interval_sum (N : ℕ) :
    (∑ p ∈ u6Primes N, Real.log (p : ℝ)) = primeIntervalSum (4 * (N : ℝ)) (9 / 2 * (N : ℝ)) := by
  unfold primeIntervalSum u6Primes
  rw [floor_four N, floor_nine_half N]

theorem u6Content_log_lower {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * (∑ p ∈ u6Primes N, sixthProfile ((p : ℝ) / N) * Real.log p) -
      (∑ p ∈ u6Primes N, Real.log (p : ℝ)) ≤ Real.log (u6Content N) := by
  rw [u6Content_log, u6PrimeWindow_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
  have hh := mul_le_mul_of_nonneg_right (sixthExponent_rounding hN p).1 hlog
  nlinarith

theorem u6Content_lower_normalized {N : ℕ} (hN : 0 < N) :
    weightedPrimeIntervalSum sixthProfile 4 (9 / 2) (N : ℝ) -
      (primeIntervalSum (4 * (N : ℝ)) (9 / 2 * (N : ℝ)) / (N : ℝ)) * (1 / (N : ℝ)) ≤
      Real.log (u6Content N) / (N : ℝ) ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← u6_prime_sum, ← u6_prime_interval_sum]
  apply (le_div_iff₀ (sq_pos_of_pos hNR)).mpr
  convert u6Content_log_lower hN using 1 <;> field_simp

theorem u6Content_eventual_growth {c : ℝ} (hc : c < 1 / 16) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ 2 ≤ Real.log (u6Content N) := by
  have hw := sixthProfile_weighted_tendsto.comp tendsto_natCast_atTop_atTop
  have he := ((primeIntervalSum_scaled_tendsto theta_ratio_tendsto_one
      (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) < 9 / 2)).comp
      tendsto_natCast_atTop_atTop).mul (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hl := hw.sub he
  simp only [mul_zero, sub_zero] at hl
  have hev := hl.eventually (lt_mem_nhds hc)
  filter_upwards [hev, eventually_gt_atTop (0 : ℕ)] with N hbound hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hh := (le_of_lt hbound).trans (u6Content_lower_normalized hN)
  exact (le_div_iff₀ (sq_pos_of_pos hNR)).mp hh

theorem u6Content_eventual_624 :
    ∀ᶠ N : ℕ in atTop, (624 / 10000 : ℝ) * (N : ℝ) ^ 2 ≤ Real.log (u6Content N) :=
  u6Content_eventual_growth (by norm_num)

theorem u6PrimeWindow_above {N p : ℕ} (hp : p ∈ u6PrimeWindow N) : 4 * N < p := by
  simp only [u6PrimeWindow, Finset.mem_filter, Finset.mem_Ioc] at hp
  omega

end
end CatalanMeasure.Parametric
