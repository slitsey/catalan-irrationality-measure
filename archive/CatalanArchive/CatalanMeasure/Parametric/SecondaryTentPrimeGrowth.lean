module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentPrimeGrowthProfile
public import CatalanArchive.CatalanMeasure.Parametric.TwentyGainPNT
public import Mathlib.Analysis.SpecificLimits.Basic
@[expose] public section
namespace CatalanMeasure.Parametric
open Filter Real
open OAI.Zeta5.Workers.W14 OAI.Zeta5.W12.ImportedPNTCoreBridge
open scoped Topology BigOperators
noncomputable section

theorem secondaryTentProfile_weighted_tendsto :
    Tendsto (weightedPrimeIntervalSum secondaryTentProfile 1 7)
      atTop (𝓝 (16/63:ℝ)) := by
  have hh := continuous_weightedPrime_tendsto
    (F := secondaryTentProfile) (by norm_num : (0:ℝ)<1)
    (by norm_num : (1:ℝ)<7)
    (continuous_secondaryTentProfile.continuousOn :
      ContinuousOn secondaryTentProfile (Set.Icc 1 7)) theta_ratio_tendsto_one
  rw [integral_secondaryTentProfile] at hh
  exact hh

/-- The encompassing interval; all factors outside the strict tent support are one. -/
def secondaryTentPrimes (N : ℕ) : Finset ℕ :=
  (Finset.Ioc N (7*N)).filter Nat.Prime

/-- Natural truncation occurs after the two integer floors and their minimum. -/
def secondaryTentExponent (N p : ℕ) : ℕ :=
  (max 0 (min (⌊((9:ℝ)*p-52*N)/2⌋ : ℤ) ⌊((44:ℝ)*N-7*p)/2⌋)).toNat

def secondaryTentContent (N : ℕ) : ℕ :=
  ∏ p ∈ secondaryTentPrimes N, p ^ secondaryTentExponent N p

private theorem floor_max_zero_min (a b : ℝ) :
    (⌊max 0 (min a b)⌋ : ℤ) = max 0 (min ⌊a⌋ ⌊b⌋) := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab, min_eq_left (Int.floor_mono hab)]
    by_cases ha : a ≤ 0
    · rw [max_eq_left ha, Int.floor_zero,
        max_eq_left (by simpa using Int.floor_mono ha)]
    · rw [max_eq_right (by linarith),
        max_eq_right (Int.floor_nonneg.mpr (by linarith))]
  · rw [min_eq_right (le_of_not_ge hab),
      min_eq_right (Int.floor_mono (le_of_not_ge hab))]
    by_cases hb : b ≤ 0
    · rw [max_eq_left hb, Int.floor_zero,
        max_eq_left (by simpa using Int.floor_mono hb)]
    · rw [max_eq_right (by linarith),
        max_eq_right (Int.floor_nonneg.mpr (by linarith))]

theorem secondaryTent_scaled_profile {N : ℕ} (hN : 0 < N) (p : ℕ) :
    (N:ℝ)*secondaryTentProfile ((p:ℝ)/N) =
      max 0 (min (((9:ℝ)*p-52*N)/2) (((44:ℝ)*N-7*p)/2)) := by
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  unfold secondaryTentProfile
  rw [mul_max_of_nonneg _ _ hNR.le, mul_zero, mul_min_of_nonneg _ _ hNR.le]
  congr 2 <;> field_simp <;> ring

theorem secondaryTentExponent_eq_floor {N : ℕ} (hN : 0 < N) (p : ℕ) :
    secondaryTentExponent N p = ⌊(N:ℝ)*secondaryTentProfile ((p:ℝ)/N)⌋₊ := by
  rw [secondaryTent_scaled_profile hN, ← Int.floor_toNat, floor_max_zero_min]
  rfl

theorem secondaryTentExponent_rounding {N : ℕ} (hN : 0 < N) (p : ℕ) :
    (N:ℝ)*secondaryTentProfile ((p:ℝ)/N)-1 ≤ secondaryTentExponent N p ∧
      (secondaryTentExponent N p : ℝ) ≤ (N:ℝ)*secondaryTentProfile ((p:ℝ)/N) := by
  rw [secondaryTentExponent_eq_floor hN]
  constructor
  · linarith [Nat.lt_floor_add_one ((N:ℝ)*secondaryTentProfile ((p:ℝ)/N))]
  · exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (secondaryTentProfile_nonneg _))

theorem secondaryTentContent_log (N : ℕ) :
    Real.log (secondaryTentContent N) =
      ∑ p ∈ secondaryTentPrimes N, (secondaryTentExponent N p : ℝ)*Real.log p := by
  unfold secondaryTentContent
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero)

theorem secondaryTent_prime_sum (N : ℕ) :
    (∑ p ∈ secondaryTentPrimes N,
      secondaryTentProfile ((p:ℝ)/N)*Real.log p)/(N:ℝ) =
      weightedPrimeIntervalSum secondaryTentProfile 1 7 (N:ℝ) := by
  unfold weightedPrimeIntervalSum secondaryTentPrimes
  simp only [one_mul, Nat.floor_natCast]
  congr 3
  rw [show (7:ℝ)*(N:ℝ) = (7*N:ℕ) by push_cast; ring, Nat.floor_natCast]

theorem secondaryTent_prime_interval_sum (N : ℕ) :
    (∑ p ∈ secondaryTentPrimes N, Real.log (p:ℝ)) =
      primeIntervalSum ((1:ℝ)*N) ((7:ℝ)*N) := by
  unfold primeIntervalSum secondaryTentPrimes
  simp only [one_mul, Nat.floor_natCast]
  congr 3
  rw [show (7:ℝ)*(N:ℝ) = (7*N:ℕ) by push_cast; ring, Nat.floor_natCast]

/-- The complete loss from integer rounding is at most one log per prime. -/
theorem secondaryTentContent_log_lower {N : ℕ} (hN : 0 < N) :
    (N:ℝ)*(∑ p ∈ secondaryTentPrimes N,
      secondaryTentProfile ((p:ℝ)/N)*Real.log p) -
      (∑ p ∈ secondaryTentPrimes N, Real.log (p:ℝ)) ≤
      Real.log (secondaryTentContent N) := by
  rw [secondaryTentContent_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hlog : 0 ≤ Real.log (p:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
  have hh := mul_le_mul_of_nonneg_right (secondaryTentExponent_rounding hN p).1 hlog
  nlinarith

theorem secondaryTentContent_lower_normalized {N : ℕ} (hN : 0 < N) :
    weightedPrimeIntervalSum secondaryTentProfile 1 7 (N:ℝ) -
      (primeIntervalSum ((1:ℝ)*N) ((7:ℝ)*N)/(N:ℝ)) * (1/(N:ℝ)) ≤
      Real.log (secondaryTentContent N)/(N:ℝ)^2 := by
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  rw [← secondaryTent_prime_sum, ← secondaryTent_prime_interval_sum]
  apply (le_div_iff₀ (sq_pos_of_pos hNR)).mpr
  convert secondaryTentContent_log_lower hN using 1 <;> field_simp <;> ring

/-- Every strict rate below the audited area is eventually supplied by the rounded product. -/
theorem secondaryTentContent_eventual_growth {c : ℝ} (hc : c < 16/63) :
    ∀ᶠ N : ℕ in atTop, c*(N:ℝ)^2 ≤ Real.log (secondaryTentContent N) := by
  have hw := secondaryTentProfile_weighted_tendsto.comp tendsto_natCast_atTop_atTop
  have he := ((primeIntervalSum_scaled_tendsto theta_ratio_tendsto_one
      (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<7)).comp
      tendsto_natCast_atTop_atTop).mul (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  have hl := hw.sub he
  simp only [mul_zero, sub_zero] at hl
  have hev := hl.eventually (lt_mem_nhds hc)
  filter_upwards [hev, eventually_gt_atTop (0:ℕ)] with N hbound hN
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hh := (le_of_lt hbound).trans (secondaryTentContent_lower_normalized hN)
  exact (le_div_iff₀ (sq_pos_of_pos hNR)).mp hh

theorem secondaryTentContent_eventual_507_2000 :
    ∀ᶠ N : ℕ in atTop, (507/2000:ℝ)*(N:ℝ)^2 ≤
      Real.log (secondaryTentContent N) :=
  secondaryTentContent_eventual_growth (by norm_num)

end
end CatalanMeasure.Parametric
