module
public import CatalanMeasure.Parametric.SecondaryTentMain
public import CatalanMeasure.Parametric.U3PrimeGrowth
public import CatalanMeasure.Parametric.U6PrimeGrowth
public import CatalanMeasure.Parametric.SecondaryTentPrimeGrowthWindow
@[expose] public section

/-!
# Combined coefficient content

The coefficient content of the canonical integer polynomial is the product of the secondary-tent
content (primes in `(52N/9, 44N/7)`), the third-band content from Lemma U3 (primes in `(8N, 9N)`) and the
sixth-window content from Lemma U6 (primes in `(4N, 9N/2)`). The three prime windows are pairwise disjoint
and lie above `2N`, so the contents multiply.
-/

namespace CatalanMeasure.Parametric
open Polynomial Filter Real OAI.InternalCatalan
open scoped Topology BigOperators
noncomputable section

/-- Combined content: secondary tent, U3 and U6 windows. -/
theorem u6_combined_content :
    ∃ c : ℕ → ℕ,
      (∀ N, 0 < c N) ∧
      (∀ N i, (c N : ℤ) ∣ (twentyMeasureIntPoly N).coeff i) ∧
      (∀ N q, q.Prime → N < q → q ≤ 2 * N → Nat.Coprime q (c N)) ∧
      (∀ᶠ N : ℕ in atTop,
        (507 / 2000 + 3331 / 10000 + 624 / 10000 : ℝ) * (N : ℝ) ^ 2 ≤ log (c N)) := by
  classical
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp secondaryTent_canonical_rank
  let T := max N₀ 1000000000000
  let cO : ℕ → ℕ := fun N => if T ≤ N then
    ∏ p ∈ secondaryTentPrimeWindow N, p ^ secondaryTentExponent N p else 1
  let cU : ℕ → ℕ := fun N => if T ≤ N then u3Content N else 1
  let cV : ℕ → ℕ := fun N => if T ≤ N then u6Content N else 1
  have hpO (N p : ℕ) (hp : p ∈ secondaryTentPrimeWindow N) : p.Prime :=
    (Finset.mem_filter.mp hp).2.1
  have hpU (N p : ℕ) (hp : p ∈ u3PrimeWindow N) : p.Prime := (Finset.mem_filter.mp hp).2.1
  have hpV (N p : ℕ) (hp : p ∈ u6PrimeWindow N) : p.Prime := (Finset.mem_filter.mp hp).2.1
  have hposO : ∀ N, 0 < cO N := by
    intro N
    by_cases hN : T ≤ N
    · simp only [cO, if_pos hN]
      exact Finset.prod_pos fun p hp => pow_pos (hpO N p hp).pos _
    · simp [cO, hN]
  have hposU : ∀ N, 0 < cU N := by
    intro N
    by_cases hN : T ≤ N
    · simp only [cU, if_pos hN, u3Content]
      exact Finset.prod_pos fun p hp => pow_pos (hpU N p hp).pos _
    · simp [cU, hN]
  have hposV : ∀ N, 0 < cV N := by
    intro N
    by_cases hN : T ≤ N
    · simp only [cV, if_pos hN, u6Content]
      exact Finset.prod_pos fun p hp => pow_pos (hpV N p hp).pos _
    · simp [cV, hN]
  have hdivO : ∀ N i, (cO N : ℤ) ∣ (twentyMeasureIntPoly N).coeff i := by
    intro N i
    by_cases hN : T ≤ N
    · simp only [cO, if_pos hN]
      apply primePowerProduct_dvd_coeff (twentyMeasureIntPoly N)
        (secondaryTentPrimeWindow N) (secondaryTentExponent N) (hpO N)
      intro p hp j
      haveI : Fact p.Prime := ⟨hpO N p hp⟩
      have hs := (Finset.mem_filter.mp hp).2.2
      exact twentyMeasureIntPoly_tent_coeff_prime_pow_dvd_of_rank
        ((le_max_right _ _).trans hN) hs.1 hs.2 (secondaryTentExponent_le_N N p)
        (hN₀ N ((le_max_left _ _).trans hN) p hs.1 hs.2) j
    · simp [cO, hN]
  have hdivU : ∀ N i, (cU N : ℤ) ∣ (twentyMeasureIntPoly N).coeff i := by
    intro N i
    by_cases hN : T ≤ N
    · simp only [cU, if_pos hN, u3Content]
      apply primePowerProduct_dvd_coeff (twentyMeasureIntPoly N)
        (u3PrimeWindow N) (thirdTentExponent N) (hpU N)
      intro p hp j
      haveI : Fact p.Prime := ⟨hpU N p hp⟩
      have hs := (Finset.mem_filter.mp hp).2.2
      have hN' : 1000000000000 ≤ N := (le_max_right _ _).trans hN
      have hNpos : 0 < N := by omega
      exact twentyMeasureIntPoly_third_coeff_dvd hN' hs.1 hs.2
        (u3_canonical_rank hNpos hs.1 hs.2) j
    · simp [cU, hN]
  have hdivV : ∀ N i, (cV N : ℤ) ∣ (twentyMeasureIntPoly N).coeff i := by
    intro N i
    by_cases hN : T ≤ N
    · simp only [cV, if_pos hN, u6Content]
      apply primePowerProduct_dvd_coeff (twentyMeasureIntPoly N)
        (u6PrimeWindow N) (sixthExponent N) (hpV N)
      intro p hp j
      haveI : Fact p.Prime := ⟨hpV N p hp⟩
      have hs := (Finset.mem_filter.mp hp).2.2
      have hN' : 1000000000000 ≤ N := (le_max_right _ _).trans hN
      exact twentyMeasureIntPoly_sixth_coeff_dvd hN' hs.1 hs.2 j
    · simp [cV, hN]
  have hcopOU : ∀ N, Nat.Coprime (cO N) (cU N) := by
    intro N
    by_cases hN : T ≤ N
    · simp only [cO, cU, if_pos hN, u3Content]
      apply Nat.Coprime.prod_left
      intro p hp
      apply Nat.Coprime.prod_right
      intro q hq
      apply Nat.Coprime.pow
      apply (Nat.coprime_primes (hpO N p hp) (hpU N q hq)).mpr
      have h1 := (Finset.mem_filter.mp hp).2.2
      have h2 := u3PrimeWindow_above hq
      have h3 := (Finset.mem_filter.mp hp).1
      simp only [Finset.mem_Ioc] at h3
      omega
    · simp [cO, cU, hN]
  have hcopOV : ∀ N, Nat.Coprime (cO N) (cV N) := by
    intro N
    by_cases hN : T ≤ N
    · simp only [cO, cV, if_pos hN, u6Content]
      apply Nat.Coprime.prod_left
      intro p hp
      apply Nat.Coprime.prod_right
      intro q hq
      apply Nat.Coprime.pow
      apply (Nat.coprime_primes (hpO N p hp) (hpV N q hq)).mpr
      have h1 := (Finset.mem_filter.mp hp).2.2
      have h2 := u6PrimeWindow_above hq
      have h3 := (Finset.mem_filter.mp hq).2.2
      omega
    · simp [cO, cV, hN]
  have hcopUV : ∀ N, Nat.Coprime (cU N) (cV N) := by
    intro N
    by_cases hN : T ≤ N
    · simp only [cU, cV, if_pos hN, u3Content, u6Content]
      apply Nat.Coprime.prod_left
      intro p hp
      apply Nat.Coprime.prod_right
      intro q hq
      apply Nat.Coprime.pow
      apply (Nat.coprime_primes (hpU N p hp) (hpV N q hq)).mpr
      have h1 := u3PrimeWindow_above hp
      have h3 := (Finset.mem_filter.mp hq).2.2
      omega
    · simp [cU, cV, hN]
  refine ⟨fun N => cO N * cU N * cV N,
    fun N => Nat.mul_pos (Nat.mul_pos (hposO N) (hposU N)) (hposV N), ?_, ?_, ?_⟩
  · intro N i
    push_cast
    have hc1 : IsCoprime (cO N : ℤ) (cU N : ℤ) :=
      Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcopOU N)
    have hc2 : IsCoprime ((cO N : ℤ) * (cU N : ℤ)) (cV N : ℤ) := by
      apply IsCoprime.mul_left
      · exact Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcopOV N)
      · exact Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcopUV N)
    exact hc2.mul_dvd (hc1.mul_dvd (hdivO N i) (hdivU N i)) (hdivV N i)
  · intro N q hq hNq hqN
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.mul_right
      · by_cases hN : T ≤ N
        · simp only [cO, if_pos hN]
          exact primePowerProduct_coprime_of_above (secondaryTentPrimeWindow N)
            (secondaryTentExponent N) (hpO N)
            (fun _ hp => secondaryTentPrimeWindow_above_twoN hp) hq hqN
        · simp [cO, hN]
      · by_cases hN : T ≤ N
        · simp only [cU, if_pos hN, u3Content]
          exact primePowerProduct_coprime_of_above (u3PrimeWindow N) (thirdTentExponent N)
            (hpU N) (fun p hp => by have := u3PrimeWindow_above hp; omega) hq hqN
        · simp [cU, hN]
    · by_cases hN : T ≤ N
      · simp only [cV, if_pos hN, u6Content]
        exact primePowerProduct_coprime_of_above (u6PrimeWindow N) (sixthExponent N)
          (hpV N) (fun p hp => by have := u6PrimeWindow_above hp; omega) hq hqN
      · simp [cV, hN]
  · filter_upwards [secondaryTentPrimeWindow_eventual_507_2000, u3Content_eventual_3331,
      u6Content_eventual_624, eventually_ge_atTop T] with N h1 h2 h3 hN
    have e1 : (cO N : ℝ) = ((∏ p ∈ secondaryTentPrimeWindow N,
        p ^ secondaryTentExponent N p : ℕ) : ℝ) := by simp [cO, if_pos hN]
    have e2 : (cU N : ℝ) = (u3Content N : ℝ) := by simp [cU, if_pos hN]
    have e3 : (cV N : ℝ) = (u6Content N : ℝ) := by simp [cV, if_pos hN]
    have hO : (0 : ℝ) < cO N := by exact_mod_cast hposO N
    have hU : (0 : ℝ) < cU N := by exact_mod_cast hposU N
    have hV : (0 : ℝ) < cV N := by exact_mod_cast hposV N
    push_cast
    rw [Real.log_mul (mul_pos hO hU).ne' hV.ne', Real.log_mul hO.ne' hU.ne', e1, e2, e3]
    linarith

end
end CatalanMeasure.Parametric
