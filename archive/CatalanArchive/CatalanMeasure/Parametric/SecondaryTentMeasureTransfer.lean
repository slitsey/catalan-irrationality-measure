module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRankContent
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentPrimeGrowthWindow
public import CatalanArchive.CatalanMeasure.Parametric.TwentyContentTransfer

/-!
# End-to-end transfer of the concrete secondary tent rank theorem

The actual canonical rank statement is an explicit hypothesis. This file
does not assert an unconditional new irrationality-measure bound.
-/

@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Filter Real OAI.InternalCatalan
open scoped Topology BigOperators
noncomputable section

theorem secondaryTentExponent_le_N (N p : ℕ) :
    secondaryTentExponent N p ≤ N := by
  rw [secondaryTentExponent_eq_int_div]
  omega

/-- The remaining concrete arithmetic obligation, on the actual canonical
scaled residue matrix and with the exact natural truncated exponent. -/
def SecondaryTentCanonicalRankHypothesis : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ (p : ℕ) [Fact p.Prime],
    52*N < 9*p → 7*p < 44*N →
      (scaledResidueMatrix (p := p) (measureBaseMatrix twenty N)).rank ≤
        20*N-secondaryTentExponent N p

/-- A uniform actual rank theorem supplies a positive common coefficient
divisor, away from all recycling primes, of logarithmic rate 507/2000. -/
theorem secondaryTent_content_of_canonical_rank
    (hrank : SecondaryTentCanonicalRankHypothesis) :
    ∃ c : ℕ → ℕ,
      (∀ N, 0 < c N) ∧
      (∀ N i, (c N : ℤ) ∣ (twentyMeasureIntPoly N).coeff i) ∧
      (∀ N q, q.Prime → N < q → q ≤ 2*N → Nat.Coprime q (c N)) ∧
      (∀ᶠ N : ℕ in atTop, (507/2000:ℝ)*(N:ℝ)^2 ≤ log (c N)) := by
  classical
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hrank
  let T := max N₀ 1000000000000
  let c : ℕ → ℕ := fun N => if T ≤ N then
    ∏ p ∈ secondaryTentPrimeWindow N, p ^ secondaryTentExponent N p else 1
  have hprime (N p : ℕ) (hp : p ∈ secondaryTentPrimeWindow N) : p.Prime := by
    exact (Finset.mem_filter.mp hp).2.1
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro N
    by_cases hN : T ≤ N
    · simp only [c, if_pos hN]
      exact Finset.prod_pos fun p hp => pow_pos (hprime N p hp).pos _
    · simp [c, hN]
  · intro N i
    by_cases hN : T ≤ N
    · simp only [c, if_pos hN]
      apply primePowerProduct_dvd_coeff (twentyMeasureIntPoly N)
        (secondaryTentPrimeWindow N) (secondaryTentExponent N) (hprime N)
      intro p hp j
      haveI : Fact p.Prime := ⟨hprime N p hp⟩
      have hs := (Finset.mem_filter.mp hp).2.2
      exact twentyMeasureIntPoly_tent_coeff_prime_pow_dvd_of_rank
        ((le_max_right _ _).trans hN) hs.1 hs.2 (secondaryTentExponent_le_N N p)
        (hN₀ N ((le_max_left _ _).trans hN) p hs.1 hs.2) j
    · simp [c, hN]
  · intro N q hq _ hqN
    by_cases hN : T ≤ N
    · simp only [c, if_pos hN]
      exact primePowerProduct_coprime_of_above (secondaryTentPrimeWindow N)
        (secondaryTentExponent N) (hprime N)
        (fun _ hp => secondaryTentPrimeWindow_above_twoN hp) hq hqN
    · simp [c, hN]
  · filter_upwards [secondaryTentPrimeWindow_eventual_507_2000,
      eventually_ge_atTop T] with N hg hN
    simpa only [c, if_pos hN] using hg

/-- Conditional numerical endpoint: all remaining input is the actual
canonical residue rank theorem, not an assumed coefficient-content rate. -/
theorem catalan_irrationalityMeasure_955_of_canonical_tent_rank
    (hrank : SecondaryTentCanonicalRankHypothesis) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(955 : ℝ)) < |catalan - (a : ℝ)/b| := by
  obtain ⟨c, hc, hdiv, hcop, hgrowth⟩ := secondaryTent_content_of_canonical_rank hrank
  have h := irrationality_measure_of_twenty_coefficient_content c hc hdiv hcop
    (χ := 507/2000) (ρ := 538/5) (η := 3551/2000)
    (κ := 955/(538/5)) (δ := 1/1000000)
    hgrowth twenty_atom_point_538_5
    (by convert twenty_measure_sharper_eta_lt using 1 <;> norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

end
end CatalanMeasure.Parametric
