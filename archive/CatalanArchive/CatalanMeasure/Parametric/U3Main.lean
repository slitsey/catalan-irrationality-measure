module
public import CatalanArchive.CatalanMeasure.Parametric.GapMain
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentMain
public import CatalanArchive.CatalanMeasure.Parametric.U3PrimeGrowth
@[expose] public section

/-!
# The 759 and 2276 irrationality-measure bounds

The coefficient content of the canonical integer polynomial is the product of
the secondary-tent content (primes in `(52N/9, 44N/7)`) and the new third-band
content from Lemma U3 (primes in `(8N, 9N)`).
-/

namespace CatalanMeasure.Parametric
open Polynomial Filter Real OAI.InternalCatalan
open scoped Topology BigOperators
noncomputable section

/-- Combined content: the old secondary-tent content times the new U3 content. -/
theorem u3_combined_content :
    ∃ c : ℕ → ℕ,
      (∀ N, 0 < c N) ∧
      (∀ N i, (c N : ℤ) ∣ (twentyMeasureIntPoly N).coeff i) ∧
      (∀ N q, q.Prime → N < q → q ≤ 2 * N → Nat.Coprime q (c N)) ∧
      (∀ᶠ N : ℕ in atTop, (507 / 2000 + 3331 / 10000 : ℝ) * (N : ℝ) ^ 2 ≤ log (c N)) := by
  classical
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp secondaryTent_canonical_rank
  let T := max N₀ 1000000000000
  let cO : ℕ → ℕ := fun N => if T ≤ N then
    ∏ p ∈ secondaryTentPrimeWindow N, p ^ secondaryTentExponent N p else 1
  let cU : ℕ → ℕ := fun N => if T ≤ N then u3Content N else 1
  have hpO (N p : ℕ) (hp : p ∈ secondaryTentPrimeWindow N) : p.Prime :=
    (Finset.mem_filter.mp hp).2.1
  have hpU (N p : ℕ) (hp : p ∈ u3PrimeWindow N) : p.Prime := (Finset.mem_filter.mp hp).2.1
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
  refine ⟨fun N => cO N * cU N, fun N => Nat.mul_pos (hposO N) (hposU N), ?_, ?_, ?_⟩
  · intro N i
    push_cast
    have hc : IsCoprime (cO N : ℤ) (cU N : ℤ) :=
      Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcopOU N)
    exact hc.mul_dvd (hdivO N i) (hdivU N i)
  · intro N q hq hNq hqN
    apply Nat.Coprime.mul_right
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
  · filter_upwards [secondaryTentPrimeWindow_eventual_507_2000, u3Content_eventual_3331,
      eventually_ge_atTop T] with N h1 h2 hN
    have e1 : (cO N : ℝ) = ((∏ p ∈ secondaryTentPrimeWindow N,
        p ^ secondaryTentExponent N p : ℕ) : ℝ) := by simp [cO, if_pos hN]
    have e2 : (cU N : ℝ) = (u3Content N : ℝ) := by simp [cU, if_pos hN]
    have hO : (0 : ℝ) < cO N := by exact_mod_cast hposO N
    have hU : (0 : ℝ) < cU N := by exact_mod_cast hposU N
    push_cast
    rw [Real.log_mul hO.ne' hU.ne', e1, e2]
    linarith

theorem measure_759_of_gap_bounds
    (F : FirstTrialBoundsAt strongTarget strongFirstCost)
    (D : SecondTrialBoundsOn strongTarget gapResidualCap (-(3/4:ℝ)) gapSecondCost gapAtomDomain)
    (hw : GapWeightBounds) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(759 : ℝ)) < |catalan - (a : ℝ) / b| := by
  obtain ⟨c, hc, hdiv, hcop, hgrowth⟩ := u3_combined_content
  have h := measure_of_content_on twentyGapNodes gapAtomDomain
    (fun N => (twenty_gap_nodes_properties N).1)
    (fun N i => ((twenty_gap_nodes_properties N).2 i).1) gap_nodes_nonzero
    (fun N i => ((twenty_gap_nodes_properties N).2 i).2) strongTarget c hc hdiv hcop
    (χ := 507 / 2000 + 3331 / 10000) (ρ := gapRadiusCost) (η := 375279 / 200000)
    (κ := 3795000 / 519037) (δ := 1 / 10000000)
    hgrowth (gap_atom_point_of_bounds F D hw) strong_eta_lt
    (by norm_num) (by norm_num [gapRadiusCost]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [gapRadiusCost]

theorem measure_2276_of_gap_bounds
    (F : FirstTrialBoundsAt strongTarget strongFirstCost)
    (D : SecondTrialBoundsOn strongTarget gapResidualCap (-(3/4:ℝ)) gapSecondCost gapAtomDomain)
    (hw : GapWeightBounds) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(2276 : ℝ)) < |catalan - (a : ℝ) / b| := by
  obtain ⟨c, hc, hdiv, _hcop, hgrowth⟩ := u3_combined_content
  obtain ⟨P₀, hnz, hsmall⟩ := content_hypotheses_on twentyGapNodes gapAtomDomain
    (fun N => (twenty_gap_nodes_properties N).1)
    (fun N i => ((twenty_gap_nodes_properties N).2 i).1) gap_nodes_nonzero
    (fun N i => ((twenty_gap_nodes_properties N).2 i).2) strongTarget c hc hdiv
    (χ := 507 / 2000 + 3331 / 10000) (ρ := gapRadiusCost) (η := 375279 / 200000)
    hgrowth (gap_atom_point_of_bounds F D hw) strong_eta_lt
  have hnz' : ∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ),
      0 < b → ¬ p ∣ b → aeval ((a : ℝ) / b) (twentyContentIntPoly c p) ≠ 0 := by
    intro p hp hprime a b hb hpb
    exact hnz p hp hprime a b hb
      (fun h => hpb (dvd_trans (show p ∣ p ^ 2 from ⟨p, by ring⟩) h))
  have hdeg : ∀ p, (twentyContentIntPoly c p).natDegree ≤ 18 * p := by
    intro p
    exact (coefficientContentQuotient_natDegree (twentyMeasureIntPoly p)
      (hc p) (hdiv p)).le.trans (twentyMeasureIntPoly_natDegree_le p)
  have hh := CatalanMeasure.irrationality_measure_of_polynomials catalan 18
    (η := 375279 / 200000 + (507 / 2000 + 3331 / 10000)) (ρ := gapRadiusCost) (by norm_num)
    (by norm_num [gapRadiusCost]) (twentyContentIntPoly c) P₀ hdeg hnz' hsmall
  simp only [Nat.cast_ofNat] at hh
  filter_upwards [hh, eventually_ge_atTop (2 : ℕ)] with b hb hb2 a
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  exact lt_of_le_of_lt
    (Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num [gapRadiusCost])) (hb a)

theorem catalan_irrationalityMeasure_759 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(759 : ℝ)) < |catalan - (a : ℝ) / b| :=
  measure_759_of_gap_bounds gapFirstTrial gapSecondTrial gap_weight_bounds

theorem catalan_irrationalityMeasure_2276 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(2276 : ℝ)) < |catalan - (a : ℝ) / b| :=
  measure_2276_of_gap_bounds gapFirstTrial gapSecondTrial gap_weight_bounds

end
end CatalanMeasure.Parametric
