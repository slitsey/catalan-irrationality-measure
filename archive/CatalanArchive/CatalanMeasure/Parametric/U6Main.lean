module
public import CatalanArchive.CatalanMeasure.Parametric.U3Main
public import CatalanMeasure.Parametric.CombinedContent
public import CatalanMeasure.Parametric.U6PrimeGrowth
@[expose] public section

/-!
# The 740 and 2220 irrationality-measure bounds

The coefficient content of the canonical integer polynomial is the product of
the secondary-tent content (primes in `(52N/9, 44N/7)`), the third-band content
from Lemma U3 (primes in `(8N, 9N)`) and the sixth-window content from Lemma U6
(primes in `(4N, 9N/2)`).  The three prime windows are pairwise disjoint and
lie above `2N`, so the contents multiply.
-/

namespace CatalanMeasure.Parametric
open Polynomial Filter Real OAI.InternalCatalan
open scoped Topology BigOperators
noncomputable section

theorem measure_740_of_gap_bounds
    (F : FirstTrialBoundsAt strongTarget strongFirstCost)
    (D : SecondTrialBoundsOn strongTarget gapResidualCap (-(3/4:ℝ)) gapSecondCost gapAtomDomain)
    (hw : GapWeightBounds) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(740 : ℝ)) < |catalan - (a : ℝ) / b| := by
  obtain ⟨c, hc, hdiv, hcop, hgrowth⟩ := u6_combined_content
  have h := measure_of_content_on twentyGapNodes gapAtomDomain
    (fun N => (twenty_gap_nodes_properties N).1)
    (fun N i => ((twenty_gap_nodes_properties N).2 i).1) gap_nodes_nonzero
    (fun N i => ((twenty_gap_nodes_properties N).2 i).2) strongTarget c hc hdiv hcop
    (χ := 507 / 2000 + 3331 / 10000 + 624 / 10000) (ρ := gapRadiusCost) (η := 375279 / 200000)
    (κ := 3700000 / 519037) (δ := 1 / 10000000)
    hgrowth (gap_atom_point_of_bounds F D hw) strong_eta_lt
    (by norm_num) (by norm_num [gapRadiusCost]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [gapRadiusCost]

theorem measure_2220_of_gap_bounds
    (F : FirstTrialBoundsAt strongTarget strongFirstCost)
    (D : SecondTrialBoundsOn strongTarget gapResidualCap (-(3/4:ℝ)) gapSecondCost gapAtomDomain)
    (hw : GapWeightBounds) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(2220 : ℝ)) < |catalan - (a : ℝ) / b| := by
  obtain ⟨c, hc, hdiv, _hcop, hgrowth⟩ := u6_combined_content
  obtain ⟨P₀, hnz, hsmall⟩ := content_hypotheses_on twentyGapNodes gapAtomDomain
    (fun N => (twenty_gap_nodes_properties N).1)
    (fun N i => ((twenty_gap_nodes_properties N).2 i).1) gap_nodes_nonzero
    (fun N i => ((twenty_gap_nodes_properties N).2 i).2) strongTarget c hc hdiv
    (χ := 507 / 2000 + 3331 / 10000 + 624 / 10000) (ρ := gapRadiusCost) (η := 375279 / 200000)
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
    (η := 375279 / 200000 + (507 / 2000 + 3331 / 10000 + 624 / 10000)) (ρ := gapRadiusCost)
    (by norm_num) (by norm_num [gapRadiusCost]) (twentyContentIntPoly c) P₀ hdeg hnz' hsmall
  simp only [Nat.cast_ofNat] at hh
  filter_upwards [hh, eventually_ge_atTop (2 : ℕ)] with b hb hb2 a
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  exact lt_of_le_of_lt
    (Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num [gapRadiusCost])) (hb a)

theorem catalan_irrationalityMeasure_740 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(740 : ℝ)) < |catalan - (a : ℝ) / b| :=
  measure_740_of_gap_bounds gapFirstTrial gapSecondTrial gap_weight_bounds

theorem catalan_irrationalityMeasure_2220 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(2220 : ℝ)) < |catalan - (a : ℝ) / b| :=
  measure_2220_of_gap_bounds gapFirstTrial gapSecondTrial gap_weight_bounds

end
end CatalanMeasure.Parametric
