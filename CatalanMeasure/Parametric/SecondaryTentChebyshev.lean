module
public import CatalanMeasure.Parametric.SecondaryTentMain
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Filter Real OAI.InternalCatalan
open scoped Topology
noncomputable section

/-- Chebyshev final prime selection, retaining the PNT-backed content estimate.
This is an alternate-criterion corollary, weaker than the published 955. -/
theorem catalan_irrationalityMeasure_2864 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ)^(-(2864:ℝ)) < |catalan-(a:ℝ)/b| := by
  obtain ⟨c, hc, hdiv, _hcop, hgrowth⟩ :=
    secondaryTent_content_of_canonical_rank secondaryTent_canonical_rank
  obtain ⟨P₀, hnz, hsmall⟩ := twentyContentIntPoly_hypotheses c hc hdiv
    (χ := 507/2000) (ρ := 538/5) (η := 3551/2000)
    hgrowth twenty_atom_point_538_5
    (by convert twenty_measure_sharper_eta_lt using 1 <;> norm_num)
  have hnz' : ∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ),
      0 < b → ¬p ∣ b → aeval ((a:ℝ)/b) (twentyContentIntPoly c p) ≠ 0 := by
    intro p hp hprime a b hb hpb
    exact hnz p hp hprime a b hb
      (fun h => hpb (dvd_trans (show p ∣ p^2 from ⟨p, by ring⟩) h))
  have hdeg : ∀ p, (twentyContentIntPoly c p).natDegree ≤ 18*p := by
    intro p
    exact (coefficientContentQuotient_natDegree (twentyMeasureIntPoly p)
      (hc p) (hdiv p)).le.trans (twentyMeasureIntPoly_natDegree_le p)
  have hh := CatalanMeasure.irrationality_measure_of_polynomials catalan 18
    (η := 3551/2000+507/2000) (ρ := 538/5) (by norm_num) (by norm_num)
    (twentyContentIntPoly c) P₀ hdeg hnz' hsmall
  simp only [Nat.cast_ofNat] at hh
  have he : (3:ℝ)*(538/5)*max (18/(3551/2000+507/2000)) 4 =
      (5810400/2029:ℝ) := by norm_num
  rw [he] at hh
  filter_upwards [hh, eventually_ge_atTop (2:ℕ)] with b hb hb2 a
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)) (hb a)

end
end CatalanMeasure.Parametric
