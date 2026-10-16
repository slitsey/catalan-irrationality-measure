module

public import CatalanMeasure.Parametric.TwentyRecycledMain

@[expose] public section

/-!
# Retaining the available twenty-family gap in the recycled criterion

This module uses the unchanged canonical integer polynomial, radius108,
and coefficient recycling. It only sharpens the rational lower bound on
the already proved real/arithmetic gap. The1099 theorem is untouched.
-/

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Polynomial Filter Real
open scoped Topology Nat

noncomputable section

theorem twenty_measure_sharper_eta_lt :
    (17755 / 10000 : ℝ) < 400 * twentyMeasureGap := by
  have hu := Real.log_two_lt_d9
  unfold twentyMeasureGap twentyDualTarget
  norm_num at hu ⊢
  linarith only [hu]

/-- The same canonical polynomial and radius108 give the stronger
    eventual integer exponent1095 after retaining the available gap. -/
theorem catalan_irrationalityMeasure_1095 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(1095 : ℝ)) < |catalan - (a : ℝ) / b| := by
  obtain ⟨P₁, hnz, hsmall⟩ :=
    twentyMeasureIntPoly_full_hypotheses twenty_measure_sharper_eta_lt
  let P₀ := max P₁ 1000000000000
  have hnz' : ∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ),
      0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (twentyMeasureIntPoly p) ≠ 0 := by
    intro p hp hprime
    exact hnz p (le_trans (le_max_left _ _) hp) hprime
  have hsmall' : ∀ p, P₀ ≤ p → p.Prime → ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(108 * (p : ℝ))) →
      |aeval x (twentyMeasureIntPoly p)| ≤
        Real.exp (-((17755 / 10000 : ℝ) * (p : ℝ) ^ 2)) := by
    intro p hp hprime
    exact hsmall p (le_trans (le_max_left _ _) hp) hprime
  have hcoeff : ∀ p, P₀ ≤ p → p.Prime → ∀ q : ℕ,
      q.Prime → p < q → q ≤ 2 * p → ∀ i ≤ 18 * p,
      (q : ℤ) ^ (2 * i) ∣ (twentyMeasureIntPoly p).coeff i := by
    intro p hp _ q hq hpq hq2p i _
    haveI : Fact q.Prime := ⟨hq⟩
    exact twentyMeasureIntPoly_coeff_prime_pow_dvd
      (le_trans (le_max_right _ _) hp) hpq hq2p i
  have hh := CatalanMeasure.irrationality_measure_of_recycled_polynomials_square_pnt
    catalan 18 (η := 17755 / 10000) (ρ := 108)
    (κ := 1095 / 108) (δ := 1 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    twentyMeasureIntPoly P₀ twentyMeasureIntPoly_natDegree_le hnz' hcoeff hsmall'
  convert hh using 1 <;> norm_num

end
end CatalanMeasure.Parametric
