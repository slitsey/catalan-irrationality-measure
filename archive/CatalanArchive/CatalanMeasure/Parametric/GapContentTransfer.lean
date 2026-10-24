module
public import CatalanArchive.CatalanMeasure.Parametric.GapSmallness
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentMain
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentChebyshev
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Filter Real OAI.InternalCatalan
open scoped Topology
noncomputable section
/-- Content can be removed from the canonical integer polynomial while retaining
the same radius and gaining its quadratic logarithmic growth in the gap. -/
theorem content_hypotheses_on
    (τ : (N : ℕ) → Fin (18*N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1:ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target : ℝ) (c : ℕ → ℕ)
    (hc : ∀ N, 0 < c N)
    (hdiv : ∀ N i, (c N : ℤ) ∣ (twentyMeasureIntPoly N).coeff i)
    {χ ρ η : ℝ} (hcontent : ∀ᶠ N : ℕ in atTop, χ * (N : ℝ) ^ 2 ≤ log (c N))
    (hpoint : WeightedAtomPointOn τ G target ρ) (hη : η < 400 * measureGapAt target) :
    ∃ P₀ : ℕ,
      (∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
        aeval ((a : ℝ) / b) (twentyContentIntPoly c p) ≠ 0) ∧
      (∀ p, P₀ ≤ p → p.Prime → ∀ x : ℝ,
        |x - catalan| ≤ exp (-(ρ * (p : ℝ))) →
        |aeval x (twentyContentIntPoly c p)| ≤ exp (-((η + χ) * (p : ℝ) ^ 2))) := by
  obtain ⟨P₁, hnz, hsmall⟩ := integer_poly_hypotheses_on τ G hτinj hτmem hτzero hτG target ρ hpoint hη
  obtain ⟨P₂, hP₂⟩ := eventually_atTop.mp hcontent
  refine ⟨max P₁ P₂, ?_, ?_⟩
  · intro p hp hprime a b hb hpb
    apply (coefficientContentQuotient_aeval_ne_zero_iff
      (twentyMeasureIntPoly p) (hc p) (hdiv p) _).mpr
    exact hnz p ((le_max_left _ _).trans hp) hprime a b hb hpb
  · intro p hp hprime x hx
    have h := coefficientContentQuotient_abs_aeval_le
      (twentyMeasureIntPoly p) (hc p) (hdiv p) x
      (η * (p : ℝ) ^ 2) (χ * (p : ℝ) ^ 2)
      (hsmall p ((le_max_left _ _).trans hp) hprime x hx)
      (hP₂ p ((le_max_right _ _).trans hp))
    simpa only [twentyContentIntPoly, add_mul] using h

/-- Reusable final transfer: coefficientwise content away from the recycling
primes, with a proved logarithmic rate, feeds the existing PNT criterion. -/
theorem measure_of_content_on
    (τ : (N : ℕ) → Fin (18*N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1:ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target : ℝ) (c : ℕ → ℕ)
    (hc : ∀ N, 0 < c N)
    (hdiv : ∀ N i, (c N : ℤ) ∣ (twentyMeasureIntPoly N).coeff i)
    (hcop : ∀ N q, q.Prime → N < q → q ≤ 2 * N → Nat.Coprime q (c N))
    {χ ρ η κ δ : ℝ}
    (hcontent : ∀ᶠ N : ℕ in atTop, χ * (N : ℝ) ^ 2 ≤ log (c N))
    (hpoint : WeightedAtomPointOn τ G target ρ) (hη : η < 400 * measureGapAt target)
    (hgap : 0 < η + χ) (hρ : 0 < ρ) (hκ : 2 < κ) (hδ : 0 < δ)
    (hwindow : 1 < 2 * (1 - δ * (2 * κ - 1)))
    (hlinear : η + χ < 2 * (18 : ℝ))
    (hpay : (18 : ℝ) + 4 * 18 * δ * κ < (η + χ) * κ) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(ρ * κ)) < |catalan - (a : ℝ) / b| := by
  obtain ⟨P₁, hnz, hsmall⟩ :=
    content_hypotheses_on τ G hτinj hτmem hτzero hτG target c hc hdiv hcontent hpoint hη
  let P₀ := max P₁ 1000000000000
  apply CatalanMeasure.irrationality_measure_of_recycled_polynomials_square_pnt
    catalan 18 hgap hρ hκ hδ hwindow hlinear hpay (twentyContentIntPoly c) P₀
  · intro p
    exact (coefficientContentQuotient_natDegree (twentyMeasureIntPoly p)
      (hc p) (hdiv p)).le.trans (twentyMeasureIntPoly_natDegree_le p)
  · intro p hp hprime
    exact hnz p ((le_max_left _ _).trans hp) hprime
  · intro p hp _ q hq hpq hq2p i _
    have : Fact q.Prime := ⟨hq⟩
    exact coefficientContentQuotient_coeff_prime_pow_dvd (twentyMeasureIntPoly p)
      (hdiv p) (hcop p q hq hpq hq2p)
      (twentyMeasureIntPoly_coeff_prime_pow_dvd
        ((le_max_right _ _).trans hp) hpq hq2p i)
  · intro p hp hprime
    exact hsmall p ((le_max_left _ _).trans hp) hprime


end
end CatalanMeasure.Parametric
