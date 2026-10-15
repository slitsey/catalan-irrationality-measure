module

public import CatalanMeasure.RecycledRealDegree

@[expose] public section

#print axioms CatalanMeasure.irrationality_measure_of_recycled_polynomials_real_degree_square_pnt
#print axioms CatalanMeasure.asymptotic_real_degree_bound_of_eventual_affine
#print axioms CatalanMeasure.irrationality_measure_of_recycled_polynomials_eventual_real_degree_square_pnt
#print axioms CatalanMeasure.irrationality_measure_of_recycled_polynomials_asymptotic_real_degree_square_pnt

open Real Filter Polynomial
open scoped Topology

/-- The old natural-degree hypotheses remain sufficient, so the new API
    adds no hidden assumption to the established recycled argument. -/
example (G : ℝ) (d : ℕ) {η ρ κ δ : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hκ : 2 < κ) (hδ : 0 < δ)
    (hwindow : 1 < 2 * (1 - δ * (2 * κ - 1)))
    (hlinear : η < 2 * (d : ℝ))
    (hpay : (d : ℝ) + 4 * d * δ * κ < η * κ)
    (Q : ℕ → ℤ[X]) (P₀ : ℕ)
    (hdeg : ∀ p, (Q p).natDegree ≤ d * p)
    (hnz : ∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (Q p) ≠ 0)
    (hcoeff : ∀ p, P₀ ≤ p → p.Prime → ∀ q : ℕ,
      q.Prime → p < q → q ≤ 2 * p →
      ∀ i ≤ d * p, (q : ℤ) ^ (2 * i) ∣ (Q p).coeff i)
    (hsmall : ∀ p, P₀ ≤ p → p.Prime → ∀ x : ℝ,
      |x - G| ≤ exp (-(ρ * p)) → |aeval x (Q p)| ≤ exp (-(η * (p : ℝ) ^ 2))) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(ρ * κ)) < |G - a / b| := by
  apply CatalanMeasure.irrationality_measure_of_recycled_polynomials_real_degree_square_pnt
    G (d : ℝ) hη hρ hκ hδ hwindow hlinear hpay Q P₀
  · intro p _ _
    exact_mod_cast hdeg p
  · exact hnz
  · intro p hp hprime q hq hpq hq2p i hi
    exact hcoeff p hp hprime q hq hpq hq2p i (hi.trans (hdeg p))
  · exact hsmall
