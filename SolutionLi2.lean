module

public import CatalanCore.Li2.Final

public section

/-!
Irrationality measure of the dilogarithm `Li₂(a/b) = ∑_{k ≥ 1} (a/b)^k/k²`: for coprime integers `a, b` with
`0 < 2|a| ≤ b`, every decay candidate `D` of the certified node table (at `ρ`, sign `a` and `t = log(b/|a|)`)
with `η = D + c(a, b) > 0` gives `|Li₂(a/b) − p/q| > q^(-μ)` for every `μ > ρ·max(2/η, 39/98)`, every
integer `p` and every sufficiently large integer `q`.
-/

namespace Li2IrrationalityMeasure

open CatalanCore.Li2 CatalanCore.Li2.Uniform

theorem li2_measure_general (a b : ℤ) (hb : 0 < b) (hab : IsCoprime a b) (ha : a ≠ 0)
    (h2 : 2 * |a| ≤ b) (ρ D μ : ℝ) (hρ : 0 < ρ)
    (hD : Candidate nodeTable (Int.sign a) (Real.log ((b : ℝ) / |(a : ℝ)|)) ρ D)
    (hη : 0 < D + cRate a b) (hμ : ρ * max (2 / (D + cRate a b)) (39 / 98) < μ) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ, (q : ℝ) ^ (-μ) <
      |(∑' k : ℕ, ((a : ℝ) / b) ^ (k + 1) / ((k : ℝ) + 1) ^ 2) - (p : ℝ) / q| :=
  CatalanCore.Li2.li2_measure_general a b hb hab ha h2 ρ D μ hρ hD hη hμ

#print axioms li2_measure_general

end Li2IrrationalityMeasure
