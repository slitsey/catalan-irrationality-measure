module

public import CatalanMeasure.GenD.Final
public import CatalanMeasure.GenD.D58.Pay
public import CatalanMeasure.GenD.D58.OddProfile

@[expose] public section

/-!
# D58: the final statement block (both banks)

`measure_592_of_data` (bank K160, `B = 592`) and `measure_590_of_data` (bank K640, `B = 590`) are
`measure_of_design` for the displaced design `(58, 9, 3, 5, 3)` with the payments of `D58.Pay`
(window parameter `w = 3/4`).  The remaining hypotheses are exactly the data not yet produced:

* `Z`            the normalizer (denominators with the recycling exponent);
* `D_growth`     the logarithmic growth of `D_N`;
* `delta_small`  smallness of `Δ_N` near Catalan's constant, i.e. the output of the field /
                 decay-certificate layer (the three trial-pair sups);
* `nonvanishing` the base-matrix (C3) certificate at `N = p`.
-/

namespace CatalanMeasure.GenD
namespace D58
open Polynomial Filter Real CatalanMeasure.Parametric OAI.InternalCatalan
open scoped Topology
noncomputable section

theorem n0_sub_g0 : ((Odd.design.n0 - Odd.design.g0 : ℕ) : ℝ) = d0 := by
  norm_num [Odd.design, d0]

/-- Bank K160: `B = 592`. -/
theorem measure_592_of_data (Z : Normalizer Odd.design) (gD tΔ : ℝ)
    (D_growth : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.log (Z.D N) ≤ (gD + ε) * (N : ℝ) ^ 2)
    (delta_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(K160.rho * (N : ℝ))) →
        |aeval x (Parametric.deltaPoly Odd.design N)| ≤ Real.exp (-((tΔ - ε) * (N : ℝ) ^ 2)))
    (eta_le : K160.eta + chi < tΔ - gD)
    (nonvanishing : ∃ N1 : ℕ, ∀ p : ℕ, N1 ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (Parametric.deltaPoly Odd.design p) ≠ 0) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(592 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have h := measure_of_design Odd.design
    { B := 592, Z := Z, w := 3 / 4, ρ := K160.rho, η := K160.eta + chi, κ := K160.kappa,
      δ := delta, pay := by rw [n0_sub_g0]; simpa [K160.B] using K160.pay_w,
      gD := gD, D_growth := D_growth, tΔ := tΔ, delta_small := delta_small,
      eta_le := eta_le, nonvanishing := nonvanishing }
  simpa using h

/-- Bank K640: `B = 590`. -/
theorem measure_590_of_data (Z : Normalizer Odd.design) (gD tΔ : ℝ)
    (D_growth : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.log (Z.D N) ≤ (gD + ε) * (N : ℝ) ^ 2)
    (delta_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(K640.rho * (N : ℝ))) →
        |aeval x (Parametric.deltaPoly Odd.design N)| ≤ Real.exp (-((tΔ - ε) * (N : ℝ) ^ 2)))
    (eta_le : K640.eta + chi < tΔ - gD)
    (nonvanishing : ∃ N1 : ℕ, ∀ p : ℕ, N1 ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (Parametric.deltaPoly Odd.design p) ≠ 0) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(590 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have h := measure_of_design Odd.design
    { B := 590, Z := Z, w := 3 / 4, ρ := K640.rho, η := K640.eta + chi, κ := K640.kappa,
      δ := delta, pay := by rw [n0_sub_g0]; simpa [K640.B] using K640.pay_w,
      gD := gD, D_growth := D_growth, tΔ := tΔ, delta_small := delta_small,
      eta_le := eta_le, nonvanishing := nonvanishing }
  simpa using h

end
end D58
end CatalanMeasure.GenD
