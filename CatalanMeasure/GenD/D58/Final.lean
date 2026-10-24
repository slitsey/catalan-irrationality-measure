module

public import CatalanMeasure.GenD.Final
public import CatalanMeasure.GenD.D58.Pay
public import CatalanMeasure.GenD.D58.Normalizer

@[expose] public section

/-!
# D58: the final statement block (both banks)

`measure_592_of_certificates` (bank K160, `B = 592`) and `measure_590_of_certificates` (bank K640,
`B = 590`) are `measure_of_design` for the displaced design `(58, 9, 3, 5, 3)`: the payments of
`D58.Pay` (window parameter `w = 3/4`), the normalizer `Znorm` with its denominator growth
`gD58` (odd profile `f58`, gain windows `segs`, 2-adic constant `2673/8`) and the decay rate
`tΔ = (target - log 2 / 2) · 58²` supplied by the field/certificate layer.

Remaining hypotheses (the only ones):
* `delta_small`  smallness of `Δ_N` near Catalan's constant, i.e. the output of the field layer
                 from the three trial-pair sups (the `WeightedAtomPoint` / `FieldsS` bridge);
* `nonvanishing` the base-matrix (C3) certificate at `N = p`.
-/

namespace CatalanMeasure.GenD
namespace D58
open Polynomial Filter Real CatalanMeasure.Parametric OAI.InternalCatalan
open scoped Topology
noncomputable section

theorem n0_sub_g0 : ((Odd.design.n0 - Odd.design.g0 : ℕ) : ℝ) = d0 := by
  norm_num [Odd.design, d0]

/-- Decay rate of `Δ_N` implied by the bank K160 field target. -/
def tDelta160 : ℝ := (K160.target - Real.log 2 / 2) * 58 ^ 2

/-- Decay rate of `Δ_N` implied by the bank K640 field target. -/
def tDelta640 : ℝ := (K640.target - Real.log 2 / 2) * 58 ^ 2

theorem eta_le160 : K160.eta + chi < tDelta160 - gD58 := by
  obtain ⟨hl, hh⟩ := log2_bounds
  unfold tDelta160 gD58
  norm_num [K160.eta, K160.etaRef, chi, chiRef, t, K160.target, lo, hi] at hl hh ⊢
  linarith

theorem eta_le640 : K640.eta + chi < tDelta640 - gD58 := by
  obtain ⟨hl, hh⟩ := log2_bounds
  unfold tDelta640 gD58
  norm_num [K640.eta, K640.etaRef, chi, chiRef, t, K640.target, lo, hi] at hl hh ⊢
  linarith

/-- Bank K160: `B = 592`. -/
theorem measure_592_of_certificates
    (delta_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(K160.rho * (N : ℝ))) →
        |aeval x (Parametric.deltaPoly Odd.design N)| ≤
          Real.exp (-((tDelta160 - ε) * (N : ℝ) ^ 2)))
    (nonvanishing : ∃ N1 : ℕ, ∀ p : ℕ, N1 ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (Parametric.deltaPoly Odd.design p) ≠ 0) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(592 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have h := measure_of_design Odd.design
    { B := 592, Z := Znorm, w := 3 / 4, ρ := K160.rho, η := K160.eta + chi, κ := K160.kappa,
      δ := delta, pay := by rw [n0_sub_g0]; simpa [K160.B] using K160.pay_w,
      gD := gD58, D_growth := fun ε hε => Znorm_growth hε, tΔ := tDelta160,
      delta_small := delta_small, eta_le := eta_le160, nonvanishing := nonvanishing }
  simpa using h

/-- Bank K640: `B = 590`. -/
theorem measure_590_of_certificates
    (delta_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(K640.rho * (N : ℝ))) →
        |aeval x (Parametric.deltaPoly Odd.design N)| ≤
          Real.exp (-((tDelta640 - ε) * (N : ℝ) ^ 2)))
    (nonvanishing : ∃ N1 : ℕ, ∀ p : ℕ, N1 ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (Parametric.deltaPoly Odd.design p) ≠ 0) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(590 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have h := measure_of_design Odd.design
    { B := 590, Z := Znorm, w := 3 / 4, ρ := K640.rho, η := K640.eta + chi, κ := K640.kappa,
      δ := delta, pay := by rw [n0_sub_g0]; simpa [K640.B] using K640.pay_w,
      gD := gD58, D_growth := fun ε hε => Znorm_growth hε, tΔ := tDelta640,
      delta_small := delta_small, eta_le := eta_le640, nonvanishing := nonvanishing }
  simpa using h

end
end D58
end CatalanMeasure.GenD
