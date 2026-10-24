module

public import CatalanMeasure.GenD.Final
public import CatalanMeasure.GenD.D58.Pay
public import CatalanMeasure.GenD.D58.Normalizer
public import CatalanMeasure.GenD.Nonvanishing
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# D58: the final statement block (both banks)

`measure_592_of_delta_small` (bank K160, `B = 592`) and `measure_590_of_delta_small` (bank K640,
`B = 590`) are `measure_of_design` for the displaced design `(58, 9, 3, 5, 3)`: the payments of
`D58.Pay` (window parameter `w = 3/4`), the normalizer `Znorm` with its denominator growth
`gD58` (odd profile `f58`, gain windows `segs`, 2-adic constant `2673/8`) and the decay rate
`tΔ = (target - log 2 / 2) · 58²` supplied by the field/certificate layer.

Remaining hypotheses (the only ones):
* `delta_small`  smallness of `Δ_N` near Catalan's constant, i.e. the output of the field layer
                 from the three trial-pair sups (the `WeightedAtomPoint` / `FieldsS` bridge);
* `c3`           the base-matrix (C3) certificate: the three `58 × 58` residue matrices modulo
                 `1009` (`B0`, `B0 + B1`, `B0 - B1`) are invertible.
-/

namespace CatalanMeasure.GenD
namespace D58
open Polynomial Filter Real CatalanMeasure.Parametric OAI.InternalCatalan
open scoped Topology
noncomputable section

instance fact1009 : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

/-- The C3 certificate for the displaced design (three residue determinants modulo 1009). -/
def C3 : Prop :=
  (baseB0Residue Odd.design 1009).det ≠ 0 ∧
    (baseB0Residue Odd.design 1009 + baseB1Residue Odd.design 1009).det ≠ 0 ∧
    (baseB0Residue Odd.design 1009 - baseB1Residue Odd.design 1009).det ≠ 0

theorem nonvanishing_d58 (c3 : C3) :
    ∃ N1 : ℕ, ∀ p : ℕ, N1 ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (Parametric.deltaPoly Odd.design p) ≠ 0 :=
  nonvanishing_of_c3 Odd.design Odd.design_admissible (by norm_num)
    (by rw [Odd.design_H]; norm_num) c3.1 c3.2.1 c3.2.2

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
theorem measure_592_of_delta_small
    (delta_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(K160.rho * (N : ℝ))) →
        |aeval x (Parametric.deltaPoly Odd.design N)| ≤
          Real.exp (-((tDelta160 - ε) * (N : ℝ) ^ 2)))
    (c3 : C3) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(592 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have h := measure_of_design Odd.design
    { B := 592, Z := Znorm, w := 3 / 4, ρ := K160.rho, η := K160.eta + chi, κ := K160.kappa,
      δ := delta, pay := by rw [n0_sub_g0]; simpa [K160.B] using K160.pay_w,
      gD := gD58, D_growth := fun ε hε => Znorm_growth hε, tΔ := tDelta160,
      delta_small := delta_small, eta_le := eta_le160, nonvanishing := nonvanishing_d58 c3 }
  simpa using h

/-- Bank K640: `B = 590`. -/
theorem measure_590_of_delta_small
    (delta_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(K640.rho * (N : ℝ))) →
        |aeval x (Parametric.deltaPoly Odd.design N)| ≤
          Real.exp (-((tDelta640 - ε) * (N : ℝ) ^ 2)))
    (c3 : C3) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(590 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have h := measure_of_design Odd.design
    { B := 590, Z := Znorm, w := 3 / 4, ρ := K640.rho, η := K640.eta + chi, κ := K640.kappa,
      δ := delta, pay := by rw [n0_sub_g0]; simpa [K640.B] using K640.pay_w,
      gD := gD58, D_growth := fun ε hε => Znorm_growth hε, tΔ := tDelta640,
      delta_small := delta_small, eta_le := eta_le640, nonvanishing := nonvanishing_d58 c3 }
  simpa using h

end
end D58
end CatalanMeasure.GenD
