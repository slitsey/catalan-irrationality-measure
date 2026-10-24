module

public import CatalanArchive.CatalanMeasure.GenD.D58.Banks160and640

@[expose] public section

/-!
# Archived: the superseded bank K160 (`B = 592`) statement blocks

Moved out of `D58.Final` and `D58.Certified` when the release switched to `B = 590`.
-/

namespace CatalanMeasure.GenD
namespace D58
open Polynomial Filter Real CatalanMeasure.Parametric OAI.InternalCatalan Set CatalanMeasure.G728
open scoped Topology
noncomputable section

/-- Decay rate of `Δ_N` implied by the bank K160 field target. -/
def tDelta160 : ℝ := (K160.target - Real.log 2 / 2) * 58 ^ 2

theorem eta_le160 : K160.eta + chi < tDelta160 - gD58 := by
  obtain ⟨hl, hh⟩ := log2_bounds
  unfold tDelta160 gD58
  norm_num [K160.eta, K160.etaRef, chi, chiRef, t, K160.target, lo, hi] at hl hh ⊢
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

section budgets
open Analytic

theorem K160.second_budget_gen {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-gC0 Odd.design + gC1 Odd.design * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      K160.normCap + (1 - a) * K160.fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * K160.residualCap + t * nearCap ≤
        -K160.target + Real.log 2 / 2 + K160.secondCost * a := by
  rw [Instances.d58_gC0, Instances.d58_gC1]
  have h := K160.second_budget_log2 ha ht
  norm_num [c07, c26] at h
  linarith

/-- Bank K160: `B = 592`, from the certificates. -/
theorem measure_592_of_certificates
    {g rc C wc : ℝ} (hg0 : 0 < g) (hg1 : g < 1)
    (ha4 : 1 - (2 * g / (1 + g ^ 2)) ^ 2 ≤ 4 * (2 * g / (1 + g ^ 2)))
    (hr1 : 1 < rc) (hr2 : rc ≤ 2)
    (hcirc : Analytic.GapCircleBound Odd.design (2 * g / (1 + g ^ 2)) rc C wc)
    (hwc : wc < K160.rho - 58 * K160.secondCost)
    (F : Analytic.FirstTrialBounds Odd.design K160.target K160.firstCost)
    (u v : ℕ → ℝ) (hu : Summable (fun k => |u k|)) (hv : Summable (fun k => |v k|))
    (MX MY : ℝ) (field_sum : MX + MY = K160.fieldCap)
    (norm_le : 2 * barrierTrialNormSq u + barrierTrialNormSq v / 2 ≤ K160.normCap)
    (near_sup : ∀ y ∈ Ioo (0 : ℝ) 1,
      -Analytic.gRes Odd.design * Real.log (1 + y ^ 2) +
        (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) * Real.log y -
          u 1 * y ≤ nearCap)
    (row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      rowFieldG (11 / 29) (3 / 29) (39 / 29) u v x ≤ MX)
    (column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG (9 / 58) (3 / 58) v s ≤ MY)
    (residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, g ≤ |x| →
      Analytic.resFieldGen (53 / 58) u x ≤ K160.residualCap)
    :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(592 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have S : Analytic.SecondFieldCert Odd.design K160.target K160.residualCap nearCap
      K160.secondCost (fun x => g ≤ |x|) :=
    { u := u, v := v, hu := hu, hv := hv, MX := MX, MY := MY, normCap := K160.normCap,
      fieldCap := K160.fieldCap, near_sup := near_sup, norm_le := norm_le,
      field_sum := field_sum,
      row_sup := by
        rw [(Analytic.Instances.d58_row_weights).1, (Analytic.Instances.d58_row_weights).2.1,
          (Analytic.Instances.d58_row_weights).2.2]
        exact row_sup,
      column_sup := by
        rw [(Analytic.Instances.d58_column_weights).1, (Analytic.Instances.d58_column_weights).2]
        exact column_sup,
      residual_sup := fun x hx hg => by
        rw [Analytic.Instances.d58_gRes]; exact residual_sup x hx hg,
      budget := fun ha ht => K160.second_budget_gen ha ht }
  refine measure_592_of_delta_small ?_ C3.c3_d58
  intro ε hε
  exact Analytic.delta_small_of_certificates Odd.design_admissible hg0 hg1 ha4 hr1 hr2 hcirc
    (w := K160.rho - 58 * K160.secondCost) hwc F S
    (r := 58 * K160.secondCost) (by norm_num [Odd.design, K160.firstCost, K160.secondCost])
    (by norm_num [Odd.design]) (by linarith)
    (by unfold tDelta160; rw [show ((Odd.design.n0 : ℕ) : ℝ) = 58 by norm_num [Odd.design]]; ring) ε hε


end budgets

end
end D58
end CatalanMeasure.GenD
