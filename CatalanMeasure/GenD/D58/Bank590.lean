module

public import CatalanMeasure.GenD.D58.Budget590
public import CatalanMeasure.GenD.D58.Certified
public import CatalanMeasure.GenD.D58.FirstTrialCert
public import CatalanMeasure.GenD.D58.Circle

@[expose] public section

/-!
# D58, bank K590 (`B = 590`, witness `gi`): payments, decay rate, first-population contract
and the certificate-level theorem

Same assembly as `K640` (`Pay`, `Final`, `FirstTrial`, `FirstTrialCert`, `Certified`), instantiated
with the constants of `D58.Budget590` (the first-trial cover certificate `hrow_D58`, `hcol_D58` is
shared: only the budget `K590.first_budget_log2` is new).
-/

namespace CatalanMeasure.GenD
namespace D58
open Polynomial Filter Real CatalanMeasure.Parametric OAI.InternalCatalan Set CatalanMeasure.G728
open CatalanMeasure.GenD.Analytic
open scoped Topology
noncomputable section

theorem K590.pay_w : PayW (3 / 4) d0 K590.rho (K590.eta + chi) K590.kappa delta K590.B := by
  unfold PayW K590.kappa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [K590.B, d0, K590.rho, K590.eta, chi, delta, t, K590.etaRef, chiRef, deltaRef,
      K590.secondCost, wcap]

/-- Decay rate of `Δ_N` implied by the bank K590 field target. -/
def tDelta590 : ℝ := (K590.target - Real.log 2 / 2) * 58 ^ 2

theorem eta_le590 : K590.eta + chi < tDelta590 - gD58 := by
  obtain ⟨hl, hh⟩ := log2_bounds
  unfold tDelta590 gD58
  norm_num [K590.eta, K590.etaRef, chi, chiRef, t, K590.target, lo, hi] at hl hh ⊢
  linarith

/-- Bank K590: `B = 590`. -/
theorem measure_590_of_delta_small_K590
    (delta_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(K590.rho * (N : ℝ))) →
        |aeval x (Parametric.deltaPoly Odd.design N)| ≤
          Real.exp (-((tDelta590 - ε) * (N : ℝ) ^ 2)))
    (c3 : C3) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(590 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have h := measure_of_design Odd.design
    { B := 590, Z := Znorm, w := 3 / 4, ρ := K590.rho, η := K590.eta + chi, κ := K590.kappa,
      δ := delta, pay := by rw [n0_sub_g0]; simpa [K590.B] using K590.pay_w,
      gD := gD58, D_growth := fun ε hε => Znorm_growth hε, tΔ := tDelta590,
      delta_small := delta_small, eta_le := eta_le590, nonvanishing := nonvanishing_d58 c3 }
  simpa using h

/-- Bank K590 first-population contract (cover certificate shared with K160 / K640). -/
def K590.firstTrial
    (hrow : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      firstRowFieldG (11 / 29) (3 / 29) (49 / 58) lamFirst (5 / 29) firstP firstV x ≤ MX1)
    (hcol : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG (9 / 58) (3 / 58) firstV s ≤ MY1) :
    FirstTrialBounds Odd.design K590.target K590.firstCost :=
  firstTrial_D58 hrow hcol K590.first_budget_log2

/-- Bank K590 first-population contract, hypothesis-free. -/
def K590.firstTrialCert : FirstTrialBounds Odd.design K590.target K590.firstCost :=
  K590.firstTrial hrow_D58 hcol_D58

theorem circ_hwc590 : (52788 / 1000 : ℝ) < K590.rho - 58 * K590.secondCost := by
  norm_num [K590.rho, K590.secondCost, wcap]

theorem K590.second_budget_gen {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-gC0 Odd.design + gC1 Odd.design * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      K590.normCap + (1 - a) * K590.fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * K590.residualCap + t * nearCap ≤
        -K590.target + Real.log 2 / 2 + K590.secondCost * a := by
  rw [Instances.d58_gC0, Instances.d58_gC1]
  have h := K590.second_budget_log2 ha ht
  norm_num [c07, c26] at h
  linarith

/-- Bank K590: `B = 590`, from the certificates. -/
theorem measure_590_of_certificates_K590
    {g rc C wc : ℝ} (hg0 : 0 < g) (hg1 : g < 1)
    (ha4 : 1 - (2 * g / (1 + g ^ 2)) ^ 2 ≤ 4 * (2 * g / (1 + g ^ 2)))
    (hr1 : 1 < rc) (hr2 : rc ≤ 2)
    (hcirc : Analytic.GapCircleBound Odd.design (2 * g / (1 + g ^ 2)) rc C wc)
    (hwc : wc < K590.rho - 58 * K590.secondCost)
    (F : Analytic.FirstTrialBounds Odd.design K590.target K590.firstCost)
    (u v : ℕ → ℝ) (hu : Summable (fun k => |u k|)) (hv : Summable (fun k => |v k|))
    (MX MY : ℝ) (field_sum : MX + MY = K590.fieldCap)
    (norm_le : 2 * barrierTrialNormSq u + barrierTrialNormSq v / 2 ≤ K590.normCap)
    (near_sup : ∀ y ∈ Ioo (0 : ℝ) 1,
      -Analytic.gRes Odd.design * Real.log (1 + y ^ 2) +
        (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) * Real.log y -
          u 1 * y ≤ nearCap)
    (row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      rowFieldG (11 / 29) (3 / 29) (39 / 29) u v x ≤ MX)
    (column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG (9 / 58) (3 / 58) v s ≤ MY)
    (residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, g ≤ |x| →
      Analytic.resFieldGen (53 / 58) u x ≤ K590.residualCap)
    :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(590 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have S : Analytic.SecondFieldCert Odd.design K590.target K590.residualCap nearCap
      K590.secondCost (fun x => g ≤ |x|) :=
    { u := u, v := v, hu := hu, hv := hv, MX := MX, MY := MY, normCap := K590.normCap,
      fieldCap := K590.fieldCap, near_sup := near_sup, norm_le := norm_le,
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
      budget := fun ha ht => K590.second_budget_gen ha ht }
  refine measure_590_of_delta_small_K590 ?_ C3.c3_d58
  intro ε hε
  exact Analytic.delta_small_of_certificates Odd.design_admissible hg0 hg1 ha4 hr1 hr2 hcirc
    (w := K590.rho - 58 * K590.secondCost) hwc F S
    (r := 58 * K590.secondCost) (by norm_num [Odd.design, K590.firstCost, K590.secondCost])
    (by norm_num [Odd.design]) (by linarith)
    (by unfold tDelta590; rw [show ((Odd.design.n0 : ℕ) : ℝ) = 58 by norm_num [Odd.design]]; ring) ε hε

end
end D58
end CatalanMeasure.GenD
